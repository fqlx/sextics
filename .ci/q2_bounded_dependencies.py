"""Sequential, source-keyed development compilation; never acceptance."""
import hashlib, json, os, pathlib, re, resource, runpy, shutil, signal, subprocess, sys, time
import yaml
ROOT = pathlib.Path.cwd()
LEAN = ROOT / 'formal/lean'
OUT = ROOT / 'compile-receipt'
CACHE = ROOT / 'q2-object-cache'
OBJ = LEAN / '.lake/build/lib/lean'
for p in [OUT, CACHE, OBJ, LEAN / 'Proposal']:
    p.mkdir(parents=True, exist_ok=True)
TARGETS = ['Proposal.GeometricFirstOrderNonemptyFlatCurve']
PINS = 'lean4:4.33.1;mathlib:0df444a360eaa60ab8c11dca51a86af692955474;direct-j1-v1'
def digest(b): return hashlib.sha256(b).hexdigest()
def save(p, v):
    p.write_text(json.dumps(v, indent=2) + '\n')
def clean(text):
    # Preserve line boundaries; remove nested comments and string literals.
    out=[]; i=0; depth=0; string=False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth+=1; out.extend('  '); i+=2
            elif text.startswith('-/', i): depth-=1; out.extend('  '); i+=2
            else: out.append('\n' if text[i]=='\n' else ' '); i+=1
        elif string:
            if text[i]=='\\' and i+1 < len(text): out.extend('  '); i+=2
            elif text[i]=='"': string=False; out.append(' '); i+=1
            else: out.append('\n' if text[i]=='\n' else ' '); i+=1
        elif text.startswith('/-', i): depth=1; out.extend('  '); i+=2
        elif text.startswith('--', i):
            j=text.find('\n',i); j=len(text) if j<0 else j
            out.extend(' '*(j-i)); i=j
        elif text[i]=='"': string=True; out.append(' '); i+=1
        else: out.append(text[i]); i+=1
    if depth or string: raise ValueError('unclosed comment or string')
    return ''.join(out)
import_re=re.compile(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([A-Za-z][A-Za-z0-9_.]*)', re.M)
checker=runpy.run_path(str(ROOT/'scripts/proposals/check.py'))
instance=yaml.safe_load((ROOT/'data/cycle-q2/instance.rec').read_text())
(LEAN/'HodgeTarget.lean').write_text(checker['target_source'](instance))
modules={}; order=[]; visiting=set(); external=set()
def source(name):
    if name.startswith('Proposal.'):
        return ROOT/'data/cycle-q2'/('/'.join(name.split('.')[1:])+'.lean')
    return LEAN/(name.replace('.','/')+'.lean')
def visit(name):
    if name in modules: return
    if name in visiting: raise ValueError('import cycle at '+name)
    p=source(name)
    if not p.exists():
        if name.startswith(('Proposal.','HodgeComputer.','HodgeTestbed.')) or name=='HodgeTarget':
            raise FileNotFoundError(str(p))
        external.add(name); return
    visiting.add(name)
    b=p.read_bytes(); text=clean(b.decode())
    deps=list(dict.fromkeys(import_re.findall(text)))
    for d in deps: visit(d)
    admissions=re.findall(r'\b(?:sorry|admit|sorryAx)\b|^\s*(?:private\s+)?axiom\s+\S+',text,re.M)
    info={'source':str(p.relative_to(ROOT)), 'source_sha256':digest(b), 'bytes':len(b), 'imports':deps, 'admission_tokens':admissions}
    dep_keys=[(d,modules[d]['key'] if d in modules else 'pinned-external') for d in deps]
    info['key']=digest(json.dumps([PINS, name, info['source_sha256'], dep_keys],sort_keys=True).encode())
    modules[name]=info; order.append(name); visiting.remove(name)
    if name.startswith('Proposal.'):
        dest=LEAN/(name.replace('.','/')+'.lean'); dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(b)
for t in TARGETS: visit(t)
plan={'targets':TARGETS,'pins':PINS,'order':order,'modules':modules,'external':sorted(external)}
save(OUT/'dependency-plan.json',plan)
(OUT/'mathlib-roots.txt').write_text(' '.join(x for x in sorted(external) if x=='Mathlib' or x.startswith('Mathlib.'))+'\n')
print('Required local modules:',len(order),'external imports:',len(external),flush=True)
print('First modules:', ', '.join(order[:12]),flush=True)
if sys.argv[1:]==['plan']: sys.exit(0)
manifest_path=CACHE/'manifest.json'
manifest=json.loads(manifest_path.read_text()) if manifest_path.exists() else {}
results=[]; started=time.monotonic(); count=0
BUDGET=int(os.environ.get('Q2_BATCH_SECONDS','420'))
CAP=int(os.environ.get('Q2_BATCH_MODULES','60'))
PER_MODULE=int(os.environ.get('Q2_MODULE_SECONDS','90'))
def report(status, next_module=None):
    save(OUT/'results.json',{'scope':'development compilation only; not protected acceptance or independent kernel replay','status':status,'next_module':next_module,'targets':TARGETS,'results':results,'required_modules':len(order),'remaining':[x for x in order if x not in {r['module'] for r in results}]})
def usage(pgid):
    rss=0
    for e in pathlib.Path('/proc').iterdir():
        if not e.name.isdigit(): continue
        try:
            if os.getpgid(int(e.name))!=pgid: continue
            for l in (e/'status').read_text().splitlines():
                if l.startswith('VmRSS:'): rss+=int(l.split()[1])
        except (OSError,ValueError): pass
    available=next(int(l.split()[1]) for l in pathlib.Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:'))
    return rss,available
for name in order:
    info=modules[name]; rel=pathlib.Path(name.replace('.','/'))
    entry=manifest.get(name)
    reusable=entry and entry.get('key')==info['key'] and entry.get('files')
    if reusable:
        reusable=all((CACHE/f).is_file() and digest((CACHE/f).read_bytes())==sha for f,sha in entry['files'].items())
    if reusable:
        for f in entry['files']:
            dest=OBJ/f; dest.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(CACHE/f,dest)
        results.append({'module':name,'status':'reused-hash-verified','key':info['key']}); continue
    if info['admission_tokens']:
        report('blocked-admission',name); print('Refusing admitted helper:',name,info['admission_tokens']); sys.exit(1)
    if count>=CAP or time.monotonic()-started>=BUDGET:
        report('checkpoint-budget',name); print('Batch checkpoint at',name,flush=True); sys.exit(2)
    output=OBJ/rel.with_suffix('.olean'); output.parent.mkdir(parents=True,exist_ok=True)
    for ext in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
        output.with_suffix(ext).unlink(missing_ok=True)
    cmd=['lake','env','lean','-j1','-M5120','-DmaxHeartbeats=0','-o',str(output.relative_to(LEAN)),str(rel.with_suffix('.lean'))]
    env=dict(os.environ); env['LEAN_PATH']=str(OBJ)+(os.pathsep+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    start=time.monotonic(); peak=0; stop=None
    log_path=OUT/(name.replace('.','_')+'.log')
    print('CHECK',name,flush=True)
    with log_path.open('w') as log:
        log.write('COMMAND: '+' '.join(cmd)+'\n'); log.flush()
        def limits(): resource.setrlimit(resource.RLIMIT_CPU,(PER_MODULE,PER_MODULE+5))
        p=subprocess.Popen(cmd,cwd=LEAN,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
        while p.poll() is None:
            rss,available=usage(p.pid); peak=max(peak,rss)
            if rss>6144*1024: stop='resident-memory ceiling'
            elif available<1536*1024: stop='available-memory reserve'
            elif time.monotonic()-start>PER_MODULE: stop='single-module deadline'
            if stop:
                try: os.killpg(p.pid,signal.SIGKILL)
                except ProcessLookupError: pass
                p.wait(); log.write('\nSTOP: '+stop+'\n'); break
            time.sleep(.15)
        code=124 if stop else p.wait()
    row={'module':name,'returncode':code,'seconds':round(time.monotonic()-start,3),'peak_group_rss_kib':peak,'guard_stop':stop,'source_sha256':info['source_sha256'],'key':info['key'],'object_exists':output.exists()}
    results.append(row); count+=1
    print(log_path.read_text()[-16000:],flush=True)
    if code or not output.exists():
        report('compiler-failure' if not stop else 'resource-stop',name); sys.exit(1)
    # Reusable objects are recorded only after a clean exit, never from a failed attempt.
    files={}
    for ext in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
        f=output.with_suffix(ext)
        if f.exists():
            r=str(f.relative_to(OBJ)); dest=CACHE/r; dest.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(f,dest); files[r]=digest(f.read_bytes())
    manifest[name]={'key':info['key'],'source_sha256':info['source_sha256'],'files':files,'run_id':os.environ.get('GITHUB_RUN_ID'),'seconds':row['seconds']}
    save(manifest_path,manifest); report('in-progress')
report('all-targets-compiled')
print('All requested targets compiled. This is not a proof of the protected certificate.',flush=True)
