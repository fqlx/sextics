"""Bounded, resumable compilation of the actual Q2 helper dependency closure.
No acceptance claim, replacement declarations, full-project target or kernel replay.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, re, signal, subprocess, time
import yaml

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / '.q2-build'
SOURCE = WORK / 'source'
OUT = WORK / 'objects'
LOGS = WORK / 'logs'
LEANROOT = ROOT / 'formal/lean'
FOCUS = 'Proposal.GeometricFirstOrderNonemptyFlatCurve'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def write(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(obj, indent=2) + '\n')
    temp.replace(path)


def command(args, cwd=LEANROOT):
    return subprocess.check_output(args, cwd=cwd, text=True, timeout=90).strip()


def prepare():
    for p in (SOURCE, OUT, LOGS):
        p.mkdir(parents=True, exist_ok=True)
    toolchain = (LEANROOT / 'lean-toolchain').read_text().strip()
    assert toolchain == 'leanprover/lean4:v4.33.1', toolchain
    import tomllib
    options = tomllib.loads((LEANROOT / 'lakefile.toml').read_text())['leanOptions']
    assert options == {'maxHeartbeats': 0}, options
    manifest = json.loads((LEANROOT / 'lake-manifest.json').read_text())
    assert next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib') == '0df444a360eaa60ab8c11dca51a86af692955474'
    solution = (ROOT / 'data/cycle-q2/Solution.lean').read_bytes()
    solution_blob = hashlib.sha1(b'blob ' + str(len(solution)).encode() + b'\0' + solution).hexdigest()
    assert solution_blob == '3422e79fc263c2b098c61ce9a9577e303aefc009', solution_blob
    spec = importlib.util.spec_from_file_location('actual_renderer', ROOT / 'scripts/proposals/check.py')
    renderer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(renderer)
    instance = yaml.safe_load((ROOT / 'data/cycle-q2/instance.rec').read_text())
    generated = {'HodgeTarget': renderer.target_source(instance)}
    witness = ROOT / 'data/cycle-q2/witness.json'
    if witness.exists():
        generated['HodgeWitness'] = renderer.witness_source(witness.read_bytes())
    order, records, active, external = [], {}, set(), set()

    def visit(name):
        assert re.fullmatch(renderer.NAME, name), name
        if name in records:
            return
        assert name not in active, ('import cycle', name)
        active.add(name)
        if name in generated:
            raw = generated[name].encode()
        elif name.startswith('Proposal.'):
            assert name.count('.') == 1 and name != 'Proposal.Solution', name
            raw = (ROOT / 'data/cycle-q2' / (name.split('.')[1] + '.lean')).read_bytes()
        elif name.startswith(('HodgeComputer', 'HodgeTestbed')):
            raw = (LEANROOT / (name.replace('.', '/') + '.lean')).read_bytes()
        else:
            external.add(name)
            active.remove(name)
            return
        code = renderer.strip_comments(raw.decode())
        assert not re.search(r'\b(sorry|admit)\b', code), ('admission', name)
        deps = []
        for line in code.splitlines():
            match = re.fullmatch(r'\s*(?:(?:public|private|meta)\s+)*import\s+(.+)', line)
            if match:
                for dep in match.group(1).split():
                    visit(dep)
                    if dep in records:
                        deps.append(dep)
        dst = SOURCE / (name.replace('.', '/') + '.lean')
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(raw)
        records[name] = {'source_sha256': sha(raw), 'dependencies': list(dict.fromkeys(deps))}
        order.append(name)
        active.remove(name)

    visit(FOCUS)
    context = sha((LEANROOT / 'lean-toolchain').read_bytes() + (LEANROOT / 'lake-manifest.json').read_bytes() + (LEANROOT / 'lakefile.toml').read_bytes())
    plan = {'focus': FOCUS, 'source_commit': command(['git', 'rev-parse', 'HEAD'], ROOT), 'protected_solution_blob': solution_blob, 'context': context, 'order': order, 'records': records, 'external': sorted(external), 'protected_acceptance': False, 'kernel_replay': False}
    write(WORK / 'plan.json', plan)
    (WORK / 'cache-roots.txt').write_text('\n'.join(sorted(n for n in external if n.startswith(('Mathlib', 'Batteries', 'Aesop', 'Qq')))) + '\n')
    print(json.dumps({'planned_modules': len(order), 'first_modules': order[:30], 'focus': FOCUS, 'protected_solution_blob': solution_blob}), flush=True)
    return plan


def sidecars(obj):
    base = obj.with_suffix('')
    return [p for ext in ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir') if (p := Path(str(base) + ext)).is_file()]


def memory(pgid):
    rss = 0
    for p in Path('/proc').iterdir():
        if p.name.isdigit():
            try:
                if os.getpgid(int(p.name)) == pgid:
                    for line in (p / 'status').read_text().splitlines():
                        if line.startswith('VmRSS:'):
                            rss += int(line.split()[1])
            except (OSError, ValueError):
                pass
    avail = next(int(s.split()[1]) for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:'))
    return rss, avail


def compile_batch(plan, args):
    prefix = Path(command(['lake', 'env', 'lean', '--print-prefix'])).resolve()
    lean = prefix / 'bin/lean'
    version = command([str(lean), '--version'])
    assert 'version 4.33.1,' in version, version
    paths = command(['lake', 'env', 'printenv', 'LEAN_PATH']).split(os.pathsep)
    paths = [str((LEANROOT / p).resolve()) for p in paths if p]
    env = {**os.environ, 'LEAN_PATH': os.pathsep.join([str(OUT)] + paths), 'LEAN_SYSROOT': str(prefix), 'LEAN_NUM_THREADS': '1'}
    cache_path = WORK / 'module-cache.json'
    cache = json.loads(cache_path.read_text()) if cache_path.exists() else {}
    report = {'scope': 'bounded helper compilation only', 'source_commit': plan['source_commit'], 'focus': FOCUS, 'version': version, 'all_selected_compiled': False, 'protected_acceptance': False, 'kernel_replay': False, 'results': []}
    signatures, count, start = {}, 0, time.monotonic()
    context = sha((plan['context'] + version + sha(lean.read_bytes())).encode())
    for name in plan['order']:
        source = SOURCE / (name.replace('.', '/') + '.lean')
        r = plan['records'][name]
        assert sha(source.read_bytes()) == r['source_sha256'], name
        signature = sha(json.dumps([context, r['source_sha256'], [signatures[d] for d in r['dependencies']]]).encode())
        signatures[name] = signature
        obj = OUT / (name.replace('.', '/') + '.olean')
        old = cache.get(name, {})
        files = {str(p.relative_to(WORK)): sha(p.read_bytes()) for p in sidecars(obj)}
        if old.get('signature') == signature and old.get('exit') == 0 and obj.exists() and files == old.get('artifacts'):
            report['results'].append({**old, 'reused': True})
            continue
        retry_interruption = (args.retry_batch_interruption and old.get('stop_reason') == 'batch deadline'
                              and args.module_seconds > old.get('seconds', 0))
        retry_heartbeat_settings = (args.retry_repository_heartbeats == name
                                    and old.get('exit') == 1
                                    and '-DmaxHeartbeats=0' not in old.get('command', []))
        if old.get('signature') == signature and old.get('exit', 0) != 0 and not (retry_interruption or retry_heartbeat_settings):
            report['stop'] = 'unchanged failure; repair before retry'
            report['next'] = name
            write(WORK / 'receipt.json', report)
            return 22
        if count >= args.modules or args.seconds - (time.monotonic() - start) < args.module_seconds:
            report['stop'], report['next'] = 'bounded batch complete', name
            write(WORK / 'receipt.json', report)
            return 20
        obj.parent.mkdir(parents=True, exist_ok=True)
        for p in sidecars(obj):
            p.unlink()
        cmd = [str(lean), '-j1', '-M5120', '-DmaxHeartbeats=0', '-o', str(obj), str(source.relative_to(SOURCE))]
        log = LOGS / (name + '.log')
        row = {'module': name, 'source_sha256': r['source_sha256'], 'signature': signature, 'command': cmd, 'reused': False, 'exit': None, 'artifacts': {}, 'module_deadline_seconds': args.module_seconds,
               'batch_deadline_seconds': args.seconds, 'retry_batch_interruption': retry_interruption,
               'retry_repository_heartbeats': retry_heartbeat_settings,
               'effective_repository_lean_options': {'maxHeartbeats': 0}}
        print('COMPILE ' + name, flush=True)
        begun, peak, reason = time.monotonic(), 0, None
        with log.open('w') as out:
            out.write('COMMAND: ' + ' '.join(cmd) + '\n'); out.flush()
            proc = subprocess.Popen(cmd, cwd=SOURCE, env=env, stdout=out, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                while proc.poll() is None:
                    rss, avail = memory(proc.pid)
                    peak = max(peak, rss)
                    if rss > 6144 * 1024: reason = 'RSS limit'
                    elif avail < 1536 * 1024: reason = 'available memory reserve'
                    elif time.monotonic() - begun > args.module_seconds: reason = 'module deadline'
                    elif time.monotonic() - start > args.seconds: reason = 'batch deadline'
                    if reason:
                        os.killpg(proc.pid, signal.SIGKILL)
                        break
                    time.sleep(.2)
            finally:
                if proc.poll() is None:
                    os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
        row.update({'exit': proc.returncode, 'seconds': round(time.monotonic()-begun, 3), 'peak_rss_kib': peak, 'stop_reason': reason})
        text = log.read_text()
        print(text[-12000:], flush=True)
        if row['exit'] == 0:
            assert obj.exists(), name
            assert not re.search(r'\bsorryAx\b', text), name
            row['artifacts'] = {str(p.relative_to(WORK)): sha(p.read_bytes()) for p in sidecars(obj)}
        cache[name] = row
        report['results'].append(row)
        write(cache_path, cache)
        write(WORK / 'receipt.json', report)
        print(json.dumps({k: row[k] for k in ('module','exit','seconds','peak_rss_kib','stop_reason')}), flush=True)
        if row['exit'] != 0:
            return 1
        count += 1
    report['all_selected_compiled'] = True
    write(WORK / 'receipt.json', report)
    return 0


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--compile', action='store_true')
    p.add_argument('--modules', type=int, default=24)
    p.add_argument('--seconds', type=int, default=240)
    p.add_argument('--module-seconds', type=int, default=90)
    p.add_argument('--retry-batch-interruption', action='store_true')
    p.add_argument('--retry-repository-heartbeats', default=None)
    a = p.parse_args()
    assert 0 < a.modules <= 48 and 0 < a.module_seconds <= 360
    assert a.module_seconds <= a.seconds <= 600
    plan = prepare()
    if a.compile:
        raise SystemExit(compile_batch(plan, a))
