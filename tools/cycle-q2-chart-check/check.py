#!/usr/bin/env python3
"""Development helper check. Never emits a certificate acceptance record.

Copies the exact local source dependency closure to a fresh Proposal layout,
compiles with the pinned toolchain, replays every successful local module, and
audits named public entry points. No admitted dependency is substituted.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "formal/lean"
SOURCE = ROOT / "data/cycle-q2"
OUT = ROOT / "chart-check-receipts"
WORK = LEAN / ".chart-check"
ROOTS = ["GeometricDegreeOneCech", "GeometricAffineCurveCharts", "GeometricAdjunctionOverlap", "GeometricResidueFrames", "GeometricDehomogenization", "GeometricCoordinateOverlap"]
AUDIT = {
 "GeometricCurveCoordinates": ["CycleQ2NormalConnecting.ambientCurveMap_g1", "CycleQ2NormalConnecting.ambientCurveMap_g2"],
 "GeometricDegreeOneCech": ["CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing", "CycleQ2GeometricProjectiveCurve.degreeNineCechClass"],
 "GeometricAffineCurveCharts": ["CycleQ2GeometricAffineCurveCharts.smoothPresentation", "CycleQ2GeometricAffineCurveCharts.actual_chart_kaehler_free", "CycleQ2GeometricAffineCurveCharts.jacobianPatch_kaehler_rank"],
 "GeometricAdjunctionOverlap": ["CycleQ2GeometricAdjunctionOverlap.conormal_change_on_curve", "CycleQ2GeometricAdjunctionOverlap.oriented_adjunction_transition", "CycleQ2GeometricAdjunctionOverlap.firstCubic_gradient"],
 "GeometricResidueFrames": ["CycleQ2GeometricResidueFrames.local_residue_eq", "CycleQ2GeometricResidueFrames.coordinate_differential_change", "CycleQ2GeometricResidueFrames.first_equations_give_relations"],
 "GeometricDehomogenization": ["CycleQ2GeometricDehomogenization.coordinateRingEquiv", "CycleQ2GeometricDehomogenization.firstCoordinateRingEquiv", "CycleQ2GeometricDehomogenization.secondCoordinateRingEquiv"],
 "GeometricCoordinateOverlap": ["CycleQ2GeometricCoordinateOverlap.transitionUnit"]
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
receipt = {"scope":"HELPERS_ONLY_NOT_PROTECTED_CERTIFICATE", "certificate_checked":False, "commit":os.environ.get("GITHUB_SHA"), "modules":{}, "commands":[]}


def strip_comments(text: str) -> str:
    out=[]; i=0; depth=0; string=False
    while i < len(text):
        if depth:
            if text.startswith("/-", i): depth+=1; i+=2
            elif text.startswith("-/", i): depth-=1; i+=2
            else:
                if text[i]=='\n': out.append('\n')
                i+=1
        elif string:
            if text[i]=='\\': i+=2
            elif text[i]=='"': string=False; out.append('"'); i+=1
            else:
                if text[i]=='\n': out.append('\n')
                i+=1
        elif text.startswith("/-", i): depth=1; out.append(' '); i+=2
        elif text.startswith("--", i):
            j=text.find('\n', i); i=len(text) if j<0 else j
        elif text[i]=='"': string=True; out.append('"'); i+=1
        else: out.append(text[i]); i+=1
    if depth or string: raise ValueError("Unclosed comment or string")
    return ''.join(out)


def save():
    OUT.mkdir(exist_ok=True)
    (OUT / "receipt.json").write_text(json.dumps(receipt, indent=2)+'\n')


def run(label, args, *, cwd=LEAN, env=None, timeout=600):
    print(label+": starting", flush=True)
    started=time.monotonic(); log=OUT / (label+".log")
    with log.open('w') as f:
        try:
            p=subprocess.run(args, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT, timeout=timeout)
            rc=p.returncode
        except subprocess.TimeoutExpired:
            rc=124; f.write("\nTIMEOUT\n")
    text=log.read_text(errors='replace')
    receipt['commands'].append({'label':label,'argv':list(map(str,args)),'returncode':rc,'seconds':round(time.monotonic()-started,3)})
    save()
    print(label+f": exit {rc}", flush=True)
    if rc: print(text[-18000:], flush=True)
    return rc,text


def main():
    OUT.mkdir(exist_ok=True)
    if WORK.exists(): shutil.rmtree(WORK)
    (WORK/'Proposal').mkdir(parents=True)
    version=subprocess.check_output(['lake','env','lean','--version'],cwd=LEAN,text=True).strip()
    if 'version 4.33.1,' not in version: raise RuntimeError('Wrong compiler: '+version)
    manifest=json.loads((LEAN/'lake-manifest.json').read_text())
    mathlib=next(p for p in manifest['packages'] if p['name']=='mathlib')
    if mathlib['rev']!='0df444a360eaa60ab8c11dca51a86af692955474': raise RuntimeError('Mathlib pin changed')
    receipt['version']=version; receipt['mathlib']=mathlib['rev']
    prefix=Path(subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=LEAN,text=True).strip())
    compiler=prefix/'bin/lean'; checker=prefix/'bin/leanchecker'
    if not checker.is_file(): raise RuntimeError('Independent kernel checker missing')
    lp=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=LEAN,text=True).strip()
    paths=[str(Path(p) if Path(p).is_absolute() else (LEAN/p).resolve()) for p in lp.split(os.pathsep) if p]
    env=os.environ.copy(); env['LEAN_PATH']=os.pathsep.join([str(WORK)]+paths)
    deps={}; order=[]; visiting=set(); texts={}
    def visit(name):
        if name in deps: return
        if name in visiting: raise RuntimeError('Import cycle '+name)
        visiting.add(name)
        text=(SOURCE/(name+'.lean')).read_text(); clean=strip_comments(text)
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',clean): raise RuntimeError('Forbidden admission/execution in '+name)
        imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',clean,re.M)
        local=[x.split('.',1)[1] for x in imports if x.startswith('Proposal.')]
        for d in local: visit(d)
        visiting.remove(name); deps[name]=local; texts[name]=text; order.append(name)
    roots=[n for n in ROOTS if (SOURCE/(n+'.lean')).is_file()]
    for name in roots: visit(name)
    receipt['roots']=roots; receipt['order']=order
    for name in order:
        text=texts[name]; (WORK/'Proposal'/(name+'.lean')).write_text(text)
        receipt['modules'][name]={'sha256':hashlib.sha256(text.encode()).hexdigest(),'compile':False,'replay':False,'audit':None}
    save()
    for name in order:
        record=receipt['modules'][name]
        if any(not receipt['modules'][d]['compile'] for d in deps[name]):
            record['blocked_by']=[d for d in deps[name] if not receipt['modules'][d]['compile']]; save(); continue
        rc,text=run('compile-'+name,[str(compiler),'-j','1','-M','5120','-o','Proposal/'+name+'.olean','Proposal/'+name+'.lean'],cwd=WORK,env=env)
        record['compile']=rc==0 and 'declaration uses \'sorry\'' not in text and 'sorryAx' not in text
        save()
        if not record['compile']: continue
        rc,_=run('replay-'+name,[str(checker),'--verbose','Proposal.'+name],cwd=WORK,env=env)
        record['replay']=rc==0
        entries=AUDIT.get(name,[])
        if entries:
            (WORK/'Audit.lean').write_text('import Proposal.'+name+'\n'+'\n'.join('#print axioms '+d for d in entries)+'\n')
            rc,txt=run('axioms-'+name,[str(compiler),'-j','1','-M','5120','Audit.lean'],cwd=WORK,env=env)
            ax=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',txt)
            free=len(re.findall(r'does not depend on any axioms',txt))
            used={a.strip() for group in ax for a in group.split(',') if a.strip()}
            record['audit']={'entries':entries,'axioms':sorted(used),'passed':rc==0 and used<=ALLOWED and len(ax)+free==len(entries)}
        save()
    receipt['all_selected_helpers_passed']=all(v['compile'] and v['replay'] and (v['audit'] is None or v['audit']['passed']) for v in receipt['modules'].values())
    save(); print(json.dumps(receipt,indent=2),flush=True)
    return 0 if receipt['all_selected_helpers_passed'] else 1

if __name__=='__main__':
    try: code=main()
    except Exception as e:
        receipt['error']=str(e); save(); raise
    raise SystemExit(code)
