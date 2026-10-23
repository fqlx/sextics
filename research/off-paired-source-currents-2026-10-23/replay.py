"""Verify frozen bytes, then replay in a NEW disposable directory."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,time
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--verify-only',action='store_true');parser.add_argument('--output',type=Path)
 args=parser.parse_args();root=Path(__file__).resolve().parent
 manifest=json.loads((root/'manifest.json').read_text())
 for name,entry in manifest['files'].items():
  assert hashlib.sha256((root/name).read_bytes()).hexdigest()==entry['sha256'],name
 print('PASS',len(manifest['files']),'frozen hashes',flush=True)
 if args.verify_only:return
 assert args.output,'supply --output pointing to a new directory'
 out=args.output.resolve();assert not out.exists(),'output must not already exist'
 assert not out.is_relative_to(root),'output must be outside the frozen snapshot'
 shutil.copytree(root,out);logs=out/'replay-logs';logs.mkdir();rows=[]
 for name in manifest['replay']['scripts']:
  start=time.monotonic();p=subprocess.run([sys.executable,name],cwd=out,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  (logs/(name.replace('/','__')+'.log')).write_text(p.stdout)
  row={'script':name,'exit_code':p.returncode,'seconds':round(time.monotonic()-start,3)}
  receipt=out/Path(name).with_suffix('.json')
  if p.returncode==0 and receipt.exists():
   q=json.loads(receipt.read_text());row['check_count']=q.get('check_count',len(q.get('checks',{})))
  rows.append(row);print(json.dumps(row),flush=True)
  if p.returncode:
   print(p.stdout);break
 (out/'replay-results.json').write_text(json.dumps(rows,indent=2)+'\n')
 assert len(rows)==len(manifest['replay']['scripts'])and all(q['exit_code']==0 for q in rows)
 print('PASS all partial-identity replays; the target remains UNSOLVED',flush=True)
if __name__=='__main__':main()
