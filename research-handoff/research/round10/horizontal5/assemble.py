#!/usr/bin/env python3
"""Assemble the properrank3 plus horizontalresidue2 connection and audit it."""
import argparse,json,pickle,time,hashlib
from pathlib import Path
from native_rf import RF,zero,flatness,ctx
HERE=Path(__file__).resolve().parent
PROPER=Path('/workspace/research/round9/cyclic_full/global_eta_frame.pickle')

def main(args):
    start=time.time();proper=pickle.load(open(PROPER,'rb'));boundary=pickle.load(open(args.boundary,'rb'))
    raw=boundary.get('connection_boundary',boundary.get('boundary_connection',boundary.get('connection')))
    if raw is None:raise KeyError('need boundary_connection or connection')
    con={};residue=pickle.load(open(HERE/'residue_connection.pickle','rb'))
    for v in ('L','r','x','s'):
        N=[[RF(0) for _ in range(5)] for _ in range(5)]
        if v!='s':
            for i in range(3):
                for j in range(3):N[i][j]=RF(proper['connection'][v][i][j])
        rows=raw[v]
        if len(rows)==5:rows=rows[3:]
        assert len(rows)==2 and all(len(row)==5 for row in rows)
        for i in range(2):
            for j in range(5):N[i+3][j]=RF(rows[i][j])
        for i in range(2):
            for j in range(2):
                assert not (N[i+3][j+3]-RF(residue['connection'][v][i][j])),('residue connection mismatch',v,i,j)
        con[v]=N
    packet={'variables':('L','r','x','s'),'curve':proper['curve'],'proper_basis':proper['basis'],'proper_basis_pole_orders':[1,1,2],
        'boundary_basis':('Res(h^4 Omega/((t-s h^2) C))','Res(W^3 h Omega/((t-s h^2) C))'),
        'connection':{v:[[z.json() for z in row] for row in M] for v,M in con.items()},
        'convention':'rowbasis: partial_j beta=N_j beta +exact; coefficientcolumns partial_j+N_j^T',
        'independent_residue_connection_exact':True,'proper_source_embedding':'Sproper in first3; last2zero',
        'theta_projection':residue['theta_projection'],'theta_residue_coefficient_horizontal_exact':residue['theta_residue_coefficient_horizontal_exact'],'theta_proper_derivative':residue['theta_proper_derivative'],
        'input_sha256':{str(PROPER):hashlib.sha256(PROPER.read_bytes()).hexdigest(),args.boundary:hashlib.sha256(Path(args.boundary).read_bytes()).hexdigest()},
        'exact_curvature':None}
    output=HERE/args.output;pickle.dump(packet,open(str(output)+'.pickle','wb'))
    print('ASSEMBLED_AND_RESIDUES_MATCH',time.time()-start,flush=True)
    checks=flatness(con);assert not any(checks.values()),checks
    packet['exact_curvature']=checks;packet['seconds']=time.time()-start;pickle.dump(packet,open(str(output)+'.pickle','wb'))
    denoms={}
    for v,M in con.items():
        D=ctx.constant(1)
        for row in M:
            for z in row:D*=z.d//D.gcd(z.d)
        denoms[v]={'degrees':[int(x) for x in D.degrees()],'terms':len(D),'factorization':[{'factor':str(f),'exponent':int(m)} for f,m in D.factor()[1]]}
    summary={k:v for k,v in packet.items() if k not in ('curve','proper_basis','connection')};summary['denominators']=denoms
    Path(str(output)+'.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary,indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('boundary');ap.add_argument('--output',default='rank5_connection');main(ap.parse_args())
