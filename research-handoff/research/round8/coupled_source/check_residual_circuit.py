"""Independent first-IBP residual evaluation using factored native pairs.

This bypasses the second Taylor-jet implementation in direct_source.py.
"""
from pathlib import Path
import json,pickle
from flint import fmpq

HERE=Path(__file__).parent
packet=pickle.loads((HERE/'coordinate_fields.pickle').read_bytes())
report=json.loads((HERE/'source_model.json').read_text())
polys=packet['polynomials']

def evaluate(poly,point,derivative=None):
    out=fmpq(0)
    for ex,c in poly.items():
        ex=list(ex);value=fmpq(c)
        if derivative is not None:
            if not ex[derivative]:continue
            value*=ex[derivative];ex[derivative]-=1
        for p,n in zip(point,ex):value*=p**n
        out+=value
    return out

records=[]
for rec in report['exact_jet_points']:
    point=list(map(fmpq,rec['point']))
    values={name:evaluate(p,point)for name,p in polys.items()}
    grad={name:[evaluate(p,point,i)for i in range(3)]for name,p in polys.items()}
    fields={name:[evaluate(pair['numerator'],point)/evaluate(pair['denominator'],point)for pair in pairs]for name,pairs in packet['fields'].items()}
    logH=[(3/point[0] if i==0 else 0)-(5/point[1]if i==1 else 0)
          +fmpq(13,3)*grad['A'][i]/values['A']-4*grad['E'][i]/values['E']
          -fmpq(4,3)*grad['S'][i]/values['S']-grad['Delta47'][i]/values['Delta47']for i in range(3)]
    phi={name:sum(z*g for z,g in zip(vec,logH))for name,vec in fields.items()}
    z=values['B']*values['R']/values['A']
    gradz=[(grad['B'][i]*values['R']+values['B']*grad['R'][i])/values['A']-z*grad['A'][i]/values['A']for i in range(3)]
    Vz={name:sum(x*y for x,y in zip(vec,gradz))for name,vec in fields.items()}
    fT=3*point[0]**3*values['S']/(2*values['B']**3*values['A'])
    Rone=phi['r']
    Rzero=-2*Vz['r']-2*z*phi['r']+2*z*Vz['L']+z*z*phi['L']
    assert fT*Rone==fmpq(rec['R_T_divided_by_rho'])
    assert fT*Rzero==fmpq(rec['R_0_divided_by_rho'])
    records.append({'point':rec['point'],'z':str(z),'fT':str(fT),
                    'phi':{name:str(x)for name,x in phi.items()},
                    'V_z':{name:str(x)for name,x in Vz.items()},
                    'normalized_hol_source':[str(Rzero),str(Rone),'0'],
                    'independent_jet_residual_match':True})
(HERE/'residual_circuit_audit.json').write_text(json.dumps({'method':'Factored polynomial dictionaries and reduced coordinate-field pairs, independent of the second Taylor jets','records':records},indent=2)+'\n')
print('All three factored-circuit residual checks passed.')
