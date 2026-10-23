"""Exact finite-monodromy connection for the physical cubic-ray quotient.

This is a complete trace-zero function-field current interface, not the
endpoint compact-cohomology truncation. No primitive is asserted.
"""
import json
from pathlib import Path
import sympy as S

s,H,B,C=S.symbols('s H B C');params=[H,B,C]
f=C*s**3+B*s+H;D=4*B**3+27*C*H**2;T=S.diff(f,s)
e=[s,s**2+2*B/(3*C)]
invT=(4*B**2+6*B*C*s**2-9*C*H*s)/D
MH=S.Matrix([[9*C*H,4*B**2],[-6*B*C,18*C*H]])/D
MB=S.Matrix([[2*B**2,-6*B*H],[9*C*H,4*B**2]])/D
MC=S.Matrix([[-(2*B**3+9*C*H**2)/C,2*B**2*H/C],
             [-3*B*H,-2*(2*B**3+9*C*H**2)/C]])/D
matrices=[MH,MB,MC]
source=S.Matrix([-B*(2*B**3-27*C*H**2),-27*B**2*C*H])/D**2
gram=S.Matrix([[-2*B/C,-3*H/C],[-3*H/C,2*B**2/(3*C**2)]])

def reduce(poly):
 return S.Poly(poly,s,domain=S.QQ.frac_field(H,B,C)).rem(S.Poly(f,s,domain=S.QQ.frac_field(H,B,C))).as_expr()

def exact_derivative(poly,v):
 return reduce(S.diff(poly,v)-S.diff(poly,s)*S.diff(f,v)*invT)

def run():
 checks=[]
 def check(name,expr):
  assert S.cancel(expr)==0,(name,S.factor(expr))
  checks.append(name)
 def matrix_check(name,expr):
  for i in range(expr.rows):
   for j in range(expr.cols):check(name+f'[{i},{j}]',expr[i,j])
 check('inverse-fs',reduce(T*invT-1))
 for v,M in zip(params,matrices):
  for j,ej in enumerate(e):
   check('basis-derivative-'+str(v)+'-'+str(j),exact_derivative(ej,v)-sum(M[i,j]*e[i]for i in range(2)))
 for i in range(3):
  for j in range(i+1,3):
   matrix_check('flatness-'+str(params[i])+str(params[j]),
       matrices[j].diff(params[i])-matrices[i].diff(params[j])
       +matrices[i]*matrices[j]-matrices[j]*matrices[i])
 matrix_check('common-scaling',H*MH+B*MB+C*MC)
 matrix_check('root-scaling',3*H*MH+2*B*MB-S.diag(1,2))
 check('source-field',reduce(B*s*invT**3)-sum(source[i]*e[i]for i in range(2)))
 matrix_check('source-second-derivative',source+B/(6*C)*(MH.diff(H)+MH*MH)[:,0])
 for v,M in zip(params,matrices):matrix_check('trace-pairing-'+str(v),gram.diff(v)-M.T*gram-gram*M)
 check('trace-pairing-determinant',gram.det()+D/(3*C**3))
 data={'parameters':['H','B','C'],'field_polynomial':str(f),
       'basis':[str(a)for a in e],'column_convention':'derivative_v e_j=sum_i Mv[i,j] e_i',
       'discriminant_denominator':str(D),'inverse_f_s':str(invT),
       'matrices':{str(v):[[str(S.factor(a))for a in M.row(i)]for i in range(2)]for v,M in zip(params,matrices)},
       'source':[str(S.factor(a))for a in source],
       'source_binding':'B*s/(3*C*s^2+B)^3 = -B/(6*C) d_H^2 s',
       'checks':checks,'check_count':len(checks),
       'status':'exact connection and source; rational trace-zero primitive remains open'}
 Path(__file__).with_name('finite-connection-results.json').write_text(json.dumps(data,indent=2))
 print('Passed',len(checks),'exact identities')

if __name__=='__main__':run()
