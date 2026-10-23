import sympy as s,json
from pathlib import Path
C,n=s.symbols('C n');d=json.loads(Path(__file__).with_name('infinity-syzygy-normalized.json').read_text());cs=[s.sympify(x,locals={'C':C})for x in d['S_low_to_high']];Delta=4*C**6-729
# S* Delta² acting C^n: exact logarithmic-derivative powers avoid assumptions.
res=0
for j,c in enumerate(cs):
 a=s.expand(s.cancel(c*Delta**2))
 for term in s.Add.make_args(a):
  power=term.as_powers_dict().get(C,0);coef=s.cancel(term/C**power)
  res+=(-1)**j*coef*s.prod(n+power-i for i in range(j))*C**(power-j)
res=s.factor(res)
print('relative expression',res)
first=s.factor(s.expand(res).coeff(C,2));second=s.factor(s.expand(res).coeff(C,-4));print('first',first,'second',second)
assert s.expand(res-first*C**2-second*C**-4)==0
Path(__file__).with_name('syzygy-euler.json').write_text(json.dumps({'meaning':'S*(Delta² C^n)=C^(n+2)first(n)+C^(n−4)second(n)','first':str(first),'second':str(second)},indent=2)+'\n')
