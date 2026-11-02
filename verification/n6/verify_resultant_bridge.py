"""Reconstruct the equations from the sextic; compare with frozen exact inputs."""
from pathlib import Path
import json
import sympy as s
from flint import fmpq_mpoly_ctx

root=Path(__file__).resolve().parent
ctx=fmpq_mpoly_ctx.get(('x','Y','T','b','c','d','e'),'lex')
x,Y,T,b,c,d,e=ctx.gens()
p=x**6+x**4+b*x**3+c*x*x+d*x+e
dp=p.derivative('x')
res=p.resultant((Y+T*x)*dp-dp.derivative('x'),'x')
r0=res.subs({'T':0});rt=res.derivative('T').subs({'T':0})
def coeff(poly,j):
    return ctx.from_dict({tuple(0 if i==1 else v for i,v in enumerate(m)):a
                          for m,a in poly.to_dict().items() if m[1]==j})
D=coeff(r0,6)
assert coeff(r0,5)==coeff(rt,5)==0
assert coeff(rt,4)==30*D
eqs=[coeff(rt,3),coeff(rt,2)-12*coeff(r0,4),
     coeff(rt,1)-6*coeff(r0,3),coeff(rt,0)-2*coeff(r0,2)]
raw=json.loads((root/'generic_system.json').read_bytes())
def same(old,new):
    return s.expand(s.sympify(old.replace('^','**'))-
                    s.sympify(str(new).replace('^','**')))==0
assert same(raw['D'],D) and same(raw['R0'],r0)
assert len(raw['equations'])==len(eqs)==4
assert all(same(old,new) for old,new in zip(raw['equations'],eqs))
bs,cs,ds,es,B,k=s.symbols('b c d e B k')
def quotient(poly,odd=False):
    v=s.Poly(s.expand(s.sympify(str(poly).replace('^','**')).subs(ds,bs*k)),bs)
    if odd:
        assert v.nth(0)==0
        v=s.Poly(v.as_expr()/bs,bs)
    assert all(m[0]%2==0 for m,a in v.terms())
    return s.Poly(sum(a*B**(m[0]//2) for m,a in v.terms()),B,cs,k,es).primitive()[1]
frozen=json.loads((root/'quotient_system.json').read_bytes())
assert quotient(D)==s.Poly(s.sympify(frozen['D']),B,cs,k,es)
for j,(new,old) in enumerate(zip(eqs,frozen['equations'])):
    assert quotient(new,j%2==0)==s.Poly(s.sympify(old),B,cs,k,es)
print('Exact resultant and quotient-system reconstruction verified.')
