from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'friedman_full_audit_20261023/deps'))
import sympy as s
b,c,d,e,B,k,Y=s.symbols('b c d e B k Y')
raw=json.loads((ROOT/'generic_system.json').read_text())
R=s.Poly(s.sympify(raw['R0'].replace('^','**')),Y)
def quotient(v,odd=False):
    P=s.Poly(s.expand(v.subs(d,b*k)),b)
    if odd:
        assert P.nth(0)==0
        P=s.Poly(P.as_expr()/b,b)
    assert all(m[0]%2==0 for m,a in P.terms())
    return s.expand(sum(a*B**(m[0]//2)for m,a in P.terms()))
rc=[quotient(R.nth(j),j in (1,3))for j in range(7)]
(ROOT/'dual_coefficients.json').write_text(json.dumps({'r':list(map(str,rc))},indent=2))
if '--exploratory-full' not in sys.argv:
    print('Exact quotient coefficients saved; full finite-field exploration skipped.')
    raise SystemExit(0)
D=rc[6];a=rc[4];g=rc[3];h=rc[2];f=rc[1];v=rc[0]
# Coefficients r_3 and r_1 before quotient have one factor b.
tests=[D*g**2-a**3,D*h-c*a**2,D*f-k*a*g,D**2*v-e*a**3]
lines='\n'.join('poly T%d=%s;'%(j,str(s.expand(v)).replace('**','^')) for j,v in enumerate(tests))
base=(ROOT/'quotient_fflex.sing').read_text()
base=base[:base.index('ring lexr')]+lines+'\nprint("DUAL NORMAL FORMS");\nreduce(T0,G);reduce(T1,G);reduce(T2,G);reduce(T3,G);\nring lexr=32003,(t,e,k,c,B),lp;\nideal H=fglm(r,G);\nfactorize(H[1]);\nquit;\n'
(ROOT/'quotient_dualff.sing').write_text(base)
(ROOT/'dual_coefficients.json').write_text(json.dumps({'r':list(map(str,rc)), 'tests':list(map(lambda p:str(s.expand(p)),tests))},indent=2))
