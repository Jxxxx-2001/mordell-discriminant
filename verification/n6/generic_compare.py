"""Exact root isolation and rational interval comparisons for all six generic branches."""
from pathlib import Path
import sys,json
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'friedman_full_audit_20261023/deps'))
sys.path.insert(0,str(ROOT.parent/'friedman_full_audit_20261023'))
import sympy as s
from interval_check import I
x=s.Symbol('x')
C=F(470184984576,9765625)
rows=json.loads((ROOT/'generic_branch_checks.json').read_text())
def poly(cs):return s.Poly(sum(s.Rational(v)*x**j for j,v in enumerate(cs)),x)
def horner(cs,box):
    result=I(0)
    for a in reversed(cs):result=result*box+I(a)
    return result
out=[]
for row in rows:
    p=poly(row['Ay_minpoly'])
    intervals=s.polys.polytools.intervals(p,eps=s.Rational(1,10**70))
    rootrows=[]
    for (lo,hi),mult in intervals:
        box=I(str(lo),str(hi));assert mult==1
        val=horner(row['objective_in_Ay'],box)
        rr={'Ay_interval':box.json(),'multiplicity':mult,'objective_square_interval':val.json()}
        if box.b<0:rr['decision']='excluded: Ay must be positive'
        elif box.a>225:rr['decision']='excluded: Ay <= 225 from q >= |sum w_i^2| = 2'
        elif box.a==box.b==225:
            bval=horner(row['B_from_Ay'],box)
            assert bval.a>0
            rr['B_interval']=bval.json()
            rr['decision']='excluded: Ay=225 forces all roots imaginary, hence B=b^2<=0'
        elif box.a>0:
            if 'B_quadratic_discriminant_in_Ay' in row:
                disc=horner(row['B_quadratic_discriminant_in_Ay'],box)
                rr['B_discriminant_interval']=disc.json()
                if disc.a>0:rr['decision']='excluded: B and dual B distinct real, cannot be complex conjugates'
            if 'decision' not in rr:
                if val.b<6**12:rr['decision']='objective strictly below regular hexagon squared'
                else:rr['decision']='UNRESOLVED'
        else:rr['decision']='UNRESOLVED Ay sign'
        print(row['index'],float((lo+hi)/2),'objective square approx',float((val.a+val.b)/2),rr['decision'],flush=True)
        rootrows.append(rr)
    out.append({'index':row['index'],'Ay_degree':p.degree(),'real_root_count':len(rootrows),'roots':rootrows})
(ROOT/'generic_comparison.json').write_text(json.dumps(out,indent=2))
print('ALL RESOLVED',all('UNRESOLVED' not in r['decision'] for branch in out for r in branch['roots']))
assert all('UNRESOLVED' not in r['decision'] for branch in out for r in branch['roots'])
assert [branch['real_root_count']for branch in out]==[1,1,2,2,3,3]
