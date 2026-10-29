"""Exact arithmetic in each rational number field of the sextic stationarity system."""
from pathlib import Path
import sys,json,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'friedman_full_audit_20261023/deps'))
import sympy as s
from flint import fmpq_poly as FP, fmpq
B,c,k,e=s.symbols('B c k e')
source=json.loads((ROOT/'generic_triangular.json').read_text())
raw=json.loads((ROOT/'dual_coefficients.json').read_text())
expressions=[s.Poly(s.sympify(v),B,c,k,e)for v in raw['r']]
eqs=[s.Poly(s.sympify(v),B,c,k,e)for v in json.loads((ROOT/'quotient_system.json').read_text())['equations']]
def fp(v):
    p=s.Poly(v,B)
    return FP([fmpq(str(p.nth(j)))for j in range(p.degree()+1)]) if not p.is_zero else FP([])
def serial(p):return [str(a)for a in p]
def expr(p):return sum(s.Rational(str(a))*B**j for j,a in enumerate(p))
out=[]
for index,branch in enumerate(source['branches']):
    start=time.monotonic();P=fp(s.sympify(branch['factor']));N=P.degree()
    maps=[FP([0,1])%P]+[fp(s.sympify(branch['maps'][str(v)]))for v in [c,k,e]]
    cache=[{0:FP([1]),1:m} for m in maps]
    def power(j,n):
        if n not in cache[j]:cache[j][n]=(power(j,n-1)*maps[j])%P
        return cache[j][n]
    def ev(pol):
        r=FP([])
        for mon,co in pol.terms():
            a=FP([fmpq(str(co))])
            for j,n in enumerate(mon):
                if n:a=(a*power(j,n))%P
            r=(r+a)%P
        return r
    def inv(v):
        g,a,h=v.xgcd(P)
        assert g.degree()==0 and g[0]!=0
        return (a/g[0])%P
    rr=list(map(ev,expressions));D=rr[6]
    assert all(ev(v).is_zero()for v in eqs)
    assert (fp(s.sympify(branch['maps']['t']))*maps[0]*D)%P==1
    Ay=rr[4]*inv(D)%P
    tests=[(D*rr[3]**2-rr[4]**3)%P,(D*rr[2]-maps[1]*rr[4]**2)%P,
           (D*rr[1]-maps[2]*rr[4]*rr[3])%P,(D**2*rr[0]-maps[3]*rr[4]**3)%P]
    # Multiplication-generated subfield Q(Ay): its dimension decides whether Ay
    # being real forces B to be real. All entries and ranks are rational.
    powers=[FP([1])]
    for j in range(N):powers.append((powers[-1]*Ay)%P)
    M=s.Matrix([[s.Rational(str(v[j]))for v in powers[:-1]]for j in range(N)])
    rank=M.rank()
    row={'index':index,'degree':N,'factor':branch['factor'],'Ay':serial(Ay),'D':serial(D),
         'dual_identity_zero':[v.is_zero()for v in tests],'Ay_field_degree':rank,
         'original_equations_zero':True,'saturation_verified':True}
    sigmaB=(maps[0]*rr[3]**2*D*inv(rr[4])**3)%P
    def compose(pol,arg):
        result=FP([])
        for co in reversed(list(pol)):result=(result*arg+co)%P
        return result
    assert compose(sigmaB,sigmaB)==maps[0]
    assert compose(Ay,sigmaB)==Ay
    assert compose(maps[1],sigmaB)==(D*rr[2]*inv(rr[4])**2)%P
    assert compose(maps[2],sigmaB)==(D*rr[1]*inv(rr[4]*rr[3]))%P
    assert compose(maps[3],sigmaB)==(D**2*rr[0]*inv(rr[4])**3)%P
    row['dual_involution_verified']=True
    row['sigmaB']=serial(sigmaB)
    H=M[:,:rank]
    def in_subfield(v):
        solution=H.gauss_jordan_solve(s.Matrix([s.Rational(str(v[j]))for j in range(N)]))[0]
        assert len(solution.free_symbols)==0
        return [str(a)for a in solution]
    minco=in_subfield(-powers[rank])+['1']
    row['Ay_minpoly']=minco
    general_obj=(powers[1]**15*D*compose(D,sigmaB)/fmpq(5**30))%P
    row['objective_in_Ay']=in_subfield(general_obj)
    if rank<N:
        row['B_trace_in_Ay']=in_subfield(maps[0]+sigmaB)
        row['B_norm_in_Ay']=in_subfield(maps[0]*sigmaB%P)
        row['B_quadratic_discriminant_in_Ay']=in_subfield(((maps[0]-sigmaB)**2)%P)
    if rank==N:
        coeff=M.inv()*s.Matrix([0,1]+[0]*(N-2)) if N>1 else s.Matrix([s.Rational(str(maps[0][0]))])
        row['B_from_Ay']=[str(v)for v in coeff]
    # For reflection-real branches the target square is Ay^15 D^2/5^30.
    obj=FP([1])
    for j in range(15):obj=obj*Ay%P
    obj=(obj*D*D/fmpq(5**30))%P
    if all(v.is_zero()for v in tests):
        assert sigmaB==maps[0]
        assert obj==general_obj
    row['objective_square_if_real']=serial(obj)
    out.append(row)
    (ROOT/'generic_branch_checks.json').write_text(json.dumps(out,indent=2))
    print('branch',index,'degree',N,'dual',row['dual_identity_zero'],'Ay degree',rank,'seconds',time.monotonic()-start,flush=True)
