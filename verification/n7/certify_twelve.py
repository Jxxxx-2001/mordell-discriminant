"""Exact dyadic interval certificates; global completeness is a cited external theorem.

No image coordinates or floating point residuals are used as proof. Rounded
midpoints and inverse-Jacobian approximations are merely input to exact checks.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,sys,hashlib,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'friedman_full_audit_20261023/deps'))
PREC=220;SCALE=1<<PREC;MIDPREC=180;R=Q(1,1<<80)
class I:
    """Closed intervals on a fixed dyadic lattice, outward rounded using integers."""
    def __init__(self,a=0,b=None,raw=False):
        if raw:self.a,self.b=int(a),int(b)
        else:
            a=Q(a)*SCALE;b=Q(a if b is None else Q(b)*SCALE)
            self.a=a.numerator//a.denominator
            self.b=-((-b.numerator)//b.denominator)
        assert self.a<=self.b
    def __add__(self,o):
        o=asI(o);return I(self.a+o.a,self.b+o.b,True)
    __radd__=__add__
    def __neg__(self):return I(-self.b,-self.a,True)
    def __sub__(self,o):return self+-asI(o)
    def __rsub__(self,o):return asI(o)+-self
    def __mul__(self,o):
        o=asI(o);v=[self.a*o.a,self.a*o.b,self.b*o.a,self.b*o.b]
        return I(min(v)//SCALE,-((-max(v))//SCALE),True)
    __rmul__=__mul__
    def __truediv__(self,o):
        o=asI(o);assert not o.a<=0<=o.b
        return self*I((SCALE*SCALE)//o.b,-((-SCALE*SCALE)//o.a),True)
    def square(self):
        lo=0 if self.a<=0<=self.b else min(self.a*self.a,self.b*self.b)
        hi=max(self.a*self.a,self.b*self.b)
        return I(lo//SCALE,-((-hi)//SCALE),True)
    def absup(self):return Q(max(abs(self.a),abs(self.b)),SCALE)
    def bounds(self):return [str(Q(self.a,SCALE)),str(Q(self.b,SCALE))]
def asI(v):return v if isinstance(v,I)else I(v)
KEEP=[j for j in range(14)if j!=1]
def full(x):
    z=[I(0)for j in range(14)]
    for j,v in zip(KEEP,x):z[j]=asI(v)
    return z
def fj(x,need_jac=True):
    z=full(x);F=[-3*v for v in z]
    J=[[I(-3 if i==j else 0)for j in range(14)]for i in range(14)]
    distances=[]
    for i in range(7):
        for j in range(i):
            v=[z[2*i+k]-z[2*j+k]for k in range(2)]
            d=v[0].square()+v[1].square();assert d.a>0
            distances.append(d)
            for k in range(2):F[2*i+k]+=v[k]/d;F[2*j+k]-=v[k]/d
            if need_jac:
                for a in range(2):
                    for b in range(2):
                        vv=v[a].square()if a==b else v[a]*v[b]
                        A=I(int(a==b))/d-2*vv/d.square()
                        J[2*i+a][2*i+b]+=A;J[2*j+a][2*j+b]+=A
                        J[2*i+a][2*j+b]-=A;J[2*j+a][2*i+b]-=A
    return [F[i]for i in KEEP],[[J[i][j]for j in KEEP]for i in KEEP],distances
def rounded(v):return Q(int(mp.nint(v*(1<<MIDPREC))),1<<MIDPREC)
def bound_1000(v):
    return [str(Q((v.a*1000)//SCALE,1000)),str(Q(-((-v.b*1000)//SCALE),1000))]
start=time.time()
inputs=ROOT/'interval_certificate_inputs.json'
if '--prepare' in sys.argv:
    import mpmath as mp
    mp.mp.dps=100
    seeds=json.loads((ROOT/'twelve_seeds_and_roots.json').read_text())
    prepared=[]
    for row in seeds:
        if row['index']in [7,8]:continue # exact centered hexagon and exact heptagon
        m=[rounded(mp.mpf(v))for v in row['solution_100digits']]
        F,J,ds=fj([I(v)for v in m])
        mat=mp.matrix([[mp.mpf(v.a+v.b)/(2*SCALE)for v in r]for r in J])
        inv=mat**-1
        C=[[rounded(inv[i,j])for j in range(13)]for i in range(13)]
        prepared.append({'index':row['index'],'midpoint':list(map(str,m)),'C':[[str(v)for v in r]for r in C]})
    inputs.write_text(json.dumps(prepared,indent=2))
prepared=json.loads(inputs.read_text());assert len(prepared)==10
proofs=[]
for row in prepared:
    m=list(map(Q,row['midpoint']));C=[list(map(Q,r))for r in row['C']]
    X=[I(v-R,v+R)for v in m];assert X[0].a>0
    Fm,_,_=fj([I(v)for v in m],False)
    _,JX,ds=fj(X)
    residual=max(sum((I(C[i][k])*Fm[k]for k in range(13)),I()).absup()for i in range(13))
    A=[[I(int(i==j))-sum((I(C[i][k])*JX[k][j]for k in range(13)),I())for j in range(13)]for i in range(13)]
    lipschitz=max(sum(v.absup()for v in r)for r in A)
    assert residual<R/4 and lipschitz<Q(1,4)
    delta=I(1)
    for d in ds:delta=delta*d
    assert delta.b<7**7*SCALE
    proofs.append({'index':row['index'],'radius':str(R),'residual_bound':str(residual),'lipschitz_bound':str(lipschitz),'self_mapping_strict':True,'contraction_strict':True,'no_collisions':True,'anchor_x_positive':True,'delta_interval':delta.bounds(),'delta_interval_readable':bound_1000(delta),'below_regular_heptagon':True})
    print(row['index'],'certified',bound_1000(delta),'residual/r',float(residual/R),'L',float(lipschitz),flush=True)
# Exact examples supply the two remaining inequivalent stationary orbits.
C7=Q(7**21,6**15);assert C7>7**7
all_values=[(Q(r['delta_interval'][0]),Q(r['delta_interval'][1]),r['index'])for r in proofs]
all_values += [(Q(7**7),Q(7**7),'regular_heptagon'),(C7,C7,'centered_regular_hexagon')]
all_values.sort()
assert len(all_values)==12
assert all(all_values[j][1]<all_values[j+1][0]for j in range(11))
# The published classification is an external mathematical premise, not a local PDF check.
source=ROOT.parent/'sources/fs12_hal.pdf'
expected_classification_sha256='d0bad7a5027d2072f2f20626442fe2b6e33310b13c4ceb57f1c62651df681de8'
if source.exists():
    if hashlib.sha256(source.read_bytes()).hexdigest()!=expected_classification_sha256:
        raise RuntimeError('Unexpected classification source PDF.')
result={'arithmetic':'integer dyadic interval arithmetic with outward rounding','precision_bits':PREC,'midpoint_bits':MIDPREC,'global_completeness_source':{'authors':'Jean-Charles Faugere and Jules Svartz','year':2012,'doi':'10.1145/2442829.2442856','local_sha256':expected_classification_sha256,'local_source_file_checked':source.exists(),'location':'Section 5.7 and Appendix Figure 4; symmetries Sections 5.2-5.5','statement_used':'Exactly twelve physical seven-vortex relative equilibria modulo rotation, reflection and relabeling, after fixing the scale.','independently_recomputed':False},'certified_additional_orbits':proofs,'explicit_orbits':{'regular_heptagon':str(7**7),'centered_regular_hexagon':str(C7)},'twelve_distinct_orbits':True,'all_other_orbits_below_candidate':True,'conclusion_scope':'Global theorem using the published completeness classification as an external premise; exact independent objective comparison.','seconds':time.time()-start}
(ROOT/'classification_based_certificate.json').write_text(json.dumps(result,indent=2))
print('ALL TWELVE DISTINCT AND ORDERED; GLOBAL COMPLETENESS USES CITED CLASSIFICATION',time.time()-start,flush=True)
