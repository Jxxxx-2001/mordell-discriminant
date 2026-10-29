"""Exact rational box exclusions. Box membership of original web points is NOT established."""
from pathlib import Path
from fractions import Fraction as F
import json
ROOT=Path(__file__).resolve().parent
class I:
    def __init__(self,a,b=None): self.a=F(a);self.b=F(a if b is None else b)
    def __add__(self,o):
        o=o if isinstance(o,I) else I(o);return I(self.a+o.a,self.b+o.b)
    __radd__=__add__
    def __neg__(self):return I(-self.b,-self.a)
    def __sub__(self,o):return self+-o if isinstance(o,I) else self+I(-o)
    def __mul__(self,o):
        o=o if isinstance(o,I) else I(o);v=[self.a*o.a,self.a*o.b,self.b*o.a,self.b*o.b];return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=o if isinstance(o,I) else I(o);assert not o.a<=0<=o.b
        return self*I(1/o.b,1/o.a)
    def sq(self):return I(0 if self.a<=0<=self.b else min(self.a*self.a,self.b*self.b),max(self.a*self.a,self.b*self.b))
    def json(self):return [str(self.a),str(self.b)]
def check(points,eps):
    n=len(points);N=n*(n-1)//2
    w=[[I(F(str(v))-eps,F(str(v))+eps)for v in p]for p in points]
    c=[sum(p[k]for p in w)/n for k in range(2)];ds={}
    for i in range(n):
        for j in range(i):ds[i,j]=sum((w[i][k]-w[j][k]).sq()for k in range(2))
    q=sum(ds.values())/n
    if any(s.a<=0 for s in ds.values())or q.a<=0:return None
    for i in range(n):
        for k in range(2):
            e=sum((w[i][k]-w[j][k])/ds[max(i,j),min(i,j)]for j in range(n)if i!=j)-N*(w[i][k]-c[k])/q
            if e.a>0 or e.b<0:return dict(point_index=i,axis=k,residual_interval=e.json(),q_interval=q.json())
    return None
def main():
    rows=json.loads((ROOT/'image_diagnostics.json').read_text(encoding='utf-8'));out=[]
    for row in rows:
        if row['n']<9:continue
        attempts=[];cert=None
        for eps in [F(2),F(1),F(1,2),F(1,4),F(1,8),F(1,16)]:
            c=check(row['image_points'],eps);attempts.append({'epsilon_pixels':str(eps),'excludes_stationarity':c is not None})
            if c:cert=dict(epsilon_pixels=str(eps),**c);break
        out.append({'n':row['n'],'coordinate_centers':[[str(v)for v in p]for p in row['image_points']],
                    'attempts':attempts,'certificate':cert,'original_web_coordinate_membership':'NOT PROVED'})
    (ROOT/'conditional_box_certificates.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
    print([(r['n'],r['certificate']['epsilon_pixels'] if r['certificate']else None)for r in out])
if __name__=='__main__':main()
