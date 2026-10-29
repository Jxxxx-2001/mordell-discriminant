"""Check outward rounding against independent exact Fraction endpoint calculations."""
from fractions import Fraction as Q
import random,json
from pathlib import Path
import certify_twelve as c
rng=random.Random(20261023)
count=0
def contains(box,a,b):
    assert Q(box.a,c.SCALE)<=a<=b<=Q(box.b,c.SCALE)
for trial in range(1000):
    a,b=sorted(Q(rng.randint(-10000,10000),rng.randint(1,10000))for j in range(2))
    d,e=sorted(Q(rng.randint(-10000,10000),rng.randint(1,10000))for j in range(2))
    X,Y=c.I(a,b),c.I(d,e)
    contains(X,a,b);contains(Y,d,e)
    contains(X+Y,a+d,b+e);contains(X-Y,a-e,b-d)
    values=[a*d,a*e,b*d,b*e];contains(X*Y,min(values),max(values))
    contains(X.square(),0 if a<=0<=b else min(a*a,b*b),max(a*a,b*b))
    if not d<=0<=e:
        values=[a/d,a/e,b/d,b/e];contains(X/Y,min(values),max(values))
    count+=1
(Path(__file__).parent/'arithmetic_self_check.json').write_text(json.dumps({'checks_against_exact_fraction_endpoints':count,'passed':True,'seed':20261023},indent=2))
print('OUTWARD ROUNDING CHECKED AGAINST EXACT FRACTIONS:',count)
