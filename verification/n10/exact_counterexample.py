"""Integer-only certificate excluding the center-plus-nonagon candidate."""
from pathlib import Path
from fractions import Fraction
from collections import Counter
import json

ROOT = Path(__file__).resolve().parent
W = [(7,0),(-7,0)] + [(sx*a,sy*b) for a,b in [(21,9),(8,20)] for sx in [-1,1] for sy in [-1,1]]
assert len(W)==len(set(W))==10
assert sum(x for x,y in W)==sum(y for x,y in W)==0
q=sum(x*x+y*y for x,y in W)
assert q==4042
distances=[(W[i][0]-W[j][0])**2+(W[i][1]-W[j][1])**2 for i in range(10) for j in range(i)]
assert len(distances)==45 and min(distances)>0
assert sum(distances)==10*q
P=1
for d in distances:P*=d
ratio=Fraction(P*9**36,q**45)
# z=sqrt(5/2021)*w; Delta(z)/C10 = P*9**36/q**45.
gap=5*P*9**36-6*q**45
assert gap>0
lo=Fraction(12037583569195,10**13)
hi=Fraction(12037583569196,10**13)
assert lo<ratio<hi
out={'status':'exact counterexample only; M10 not determined',
     'coordinates_w':W,'centroid':[0,0],'q':q,'normalization_squared':'5/2021',
     'distance_squared_multiplicities':dict(sorted(Counter(distances).items())),
     'P':str(P),'ratio_numerator':str(ratio.numerator),'ratio_denominator':str(ratio.denominator),
     'strict_comparison':'Delta(z) > (6/5)*C10',
     'positive_integer_5P9pow36_minus_6qpow45':str(gap),
     'certified_ratio_interval':[str(lo),str(hi)]}
(ROOT/'exact_counterexample_certificate.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps(out,indent=2))
