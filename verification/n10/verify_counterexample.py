"""Exact verification of the historical ten-point counterexample (1999)."""
from pathlib import Path
import json
points=[(11183,0),(-11183,0)]
for a,b in [(32765,14669),(12323,31572)]:
    points += [(sx*a,sy*b) for sx in [-1,1] for sy in [-1,1]]
assert len(points)==len(set(points))==10
assert sum(x for x,y in points)==sum(y for x,y in points)==0
q=sum(x*x+y*y for x,y in points)
assert q==9999608174
product=1
count=0
for i,(x,y) in enumerate(points):
    for X,Y in points[:i]:
        d=(x-X)**2+(y-Y)**2
        assert d>0
        product*=d
        count+=1
assert count==45
left=9**36*product
right=q**45
assert left>right
record={'source':'Gueron and Shafrir (1999), Figure 1',
        'points':points,'q':q,'pairs':count,
        'left_integer':str(left),'right_integer':str(right),
        'strict_inequality':True,'conclusion':'M10 > C10'}
Path('counterexample_check.json').write_text(json.dumps(record,indent=2),encoding='utf8')
print('45 pairs; exact integer comparison verified; M10 > C10')
