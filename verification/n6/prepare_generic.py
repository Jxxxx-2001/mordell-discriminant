from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'friedman_full_audit_20261023/deps'))
import sympy as s
b,c,d,e,B,k=s.symbols('b c d e B k')
raw=json.loads((ROOT/'generic_system.json').read_text())
E=[s.sympify(v.replace('^','**'))for v in raw['equations']]
D=s.sympify(raw['D'].replace('^','**'))
def quotient(v,odd=False):
    v=s.Poly(s.expand(v.subs(d,b*k)),b)
    if odd:
        assert v.nth(0)==0
        v=s.Poly(v.as_expr()/b,b)
    assert all(mon[0]%2==0 for mon,co in v.terms())
    return s.Poly(sum(co*B**(mon[0]//2)for mon,co in v.terms()),B,c,k,e).primitive()[1].as_expr()
F=[quotient(v,i%2==0)for i,v in enumerate(E)]
DD=quotient(D)
for char in [0,32003]:
    pr=f'ring r={char},(t,e,k,c,B),dp;\noption(redSB);\npoly D='+str(DD).replace('**','^')+';\n'
    for i,f in enumerate(F):pr+=f'poly E{i}='+str(f).replace('**','^')+';\n'
    pr+='ideal I=E0,E1,E2,E3,t*B*D-1;\nprint("START BASIS");\nideal G=std(I);\nprint("BASIS DONE");\nsize(G);\nvdim(G);\n'
    pr+=f'write("quotient_basis_{char}.txt",G);\nquit;\n'
    (ROOT/f'quotient_{char}.sing').write_text(pr,encoding='utf-8')
(ROOT/'quotient_system.json').write_text(json.dumps({'equations':list(map(str,F)),'D':str(DD),'substitution':'d=b*k, B=b^2, chart A=1,b!=0'},indent=2),encoding='utf-8')
print('Prepared exact and finite-field exploratory systems')
