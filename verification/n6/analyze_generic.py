from pathlib import Path
import json,sys,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'friedman_full_audit_20261023/deps'))
import sympy as s
B,c,k,e,t=s.symbols('B c k e t')
items=(ROOT/'quotient_lex_modexact.txt').read_text().strip().split(',')
H=[s.sympify(v.replace('^','**'))for v in items]
P=s.Poly(H[0],B).clear_denoms()[1].primitive()[1]
assert P.degree()==35
print('FACTORING',flush=True)
factors=s.factor_list(P)[1]
result={'P':str(P.as_expr()),'branches':[]}
for ff,multiplicity in factors:
    maps={}
    for var,h in zip([c,k,e,t],H[1:]):
        lead=s.diff(h,var)
        assert lead.is_Rational and lead!=0
        maps[str(var)]=str(s.rem(var-h/lead,ff.as_expr(),B))
    rr={'factor':str(ff.as_expr()),'degree':ff.degree(),'multiplicity':multiplicity,'maps':maps}
    result['branches'].append(rr)
    print(rr,flush=True)
(ROOT/'generic_triangular.json').write_text(json.dumps(result,indent=2))
