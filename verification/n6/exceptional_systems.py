"""All coefficient charts outside A=1,b!=0; no reflection assumption."""
from pathlib import Path
import sys,json,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'friedman_full_audit_20261023/deps'))
from flint import fmpq_mpoly_ctx
import sympy as s
ctx=fmpq_mpoly_ctx.get(('x','Y','T','b','c','d','e'),'lex');x,Y,T,b,c,d,e=ctx.gens()
def coeff(poly,k):return ctx.from_dict({tuple(0 if i==1 else v for i,v in enumerate(m)):a for m,a in poly.to_dict().items()if m[1]==k})
charts=[('A1_b0_d_nonzero',x**6+x**4+c*x*x+d*x+e,[3],['c','d','e'],'d'),
        ('A0_b1',x**6+x**3+c*x*x+d*x+e,[4],['c','d','e'],'1'),
        ('A0_b0_c1',x**6+x*x+d*x+e,[4,3],['d','e'],'1'),
        ('A0_b0_c0_d1',x**6+x+e,[4,3,2],['e'],'1')]
results=[]
for name,p,zeros,variables,sat in charts:
    R=p.resultant((Y+T*x)*p.derivative('x')-p.derivative('x').derivative('x'),'x')
    R0=R.subs({'T':0});Rt=R.derivative('T').subs({'T':0});D=coeff(R0,6)
    E=[coeff(Rt,3),coeff(Rt,2)-12*coeff(R0,4),coeff(Rt,1)-6*coeff(R0,3),coeff(Rt,0)-2*coeff(R0,2)]
    E += [coeff(R0,j)for j in zeros]
    E=[s.sympify(str(v).replace('^','**'))for v in E if v!=0];Ds=s.sympify(str(D).replace('^','**'));t=s.Symbol('t')
    vs=tuple(map(s.Symbol,reversed(variables)))
    print('START',name,flush=True)
    G=s.groebner(E+[t*s.sympify(sat)*Ds-1],t,*vs,order='grevlex')
    print('BASIS',len(G.polys),flush=True)
    if G.is_zero_dimensional:G=G.fglm('lex')
    if name in ['A1_b0_d_nonzero','A0_b0_c1']:
        assert len(G.polys)==1 and G.polys[0].as_expr()==1
    elif name=='A0_b1':
        assert all(G.reduce(v)[1]==0 for v in [s.Symbol('c'),s.Symbol('d'),25*s.Symbol('e')**2-17*s.Symbol('e')+1])
        assert not (len(G.polys)==1 and G.polys[0].as_expr()==1)
    else:
        assert G.reduce(s.Symbol('e'))[1]==0
        assert not (len(G.polys)==1 and G.polys[0].as_expr()==1)
    rr={'name':name,'p':str(p),'D':str(D),'equations':list(map(str,E)),'basis':[str(s.factor(v.as_expr()))for v in G.polys]}
    results.append(rr);print(rr['basis'],flush=True)
    (ROOT/'exceptional_results.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
