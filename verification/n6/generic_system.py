"""Build all four necessary sextic stationary equations, with no symmetry assumption."""
from pathlib import Path
import sys,json,time
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'friedman_full_audit_20261023/deps'))
from flint import fmpq_mpoly_ctx
start=time.monotonic()
ctx=fmpq_mpoly_ctx.get(('x','Y','T','b','c','d','e'),'lex')
x,Y,T,b,c,d,e=ctx.gens()
p=x**6+x**4+b*x**3+c*x*x+d*x+e
pp=p.derivative('x');ppp=pp.derivative('x')
print('building resultant',flush=True)
R=p.resultant((Y+T*x)*pp-ppp,'x')
print('resultant terms',len(R.to_dict()),'seconds',time.monotonic()-start,flush=True)
R0=R.subs({'T':0});Rt=R.derivative('T').subs({'T':0})
def coeff(poly,k):
    return ctx.from_dict({tuple(0 if i==1 else v for i,v in enumerate(m)):a for m,a in poly.to_dict().items() if m[1]==k})
D=coeff(R0,6)
assert coeff(R0,5)==0 and coeff(Rt,5)==0 and coeff(Rt,4)==30*D
E=[coeff(Rt,3),coeff(Rt,2)-12*coeff(R0,4),coeff(Rt,1)-6*coeff(R0,3),coeff(Rt,0)-2*coeff(R0,2)]
factors=[]
for v in E:
    fac=v.factor();print('equation terms',len(v.to_dict()),'factors',str(fac),flush=True);factors.append(str(fac))
out={'scope':'generic coefficient chart A=1, unrestricted centered sextic; necessary equations','polynomial':str(p),'D':str(D),'equations':[str(v)for v in E], 'R0':str(R0),'factors':factors,'seconds':time.monotonic()-start}
(ROOT/'generic_system.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
program='ring r=0,(t,e,d,c,b),dp;\noption(redSB);\npoly D='+str(D)+';\n'
for i,v in enumerate(E):program+=f'poly E{i}='+str(v)+';\n'
program+='ideal I=E0,E1,E2,E3,t*D-1;\nprint("START BASIS");\nideal G=std(I);\nprint("BASIS DONE");\nsize(G);\nvdim(G);\nwrite("generic_basis.txt",G);\nquit;\n'
(ROOT/'generic.sing').write_text(program,encoding='utf-8')
print('DONE',time.monotonic()-start,flush=True)
