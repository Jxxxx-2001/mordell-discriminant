"""Necessary stationary equations for the centrally symmetric six-point branch only."""
from pathlib import Path
import sys,time,json
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'friedman_full_audit_20261023/deps'))
import sympy as s
u,b,c=s.symbols('u b c');K=s.QQ.frac_field(b,c)
g=s.Poly(u**3+u**2+b*u+c,u,domain=K)
U=s.Poly(u,u,domain=K)
f=(s.Poly(15*u**2+6*u+b,u,domain=K)*s.invert(U*g.diff(),g)).rem(g)
def mul(a,b):return (a*b).rem(g)
def tr(p):return s.factor(3*p.nth(0)-p.nth(1)+(1-2*b)*p.nth(2))
f2=mul(f,f);P=mul(U,f2);P2=mul(P,P)
M1=2*tr(mul(U,f));assert M1==30
S2=2*tr(P);S4=2*tr(P2)
M3=2*tr(mul(mul(U,f),P));M5=2*tr(mul(mul(U,f),P2))
eq=[s.factor(s.together(M3-9*S2).as_numer_denom()[0]),s.factor(s.together(M5-7*S4-S2**2).as_numer_denom()[0])]
print('EQUATIONS',eq,flush=True)
disc=s.discriminant(g.as_expr(),u);t=s.symbols('t')
print('SATURATION',c*disc,flush=True)
G=s.groebner(eq+[t*c*disc-1],t,c,b,order='grevlex');print('BASIS DONE',len(G.polys),flush=True)
if G.is_zero_dimensional:G=G.fglm('lex')
for p in G.polys:print(s.factor(p.as_expr()),flush=True)
P3=mul(P2,P);tr1=tr(P);tr2=tr(P2);tr3=tr(P3)
Ay=-tr1;By=s.factor((tr1**2-tr2)/2);Cy=s.factor(-(tr1**3-3*tr1*tr2+2*tr3)/6)
for name,e in [('Bdual',By-b*Ay**2),('Cdual',Cy-c*Ay**3)]:
    num=s.together(e).as_numer_denom()[0]
    remainder=s.factor(G.reduce(s.expand(num))[1])
    assert remainder==0
    print(name,'REDUCED',remainder,flush=True)
print('AY',Ay,flush=True)
print('REAL BRANCH NUMERICS',flush=True)
bp=(5*b-1)*(5*b*b+36*b-9)*(5*b**3-9*b*b+15*b-3)
cp=(225*b**5+1225*b**4-2584*b**3+5376*b**2-2013*b+207)/180
for bb in s.nroots(bp,maxsteps=200):
    cc=cp.subs(b,bb);aa=Ay.subs({b:bb,c:cc})
    print('b,c,Ay',bb,cc.evalf(),aa.evalf(),flush=True)
sys.path.insert(0,str(ROOT.parent/'friedman_full_audit_20261023'))
from interval_check import I
certs=[]
for fac in [5*b-1,5*b*b+36*b-9,5*b**3-9*b*b+15*b-3]:
    def red(v):return s.rem(v,fac,b)
    cmod=red(cp)
    def field(v):
        num,den=s.together(v).as_numer_denom();return red(red(num)*s.invert(red(den),fac,b))
    amod=field(Ay.subs(c,cmod));dmod=red(disc.subs(c,cmod))
    val=s.Rational(4096,5**30)*cmod**2*dmod**4
    val=red(val)
    for k in range(15):val=red(val*amod)
    roots=s.Poly(fac,b).intervals(eps=s.Rational(1,10**12))
    for interval,multiplicity in roots:
        a0,a1=interval;box=I(str(a0),str(a1));res=I(0)
        for coeff in s.Poly(val,b).all_coeffs():res=res*box+I(str(coeff))
        assert res.b<6**12
        certs.append(dict(factor=str(fac),root_interval=[str(a0),str(a1)],Phi_squared_modulus=str(val),upper=str(res.b),below_regular_hexagon_squared=True))
print('ALL A=1 EVEN BRANCHES STRICTLY BELOW REGULAR HEXAGON',flush=True)
assert len(certs)==4
(ROOT/'even_branch_comparison.json').write_text(json.dumps(certs,indent=2),encoding='utf-8')
# Exceptional chart A=0, B=1. The physical dual A coefficient must also vanish.
g0=s.Poly(u**3+u+c,u,domain=s.QQ.frac_field(c));U0=s.Poly(u,u,domain=s.QQ.frac_field(c))
f0=(s.Poly(15*u**2+1,u,domain=s.QQ.frac_field(c))*s.invert(U0*g0.diff(),g0)).rem(g0)
def tr0(p):return s.factor(3*p.nth(0)-2*p.nth(2))
P0=(U0*f0*f0).rem(g0)
ay0=-tr0(P0)
print('A=0 B=1 DUAL A',ay0,flush=True)
e0=2*tr0((U0*f0*P0).rem(g0))-18*tr0(P0)
num0=s.together(e0).as_numer_denom()[0];an0=s.together(ay0).as_numer_denom()[0]
exG=s.groebner([num0,an0,t*c*s.discriminant(g0.as_expr(),u)-1],t,c)
print('EXCEPTIONAL BASIS',[str(p.as_expr())for p in exG.polys],flush=True)
assert len(exG.polys)==1 and exG.polys[0].as_expr()==1
(ROOT/'even_branch_result.json').write_text(json.dumps({'scope':'necessary equations only, A=1 chart of even sextic','equations':[str(e)for e in eq],'basis':[str(s.factor(p.as_expr()))for p in G.polys]},indent=2),encoding='utf-8')
