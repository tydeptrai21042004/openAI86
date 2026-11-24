#!/usr/bin/env python3
"""Exact arithmetic regressions for the V26 components, not Lean certificates."""
from fractions import Fraction as F
from itertools import product
import random
rng=random.Random(26)
counts={}
def check(name, condition):
    assert condition, name
    counts[name]=counts.get(name,0)+1

def vec(n): return [F(rng.randint(-20,20),rng.randint(1,8)) for _ in range(n)]
for _ in range(600):
    a,b,ga,y,z=vec(5)
    if a!=b:
        check('linear_phase',ga*(z-y)/(b-a)==-ga*y/(b-a)+ga*z/(b-a))
    m,f=vec(5),vec(5); A=max(map(abs,m))
    check('multiplier_energy',sum((x*y)**2 for x,y in zip(m,f))<=A*A*sum(x*x for x in f))
    # Exact contrapositive of the separator contradiction.
    sigma,kappa,M,n=[abs(x)+F(1,8) for x in vec(4)]; n+=1
    u=sigma*n*n
    check('separator_threshold',sigma*u>sigma*sigma)
    M=2*sigma/kappa+M
    check('separator_budget',kappa/sigma>1/M)
    a,b=vec(4),vec(5); z=[vec(5) for _ in a]
    A,B=sum(map(abs,a)),sum(map(abs,b)); delta=max(abs(x) for row in z for x in row)
    check('weighted_pair',abs(sum(x*sum(y*v for y,v in zip(b,row)) for x,row in zip(a,z)))<=A*B*delta)
    x,B=abs(rng.randint(-12,12)),rng.randint(1,7); p=rng.randint(1,4); q=rng.randint(p,6)
    check('tail_clipping',(F(x)**p if x>B else 0)<=F(B)**(p-q)*F(x)**q)
    # Product majorant in independent pair coordinates (finite quadrature model only).
    aa,bb=[abs(x) for x in vec(4)],[abs(x) for x in vec(5)]
    C=abs(F(rng.randint(-7,7),3)); weights=[abs(x) for x in vec(4)]; weights2=[abs(x) for x in vec(5)]
    values=[[C*x*y*F(rng.randint(-3,3),3) for y in bb] for x in aa]
    lhs=abs(sum(w*sum(v*t for v,t in zip(weights2,row)) for w,row in zip(weights,values)))
    check('pair_L1',lhs<=C*sum(w*x for w,x in zip(weights,aa))*sum(w*x for w,x in zip(weights2,bb)))
    # Orthogonal refit of one coordinate: actual old and new projections.
    x=vec(3); old=[x[0],0,0]; new=[x[0],x[1],0]; phi=[0,F(rng.choice([-2,-1,1,2])),0]
    mom=abs(sum((u-v)*p for u,v,p in zip(x,old,phi))); K=abs(phi[1])
    check('fresh_projection_jump',(mom/K)**2<=sum((u-v)**2 for u,v in zip(new,old)))
    w=[abs(x)+1 for x in vec(5)]; a=vec(5); W=sum(w); rho=max(F(0),sum(x*y for x,y in zip(w,a))/W)
    if sum(x*y for x,y in zip(w,a))>=W*rho:
        check('child_moment_energy',W*rho*rho<=sum(x*y*y for x,y in zip(w,a)))
    # Energy telescope with arbitrary nonnegative charges and nonnegative slack.
    c=abs(F(rng.randint(-9,9),5)); charges=[abs(v) for v in vec(5)]; E=[F(0)]
    for v in charges:E.append(E[-1]+c*v+abs(F(rng.randint(-9,9),5)))
    check('insertion_telescope',c*sum(charges)<=E[-1]-E[0])
    a=vec(5); e=vec(1)[0]; total=sum(a)+e; eta=abs(total)+abs(vec(1)[0])
    check('cell_minimum',abs(total)<=sum(min(eta,abs(v)) for v in a)+abs(e))
    Tr,Tt,Zr,Zt,Zb=vec(5)
    check('rolling_increment',Tt*(Zt-Zb)-Tr*(Zr-Zb)==Tt*(Zt-Zr)+(Tt*(Zr-Zb)-Tr*(Zr-Zb)))
    w=vec(8); b=rng.randrange(4); n=rng.randrange(4)
    check('prefix_telescope',w[b+n]==w[b]+sum(w[b+j+1]-w[b+j] for j in range(n)))
# Exact marked winner injection on all integer score vectors in a box.
def winner(s):return max(range(len(s)),key=lambda i:(s[i],-i))
def shift(s,g):
    v=winner(s);return tuple(x+(g if i==v else 0) for i,x in enumerate(s))
for gap in (1,2,5):
    seen=set()
    for s in product(range(-3,4),repeat=3):
        t=shift(s,gap);v=winner(s)
        check('winner_shift_marked',all(t[v]>=t[i]+gap for i in range(3) if i!=v))
        check('winner_shift_injective',t not in seen);seen.add(t)
    for _ in range(800):
        s=tuple(rng.randint(-10,10) for _ in range(3)); t=tuple(x+rng.randint(0,6) for x in s)
        v,w=winner(s),winner(t)
        if s[v]==t[w] and all(t[w]>=t[i]+gap for i in range(3) if i!=w):
            check('fixed_top_winner',v==w)
# Actual exact expectation over independent sign arrays of length two.
for a,b in product(range(2),repeat=2):
    for _ in range(50):
        z={idx:F(rng.randint(-9,9),7) for idx in product(range(2),repeat=4)}
        total=F(0)
        for signs in product((-1,1),repeat=6):
            e,h,r=signs[:2],signs[2:4],signs[4:]
            total+=sum(e[a]*h[b]*e[i]*h[j]*r[p]*r[q]*v for (i,j,p,q),v in z.items())
        check('actual_sign_expectation',total/64==sum(z[a,b,p,p] for p in range(2)))
for k,v in sorted(counts.items()):print(f'{k}: {v}')
print(f'PASS: {sum(counts.values())} exact V26 model checks (not kernel verification)')
