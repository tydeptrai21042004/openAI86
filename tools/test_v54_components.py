#!/usr/bin/env python3
"""Finite/exact arithmetic regression models, not Lean proof certificates."""
from fractions import Fraction as F
from itertools import product
from random import Random
r=Random(54)
counts={k:0 for k in ('masked_refinement','orthogonal_refit','greedy','fourth_moment','chart_phase','retained_absorption')}
# Refine a partition into fibres of a surjective parent function. Masks
# grow in the child. Each selected old column equals its child sum.
for _ in range(500):
    n=r.randint(1,12); labs=r.randint(1,8); children=r.randint(1,n); parents=r.randint(1,children)
    pa=[r.randrange(parents) for i in range(children)]; cell=[r.randrange(children) for i in range(n)]
    old=[{j for j in range(labs) if r.randrange(2)} for _ in range(parents)]
    new=[old[pa[i]]|{j for j in range(labs) if r.randrange(2)} for i in range(children)]
    vals=[[F(r.randint(-9,9),3) for _ in range(n)] for _ in range(labs)]
    for a,i,x in product(range(parents),range(labs),range(n)):
        lhs=vals[i][x] if pa[cell[x]]==a and i in old[a] else 0
        rhs=sum(vals[j][x] for b,j in product(range(children),range(labs)) if i in old[a] and pa[b]==a and i==j and j in new[b] and cell[x]==b)
        assert lhs==rhs
    counts['masked_refinement']+=1
# Exact finite Hilbert model: disjoint atom support, one nonzero column
# per atom. Projection residual is orthogonal to every local column.
for _ in range(300):
    n=r.randint(1,20); m=r.randint(1,5); atoms=[r.randrange(m) for _ in range(n)]
    z=[F(r.randint(-9,9),3) for _ in range(n)]; phi=[F(r.randint(1,7),4) for _ in range(n)]
    ref=[F(0)]*n
    for a in range(m):
        ids=[i for i in range(n) if atoms[i]==a]
        if ids:
            c=sum(z[i]*phi[i] for i in ids)/sum(phi[i]**2 for i in ids)
            for i in ids: ref[i]=c*phi[i]
            assert sum((z[i]-ref[i])*phi[i] for i in ids)==0
    assert sum(x*x for x in ref)==sum(x*y for x,y in zip(z,ref))
    counts['orthogonal_refit']+=1
# Actual consecutive right-to-left greedy rule; retain item identities.
for _ in range(700):
    cap=r.randint(2,40); delta=r.randint(0,cap); w=[r.randint(0,delta) for _ in range(r.randint(0,80))]; blocks=[]
    for x in reversed(range(len(w))):
        if blocks and w[x]+sum(w[i] for i in blocks[0])<=cap: blocks[0].insert(0,x)
        else: blocks.insert(0,[x])
    assert [x for b in blocks for x in b]==list(range(len(w)))
    assert all(sum(w[i] for i in b)<=cap for b in blocks)
    assert all(sum(w[i] for i in b)>cap-delta for b in blocks[1:])
    counts['greedy']+=1
# Exact Gaussian-integer coefficient energy, both resonance equations.
for _ in range(400):
    s=r.sample(range(-12,13),r.randint(1,8)); w={a:r.randint(-6,6)**2+r.randint(-6,6)**2 for a in s}
    mass=sum(w[a]*w[b] for a,b,c,d in product(s,repeat=4) if a+b==c+d and a*a+b*b==c*c+d*d)
    assert mass==2*sum(w.values())**2-sum(x*x for x in w.values())
    counts['fourth_moment']+=1
# Arbitrary rational nonsymmetric C, exact phase expansion.
for _ in range(500):
    d=r.randint(1,5); mat=[[F(r.randint(-5,5),3) for _ in range(d)] for _ in range(d)]
    u,n,m,v=[[F(r.randint(-9,9),4) for _ in range(d)] for _ in range(4)]
    add=lambda a,b:[x+y for x,y in zip(a,b)]
    sub=lambda a,b:[x-y for x,y in zip(a,b)]
    C=lambda a,b:sum(a[i]*mat[i][j]*b[j] for i in range(d) for j in range(d))
    lhs=C(add(add(u,m),v),add(sub(u,n),v))-C(u,sub(u,n))
    rhs=C(u,add(m,v))-(C(u,m)-C(m,u))+C(v,sub(u,n))-C(m,n)+C(m,v)+C(v,v)
    assert lhs==rhs
    counts['chart_phase']+=1
# Rational model of the last combination with η^c = t, and both
# separately bounded powered terms at most constant*t.
for _ in range(400):
    t=F(r.randint(1,12),12); A,B,E,CN,R=[F(r.randint(0,10),3) for _ in range(5)]
    x,y=F(r.randint(0,12),12)*t,F(r.randint(0,12),12)*t
    assert (A*x+B*(1+CN)*y)*R+E*t*R <= (A+B+E)*t*(1+CN)*R
    counts['retained_absorption']+=1
print(counts,'total:',sum(counts.values()))
