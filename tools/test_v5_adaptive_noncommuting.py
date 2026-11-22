#!/usr/bin/env python3
"""Exact rational stress tests for V5's row-adaptive noncommuting Bessel step.

These are counterexample searches, NOT a substitute for Lean kernel checking.
"""
from fractions import Fraction as F
from random import Random
import json

r = Random(8605)
count = 0
cross_checks = 0


def eye(n):
    return [[F(int(i == j)) for j in range(n)] for i in range(n)]


def mm(a,b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def transpose(a):
    return [list(x) for x in zip(*a)]


def mv(a,x):
    return [sum((u*v for u,v in zip(row,x)), F(0)) for row in a]


def energy(x):
    return sum((v*v for v in x), F(0))


def orthogonal(n, t):
    out = eye(n)
    # Givens 3/5, 4/5 rotates rationally and avoids floating-point tests.
    for j in range(n*2):
        p = (j+t)%n
        q = (p+1)%n
        if p == q: continue
        u=eye(n)
        u[p][p]=F(3,5); u[q][q]=F(3,5)
        u[p][q]=F(-4,5); u[q][p]=F(4,5)
        out=mm(u,out)
    assert mm(out,transpose(out)) == eye(n)
    return out


def proj(U,k):
    n=len(U)
    return [[sum((U[i][a]*U[j][a] for a in range(min(k,n))), F(0))
             for j in range(n)] for i in range(n)]


def block_apply(U,b,x):
    p=mv(proj(U,b+1),x)
    q=mv(proj(U,b),x)
    return [a-c for a,c in zip(p,q)]


def adaptive(Ulayers,choices,x):
    n=len(x)
    outs=[]
    for row in range(4*n):
        y=x
        for i,U in enumerate(Ulayers):
            y=block_apply(U,choices[i][row],y)
        # 4 duplicates of coordinate testing at one half amplitude => Bessel equality.
        outs.append(y[row%n]/2)
    return outs


for n in (2,3,4):
    for layers in (0,1,2,3,4):
        for trial in range(120):
            x=[F(r.randint(-5,5),r.randint(1,5)) for _ in range(n)]
            Us=[orthogonal(n, 3*i+trial%7) for i in range(layers)]
            choices=[[r.randrange(n+2) for _ in range(4*n)]
                     for _ in range(layers)]
            z=adaptive(Us,choices,x)
            assert energy(z) <= energy(x), (n,layers,trial)
            count+=1
            if layers:
                y=[F(r.randint(-3,3)) for _ in range(n)]
                assert sum((energy(block_apply(Us[0],b,y))
                            for b in range(n+2)), F(0)) == energy(y)
                cross_checks+=1

# General (non-projection) Bessel layers: Q0=(3/5)U, Q1=(4/5)V.
# Each U,V is rational-orthogonal and hence ∑_b ||Q_b y||² = ||y||².
for n in (2, 3, 4):
    for depth in range(1, 7):
        for trial in range(100):
            x=[F(r.randint(-4,4),r.randint(1,5)) for _ in range(n)]
            transforms=[(orthogonal(n, trial+5*k), orthogonal(n, trial+5*k+1))
                        for k in range(depth)]
            picks=[[r.randrange(2) for _ in range(4*n)] for _ in range(depth)]
            rows=[]
            for row in range(4*n):
                y=x
                for k in range(depth):
                    b=picks[k][row]
                    y=mv(transforms[k][b],y)
                    c=(F(3,5) if b==0 else F(4,5))
                    y=[c*value for value in y]
                rows.append(y[row%n]/2)
            assert energy(rows) <= energy(x), (n,depth,trial,'general')
            count += 1

# Check noncommutation really occurs, so tests are not all coordinate cases.
n=3
P=proj(orthogonal(n,0),1)
Q=proj(orthogonal(n,1),1)
assert mm(P,Q)!=mm(Q,P)

# Multilevel triangle + Cauchy--Schwarz: sums of independent row outputs.
for n in (2,3,4):
    for trial in range(100):
        x=[F(r.randint(-4,4),r.randint(1,4)) for _ in range(n)]
        levels=r.randrange(1,5)
        outputs=[[F(0)]*(4*n) for _ in range(levels)]
        for k in range(levels):
            layers=r.randrange(0,4)
            us=[orthogonal(n, k+2*i+trial%5) for i in range(layers)]
            choices=[[r.randrange(n+2) for _ in range(4*n)]
                     for _ in range(layers)]
            outputs[k]=adaptive(us,choices,x)
        total=[sum((out[row] for out in outputs),F(0))
               for row in range(4*n)]
        assert energy(total) <= levels*levels*energy(x)
        count+=1

print(json.dumps({'status':'PASS', 'exact_rational_tests':count,
                  'one_layer_Bessel_checks':cross_checks,
                  'noncommutation_witness':'PASS', 'lean_kernel':'NOT_RUN'},indent=2))
