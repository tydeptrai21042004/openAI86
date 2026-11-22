#!/usr/bin/env python3
"""Exact rational sanity checks for finite noncommuting row/variation bounds.
Neither this script nor the static Lean scans constitute kernel verification.
"""
from fractions import Fraction as F
from itertools import product

checks=0

def dot(x,y): return sum(a*b for a,b in zip(x,y))
def norm2(x): return dot(x,x)
def projection(a,b):
    z=a*a+b*b
    return ((a*a/z,a*b/z),(a*b/z,b*b/z))
def mv(M,x): return tuple(sum(M[i][j]*x[j] for j in range(2)) for i in range(2))
def diff(x,y): return tuple(a-b for a,b in zip(x,y))
def zmat(): return ((F(0),F(0)),(F(0),F(0)))
def ident(): return ((F(1),F(0)),(F(0),F(1)))

Ps=[projection(F(a),F(b)) for a,b in [(3,4),(5,12),(8,15),(7,24),(20,21)]]
zero=zmat(); one=ident()
levels=[[zero,p,one,one,one,one] for p in Ps]
rows=((F(3,5),F(4,5)),(F(-4,5),F(3,5)))

# T = 0...5; m = 0...5.  At every fixed level, chains are
# noncommuting orthogonal projection products (one from each family).
for T in range(6):
    for m in range(6):
        for x in ((F(1),F(2)),(F(3),F(-2)),(F(0),F(1)),(F(-4),F(5))):
            out=[]
            for t in range(T+1):
                y=x
                for i in range(m):
                    y=mv(levels[i][min(t,5)],y)
                assert norm2(y)<=norm2(x)
                out.append(y)
                checks+=1
            variation=sum(norm2(diff(out[t+1],out[t])) for t in range(T))
            assert variation<=4*T*norm2(x)
            checks+=1
            if m==1:
                assert variation <= norm2(x)
                checks+=1
            if m==0:
                assert variation==0
                checks+=1
            for n0,n1 in product(range(T+1),repeat=2):
                lhs=dot(rows[0],out[n0])**2+dot(rows[1],out[n1])**2
                assert lhs <= (T+1)*norm2(x), (m,T,x,n0,n1)
                if n0==n1:
                    assert lhs <= norm2(x)
                checks+=1
print(f'V8 coarse finite-prefix/variation exact rational checks: {checks:,} PASS')
