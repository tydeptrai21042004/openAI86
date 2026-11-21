#!/usr/bin/env python3
"""Reproducible tests for newly authored symmetric PV algebra (not a proof)."""
import cmath,random
rng=random.Random(20261121)
checks=0

def close(a,b,rtol=2e-11):
    return abs(a-b) < rtol*(1+abs(a)+abs(b))

# Algebraic three-factor identity and norm inequality.
for k in range(4000):
    a=[complex(rng.uniform(-4,4),rng.uniform(-4,4)) for _ in range(3)]
    b=[complex(rng.uniform(-4,4),rng.uniform(-4,4)) for _ in range(3)]
    left=a[0]*a[1]*a[2]-b[0]*b[1]*b[2]
    terms=[(a[0]-b[0])*a[1]*a[2],b[0]*(a[1]-b[1])*a[2],b[0]*b[1]*(a[2]-b[2])]
    assert close(left,sum(terms))
    assert abs(left) <= sum(map(abs,terms))+1e-10
    checks+=2

# Weighted symmetrized finite PV identity for nontrivial complex Schwartz-like signals.
def f(j,x):
    return cmath.exp(-(.2+j*.12)*(x-0.3*j)**2)*cmath.exp(1j*(j+1.4)*x)
def prod(x,t,sign):
    z=1+0j
    for j in range(3):z*=f(j,x+sign*(j+1)*t)
    return z
def K(x,t,sign):
    return prod(x,t,sign)/t
for k in range(600):
    x=rng.uniform(-2,2)
    ts=[rng.uniform(.025,3) for _ in range(8)]
    weights=[complex(rng.random(),rng.random()) for _ in ts]
    minus=sum(w*(K(x,t,-1)+K(x,-t,-1)) for w,t in zip(weights,ts))
    plus=sum(w*(K(x,t,1)+K(x,-t,1)) for w,t in zip(weights,ts))
    assert close(minus,-plus)
    checks+=1

# After symmetrization the singular numerator tends to zero at t=0;
# the difference quotient is bounded on shrinking test intervals.
for x in [-1,0,0.6,3]:
    mags=[]
    for t in [2.**(-j) for j in range(4,18)]:
        num=prod(x,t,-1)-prod(x,t,1)
        mags.append(abs(num/t))
        checks+=1
    assert max(mags)<200
    checks+=1
print('PASS symmetric PV finite / complex algebra tests:',checks)
