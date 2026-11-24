#!/usr/bin/env python3
"""Exact arithmetic regressions, not a Lean certificate."""
from fractions import Fraction as F
from random import Random
rng=Random(37)
for trial in range(350):
    depth=rng.randrange(0,8); n=2**depth
    w=[F(rng.randrange(0,10),rng.randrange(1,8)) for _ in range(n)]
    f=[F(rng.randrange(0,30),rng.randrange(1,10)) for _ in range(n)]
    M=[F(0)]*n
    for k in range(depth+1):
        width=2**(depth-k)
        for start in range(0,n,width):
            idx=range(start,start+width)
            mass=sum(w[x] for x in idx); avg=sum(w[x]*f[x] for x in idx)/mass if mass else F(0)
            for x in idx: M[x]=max(M[x],avg)
        lhs=sum(w[x]*M[x]**2 for x in range(n))
        assert lhs<=2*sum(w[x]*f[x]*M[x] for x in range(n))
        assert lhs<=4*sum(w[x]*f[x]**2 for x in range(n))
# Gaussian integer arithmetic; small values exactly representable by Python complex.
def sq(z): return int(z.real)**2+int(z.imag)**2
for trial in range(350):
    m=rng.randrange(1,10); v=rng.randrange(0,12)
    phi=[[complex(rng.randrange(-4,5),rng.randrange(-4,5)) for _ in range(m)] for _ in range(v)]
    coeff=[[complex(rng.randrange(-3,4),rng.randrange(-3,4)) for _ in range(v)] for _ in range(m)]
    # Coordinate rows are a Bessel family of constant 1.
    tau2=max(sum(map(sq,e)) for e in coeff)
    lhs=sum(sq(sum(coeff[r][j]*phi[j][r] for j in range(v))) for r in range(m))
    rhs=tau2*sum(sum(map(sq,p)) for p in phi)
    assert lhs<=rhs
print('350 exact weighted dyadic maximal cases and 350 Gaussian-integer coordinate-row cases passed (not kernel verification).')
