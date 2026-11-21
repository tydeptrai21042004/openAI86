#!/usr/bin/env python3
"""Exact rational special-case regressions for Lemma 3.5 ratio bound."""
from fractions import Fraction
from random import Random
rng=Random(3352026)
tests=0
for B in range(2,20):
    for _ in range(200):
        p=rng.choice([i for i in range(-B,B+1) if i])
        q=rng.randrange(1,B+1)
        r=rng.choice([i for i in range(-B,B+1) if i])
        s=rng.randrange(1,B+1)
        a,b=Fraction(p,q),Fraction(r,s)
        ξ=Fraction(rng.randrange(-10**8,10**8),rng.randrange(1,100))
        assert Fraction(1,B)<=abs(a)<=B
        assert Fraction(1,B)<=abs(b)<=B
        assert abs(a*ξ)<=B*B*abs(b*ξ)
        assert abs(b*ξ)<=B*B*abs(a*ξ)
        tests+=1
print(f'PASS: {tests} exact rational height-ratio tests')
