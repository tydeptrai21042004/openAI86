#!/usr/bin/env python3
"""Numerical stress checks of two symmetric truncation conventions.

These checks are deliberately NOT Lean proofs. They provide regression
coverage for the only possible global sign and domain changes in the
manuscript's minus-shift versus upstream plus-shift definitions.
"""
import numpy as np
from numpy.polynomial.legendre import leggauss


def value(y, a, center, b, c):
    return np.exp(-a * (y-center)**2 + 1j * (b*y + c*y*y))


def trunc(f, x, eps, upper, plus):
    nodes, weights = leggauss(256)
    # Symmetric pairs, using independent negative/positive evaluation.
    # Test exact finite-truncation sign with transformed variable.
    grid = (upper-eps)*0.5*(nodes+1) + eps
    w = weights*(upper-eps)*0.5
    ans = 0j
    for s in (-1, 1):
        t=s*grid
        product=np.ones_like(t,dtype=complex)
        for j,(a,center,b,c) in enumerate(f, start=1):
            product *= value(x + (1 if plus else -1)*j*t,a,center,b,c)
        ans += np.dot(w, product/t)
    return ans


def run():
    rng=np.random.default_rng(86086)
    worst=0.
    for _ in range(90):
        f=[(float(rng.uniform(.5,1.7)),float(rng.uniform(-1,1)),
            float(rng.uniform(-2,2)),float(rng.uniform(-.6,.6))) for j in range(3)]
        x=float(rng.uniform(-1.5,1.5))
        eps=float(rng.uniform(.08,.3))
        v1=trunc(f,x,eps,8,False)
        v2=trunc(f,x,eps,8,True)
        err=abs(v1+v2)
        worst=max(worst,err)
        assert err < 2e-12*(1+abs(v1)+abs(v2)),(v1,v2,err)
    print(f'PASS: 90 complex-valued Schwartz-like finite-truncation sign cases; max absolute residual={worst:.3g}')

if __name__=='__main__':
    run()
