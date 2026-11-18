#!/usr/bin/env python3
"""Supplementary numerical checks ONLY. Not formal verification."""
from math import exp, log
from scipy.integrate import quad

shifts = (1, 2, 3)
def prod(x, t):
    return exp(-sum((x-j*t)**2 for j in shifts))

def trunc_minus(x, eps, R):
    return quad(lambda t:(prod(x,t)-prod(x,-t))/t,eps,R,epsabs=1e-12)[0]

def trunc_plus(x, eps, R):
    return quad(lambda t:(prod(x,-t)-prod(x,t))/t,eps,R,epsabs=1e-12)[0]

for x in (0., .2, .5, 1.):
    left=trunc_minus(x, 1e-4, 8.)
    right=trunc_plus(x, 1e-4, 8.)
    assert abs(left + right)<1e-10, (x,left,right)
    print(f'x={x}: truncated minus={left:+.12f}, plus={right:+.12f}')
assert trunc_minus(0.,1e-4,8.)==0.
print('PASS: numerical sign inversion. This does not verify the L3 estimate.')
