#!/usr/bin/env python3
"""Stress tests for a new local PV numerator estimate; NOT a Lean proof."""
import cmath, math, random
rng=random.Random(20261121)
trials=5000
for _ in range(trials):
    x=rng.uniform(-2,2)
    t=rng.uniform(-0.5,0.5)
    a=[rng.uniform(0.1,1.4) for _ in range(3)]
    b=[rng.uniform(-3,3) for _ in range(3)]
    f=lambda j,y: cmath.exp(-a[j]*a[j]*y*y+1j*b[j]*y)
    left=[f(j,x-(j+1)*t) for j in range(3)]
    right=[f(j,x+(j+1)*t) for j in range(3)]
    numerator=left[0]*left[1]*left[2]-right[0]*right[1]*right[2]
    identity=(left[0]-right[0])*left[1]*left[2]+right[0]*(left[1]-right[1])*left[2]+right[0]*right[1]*(left[2]-right[2])
    assert abs(numerator-identity)<5e-14
    # For |y| <= |x|+3|t|, |f_j'(y)| <= 2a_j^2 R+|b_j|.
    # Hence the difference over an interval of length 2(j+1)|t|
    # is bounded by 2(j+1)|t| sup|f_j'|.
    radius=abs(x)+3*abs(t)
    local_L=[2*(j+1)*(2*a[j]*a[j]*radius+abs(b[j])) for j in range(3)]
    assert abs(numerator) <= sum(local_L)*abs(t)+2e-13
print(f'PASS: {trials} complex Gaussian/oscillatory local cancellation samples')
