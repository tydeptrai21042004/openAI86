#!/usr/bin/env python3
"""Sanity checks for newly authored independent finite Lean statements.

These tests are NOT Lean elaboration or evidence for Theorem 1.1.
"""
import numpy as np
rng=np.random.default_rng(860119)
for trial in range(400):
    dim=int(rng.integers(1,7)); depth=int(rng.integers(0,17))
    x=rng.normal(size=dim)+1j*rng.normal(size=dim)
    new=x.copy(); old=x.copy(); delta=np.zeros(dim,dtype=complex)
    for _ in range(depth):
        P=rng.normal(size=(dim,dim))+1j*rng.normal(size=(dim,dim))
        Q=rng.normal(size=(dim,dim))+1j*rng.normal(size=(dim,dim))
        P/=2*dim;Q/=2*dim
        delta=P@delta+P@old-Q@old
        new,old=P@new,Q@old
        assert np.linalg.norm(delta-(new-old)) < 1e-8 * max(1,np.linalg.norm(new-old))
    assert np.allclose(delta,new-old,rtol=1e-9,atol=1e-10)
for trial in range(400):
    D=int(rng.integers(0,40)); n=int(rng.integers(0,D+1))
    v=rng.uniform(-D,D,size=n)
    assert np.sum(v*v) <= D**3 + 1e-8
for trial in range(400):
    D=int(rng.integers(0,100)); rootsize=16*D
    sizes=rng.integers(0,D+1,size=4)
    # Deterministic upper bound from the four family size hypotheses.
    assert 4*np.sum(sizes) <= rootsize
print('PASS: 1200 independently authored finite-component numerical checks')
print('WARNING: these are sanity checks, NOT Lean kernel verification or an analytic proof')
