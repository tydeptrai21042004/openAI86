#!/usr/bin/env python3
"""Stress test the *full numeric statement* of manuscript Lemma 3.3.

Complex Hilbert spaces, nested orthogonal projections with noncommuting
layers, complex Bessel rows, and arbitrary row prefix times. This is
falsification-oriented numerical testing, NEVER a Lean kernel proof.
"""
from math import ceil, log2
import numpy as np
rng=np.random.default_rng(86033003)
number=800
max_comm=max_row=max_jump=0.0
for trial in range(number):
    n=int(rng.integers(1,9))
    m=int(rng.integers(0,6))
    T=int(rng.integers(0,24))
    projs=[]
    for _ in range(m):
        X=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n))
        q,_=np.linalg.qr(X)
        ranks=np.sort(rng.integers(0,n+1,size=T+1))
        projs.append([q[:,:r]@q[:,:r].conj().T for r in ranks])
    z=[]
    for k in range(T+1):
        v=np.eye(n, dtype=complex)
        for j in range(m):
            v=projs[j][k]@v
        z.append(v)
    if m>=2:
        max_comm=max(max_comm,float(np.linalg.norm(
            projs[0][-1]@projs[1][-1]-projs[1][-1]@projs[0][-1], 2)))
    g=rng.normal(size=n)+1j*rng.normal(size=n)
    rows=int(rng.integers(1,25))
    b=rng.normal(size=(rows,n))+1j*rng.normal(size=(rows,n))
    b/=max(1.0,float(np.linalg.norm(b,2)))
    select=rng.integers(0,T+1,size=rows)
    row_sq=sum(abs(b[v]@(z[select[v]]@g))**2 for v in range(rows))
    jump_sq=sum(float(np.linalg.norm((z[k]-z[k-1])@g)**2) for k in range(1,T+1))
    L=1+ceil(log2(T+1))
    bound_rows=(L**(2*m))*float(np.linalg.norm(g)**2)
    bound_jumps=(m**2)*(L**(2*max(0,m-1)))*float(np.linalg.norm(g)**2)
    assert row_sq <= bound_rows*(1+1e-9)+1e-12, (trial,'row')
    assert jump_sq <= bound_jumps*(1+1e-9)+1e-12, (trial,'jump')
    if bound_rows: max_row=max(max_row,row_sq/bound_rows)
    if bound_jumps: max_jump=max(max_jump,jump_sq/bound_jumps)
print(f'PASS: {number} complex noncommuting Lemma 3.3 tests; '
      f'commutator max={max_comm:.4f}, row ratio max={max_row:.4f}, '
      f'jump ratio max={max_jump:.4f}')
print('WARNING: no machine-checked Lean proof is implied by these tests.')
