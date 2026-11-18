"""Numerical smoke checks for the exact two bounds of OpenAI #086, Lemma 3.3.
Not a Lean proof. Cross-layer orthogonal projections generally do NOT commute.
"""
from __future__ import annotations
import numpy as np
from math import ceil, log2
rng = np.random.default_rng(86033)
max_ratio_row = max_ratio_jump = max_comm = 0.0
for trial in range(160):
    dimension = int(rng.integers(2, 9))
    layers = int(rng.integers(1, 5))
    horizon = int(rng.integers(1, 12))
    bases = [np.linalg.qr(rng.normal(size=(dimension,dimension)))[0] for _ in range(layers)]
    projections = []
    for basis in bases:
        # random nondecreasing ranks -> orthogonal nested projections
        ranks = np.sort(rng.integers(0,dimension+1,size=horizon+1))
        projections.append([basis[:,:r] @ basis[:,:r].T for r in ranks])
    z = []
    for n in range(horizon+1):
        prod = np.eye(dimension)
        for layer in range(layers):
            prod = projections[layer][n] @ prod
        z.append(prod)
    if layers >= 2:
        max_comm = max(max_comm, float(np.linalg.norm(
            projections[0][horizon] @ projections[1][horizon] -
            projections[1][horizon] @ projections[0][horizon])))
    g = rng.normal(size=dimension)
    rows = int(rng.integers(1, 24))
    rmat = rng.normal(size=(rows, dimension))
    rmat /= max(1, np.linalg.norm(rmat,2))  # contraction: A^T A <= Id
    row_times = rng.integers(0,horizon+1,size=rows)
    left = sum((rmat[v] @ (z[row_times[v]] @ g))**2 for v in range(rows))
    jump = sum(np.linalg.norm((z[n]-z[n-1]) @ g)**2 for n in range(1,horizon+1))
    L = 1 + ceil(log2(horizon+1))
    right_row = L**(2*layers)*np.linalg.norm(g)**2
    right_jump = layers**2*L**(2*(layers-1))*np.linalg.norm(g)**2
    assert left <= right_row*(1+1e-10)
    assert jump <= right_jump*(1+1e-10)
    max_ratio_row=max(max_ratio_row,left/right_row)
    max_ratio_jump=max(max_ratio_jump,jump/right_jump)
print(f"160 PASS numeric cases; maximum commutator norm {max_comm:.4g}; "
      f"row ratio {max_ratio_row:.4g}; jump ratio {max_ratio_jump:.4g}")
print("WARNING: numerical evidence is NOT a formal proof, and not a Lean build.")
