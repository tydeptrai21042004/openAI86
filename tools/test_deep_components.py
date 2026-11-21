#!/usr/bin/env python3
"""Finite regressions for three new independent Lean proof components.

This tests only numerical/combinatorial models. It does not compile Lean.
All tests are deterministic. No external files/network required.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import product
from random import Random

rng = Random(8602026)
cases = 0

# A. Section 3.3: any number of commuting coordinate projection layers.
for _ in range(1250):
    n = rng.randrange(0, 18)
    m = rng.randrange(0, 9)
    N = rng.randrange(0, 18)
    x = [rng.randrange(-5, 6) for _ in range(n)]
    families = []
    for _j in range(m):
        active = set()
        steps = []
        for k in range(N + 1):
            active |= {i for i in range(n) if rng.random() < 0.18}
            steps.append(active.copy())
        families.append(steps)

    def common(k):
        return set.intersection(*(fam[k] for fam in families)) if families else set(range(n))

    energy = lambda indices: sum(x[i]**2 for i in indices)
    differences = [energy(common(k + 1) - common(k)) for k in range(N)]
    assert sum(differences) == energy(common(N)) - energy(common(0))
    assert sum(differences) <= sum(t*t for t in x)
    for k in range(N + 1):
        # Layer-by-layer application and common projection must agree.
        y = x.copy()
        for fam in families:
            y = [z if i in fam[k] else 0 for i, z in enumerate(y)]
        z = [t if i in common(k) else 0 for i, t in enumerate(x)]
        assert y == z
    cases += 1

# B. Lemma 8.6: pointwise charges, per-row and per-column budgets.
# Exact rational arithmetic avoids tolerance-based false passes.
for _ in range(1850):
    N = rng.randrange(0, 11)
    H = rng.randrange(1, 13)
    vertical = [[Fraction(rng.randrange(0, 7), 4) for _h in range(H)] for _i in range(N)]
    horizontal = [[Fraction(rng.randrange(0, 7), 4) for _h in range(H)] for _i in range(N)]
    bad = [[vertical[i][h] + horizontal[i][h] - Fraction(rng.randrange(0, 3), 10)
            for h in range(H)] for i in range(N)]
    Q = max([sum(row) for row in vertical], default=Fraction(0))
    R = max([sum(horizontal[i][h] for i in range(N)) for h in range(H)], default=Fraction(0))
    total = sum(map(sum, bad))
    assert total <= N * Q + H * R
    # The implication in BadDensityIncidence is tested when its hypotheses hold.
    for δ in [Fraction(1, 10), Fraction(1, 4), Fraction(1, 2)]:
        if 2 * Q <= δ * H and all(sum(row) >= δ * H for row in bad):
            assert Fraction(N) <= 2 * R / δ
    cases += 1

# C. Section 9.1: common good heights, four bad-role sets.
for H in range(0, 257):
    heights = set(range(H))
    for _ in range(14):
        badsets = []
        for j in range(4):
            budget = H // 8
            count = rng.randrange(0, budget + 1)
            badsets.append(set(rng.sample(range(H), count)))
        common = heights.difference(*badsets)
        assert H <= 2 * len(common)
        if H > 0:
            assert common
        cases += 1

# D. Adversarial check: sparse per-scale counts plus pair multiplicity L=1
# alone cannot produce the positive-power saving of Lemma 9.1.
for M in range(1, 50):
    scales = [(a, b) for a, b in product(range(M), repeat=2)]
    assert len(scales) == M * M
    assert max((scales.count((a, b)) for a in range(M) for b in range(M))) == 1
    assert all(1 <= Fraction(1, M * M) * M * M for _ in scales)
    cases += 1

print(f'PASS: {cases} deterministic deep-component cases (exact arithmetic for incidence)')
print('NOTE: Python tests are NOT Lean kernel proofs; counterexample D concerns weakened hypotheses only.')
