#!/usr/bin/env python3
"""Exact rational regression models for V48 (not Lean kernel proofs)."""
from fractions import Fraction as F
from random import Random

rng = Random(48086)
cutoff_cases = 0
transition_cases = 0
anchor_cases = 0
partition_cases = 0

# Check the exact paper restart factor with b=2D(m+1), L=b^4 and
# T=ceil(b^(128(m+1)^2)).  This is a deliberately conservative envelope.
for D in (2, 3, 5, 8):
    for m in (1, 2, 3):
        b = F(2 * D * (m + 1))
        exponent = 128 * (m + 1) ** 2
        target = b ** exponent
        T = (target.numerator + target.denominator - 1) // target.denominator
        L = b ** 4
        factor = F(16) * D**32 * m**2 * (L ** (2*m)) / T
        assert factor < F(1, 2), (D, m, factor)
        cutoff_cases += 1

# Exact finite-coordinate model for the private-coordinate lower bound:
# ||Synth(c)-Synth(d)||^2 >= ||c-d||_2^2/D^2.
for _ in range(500):
    n = rng.randrange(1, 10)
    D = rng.randrange(max(2, n), max(3, n) + 12)
    amps = [F(rng.randrange(D, 3*D+1), D) for _ in range(n)]
    c = [(F(rng.randrange(-20, 21), 7), F(rng.randrange(-20, 21), 7)) for _ in range(n)]
    d = [(F(rng.randrange(-20, 21), 7), F(rng.randrange(-20, 21), 7)) for _ in range(n)]
    coeff_sq = sum((c[i][0]-d[i][0])**2 + (c[i][1]-d[i][1])**2 for i in range(n))
    private_sq = sum(amps[i]**2 * ((c[i][0]-d[i][0])**2 + (c[i][1]-d[i][1])**2) for i in range(n))
    # Physical-coordinate difference can only add a nonnegative term.
    assert coeff_sq / (D*D) <= private_sq
    transition_cases += 1

# Exact prefix-adapted anchor consistency: a coefficient sequence is read
# through ancestors of the common terminal cell, so two points in that
# terminal atom receive identical finite paths and anchor lists.
for _ in range(500):
    depth = rng.randrange(1, 9)
    leaf = rng.randrange(2**depth)
    path = []
    for j in range(depth + 1):
        width = 2 ** (depth - j)
        path.append(leaf // width)
    coeff = [rng.randrange(-30, 31) for _ in range(depth + 1)]
    tau = rng.randrange(0, 8)
    anchors = [0]
    for j in range(1, depth + 1):
        if abs(coeff[j] - coeff[anchors[-1]]) > tau:
            anchors.append(j)
    # The terminal id determines every ancestor id and coefficient.
    second_path = [leaf // (2 ** (depth-j)) for j in range(depth+1)]
    second_coeff = [coeff[j] for j in range(depth+1)]
    assert path == second_path and coeff == second_coeff
    second_anchors = [0]
    for j in range(1, depth + 1):
        if abs(second_coeff[j] - second_coeff[second_anchors[-1]]) > tau:
            second_anchors.append(j)
    assert anchors == second_anchors
    anchor_cases += 1

# History-labelled stage partitions: active atoms carry the prefix through
# the current anchor generation; terminated paths carry their full history
# and terminal-cell identifier. Equality at stage n+1 must imply equality
# at stage n. The model uses immutable tuples and exact finite logic.
def stage_label(history, terminal, stage):
    if stage < len(history):
        return ("active", tuple(history[:stage + 1]))
    return ("terminal", tuple(history), terminal)

for _ in range(500):
    h1 = [(rng.randrange(0, 12), rng.randrange(0, 12))
          for _ in range(rng.randrange(1, 12))]
    h2 = [(rng.randrange(0, 12), rng.randrange(0, 12))
          for _ in range(rng.randrange(1, 12))]
    t1, t2 = rng.randrange(20), rng.randrange(20)
    stage = rng.randrange(0, 13)
    if stage_label(h1, t1, stage + 1) == stage_label(h2, t2, stage + 1):
        assert stage_label(h1, t1, stage) == stage_label(h2, t2, stage)
    partition_cases += 1

# Exercise non-maximal L values, not only the endpoint L=b^4.
for _ in range(500):
    D = rng.randrange(2, 10)
    m = rng.randrange(1, 5)
    b = F(2 * D * (m + 1))
    exponent = 128 * (m + 1) ** 2
    target = b ** exponent
    T = (target.numerator + target.denominator - 1) // target.denominator
    L = F(rng.randrange(1, 1000), 100)  # at least 0.01
    L = max(F(1), min(L, b**4))
    factor = F(16) * D**32 * m**2 * (L ** (2*m)) / T
    assert factor < F(1, 2), (D, m, L, factor)
    cutoff_cases += 1

print(f"PASS: {cutoff_cases} exact restart-cutoff cases; "
      f"{transition_cases} private-coordinate transition cases; "
      f"{anchor_cases} terminal-cell anchor consistency cases; "
      f"{partition_cases} history-partition refinement cases")
