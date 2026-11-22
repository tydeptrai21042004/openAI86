#!/usr/bin/env python3
"""Deterministic finite cross-checks; NOT Lean-kernel proof verification.

Checks the arithmetic statements and reconstruction principle used in
FiniteTonelliBudget, FiniteMultifamilyStops, ArbitraryColoredPaths,
and CompressionRowError. All tests are independently written.
"""
from itertools import product
from collections import defaultdict
from random import Random
import math

rng = Random(861133)

# Finite Tonelli: weighted pathwise budget implies weighted total budget.
for _ in range(2200):
    p, c = rng.randrange(1, 10), rng.randrange(1, 11)
    weights = [rng.random() * 5 for _ in range(p)]
    occupancy = [[rng.random() * 3 for _ in range(p)] for _ in range(c)]
    A = max(sum(occupancy[i][x] for i in range(c)) for x in range(p))
    lhs = sum(weights[x] * occupancy[i][x] for i in range(c) for x in range(p))
    rhs = A * sum(weights)
    assert lhs <= rhs + 1e-9 * max(1.0, rhs)

# Any union of stopping families has <= sum cardinalities.
for _ in range(2200):
    size, n = rng.randrange(1, 25), rng.randrange(0, 13)
    sets = [{x for x in range(size) if rng.random() < 0.35} for _ in range(n)]
    assert len(set().union(*sets)) <= sum(map(len, sets))

# Proper edge coloring: a path from fixed u is reconstructed by ordered
# colors. The color (u,v) is proper on both sides, with repeated vertices.
for U, V, steps in product(range(1, 4), range(1, 4), range(0, 4)):
    for start in range(U):
        records = {}
        for nodes in product(range(V * U), repeat=steps):
            u = start
            colors = []
            for node in nodes:
                v, next_u = divmod(node, U)
                colors.extend(((u, v), (next_u, v)))
                u = next_u
            key = tuple(colors)
            assert key not in records or records[key] == nodes
            records[key] = nodes

# Row compression error: real finite Cauchy-Schwarz + Bessel/Fubini.
for _ in range(1600):
    rows, labels = rng.randrange(1, 9), rng.randrange(1, 11)
    e = [[rng.uniform(-1, 1) for _ in range(labels)] for _ in range(rows)]
    z = [[rng.uniform(-2, 2) for _ in range(labels)] for _ in range(rows)]
    tau2 = max(sum(x*x for x in line) for line in e)
    energy = [sum(z[r][v] ** 2 for r in range(rows)) for v in range(labels)]
    lhs = sum(sum(e[r][v]*z[r][v] for v in range(labels))**2 for r in range(rows))
    rhs = tau2 * sum(energy)
    assert lhs <= rhs + 1e-9 * max(1.0, rhs)

# First-failure role assignment: all earlier roles pass, the first fails,
# and later roles are unconstrained, for arbitrary finite test strings.
for _ in range(2200):
    bs = [rng.choice((False, True)) for _ in range(rng.randrange(0, 80))]
    first = next((i for i, b in enumerate(bs) if not b), None)
    assert (first is None) == all(bs)
    if first is not None:
        assert all(bs[:first]) and not bs[first]
    for n in range(min(len(bs), 12)):
        assert ([True] * n + [False] + bs)[n] is False

# Finite first-success weights and geometric failure-history summation,
# checked exactly over rational data, including q=0 and q=1.
from fractions import Fraction
for _ in range(900):
    q = Fraction(rng.randrange(0, 16), 15)
    N = rng.randrange(0, 24)
    mass = sum(((1-q) * (q**n) for n in range(N)), Fraction(0))
    assert mass + q**N == 1
    assert mass <= 1
    r = Fraction(rng.randrange(0, 15), 15)
    A = Fraction(rng.randrange(0, 25), 7)
    assert sum((A*r**n for n in range(N)), Fraction(0)) <= A/(1-r)

print('PASS: new finite bridges (Tonelli 2200, stops 2200, proper paths exhaustive, rows 1600, first-failure 2200, rational first-success 900)')
