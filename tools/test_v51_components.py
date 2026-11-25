#!/usr/bin/env python3
"""Exact arithmetic regressions for V51; these are not Lean certificates."""
from fractions import Fraction as Q
from itertools import product
import random

random.seed(51051)

# Lemma 4.3 / Lemma 7.2: the two progression constraints have precisely
# the two-parameter nullspace c_j(h+j h'), c=(-1,3,-3,1).
for _ in range(1000):
    m0 = Q(random.randint(-20, 20), random.randint(1, 9))
    m1 = Q(random.randint(-20, 20), random.randint(1, 9))
    m2 = -3*m0 - 2*m1
    m3 = 2*m0 + m1
    assert m0+m1+m2+m3 == 0
    assert m1+2*m2+3*m3 == 0
    h = -m0
    hp = m0 + m1/3
    assert m0 == -h
    assert m1 == 3*(h+hp)
    assert m2 == -3*(h+2*hp)
    assert m3 == h+3*hp
    assert -m0*m0 + m1*m1/3 - m2*m2/3 + m3*m3 == 0

# Section 5: four-slot product telescoping over exact rationals.
for _ in range(1000):
    a = [Q(random.randint(-7, 7), random.randint(1, 7)) for _ in range(4)]
    b = [Q(random.randint(-7, 7), random.randint(1, 7)) for _ in range(4)]
    lhs = a[0]*a[1]*a[2]*a[3] - b[0]*b[1]*b[2]*b[3]
    rhs = ((a[0]-b[0])*a[1]*a[2]*a[3]
           + b[0]*(a[1]-b[1])*a[2]*a[3]
           + b[0]*b[1]*(a[2]-b[2])*a[3]
           + b[0]*b[1]*b[2]*(a[3]-b[3]))
    assert lhs == rhs

# Proposition 8.9: exact finite colour partition and event-error budget.
for _ in range(500):
    n = random.randint(1, 15)
    gcount = random.randint(1, 7)
    colour = [random.randrange(gcount) for _ in range(n)]
    p = [Q(random.randint(-5, 5), random.randint(1, 6)) for _ in range(n)]
    err = [Q(random.randint(-4, 4), random.randint(1, 6)) for _ in range(n)]
    t = [p[i]+err[i] for i in range(n)]
    total = sum(x*x for x in t)
    by_colour = sum(sum(t[i] for i in range(n) if colour[i] == g)**2
                    for g in range(gcount))
    # The actual theorem uses a supplied within-colour near-orthogonality
    # factor K; this test checks the exact partition identity only.
    partition_energy = sum(t[i]*t[i] for g in range(gcount)
                           for i in range(n) if colour[i] == g)
    assert partition_energy == total
    assert by_colour >= 0

print("V51 exact regressions: 2,500 passed (1,000 Weyl, 1,000 product, 500 colour partition)")
print("These tests are not Lean kernel certificates and do not verify the analytic hypotheses.")
