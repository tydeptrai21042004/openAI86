#!/usr/bin/env python3
"""Exact regression checks for V52 components; never Lean certificates."""
from fractions import Fraction as Q
from itertools import product
import random
import cmath
import math

random.seed(52052)

# Lemma 9.1 p.84: min(alpha*M^2, L*x_b*y_b) and the two role budgets
# imply (sum mass)^2 <= L*alpha*M^4.
for _ in range(1200):
    n = random.randint(1, 12)
    M = Q(random.randint(2, 30), random.randint(1, 5))
    alpha = Q(random.randint(1, 12), random.randint(1, 8))
    L = Q(random.randint(1, 12), random.randint(1, 5))
    rawx = [Q(random.randint(0, 30), random.randint(1, 8)) for _ in range(n)]
    rawy = [Q(random.randint(0, 30), random.randint(1, 8)) for _ in range(n)]
    # Normalize both role budgets to <= M.
    sx, sy = sum(rawx), sum(rawy)
    x = [v*M/sx if sx else Q(0) for v in rawx]
    y = [v*M/sy if sy else Q(0) for v in rawy]
    mass = []
    for a, b in zip(x, y):
        cap = min(alpha*M*M, L*a*b)
        # Exact rational fraction of the available block cap.
        mass.append(cap * Q(random.randint(0, 100), 100))
    assert sum(x) <= M and sum(y) <= M
    assert all(0 <= m <= alpha*M*M and m <= L*a*b
               for m, a, b in zip(mass, x, y))
    assert sum(mass)**2 <= L*alpha*M**4

# Section 10.3: explicit q and alpha choices.
for _ in range(1000):
    C19 = Q(random.randint(1, 100), random.randint(1, 10))
    C5 = Q(random.randint(1, 100), random.randint(1, 10))
    C4 = Q(random.randint(0, 100), random.randint(1, 10))
    eps = Q(random.randint(1, 100), random.randint(1, 10))
    d = 1/(16*(C19*C5+1))
    q = 2+d
    alpha = eps/(4*(C4+1))
    assert 2 < q < 3
    assert C19*C5*(q-2) < Q(1, 8)
    assert alpha > 0 and alpha*C4 < eps/2

# Lemma 4.3 p.17: repeated unimodular samples with per-step error e.
# Use exact rational complex pairs and fourth-root phases.
units = [(Q(1),Q(0)),(Q(-1),Q(0)),(Q(0),Q(1)),(Q(0),Q(-1))]
def cadd(a,b): return (a[0]+b[0],a[1]+b[1])
def cmul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def norm2(a): return a[0]*a[0]+a[1]*a[1]
for _ in range(800):
    M = random.randint(1, 12)
    delta = Q(random.randint(2, 20), random.randint(1, 5))
    e = delta/Q(4*M)
    f = (delta, Q(0))
    vals = [f]
    for j in range(M):
        u = random.choice(units)
        # Pick a rational error with modulus <= e.
        er = Q(random.randint(-2,2), 20)*e
        ei = Q(random.randint(-2,2), 20)*e
        err = (er,ei)
        assert norm2(err) <= e*e
        vals.append(cadd(cmul(u, vals[-1]), err))
    for v in vals:
        # The triangle-inequality lower bound is 3δ/4 - M e = δ/2.
        assert math.sqrt(float(norm2(v))) + 1e-12 >= float(delta/2)

print('V52 exact regressions: 3,000 passed (1,200 nonfuture-pair, 1,000 parameter-order, 800 Weyl samples)')
print('These tests validate finite exact/rational models only; they are not Lean kernel certificates.')
