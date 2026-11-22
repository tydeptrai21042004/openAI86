#!/usr/bin/env python3
"""Deterministic numerical/fraction sanity checks; NOT Lean kernel verification.

Covers mathematical statements of the newly authored projection, first-success,
finite Cauchy--Schwarz, and noncommutative contraction modules. These tests catch
counterexamples/regressions; the Lean proofs still require a Lake build.
"""
from fractions import Fraction
import numpy as np

rng = np.random.default_rng(861122)
checks = {"nested_projection": 0, "first_success_exact": 0,
          "finite_cauchy_schwarz": 0, "compression_row": 0,
          "noncommuting_perturbation": 0, "prefix_row_counterexample": 0}

for n in range(1, 11):
    for _ in range(100):
        Q, _ = np.linalg.qr(rng.standard_normal((n, n)))
        x = rng.standard_normal(n)
        # Arbitrary nested subspaces (same orthogonal basis, not just coordinates)
        ranks = sorted(rng.integers(0, n + 1, size=30))
        Ps = [Q[:, :r] @ Q[:, :r].T for r in ranks]
        inc = sum(float(np.linalg.norm((Ps[k + 1] - Ps[k]) @ x) ** 2)
                  for k in range(len(Ps)-1))
        terminal = float(np.linalg.norm(Ps[-1] @ x) ** 2 -
                         np.linalg.norm(Ps[0] @ x) ** 2)
        assert abs(inc - terminal) < 1e-9 * (1 + np.linalg.norm(x)**2)
        assert inc <= np.linalg.norm(x)**2 + 1e-9
        checks["nested_projection"] += 1

for _ in range(1000):
    N = int(rng.integers(0, 30))
    q = [Fraction(int(rng.integers(0, 100)), 100) for _ in range(N)]
    surv = Fraction(1)
    first = Fraction(0)
    for qi in q:
        first += surv * (1 - qi)
        surv *= qi
    assert first + surv == 1
    r = max(q, default=Fraction(0))
    assert surv <= r**N
    assert first >= 1 - r**N
    checks["first_success_exact"] += 1

for _ in range(2500):
    count = int(rng.integers(1, 32))
    a = rng.standard_normal(count)
    b = rng.standard_normal(count)
    assert (a @ b)**2 <= (a @ a)*(b @ b) + 1e-8
    checks["finite_cauchy_schwarz"] += 1

for _ in range(750):
    rows = int(rng.integers(1, 20))
    cols = int(rng.integers(1, 20))
    tau = rng.random() * 2
    err = rng.standard_normal((rows, cols))
    norm = np.linalg.norm(err, axis=1)
    err = err * (tau / np.maximum(norm, 1e-10))[:, None]
    sig = rng.standard_normal((rows, cols))
    E = np.sum(sig*sig, axis=0)
    lhs = float(np.sum(np.sum(err * sig, axis=1)**2))
    rhs = float(tau*tau*np.sum(E))
    assert lhs <= rhs + 1e-8
    checks["compression_row"] += 1

for _ in range(900):
    n = int(rng.integers(1, 6))
    length = int(rng.integers(0, 15))
    Aprod = np.eye(n)
    Bprod = np.eye(n)
    budget = 0.0
    for __ in range(length):
        A = rng.standard_normal((n,n))
        B = rng.standard_normal((n,n))
        A /= max(np.linalg.norm(A, ord=2), 1.0)
        B /= max(np.linalg.norm(B, ord=2), 1.0)
        Aprod = Aprod @ A
        Bprod = Bprod @ B
        budget += float(np.linalg.norm(A - B, ord=2))
    err = float(np.linalg.norm(Aprod - Bprod, ord=2))
    assert err <= budget + 1e-8
    checks["noncommuting_perturbation"] += 1


# Parseval rows evaluated at *different* nested prefix levels need not be
# a contraction. The exact ratio 29/25 exceeds one.
a = Fraction(3,5)**2 + Fraction(-7,5)**2
assert a == Fraction(58,25) and a > 2
checks["prefix_row_counterexample"] += 1
print("PASS continuation projection/probability checks", checks)
print("PASS rational varying-prefix counterexample: ratio", a/Fraction(2), "(> 1)")
