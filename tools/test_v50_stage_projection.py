#!/usr/bin/env python3
"""Exact finite-dimensional regression models for the V50 stage-span bridge.

These tests check rational linear algebra only. They are not Lean kernel
certificates and do not establish the paper's geometric refinement premise.
"""
from fractions import Fraction as F
from random import Random
import json
import sys

rng = Random(50)


def zeros(n, m):
    return [[F(0) for _ in range(m)] for _ in range(n)]


def transpose(A):
    return [list(row) for row in zip(*A)] if A else []


def mm(A, B):
    if not A:
        return []
    return [[sum((A[i][k] * B[k][j] for k in range(len(B))), F(0))
             for j in range(len(B[0]))] for i in range(len(A))]


def rank(A):
    A = [row[:] for row in A]
    if not A:
        return 0
    n, m = len(A), len(A[0])
    r = 0
    for c in range(m):
        pivot = next((i for i in range(r, n) if A[i][c]), None)
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        q = A[r][c]
        A[r] = [x / q for x in A[r]]
        for i in range(n):
            if i != r and A[i][c]:
                q = A[i][c]
                A[i] = [x - q*y for x, y in zip(A[i], A[r])]
        r += 1
        if r == n:
            break
    return r


def inverse(A):
    n = len(A)
    M = [A[i][:] + [F(int(i == j)) for j in range(n)] for i in range(n)]
    for c in range(n):
        pivot = next((i for i in range(c, n) if M[i][c]), None)
        if pivot is None:
            raise ValueError("singular matrix")
        M[c], M[pivot] = M[pivot], M[c]
        q = M[c][c]
        M[c] = [x / q for x in M[c]]
        for i in range(n):
            if i != c and M[i][c]:
                q = M[i][c]
                M[i] = [x - q*y for x, y in zip(M[i], M[c])]
    return [row[n:] for row in M]


def mat_eq(A, B):
    return len(A) == len(B) and all(len(x) == len(y) and x == y for x, y in zip(A, B))


def orth_proj(A):
    # A has full column rank; P = A(A^T A)^(-1)A^T.
    At = transpose(A)
    return mm(mm(A, inverse(mm(At, A))), At)


def hstack(A, B):
    return [a + b for a, b in zip(A, B)]


def sub(A, B):
    return [[x-y for x, y in zip(a, b)] for a, b in zip(A, B)]


def random_fraction():
    return F(rng.randint(-4, 4), rng.randint(1, 5))


def one_case():
    # Fine columns model the next-stage atom/label family.  Coarse columns
    # are arbitrary exact linear combinations of those fine columns.
    ambient = rng.randint(5, 8)
    fine_count = rng.randint(2, min(4, ambient))
    coarse_count = rng.randint(1, fine_count)
    Fmat = zeros(ambient, fine_count)
    for j in range(fine_count):
        Fmat[j][j] = F(1)
        for i in range(fine_count, ambient):
            Fmat[i][j] = random_fraction()
    Cmat = zeros(fine_count, coarse_count)
    for j in range(coarse_count):
        Cmat[j][j] = F(1)
        for i in range(coarse_count, fine_count):
            Cmat[i][j] = random_fraction()
    coarse = mm(Fmat, Cmat)

    assert rank(Fmat) == fine_count
    assert rank(coarse) == coarse_count
    assert rank(Fmat) == rank(hstack(Fmat, coarse))  # coarse span is included

    Pf = orth_proj(Fmat)
    Pc = orth_proj(coarse)
    assert mat_eq(mm(Pc, Pf), Pc)
    assert mat_eq(mm(Pf, Pc), Pc)

    # Exact synthesis-increment identity for arbitrary coefficients.
    c = [random_fraction() for _ in range(fine_count)]
    d = [random_fraction() for _ in range(fine_count)]
    lhs = mm(Fmat, [[c[i]-d[i]] for i in range(fine_count)])
    rhs = sub(mm(Fmat, [[c[i]] for i in range(fine_count)]),
              mm(Fmat, [[d[i]] for i in range(fine_count)]))
    assert mat_eq(lhs, rhs)


N = 500
for _ in range(N):
    one_case()

print(json.dumps({
    "status": "PASS_EXACT_RATIONAL_MODEL_ONLY",
    "cases": N,
    "checks_per_case": [
        "coarse local columns lie in the next-stage span",
        "actual rational orthogonal projections are nested",
        "projection products satisfy P_coarse P_fine = P_coarse",
        "coefficient synthesis increments are exact"
    ],
    "lean_kernel_certificate": False,
    "paper_geometric_refinement_derived": False
}, indent=2))
