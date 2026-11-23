#!/usr/bin/env python3
"""Independent exact-arithmetic checks for four V10 finite bridges.

These are finite counterexample/regression tests, NOT Lean-kernel certificates.
No numerical or combinatorial test proves an arbitrary theorem.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import product
import math
import random


def R(a: int, b: int = 1) -> F:
    return F(a, b)


def check_threshold() -> int:
    tests = 0
    values = [R(0), R(1, 10), R(1, 3), R(1), R(3, 2)]
    betas = [R(1, 10), R(1, 2), R(9, 10)]
    for a, b, u, v, beta in product(range(5), range(5), values, values, betas):
        bad = int(a + b > 0 or beta < u + v)
        upper = a + b + (u + v) / beta
        assert bad <= upper, (a, b, u, v, beta)
        tests += 1
    return tests


def check_height_lag(rng: random.Random) -> int:
    tests = 0
    for _ in range(1700):
        H, lag = rng.randint(1, 40), rng.randint(0, 8)
        p = [rng.randint(0, 2)]
        for _ in range(H + lag + 1):
            p.append(p[-1] + rng.randrange(0, 4))
        left = sum(p[h + lag] - p[h] for h in range(H))
        right = sum(p[H + r] - p[r] for r in range(lag))
        cap = max(p)
        assert left == right
        assert left <= lag * cap
        tests += 1
    return tests


def check_position_gap(rng: random.Random) -> int:
    tests = 0
    for _ in range(2500):
        N = rng.randint(0, 12)
        p = [rng.randrange(0, 10)]
        c = []
        for i in range(N + 1):
            c.append(p[i] + rng.randint(0, 15))
            if i < N:
                p.append(c[-1] + rng.randint(0, 15))
        gap = sum(c[i] - p[i] for i in range(N + 1))
        assert gap <= c[N] - p[0]
        assert gap <= c[N]
        tests += 1
    # Endpoint inclusion really is essential for a *nonnegative* last gap.
    P, C = [0, 3], [1, 2]
    assert P[0] <= C[0] <= P[1]
    assert C[-1] - P[-1] < 0
    return tests + 1


def check_rank_density(rng: random.Random) -> int:
    tests = 0
    for _ in range(1500):
        M = rng.randint(1, 15)
        T = rng.randint(1, 20)
        active = [[rng.random() < 0.3 for _ in range(M)] for _ in range(T)]
        # Make every rank activated at time t appear in a set of at least rank+1 elements.
        size = [max((r + 1 for r in range(M) if active[t][r]), default=1)
                + rng.randint(0, 3) for t in range(T)]
        max_occ = max(sum(active[t][r] for t in range(T)) for r in range(M))
        mass = sum(sum(R(1, size[t]) for r in range(M) if active[t][r])
                   for t in range(T))
        harmonic = sum((R(1, r + 1) for r in range(M)), R(0))
        assert mass <= max_occ * harmonic
        tests += 1
    return tests


def check_full_bridge(rng: random.Random) -> int:
    tests = 0
    # Representative cases in which pointwise badness is dominated by
    # two interleaved log differences, plus zero exception incidence.
    for _ in range(1200):
        N, H, lag = rng.randint(0, 8), rng.randint(2, 40), rng.randint(0, 5)
        # Generating monotone p in both axes and interleaved c allows exact
        # tests of all hypotheses without supplying fake incidence budgets.
        height = [0]
        for h in range(H + lag + 2):
            height.append(height[-1] + rng.choice([0, 0, 1]))
        p = [[4 * i + height[h] for h in range(H + lag + 2)]
             for i in range(N + 1)]
        c = [[p[i][h] + rng.randint(0, 3) for h in range(H + lag + 2)]
             for i in range(N + 1)]
        L = max(max(row) for row in c)
        vertical = [[p[i][h + lag] - p[i][h] for h in range(H)]
                    for i in range(N + 1)]
        horizontal = [[c[i][h + lag] - p[i][h + lag] for h in range(H)]
                      for i in range(N + 1)]
        bad = [[int(vertical[i][h] + horizontal[i][h] > 0)
                for h in range(H)] for i in range(N + 1)]
        assert all(sum(vertical[i]) <= lag * L for i in range(N + 1))
        assert all(sum(horizontal[i][h] for i in range(N + 1)) <= L
                   for h in range(H))
        assert all(bad[i][h] <= vertical[i][h] + horizontal[i][h]
                   for i in range(N + 1) for h in range(H))
        delta = F(min((sum(bad[i]) for i in range(N + 1)), default=0), H)
        # Check final conditional conclusion only when its absorption
        # condition is actually satisfied; no vacuous assertion that it always is.
        if delta > 0 and 2 * lag * L <= delta * H:
            assert N + 1 <= 2 * L / delta
        tests += 1
    return tests




def check_nested_set_rank_threshold(rng: random.Random) -> int:
    tests = 0
    ranks = [lambda n: n // 3, lambda n: n.bit_length() - 1 if n else 0,
             lambda n: n // 10]
    for _ in range(1700):
        universe = list(range(rng.randint(1, 80)))
        old = {x for x in universe if rng.random() < 0.2}
        new = old | {x for x in universe if rng.random() < 0.2}
        cur = new | {x for x in universe if rng.random() < 0.2}
        rank = rng.choice(ranks)
        a, b, c = rank(len(old)), rank(len(new)), rank(len(cur))
        assert a <= b <= c
        u = R(rng.randint(0, 20), 30)
        v = R(rng.randint(0, 20), 30)
        beta = R(rng.randint(1, 9), 10)
        bad = int(a != c or beta < u + v)
        bound = (b - a) + (c - b) + (u + v) / beta
        assert bad <= bound
        tests += 1
    return tests

def check_sparse_projection_rows(rng: random.Random) -> int:
    try:
        import numpy as np
    except ImportError:
        print("[skip] numpy unavailable; sparse projection numeric checks skipped")
        return 0
    np_rng = np.random.default_rng(12345)
    tests = 0
    for _ in range(1500):
        d = 5
        K = rng.randrange(1, 6)
        layers = rng.randrange(0, 5)
        # Orthogonal-row Bessel family: B^T B <= I.
        U, _ = np.linalg.qr(np_rng.normal(size=(d, d)))
        B = U[:rng.randrange(1, d + 1), :]
        x = np_rng.normal(size=d)
        # Each layer at each sampled depth is an orthogonal projection;
        # commutativity is neither assumed nor used.
        outputs = []
        for _k in range(K):
            y = x.copy()
            for _j in range(layers):
                Q, _ = np.linalg.qr(np_rng.normal(size=(d, d)))
                rank = rng.randint(0, d)
                y = Q[:, :rank] @ (Q[:, :rank].T @ y)
            outputs.append(y)
        choices = [rng.randrange(K) for _ in range(B.shape[0])]
        lhs = sum(float(B[r] @ outputs[choices[r]]) ** 2
                  for r in range(B.shape[0]))
        rhs = K * float(x @ x)
        assert lhs <= rhs + 1e-10 * max(1., rhs), (lhs, rhs)
        tests += 1
    return tests


def main() -> None:
    rng = random.Random(866101)
    categories = {
        'integer_badness_indicator': check_threshold(),
        'nested_finite_set_floor_rank': check_nested_set_rank_threshold(rng),
        'height_lag_exact': check_height_lag(rng),
        'interleaved_position_gap': check_position_gap(rng),
        'ranked_exceptional_fraction': check_rank_density(rng),
        'combined_height_and_position': check_full_bridge(rng),
        'noncommuting_sparse_choice_rows': check_sparse_projection_rows(rng),
    }
    for name, count in categories.items():
        print(f'PASS {name}: {count:,} tests')
    print(f'TOTAL: {sum(categories.values()):,} independent finite tests PASS')
    print('LIMIT: no Lean kernel proof; complete manuscript goals remain open')


if __name__ == '__main__':
    main()
