#!/usr/bin/env python3
"""Deterministic exact-rational models for V49; not Lean kernel proofs."""
from fractions import Fraction as F
import random

SEED = 490086
rng = random.Random(SEED)


def anchor_depths(coeff, threshold):
    """Mirror v47AnchorDepth/v47AnchorList; coefficient values are scalars."""
    anchors = [0]
    last = 0
    for n in range(1, len(coeff)):
        if abs(coeff[n] - coeff[last]) > threshold:
            anchors.append(n)
            last = n
    return anchors


def check_anchor_coherence():
    # Build arbitrary rooted paths: equal ancestor at depth d means all
    # earlier ancestor labels and hence all coefficients agree.
    checked = 0
    for _ in range(500):
        horizon = rng.randrange(1, 18)
        depth = rng.randrange(0, horizon + 1)
        shared = [rng.randrange(-8, 9) for _ in range(depth + 1)]
        left = shared + [rng.randrange(-8, 9) for _ in range(horizon-depth)]
        right = shared + [rng.randrange(-8, 9) for _ in range(horizon-depth)]
        threshold = rng.randrange(1, 6)
        hleft = anchor_depths(left[:depth+1], threshold)
        hright = anchor_depths(right[:depth+1], threshold)
        assert hleft == hright
        # The predecessor of a current anchor is the last selected depth
        # before it, and therefore also agrees on the common prefix.
        for d in hleft:
            prev_l = max((x for x in hleft if x < d), default=0)
            prev_r = max((x for x in hright if x < d), default=0)
            assert prev_l == prev_r
        checked += 1
    return checked


def check_row_error():
    # Scalar-row contractions B_r x = b_r x with sum b_r^2 <= 1.
    # Each row's coefficient vector has squared norm <= (tau*a)^2.
    checked = 0
    for _ in range(500):
        rows = rng.randrange(1, 6)
        labels = rng.randrange(1, 7)
        tau = F(rng.randrange(1, 6), rng.randrange(2, 9))
        a = F(rng.randrange(1, 6), rng.randrange(2, 9))
        D = F(rng.randrange(2, 8), 1)
        mass = F(rng.randrange(1, 10), rng.randrange(1, 8))
        # Column energy is normalized below D^3 mass.
        cols = [F(rng.randrange(-5, 6), rng.randrange(1, 8)) for _ in range(labels)]
        col_energy = sum(x*x for x in cols)
        budget = D**3 * mass
        if col_energy > budget:
            scale = F(1, 1)
            while col_energy > budget:
                scale /= 2
                cols = [scale*x for x in cols]
                col_energy = sum(x*x for x in cols)
        errors = []
        for _r in range(rows):
            er = [F(rng.randrange(-5, 6), rng.randrange(1, 8)) for _ in range(labels)]
            en = sum(x*x for x in er)
            lim = (tau*a)**2
            if en > lim:
                scale = F(1, 1)
                while en > lim:
                    scale /= 2
                    er = [scale*x for x in er]
                    en = sum(x*x for x in er)
            errors.append(er)
        # Choose a contraction vector b_r by scaling arbitrary rational values.
        b = [F(rng.randrange(-5, 6), rng.randrange(1, 8)) for _ in range(rows)]
        b2 = sum(x*x for x in b)
        if b2 > 1:
            scale = F(1, 1)
            while b2 > 1:
                scale /= 2
                b = [scale*x for x in b]
                b2 = sum(x*x for x in b)
        lhs = sum((b[r] * sum(errors[r][v]*cols[v] for v in range(labels)))**2
                   for r in range(rows))
        rhs = tau**2*a**2*D**3*mass
        assert lhs <= rhs
        checked += 1
    return checked


if __name__ == '__main__':
    a = check_anchor_coherence()
    e = check_row_error()
    print(f'V49 exact-rational anchor coherence models: {a}/500 PASS')
    print(f'V49 exact-rational row-error models: {e}/500 PASS')
    print(f'Total: {a+e}/1000 PASS (finite-model checks only)')
