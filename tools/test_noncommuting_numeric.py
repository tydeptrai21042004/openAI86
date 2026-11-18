#!/usr/bin/env python3
"""Deterministic mathematical sanity checks, not a Lean proof."""
import numpy as np

p = np.array([[1.,0.],[0.,0.]])
q = np.full((2,2),.5)
e = np.eye(2)
assert np.allclose(p@p,p) and np.allclose(q@q,q)
assert np.allclose(p,p.T) and np.allclose(q,q.T)
assert not np.allclose(p@q,q@p)
assert np.linalg.norm(p,2) <= 1+1e-12 and np.linalg.norm(q,2) <= 1+1e-12

rng=np.random.default_rng(86086)
checks=0
for n in range(1,9):
    for _ in range(100):
        pairs=[(rng.normal(size=(2,2))/4, rng.normal(size=(2,2))/4) for i in range(n)]
        def left(ps):
            z=e.copy()
            for a,b in ps:z=z@a
            return z
        def right(ps):
            z=e.copy()
            for a,b in ps:z=z@b
            return z
        # The Lean orderedLeft folds from the list HEAD on the left.
        def left_rec(ps):
            return e if not ps else ps[0][0] @ left_rec(ps[1:])
        def right_rec(ps):
            return e if not ps else ps[0][1] @ right_rec(ps[1:])
        def difference(ps):
            return np.zeros((2,2)) if not ps else (ps[0][0]-ps[0][1])@left_rec(ps[1:])+ps[0][1]@difference(ps[1:])
        def budget(ps):
            return 0. if not ps else np.linalg.norm(ps[0][0]-ps[0][1],2)*np.linalg.norm(left_rec(ps[1:]),2)+np.linalg.norm(ps[0][1],2)*budget(ps[1:])
        err=left_rec(pairs)-right_rec(pairs)
        assert np.allclose(err,difference(pairs),atol=1e-10)
        assert np.linalg.norm(err,2) <= budget(pairs)+1e-10
        checks+=1
print(f'PASS: self-adjoint idempotent/noncommuting projections and {checks} ordered-product algebra/norm checks')
print('STATUS: NUMERICAL_SANITY_ONLY. No Lean kernel compilation performed.')
