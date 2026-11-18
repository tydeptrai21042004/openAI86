# A relevant analytic inequality — handwritten argument only

For Schwartz inputs `f_j` and `0 < r < R`, define

    T^{r,R}(f_1,f_2,f_3)(x)
      = ∫_{r<|t|<R} f_1(x-t) f_2(x-2t) f_3(x-3t) dt/t.

Triangle inequality, Tonelli, Hölder in `x`, and translation invariance yield

    ||T^{r,R}(f_1,f_2,f_3)||_1
      <= ∫_{r<|t|<R} (1/|t|) Π_j ||f_j(·-jt)||_3 dt
      = 2 log(R/r) Π_j ||f_j||_3.

This elementary bound is NOT uniform in `r,R`. Theorem 1.1 asserts an
estimate independent of the truncation scales after cancellation and
passage to the principal value. Its proof requires Sections 2–10 of the
source manuscript. The integral argument in this note is **not formalized
by Lean** and cannot substitute for the missing proof.

The Lean file `SymmetricKernel.lean` gives the exact pointwise
symmetrization of the integrand that is used when studying `r -> 0`.
