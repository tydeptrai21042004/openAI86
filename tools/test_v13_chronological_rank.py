#!/usr/bin/env python3
"""Independent exact finite regressions for V13 manuscript Lemmas 8.5/8.6.

These are NOT Lean kernel proofs. They test first-entry ordering of arbitrary
nested finite label sets, rank permutation, exceptional-density accounting,
and automatic initial bad-height counts with Fractions.
"""
from fractions import Fraction
import itertools
import random

rng = random.Random(20261122)
checks = dict(first_entry=0, rank_injective=0, rank_le_size=0,
              harmonic_reindex=0, density=0, initial_heights=0,
              adversarial_fixed_order=0, absent_labels=0, exhaustive_small_chains=0)


def verify_case(M,T):
    # Genuine nested sets, not prefixes of the native index order.
    order=list(range(M)); rng.shuffle(order)
    entry={r:rng.randrange(T) for r in order} if T else {}
    S=[{r for r in range(M) if entry[r]<=t} for t in range(T)]
    rank_order=sorted(range(M), key=lambda r:(entry[r],r))
    ranks={r:j+1 for j,r in enumerate(rank_order)}
    assert sorted(ranks.values())==list(range(1,M+1))
    checks['rank_injective']+=1
    for r in range(M):
        assert entry[r]==min(t for t in range(T) if r in S[t])
        checks['first_entry']+=1
    for t in range(T):
        for r in S[t]:
            prefix={s for s in range(M) if (entry[s],s)<=(entry[r],r)}
            assert prefix<=S[t]
            assert ranks[r]<=len(S[t])
            checks['rank_le_size']+=1
    harmonic=sum((Fraction(1,r) for r in range(1,M+1)),Fraction(0))
    computed=sum((Fraction(1,ranks[r]) for r in range(M)),Fraction(0))
    assert harmonic==computed
    checks['harmonic_reindex']+=1
    # E_t may contain labels outside S_t; the manuscript intersects them.
    E=[]
    for t in range(T):
        E.append({r for r in range(M) if rng.randrange(4)==0})
    count={r:sum(r in E[t] and r in S[t] for t in range(T)) for r in range(M)}
    A=max(count.values(),default=0)
    left=sum((Fraction(len(E[t]&S[t]),len(S[t])) if S[t] else Fraction(0)
              for t in range(T)),Fraction(0))
    right=A*computed
    assert left<=right, (M,T,order,S,E,left,right)
    checks['density']+=1

for M in range(1,8):
    for T in range(1,9):
        for _ in range(250):
            verify_case(M,T)

# Exhaustively cover arbitrary nested chains, including labels absent from
# every observed set, the corner case handled by extendFiniteChain.
for M in range(0,5):
    for T in range(0,5):
        for times in itertools.product(range(T+1), repeat=M):
            sets=[{r for r in range(M) if times[r]<=t} for t in range(T)]
            order=sorted(range(M),key=lambda r:(times[r],r))
            ranks={r:i+1 for i,r in enumerate(order)}
            assert sorted(ranks.values())==list(range(1,M+1))
            for t in range(T):
                for r in sets[t]:
                    assert ranks[r]<=len(sets[t]); checks['rank_le_size']+=1
            absent=sum(1 for r in range(M) if times[r]==T)
            checks['absent_labels']+=absent
            for _ in range(3):
                exc=[{r for r in range(M) if rng.randrange(2)} for t in range(T)]
                counted=[sum(r in sets[t]&exc[t] for t in range(T)) for r in range(M)]
                A=max(counted,default=0)
                lhs=sum((Fraction(len(sets[t]&exc[t]),len(sets[t])) if sets[t]
                         else Fraction(0) for t in range(T)),Fraction(0))
                H=sum((Fraction(1,i+1) for i in range(M)),Fraction(0))
                assert lhs<=A*H
                checks['exhaustive_small_chains']+=1

for J in range(0,90):
    for lag in range(0,90):
        total=sum(1 for h in range(J) if h<lag)
        assert total==min(J,lag)
        checks['initial_heights']+=1

# The V12 original-index rank hypothesis is not automatic for growing sets.
# Example: label 6 appears alone at the first step, so its native index + 1
# is 7 but its constructed first-entry rank is 1.
S0={6}
assert 6+1 > len(S0)
assert sorted(S0,key=lambda x:(0,x)).index(6)+1==len(S0)
checks['adversarial_fixed_order']+=1

print('V13 exact chronological-rank/initial-height regressions PASS',checks,
      'total=',sum(checks.values()),'; not Lean kernel proof')
