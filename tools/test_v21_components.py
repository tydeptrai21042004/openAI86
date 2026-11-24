#!/usr/bin/env python3
"""Deterministic exact model regression. This is NOT Lean verification."""
from fractions import Fraction as F
from itertools import permutations
from math import prod, factorial
import random
rng=random.Random(86021)
counts={}
def check(group, condition):
    if not condition: raise AssertionError(group)
    counts[group]=counts.get(group,0)+1

def det(A):
    n=len(A)
    return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))*prod(A[i][p[i]] for i in range(n)) for p in permutations(range(n)))

for _ in range(1800):
    n=rng.randrange(0,9); H=rng.randrange(1,21)
    p=[rng.randint(-H,H) for i in range(n)]; q=[rng.randint(1,H) for i in range(n)]
    Q=prod(q)
    check('denominator_size',0<Q<=H**n)
    for i in range(n):
        a=p[i]*prod(q[:i]+q[i+1:]); check('denominator_coordinate',Q*F(p[i],q[i])==a and abs(a)<=H**n)
for _ in range(1000):
    n=rng.randrange(1,5); H=rng.randrange(1,10)
    A=[[rng.randint(-H,H) for j in range(n)] for i in range(n)]; b=[rng.randint(-H,H) for i in range(n)]
    d=det(A); adj=[[(-1)**(i+j)*det([[A[r][c] for c in range(n) if c!=i] for r in range(n) if r!=j]) for j in range(n)] for i in range(n)]
    check('adjugate_identity',all(sum(adj[i][k]*A[k][j] for k in range(n))==d*(i==j) for i in range(n) for j in range(n)))
    if d:
        num=[sum(adj[i][j]*b[j] for j in range(n)) for i in range(n)]; c=[F(k,d) for k in num]
        check('cramer_bridge',all(sum(A[i][j]*c[j] for j in range(n))==b[i] for i in range(n)))
        check('cramer_l1',sum(map(abs,c))<=n*factorial(n)*H**n)
for _ in range(800):
    T=rng.randrange(0,8); X=range(2**T); stops={(n,k) for n in range(T+1) for k in range(2**n) if rng.random()<.18}
    def cell(n,x): return x>>(T-n)
    cuts=[next(n for n in range(T+1) if (n,cell(n,x)) in stops or n==T) for x in X]
    labels=[(n,cell(n,x)) for x,n in zip(X,cuts)]
    check('cut_coverage',all(0<=n<=T for n in cuts))
    check('first_stop',all(all((j,cell(j,x)) not in stops for j in range(cuts[x])) for x in X))
    check('cut_fibers',all(all(labels[y]==labels[x] for y in X if cell(cuts[x],y)==cell(cuts[x],x)) for x in X))
    # Local moment preservation on each cut by actual conditional averages.
    z=[F(rng.randint(-20,20),rng.randrange(1,9)) for x in X]
    for lab in set(labels):
        ix=[x for x in X if labels[x]==lab]; g=sum(z[x] for x in ix)/len(ix)
        check('cut_moment',len(ix)*g==sum(z[x] for x in ix))
for _ in range(1000):
    # Rational subspace represented by nullspace of a rational row.
    n=rng.randrange(1,12); a=[rng.randint(-9,9) for j in range(n)]; w=[F(rng.randint(-9,9),rng.randrange(1,8)) for j in range(n)]; k=rng.choice(list(range(-10,0))+list(range(1,11)))
    v=sum(x*y for x,y in zip(a,w)); check('saturation', (k*v==0)==(v==0))
    n=rng.randrange(1,16); N=rng.randrange(1,18); coeff=[F(rng.randint(-20,20),rng.randrange(1,10)) for i in range(n)]; masks=[{i for i in range(n) if rng.random()<.3} for x in range(N)]; weights=[F(rng.randrange(0,15),rng.randrange(1,9)) for x in range(N)]; D=max(map(len,masks))
    S=sum(w*sum(coeff[i] for i in s)**2 for w,s in zip(weights,masks)); B=sum(w*sum(coeff[i]**2 for i in s) for w,s in zip(weights,masks))
    check('integrated_overlap',S<=D*B)
    check('supported_square_sum',B==sum(coeff[i]**2*sum(w for w,s in zip(weights,masks) if i in s) for i in range(n)))
for _ in range(1400):
    n=rng.randrange(1,32); pred=[[j for j in range(i) if rng.random()<.15] for i in range(n)]; ranks=[]
    for i in range(n):ranks.append(1+max((ranks[j] for j in pred[i]),default=0))
    C=max(ranks); check('chain_rank',all(1<=r<=C for r in ranks) and all(ranks[j]<ranks[i] for i in range(n) for j in pred[i]))
    # Independently enumerate all attainable chain lengths by dynamic sets.
    lengths=[]
    for i in range(n):lengths.append({0}|{k+1 for j in pred[i] for k in lengths[j]})
    check('rank_first_absent',all(ranks[i]==next(k for k in range(n+1) if k not in lengths[i]) for i in range(n)))
    energy=[F(rng.randrange(0,20),rng.randrange(1,9)) for i in range(n)]; sums=[sum(e for r,e in zip(ranks,energy) if r==g) for g in range(1,C+1)]
    check('color_energy',sum(energy)==sum(sums)<=C*max(sums))
    p=[F(rng.randrange(-20,21),7) for i in range(n)]; t=[F(rng.randrange(-20,21),9) for i in range(n)]; check('subtotal_perturbation',sum(v*v for v in t)<=2*sum(v*v for v in p)+2*sum((v-u)**2 for v,u in zip(t,p)))
for _ in range(1200):
    # Exact heterogeneous group maps and adjoints; Frobenius bound is a valid
    # synthesis bound, not claimed to be optimal.
    n=rng.randrange(1,7); dims=[rng.randrange(1,5) for _ in range(rng.randrange(1,5))]; A=[[[F(rng.randrange(-5,6),7) for j in range(n)] for i in range(d)] for d in dims]; x=[F(rng.randrange(-10,11),9) for j in range(n)]
    y=[[sum(a*b for a,b in zip(row,x)) for row in M] for M in A]; z=[sum(M[i][j]*w[i] for M,w in zip(A,y) for i in range(len(M))) for j in range(n)]; S=sum(v*v for w in y for v in w); C=sum(a*a for M in A for row in M for a in row)
    check('adjoint_pairing',sum(a*b for a,b in zip(x,z))==S)
    check('group_synthesis',sum(a*a for a in z)<=C*S)
    check('group_bessel',S<=C*sum(a*a for a in x))
# Confirm the strict axiom parser cannot interpret an absent report as success.
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
for bad in ('', 'NOT VERIFIED: missing lake', "'OpenAI086.v21_paper_lemma33_prefix' depends on axioms: [sorryAx]"):
    try: parse_axioms(bad,'OpenAI086.v21_paper_lemma33_prefix')
    except UnrecognizedAxiomReport: check('fail_closed_parser',True)
    else: raise AssertionError('parser accepted invalid report')
for k,v in counts.items(): print(f'{k}: {v} PASS')
print(f'V21 TOTAL: {sum(counts.values())} exact model checks PASS')
