#!/usr/bin/env python3
"""Exact rational counterexample tests for V6 finite identities. NOT Lean proofs."""
from fractions import Fraction as F
from random import Random
import json
r=Random(20261122)
checks={}

def check(name,fn,n):
    for k in range(n):
        if not fn(k):
            raise AssertionError((name,k))
    checks[name]=n

def dyadic_blocks(k,start,length):
    if k==0:
        return [] if length==0 else [(start,1)]
    if length==2**k:return [(start,2**k)]
    if length<=2**(k-1):return dyadic_blocks(k-1,start,length)
    return [(start,2**(k-1))]+dyadic_blocks(k-1,start+2**(k-1),length-2**(k-1))

def bridge_test(_):
    k=r.randrange(0,10)
    N=r.randrange(2**k)
    d=r.randrange(1,5)
    P=[[[F(r.randrange(-4,5)) for _ in range(d)] for _ in range(d)] for _ in range(N+1)]
    x=[F(r.randrange(-4,5)) for _ in range(d)]
    def matvec(A):return [sum((A[i][j]*x[j] for j in range(d)),F(0)) for i in range(d)]
    px=[matvec(a) for a in P]
    inc=[px[0]]+[[px[t][j]-px[t-1][j] for j in range(d)] for t in range(1,N+1)]
    bs=dyadic_blocks(k,0,N+1)
    assert sum(w for s,w in bs)==N+1
    assert all(w>0 and w&(w-1)==0 and s%w==0 for s,w in bs)
    assert len({w for _,w in bs})==len(bs)
    y=[sum((inc[t][j] for start,width in bs for t in range(start,start+width)),F(0)) for j in range(d)]
    return y==px[N]
check('operator_dyadic_prefix_exact_fraction',bridge_test,5000)

def closure_step(S,adj):return S|set().union(*(adj[v] for v in S)) if S else set(S)
def closure_test(_):
    n=r.randrange(1,11)
    U=set(range(n))
    adj=[{j for j in range(n) if r.randrange(3)==0} for i in range(n)]
    S={i for i in U if r.randrange(2)==0}
    T=S|{i for i in U if r.randrange(2)==0}
    S2,T2=S.copy(),T.copy()
    previous=S.copy()
    for _ in range(8):
        S2=closure_step(S2,adj)
        T2=closure_step(T2,adj)
        assert previous<=S2 and S2<=T2
        previous=S2
    return True
check('finite_catalog_extensive_monotone',closure_test,1500)

def clip_test(_):
    eta=F(r.randrange(0,20),r.randrange(1,10))
    values=[F(r.randrange(0,40),r.randrange(1,10)) for _ in range(r.randrange(0,30))]
    return all(min(eta,a)**2<=eta*a for a in values) and sum((min(eta,a)**2 for a in values),F(0)) <= eta*sum(values,F(0))
check('finite_clipping_square_fraction',clip_test,3000)

def path_test(_):
    a=[F(r.randrange(-100,101),r.randrange(1,25)) for _ in range(r.randrange(1,50))]
    increments=[a[i+1]-a[i] for i in range(len(a)-1)]
    K=max((abs(t) for t in increments),default=F(0))
    return sum(increments,F(0))==a[-1]-a[0] and abs(a[-1]-a[0])<=(len(a)-1)*K
check('finite_path_endpoints_fraction',path_test,3000)

def gowers_test(_):
    x,h1,h2,h3,lam,beta,gamma=(F(r.randrange(-10,11)) for _ in range(7))
    def difference(f):
        return (f(x+h1+h2+h3)-f(x+h1+h2)-f(x+h1+h3)-f(x+h2+h3)
               +f(x+h1)+f(x+h2)+f(x+h3)-f(x))
    return difference(lambda y:lam*y*y+beta*y+gamma)==0 and difference(lambda y:y*y*y)==6*h1*h2*h3
check('quadratic_and_cubic_cube_exact_fraction',gowers_test,3000)

def fourcs_test(_):
    n=r.randrange(0,25)
    a,b,c,d=([F(r.randrange(-20,21),r.randrange(1,10)) for j in range(n)] for i in range(4))
    left=sum((a[i]*b[i]*c[i]*d[i] for i in range(n)),F(0))**2
    right=sum((a[i]**2*b[i]**2 for i in range(n)),F(0))*sum((c[i]**2*d[i]**2 for i in range(n)),F(0))
    return left<=right
check('finite_fourlinear_cs_fraction',fourcs_test,3000)


# Finite-real candidate for the full row-prefix and variation statements
# of Lemma 3.3, tested on genuinely noncommuting rational projections.
def l33_projection_test(_):
    T=r.randrange(0,12)
    m=r.randrange(0,6)
    axes=[(F(1),F(0)),(F(0),F(1)),(F(3,5),F(4,5)),(F(5,13),F(12,13))]
    families=[]
    for i in range(m):
        u=axes[r.randrange(len(axes))]
        first=r.randrange(T+2)
        second=r.randrange(first,T+2)
        def P(n,u=u,first=first,second=second):
            if n<first:return ((F(0),F(0)),(F(0),F(0)))
            if n>=second:return ((F(1),F(0)),(F(0),F(1)))
            return ((u[0]*u[0],u[0]*u[1]),(u[1]*u[0],u[1]*u[1]))
        families.append(P)
    x=(F(r.randrange(-10,11)),F(r.randrange(-10,11)))
    def apply(A,y):return (A[0][0]*y[0]+A[0][1]*y[1],A[1][0]*y[0]+A[1][1]*y[1])
    def product(n):
        y=x
        for fam in families:y=apply(fam(n),y)
        return y
    z=[product(n) for n in range(T+1)]
    L=max(1,(T+1).bit_length()-1)+2 # upper envelope of Nat.log2(T+1)+2
    E=x[0]**2+x[1]**2
    choice0=r.randrange(T+1)
    choice1=r.randrange(T+1)
    row=z[choice0][0]**2+z[choice1][1]**2
    variation=sum(((z[n+1][j]-z[n][j])**2 for n in range(T) for j in range(2)),F(0))
    return row<=L**(2*m)*E and variation<=m*m*L**(2*max(m-1,0))*E
check('nested_noncommuting_L33_goal_fraction',l33_projection_test,2400)

print(json.dumps({'status':'exact_fraction_checks_only_not_lean_kernel', 'counts':checks, 'total':sum(checks.values()), 'pass':True},indent=2))
