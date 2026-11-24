#!/usr/bin/env python3
"""Deterministic exact arithmetic regressions for the V25 proof candidates.
These test the algebraic bounds and identities, not Lean elaboration or
Schwartz-space integrability in general.
"""
from fractions import Fraction as F
from itertools import product
import random
rng=random.Random(25)
count=0

def check(v):
    global count
    assert v
    count+=1

W=lambda x:1+x*x
vals=[F(i,3) for i in range(-15,16)]
for x,t in product(vals,repeat=2):
    check(W(x)*W(t)<=16*W(x-t)**2*W(x-2*t)**2)
    if abs(t)<=1:
        for j in (-3,-2,-1,1,2,3):
            check(W(x)*W(t)<=40*W(x+j*t))
# Rational smooth rapidly decaying examples (not Schwartz: only model tests).
# g(x)=(1+x²)^-2, sup and Lipschitz and weighted order-4 budget <= 4.
# Distinct translated/scaled rational test profiles, all have an explicit
# generous common seminorm-style bound of 64 for these checks.
def g(i,x):return F(i+1,1)/(1+(x-F(i,2))**2)**2

def kernel(x,t):
    if not t:return F(0)
    return g(0,x-t)*g(1,x-2*t)*g(2,x-3*t)/t

def pair(x,t):return kernel(x,t)+kernel(x,-t)
for x,t in product(vals,repeat=2):
    check(pair(x,t)==pair(x,-t))
    check(W(x)*W(t)*abs(pair(x,t))<=480*64**3)
    if t:check(pair(x,t)==(g(0,x-t)*g(1,x-2*t)*g(2,x-3*t)-g(0,x+t)*g(1,x+2*t)*g(2,x+3*t))/t)
# Exact symmetric/skew bilinear splitting, with fast-fast isotropy.
for _ in range(500):
    u,n=[tuple(F(rng.randint(-8,8),3) for _ in range(2)) for _ in range(2)]
    a,b,c=[F(rng.randint(-6,6),5) for _ in range(3)]
    B=lambda x,y:a*x[0]*y[0]+b*(x[0]*y[1]+x[1]*y[0])+c*x[1]*y[1]
    w=tuple(x-y for x,y in zip(u,n))
    check(B(u,w)==(B(u,u)+B(w,w)-B(n,n))/2)
    uf,us=(u[0],F(0)),(F(0),u[1]); nf,ns=(n[0],F(0)),(F(0),n[1])
    A=lambda x,y:b*(x[0]*y[1]-x[1]*y[0])
    check(A(u,w)==A(uf,us)-A(uf,ns)+A(us,w))
for m2,m3 in product(vals,repeat=2):
    m0,m1=m2+2*m3,-2*m2-3*m3
    check(-m0*m0+m1*m1/3-m2*m2/3+m3*m3==0)
for a,b,c in product(range(-6,7),repeat=3):
    d=a+b-c
    if a*a+b*b==c*c+d*d:check((a==c and b==d) or (a==d and b==c))
for _ in range(500):
    d,n0,n1,u,v,j=[F(rng.randint(-9,9),5) for _ in range(6)]
    check(d*((1-j)*n0+j*n1+(1-j)*u+j*v)==(1-j)*d*(n0+u)+j*d*(n1+v))
# Two-step coordinate group law for an actual bilinear form on Q².
B=lambda x,y:x[0]*y[1]+2*x[1]*y[0]
add=lambda x,y:tuple(a+b for a,b in zip(x,y))
neg=lambda x:tuple(-a for a in x)
mul=lambda a,b:(add(a[0],b[0]),a[1]+b[1]+B(a[0],b[0]))
inv=lambda a:(neg(a[0]),-a[1]+B(a[0],a[0]))
for _ in range(500):
    a,b,c=[((rng.randint(-8,8),rng.randint(-8,8)),rng.randint(-8,8)) for _ in range(3)]
    check(mul(mul(a,b),c)==mul(a,mul(b,c)))
    check(mul(a,inv(a))==((0,0),0));check(mul(inv(a),a)==((0,0),0))
    theta=(rng.randint(-8,8),rng.randint(-8,8));g=lambda n:((a[0][0]+n*theta[0],a[0][1]+n*theta[1]),b[1]+n*c[1]+n*n*a[1])
    D=lambda n:mul(g(n+1),inv(g(n)))
    DD=lambda n:mul(D(n+1),inv(D(n)))
    n=rng.randint(-10,10)
    check(DD(n)==((0,0),g(n+2)[1]-2*g(n+1)[1]+g(n)[1]-B(theta,theta)))
print(f'V25: {count} exact model assertions PASS (not Lean).')
