"""Independent exact and numerical tests of the fixed-degree conservative balance theorem.
No proof assistant code is imported. Run Python 3.10+, numpy, scipy, sympy.
"""
from fractions import Fraction as F
from math import comb
import random
import numpy as np
from scipy.optimize import linprog
import sympy as sp

rng=random.Random(20261126)
x=sp.Symbol('x')
def basis(d,i,t): return t**i*(1-t)**(d-i)
def elevate(c):
    return [(c[i] if i<len(c) else F(0))+(c[i-1] if i else F(0)) for i in range(len(c)+1)]
def field_from_flux(w,a,t):
    d=len(w)-1
    return sum(w[i][j]*(j-i)*basis(d,i,t)/basis(d,i,a) for i in range(d+1) for j in range(d+1))
def factor_from_flux(w,a):
    d=len(w)-1
    v=[sum(w[i][j]*(j-i) for j in range(d+1)) for i in range(d+1)]
    assert sum(v)==0
    p=[sum(v[:i+1]) for i in range(d)]
    assert min(p,default=0)>=0
    return [p[i]/(a**(i+1)*(1-a)**(d-i)) for i in range(d)]
def random_balanced(d):
    w=[[F(0) for _ in range(d+1)] for _ in range(d+1)]
    for _ in range(rng.randint(1,9)):
        k=rng.randint(2,d+1); cycle=rng.sample(range(d+1),k); weight=F(rng.randint(1,9),rng.randint(1,9))
        for i,j in zip(cycle,cycle[1:]+cycle[:1]): w[i][j]+=weight
    assert all(sum(w[i])==sum(w[j][i] for j in range(d+1)) for i in range(d+1))
    return w

exact_cases=0
for _ in range(800):
    D=rng.randint(1,10); a=F(rng.randint(1,19),20)
    g=[F(0)]*D; nets=[]
    for d in range(1,D+1):
        if rng.random()<.4: continue
        w=random_balanced(d); nets.append(w)
        c=factor_from_flux(w,a)
        for _ in range(D-d): c=elevate(c)
        g=[i+j for i,j in zip(g,c)]
    for t in (F(1,17),F(3,7),F(11,13)):
        true=sum(field_from_flux(w,a,t) for w in nets)
        predicted=(a-t)*sum(c*basis(D-1,i,t) for i,c in enumerate(g))
        assert true==predicted
        # Independently evaluate the proposed adjacent reversible rates.
        chain=sum(c*(a*basis(D,i,t)-(1-a)*basis(D,i+1,t)) for i,c in enumerate(g))
        assert chain==true
        exact_cases+=1
print('Exact rational mixed-network/chain identities:',exact_cases)

lp_cases=0
for D in range(1,8):
    pairs=[(i,j) for i in range(D+1) for j in range(D+1) if i!=j]
    A=np.zeros((2*(D+1),len(pairs)))
    for z,(i,j) in enumerate(pairs):
        A[i,z]+=1; A[j,z]-=1; A[D+1+i,z]=j-i
    for trial in range(100):
        a=F(rng.randint(1,9),10)
        c=[F(rng.randint(-4,7),rng.randint(1,3)) for _ in range(D)]
        # Construct raw f coefficients by distributing (a-t)=a(1-t)-(1-a)t.
        fc=[F(0)]*(D+1)
        for i,v in enumerate(c): fc[i]+=a*v; fc[i+1]-=(1-a)*v
        v=[fc[i]*basis(D,i,a) for i in range(D+1)]
        res=linprog(np.zeros(len(pairs)), A_eq=A,b_eq=[0.]*(D+1)+list(map(float,v)),bounds=(0,None),method='highs')
        assert res.status in (0,2), res.message
        assert res.success==all(z>=0 for z in c),(D,a,c,res.message)
        lp_cases+=1
print('Independent full directed equilibrium-flow LP comparisons:',lp_cases)

quad_cases=0
for n in range(2,101):
    threshold=F(1,4*(n-1 if n%2==0 else n))
    for eps in [threshold/2,threshold,threshold*2]:
        c=[eps+F(1,4)-F(i,n)+F(i*(i-1),n*(n-1)) for i in range(n+1)]
        assert min(c)==eps-threshold
        for t in (F(1,7),F(1,2),F(7,9)):
            assert sum(c[i]*comb(n,i)*basis(n,i,t) for i in range(n+1))==(t-F(1,2))**2+eps
        quad_cases+=1
print('Exact quadratic degree-threshold comparisons:',quad_cases)
# Symbolic check at selected degrees.
for n in range(2,13):
    eps=sp.Symbol('eps'); p=sum((eps+sp.Rational(1,4)-sp.Rational(i,n)+sp.Rational(i*(i-1),n*(n-1)))*comb(n,i)*x**i*(1-x)**(n-i) for i in range(n+1))
    assert sp.expand(p-((x-sp.Rational(1,2))**2+eps))==0
print('Symbolic polynomial identities: 11')
