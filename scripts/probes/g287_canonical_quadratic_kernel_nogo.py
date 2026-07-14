#!/usr/bin/env python3
"""Exact #466 probe: complete canonical linear and homogeneous-quadratic kernel features.

For n=16, generator-independent linear kernel-input Fourier features are the Ramanujan
aggregates T_d, d in {2,4,8,16}.  This probe computes the complete p<2600, r=5/6
census, checks that no homogeneous quadratic in those four features strictly separates
the CORE signs, and verifies exact positive Farkas circuits for both the linear (5-cell)
and quadratic (11-cell) feature spaces.  Floating LP is discovery/diagnostic only; the
reported obstructions are exact integer identities.
"""
from __future__ import annotations
import importlib.util
import math
from itertools import combinations_with_replacement
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

ROOT=Path(__file__).resolve().parents[2]
P=ROOT/'scripts/probes/g276_termwise_weil_l1_probe.py'
spec=importlib.util.spec_from_file_location('g276',P)
g=importlib.util.module_from_spec(spec); spec.loader.exec_module(g)
DS=(2,4,8,16)
PAIRS=tuple(combinations_with_replacement(range(4),2))

def mu(x):
    if x==1:return 1
    ans=1;p=2
    while p*p<=x:
        if x%p==0:
            x//=p
            if x%p==0:return 0
            ans=-ans
        p+=1
    return -ans if x>1 else ans

def phi(x):
    ans=x;p=2
    while p*p<=x:
        if x%p==0:
            ans=ans//p*(p-1)
            while x%p==0:x//=p
        p+=1
    return ans//x*(x-1) if x>1 else ans

def ramanujan(d,j):
    q=d//math.gcd(d,j%d); m=mu(q)
    return 0 if m==0 else m*phi(d)//phi(q)

def cell(p,r):
    W,hist,root=g.profiles(p,16)
    R=g.additive_corr_exact_fft(hist[r],hist[r-1])
    G,zroot=g.subgroup(p,16); assert root==zroot
    H=[]
    for u in G:
        a=(2-u)%p
        H.append(16*R[0] if a==0 else sum(R[(a*x)%p] for x in G))
    total=sum(R)
    A=p*sum(W[x]*R[x] for x in range(p))-256*total
    assert A==p*sum(H)-256*total
    T=[p*sum(ramanujan(d,j)*h for j,h in enumerate(H)) for d in DS]
    gg=math.gcd(*[abs(x) for x in T]); U=[x//gg for x in T]
    Q=[U[i]*U[j] for i,j in PAIRS]
    return dict(p=p,r=r,A=A,T=T,U=U,Q=Q)

def positive_relation(rows,weights,dim,key):
    assert len(rows)==len(weights) and all(w>0 for w in weights)
    sums=[sum(w*((1 if z['A']>0 else -1)*z[key][j]) for z,w in zip(rows,weights))
          for j in range(dim)]
    assert sums==[0]*dim,sums
    return sums

def main():
    rows=[]
    for p in range(17,2601):
        if (p-1)%16==0 and g.is_prime(p):
            rows += [cell(p,5),cell(p,6)]
    assert len(rows)==84
    y=np.array([1 if z['A']>0 else -1 for z in rows],float)
    X=np.array([z['Q'] for z in rows],float)
    X=X/np.max(np.abs(X),axis=1)[:,None]
    d=10
    # max t with y_i<a,Q_i> >= t and ||a||_1<=1
    c=np.r_[np.zeros(2*d),-1.]
    Aub=[]
    for xi,yi in zip(X,y): Aub.append(np.r_[-yi*xi,yi*xi,1.])
    Aub.append(np.r_[np.ones(2*d),0.])
    sol=linprog(c,A_ub=np.array(Aub),b_ub=np.r_[np.zeros(len(rows)),1.],
                bounds=[(0,None)]*(2*d)+[(None,None)],method='highs')
    assert sol.success and abs(sol.x[-1])<1e-10,sol

    by={(z['p'],z['r']):z for z in rows}
    linear_keys=[(113,6),(1889,6),(2129,6),(2593,5),(2593,6)]
    linear_w=[201509006170048,579259743381,520097612828,
              4174444248727,2109973613412]
    positive_relation([by[k] for k in linear_keys],linear_w,4,'U')

    quad_keys=[(113,5),(241,6),(337,6),(353,5),(449,5),(769,5),
               (977,6),(1217,5),(1249,6),(1777,6),(2273,6)]
    quad_w=[
      11308242874832261572052183566626781414659316407602105031566717756454192,
      5545395965739983420010862625442000127212733512612622606100727773394813,
      3492805965182985206647536641660394624909840337611522612856160317309184,
      13983000195570496051288545395768579696389962745181207272025935188289232,
      1573179179079669437886174590565848493435097834355219103296674926056580,
      244142748137291338636829266720419636475465291169939190898370781168416,
      110241997960278095030459289115345232313710872887127117460361113618015,
      1007251487898994986904786060080228399921905389253337700472740655923488,
      1526486021713370574044212582355307680990040413804551200469942473851104,
      891416934309140711299857485350182791519957500800239422684400646229632,
      1582720926493957971050302814118779667794269851352565398079629218360128]
    positive_relation([by[k] for k in quad_keys],quad_w,10,'Q')

    print('G287 PASS')
    print('census: 84 exact n=16 cells, ranks 5/6, p<2600')
    print('canonical linear dimension: 4; exact positive circuit: 5 cells')
    print('canonical homogeneous quadratic dimension: 10; exact positive circuit: 11 cells')
    print('quadratic max normalized L1 margin:',sol.x[-1])
    print('quadratic witness primes:',quad_keys)

if __name__=='__main__':main()
