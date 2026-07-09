#!/usr/bin/env python3
"""ADVERSARIAL re-check of C040 REFUTED: hunt for ANY negative defect D_r=E_r^Fq - E_r^C
in the prize regime (proper dyadic subgroup, large prime, beta 4-5), with MANY primes per band
and ALL r up to rmax. If none found, the attacker's 'never negative' holds; if one found, downgrade.

Also: structural argument check. E_r^Fq counts solutions in F_p of x1+...+xr = y1+...+yr (xi,yi in mu_n).
E_r^C counts the SAME equation over C (no wraparound). Over F_p, EVERY char-0 solution is also a
mod-p solution (reduce), PLUS possibly extra solutions where char-0 sums differ but coincide mod p.
=> E_r^Fq >= E_r^C ALWAYS (defect >= 0). A NEGATIVE defect would be a logical impossibility.
We test this structural inequality exactly to confirm it can never be negative.
"""
import math, itertools, cmath
from collections import defaultdict

def is_prime(m):
    if m<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%p==0: return m==p
    d=m-1;s=0
    while d%2==0: d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def primes_1_mod_n(n, lo, hi, count):
    out=[]; start=lo-(lo%n)+1
    if start<lo: start+=n
    p=start
    while p<=hi and len(out)<count:
        if is_prime(p): out.append(p)
        p+=n
    return out

def order_n_gen(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        s=set();x=1
        for _ in range(n): s.add(x);x=x*h%p
        if len(s)==n: return h
    return None

def Er_Fq(p,n,h,rmax):
    mu=[pow(h,i,p) for i in range(n)]
    R=[0]*p
    for x in mu: R[x]+=1
    Es={};cur=R[:]
    for r in range(1,rmax+1):
        Es[r]=sum(c*c for c in cur)
        if r<rmax:
            nxt=[0]*p
            for v in range(p):
                cv=cur[v]
                if cv:
                    for x in mu: nxt[(v+x)%p]+=cv
            cur=nxt
    return Es

def Er_C(n,rmax,cap=5_000_000):
    pts=[cmath.exp(2j*math.pi*i/n) for i in range(n)]
    res={}
    for r in range(1,rmax+1):
        if n**r>cap: res[r]=None;continue
        cnt=defaultdict(int)
        for combo in itertools.product(range(n),repeat=r):
            s=sum(pts[i] for i in combo)
            cnt[(round(s.real,7),round(s.imag,7))]+=1
        res[r]=sum(v*v for v in cnt.values())
    return res

neg_found=[]
total_rows=0
for n in (8,16,32):
    rmax = 6 if n==8 else (5 if n==16 else 4)
    Ec=Er_C(n,rmax)
    for beta in (4.0,4.25,4.5,4.75,5.0):
        target=int(round(n**beta))
        ps=primes_1_mod_n(n, max(target-200*n,n+1), target+2000*n, 6)  # 6 primes per band
        for p in ps:
            if p>6_500_000: continue
            h=order_n_gen(p,n)
            if h is None: continue
            Efq=Er_Fq(p,n,h,rmax)
            for r in range(1,rmax+1):
                if Ec.get(r) is None: continue
                D=Efq[r]-Ec[r]
                total_rows+=1
                if D<0:
                    neg_found.append((n,beta,p,r,D,Efq[r],Ec[r]))

print(f"Scanned {total_rows} (n,beta,p,r) rows in prize regime beta in [4,5], proper dyadic subgroup, large prime.")
if neg_found:
    print("!!! NEGATIVE DEFECT FOUND (would downgrade REFUTED):")
    for row in neg_found: print("   ",row)
else:
    print("NO negative defect anywhere. D_r = E_r^Fq - E_r^C >= 0 in EVERY row.")
    print("=> Confirms attacker premise-refutation (1)&(2): the C040 'defect negative' is impossible/false.")
    print("   Structural reason: every char-0 additive-energy solution reduces to a distinct-or-merged")
    print("   mod-p solution, so E_r^Fq >= E_r^C identically; defect can only be 0 (no extra coincidences,")
    print("   r below the wall) or positive (mod-p coincidences = the W-anomaly).")
