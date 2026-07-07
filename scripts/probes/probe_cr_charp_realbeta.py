#!/usr/bin/env python3
"""
probe_cr_charp_realbeta.py  (issue #444, [cr-monotonicity-deep], CHAR-P at REAL beta)

The char-0 result (probe_cr_deep_charzero / _slack_structure): c_r<=1 for ALL r is EXACTLY
  slack_{r+1} >= n*slack_r,  slack_r := Wick_r - E_r^char0 >= 0  (Lam-Leung),
and the measured margin slack_{r+1}/(n slack_r) -> 2r+1 (the Wick recursion ratio), so c_r->0
deep in char-0 with HUGE room.  That is a CHAR-0 ALL-r corollary of Lam-Leung.

NOW: does char-p inherit c_r<=1 up to the faithfulness depth?  In char-p,
  E_r^{Fp} = E_r^char0 + SPUR_r,   SPUR_r >= 0  (mod-p coincidences only ADD).
DC-subtracted: A_r = E_r^{Fp} - n^{2r}/q.  a_r = A_r/Wick_r.  c_r = (A_{r+1} - n A_r)/(2r n Wick_r).
So  c_r^{Fp} - c_r^{c0} = [ (SPUR_{r+1}-n SPUR_r) - (DC_{r+1}-n DC_r) ] / (2r n Wick_r),
DC_r = n^{2r}/q.  The DC term is NEGATIVE-leaning (subtracts), helps; the SPUR term is the danger.

c_r^{Fp} <= 1  <=>  slack^{Fp}_{r+1} >= n slack^{Fp}_r,  slack^{Fp}_r = Wick_r - A_r
            = slack^{c0}_r - SPUR_r + DC_r.
So the char-p slack is the char-0 slack MINUS spur PLUS DC.  c_r^{Fp}<=1 can fail only when
spur erodes the (huge, ~2r+1 factor) char-0 slack margin faster than it grows.

MEASURE: at REAL prize beta = 1 + 128/log2(n) we cannot reach n=2^30, p~n*2^128 exactly, but
we model the regime with the LARGEST tractable p at the matched beta-ridge and watch:
  - SPUR_r onset (first r with E_r^{Fp} > E_r^char0)
  - whether c_r^{Fp} <= 1 holds up to that onset and beyond
  - the char-p slack margin slack^{Fp}_{r+1}/(n slack^{Fp}_r)
We use moderate n (8,16) and primes spanning beta from ~2 up to as high as tractable, plus a
DEDICATED breaker check: the known spur breaker zeta^0+zeta^1+zeta^11+zeta^13=0 mod 97 (n=16).
"""
from fractions import Fraction
from collections import defaultdict

def is_prime(p):
    if p<2: return False
    if p%2==0: return p==2
    i=3
    while i*i<=p:
        if p%i==0: return False
        i+=2
    return True

def subgroup_mu_n(p,n):
    def order(a):
        o,x=1,a%p
        while x!=1: x=(x*a)%p; o+=1
        return o
    g=next(c for c in range(2,p) if order(c)==p-1)
    h=pow(g,(p-1)//n,p)
    S,x=set(),1
    for _ in range(n): S.add(x); x=(x*h)%p
    assert len(S)==n
    return sorted(S)

def energy_charp(S,p,r):
    cur=[0]*p
    for a in S: cur[a%p]+=1
    for _ in range(r-1):
        nxt=[0]*p
        for v in range(p):
            cv=cur[v]
            if cv:
                for a in S: nxt[(v+a)%p]+=cv
        cur=nxt
    return sum(c*c for c in cur)

def rep_vectors(n):
    half=n//2; reps=[]
    for j in range(n):
        v=[0]*half
        if j<half: v[j]=1
        else: v[j-half]=-1
        reps.append(tuple(v))
    return reps

def char0_energy_upto(n,R):
    reps=rep_vectors(n); half=n//2
    cur=defaultdict(int); cur[tuple([0]*half)]=1; out={}
    for r in range(1,R+1):
        nxt=defaultdict(int)
        for v,c in cur.items():
            for rv in reps:
                w=tuple(v[i]+rv[i] for i in range(half)); nxt[w]+=c
        cur=nxt; out[r]=sum(c*c for c in cur.values())
    return out

def df(r):
    res=1
    for k in range(1,r+1): res*=(2*k-1)
    return res

from math import log
def main():
    print("ISSUE #444 [cr-monotonicity-deep] CHAR-P at real beta: does c_r<=1 inherit?\n")
    print("c_r^{Fp}<=1  <=>  slack^{Fp}_{r+1} >= n slack^{Fp}_r, slack^{Fp}=Wick-A, A=E^{Fp}-n^{2r}/p.\n")
    for n in [8, 16]:
        E0 = char0_energy_upto(n, 8)
        # pick primes spanning beta; biggest tractable energy compute keeps p modest (p^? mem),
        # but energy_charp is O(p*n*r) -> p up to ~few*10^4 fine
        prime_caps = [n*50+1, n*300+1, n*2000+1]
        ps = []
        for base in prime_caps:
            pp = base
            while not is_prime(pp): pp += 1  # may drift off the k*n+1 ridge; fix:
            # better: search p=k*n+1 prime near base
            k = base//n
            while not is_prime(k*n+1): k += 1
            ps.append(k*n+1)
        ps = sorted(set(ps))
        print(f"==== n={n} ====")
        for p in ps:
            beta = log(p)/log(n)
            S = subgroup_mu_n(p, n)
            Rmax = 7
            print(f"  -- p={p}, beta={beta:.3f}, m=(p-1)/n={(p-1)//n} --")
            print(f"     {'r':>2} {'SPUR_r':>12} {'a_r^Fp':>11} {'c_r^Fp':>11} {'slackFp_margin':>16}")
            A = {}; slackFp = {}
            firstspur = None
            firstcrviol = None
            for r in range(1, Rmax+1):
                Efp = energy_charp(S, p, r)
                spur = Efp - E0[r]
                if spur > 0 and firstspur is None: firstspur = r
                Ar = Fraction(Efp) - Fraction(n**(2*r), p)
                A[r] = Ar
                Wr = df(r)*n**r
                slackFp[r] = Wr - Ar
                ar = float(Ar/Wr)
                if r >= 2:
                    cr = float((A[r] - n*A[r-1])/(2*(r-1)*n*(df(r-1)*n**(r-1))))
                    mg = float(slackFp[r]/(n*slackFp[r-1])) if slackFp[r-1] != 0 else float('nan')
                    flag = "" if cr <= 1+1e-12 else " c>1!!"
                    if cr > 1+1e-12 and firstcrviol is None: firstcrviol = r-1
                    print(f"     {r-1:>2} {spur if r==2 else '':>12} {ar:>11.6f} {cr:>11.6f}{flag} {mg:>16.4f}")
                else:
                    print(f"     {'(r=1)':>2} {'':>12} {ar:>11.6f} {'--':>11} {'--':>16}")
            print(f"     spur onset r*={firstspur}, first c_r>1 at r={firstcrviol}\n")
    print("="*70)
    print("Read: does c_r^Fp exceed 1 once SPUR turns on (deep r), or stay <=1?")

if __name__ == "__main__":
    main()
