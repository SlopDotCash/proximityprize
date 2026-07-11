#!/usr/bin/env python3
"""
Opus-core CORE probe (#509 dual): is repRF(g,n,2,0) BOUNDED ABOVE at depth 2?
S0(2) = #{ (i,j) in Fin n x Fin n : g^i + g^j = 0 in F_p }.
Antipodal count A(n,2)=n counts the n pairs (i, i+m). Question: are there OTHER
solutions g^i + g^j = 0 with j != i+m, i.e. accidental char-p coincidences that
push S0(2) ABOVE n? If never, then repRF g n 2 0 <= n UNCONDITIONALLY (a clean
exact-at-large-p, bounded-everywhere ceiling), the dual of G181's floor S0>=n.

Mechanism check: g^i + g^j = 0  <=>  g^j = -g^i  <=>  g^(j-i) = -1  <=>  g^(j-i)=g^m
(since g^m=-1 is the UNIQUE element of order 2 in the cyclic group <g> of even order).
So j-i = m (mod n) is FORCED — no accidental extra solutions possible, EVER, in any
characteristic, because -1 has a unique preimage under the injective map t|->g^t on Fin n.
=> S0(2) = n EXACTLY, all p, all even n. Verify exhaustively incl. tiny p.
"""
from collections import Counter

def is_prime(x):
    if x<2:return False
    d=2
    while d*d<=x:
        if x%d==0:return False
        d+=1
    return True

def find_gen(p,n):
    if (p-1)%n!=0:return None
    def order(a):
        o=1;x=a%p
        while x!=1:
            x=(x*a)%p;o+=1
            if o>p:return None
        return o
    for a in range(2,p):
        if order(a)==p-1:
            g=pow(a,(p-1)//n,p)
            if order(g)==n and pow(g,n//2,p)==p-1:
                return g
    return None

def S0_depth2(p,g,n):
    roots=[pow(g,t,p) for t in range(n)]
    c=0
    for i in range(n):
        for j in range(n):
            if (roots[i]+roots[j])%p==0: c+=1
    return c

print("even n, all primes p with n|(p-1), check S0(2)==n exactly:")
maxviol=0
rows=0
for n in range(2,33,2):
    for p in range(3,4000):
        if not is_prime(p): continue
        if (p-1)%n!=0: continue
        g=find_gen(p,n)
        if g is None: continue
        s0=S0_depth2(p,g,n)
        rows+=1
        if s0!=n:
            maxviol=max(maxviol,1)
            print(f"  VIOLATION n={n} p={p} g={g} S0(2)={s0} != n={n}")
        # only sample a few primes per n to keep it fast
        if p>500 and n>8: break
print(f"checked {rows} (n,p) rows. violations: {'NONE - S0(2)=n unconditional' if maxviol==0 else 'FOUND'}")

# ODD n control: is there any j with g^i+g^j=0? need g^(j-i)=-1 but -1 not in <g> for odd order
print("\nodd n control (no -1 in <g>, so S0(2) should be 0):")
for n in [3,5,7,9,15]:
    found=False
    for p in range(3,2000):
        if not is_prime(p) or (p-1)%n!=0: continue
        # generator of order n
        def order(a):
            o=1;x=a%p
            while x!=1:
                x=(x*a)%p;o+=1
                if o>p:return None
            return o
        g=None
        for a in range(2,p):
            if order(a)==p-1:
                cand=pow(a,(p-1)//n,p)
                if order(cand)==n: g=cand;break
        if g is None: continue
        s0=S0_depth2(p,g,n)
        print(f"  n={n} p={p} S0(2)={s0}  (expect 0)")
        found=True
        break
