#!/usr/bin/env python3
"""
C057 follow-up: WHERE does char-0 vs char-p diverge, and is it the Newton-window object
or the single-constraint object?

The grounding (issue line 1782) reports "e_1=0 alone -> 480 spurious non-antipodal
sum-zero subsets at mu_16, p=97". That is the SINGLE-constraint count, NOT the
consecutive Newton window p_1..p_L. The Newton bridge (C057's claim) is about the
CONSECUTIVE window e_1..e_{t-1}=0 <=> p_1..p_{t-1}=0. We test both objects to pin
exactly which one C057's identity governs, and whether the char-p transfer of the
*consecutive window* is the actual wall.

Compare three counts of balanced subsets S (|S|=n/2) of mu_n in F_q:
  A) single power sum:   p_L(S)=0   (one constraint at exponent L)
  B) consecutive window: p_1=...=p_L(S)=0
  C) the SINGLE e_1 antipodal test:  p_1(S)=0   (= L=1 of both)

We sweep beta DOWN (small q) to FORCE the char-p inflation, locating the onset, and
also test the documented mu_16 p=97 spurious case directly.
"""
import itertools, math

def isprime(x):
    if x<2: return False
    d=2
    while d*d<=x:
        if x%d==0: return False
        d+=1
    return True

def factor(m):
    fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    return fs

def subgroup(n,q):
    assert (q-1)%n==0
    for g in range(2,q):
        if all(pow(g,(q-1)//r,q)!=1 for r in factor(q-1)):
            h=pow(g,(q-1)//n,q)
            return [pow(h,j,q) for j in range(n)]
    raise RuntimeError

def is_antipodal(S, mu, q):
    """A balanced subset is 'antipodal' if it's a union of {x,-x} pairs (x,-x both in S)."""
    Sset=set(S)
    return all(((q-x)%q) in Sset for x in S)

def count_single(n,a,L,q):
    mu=subgroup(n,q); c=0
    for S in itertools.combinations(mu,a):
        if sum(pow(x,L,q) for x in S)%q==0: c+=1
    return c

def count_window(n,a,L,q):
    mu=subgroup(n,q); c=0
    for S in itertools.combinations(mu,a):
        if all(sum(pow(x,j,q) for x in S)%q==0 for j in range(1,L+1)): c+=1
    return c

def count_e1_antipodal(n,a,q):
    """#{S: p_1(S)=0} and #{S: p_1=0 AND antipodal}."""
    mu=subgroup(n,q); tot=0; anti=0
    for S in itertools.combinations(mu,a):
        if sum(S)%q==0:
            tot+=1
            if is_antipodal(S,mu,q): anti+=1
    return tot,anti

print("="*78)
print("C057 mechanism: single-constraint vs consecutive-window, char-p inflation onset")
print("="*78)

# 1) Reproduce documented mu_16 spurious at p=97 (small prime, beta_n ~ log_16 97 = 1.65)
n=16; a=8
for q in [97, 113, 193, 65537]:
    if (q-1)%n: continue
    beta=round(math.log(q)/math.log(n),2)
    tot,anti=count_e1_antipodal(n,a,q)
    print(f"\n[mu_16, q={q}, beta~{beta}] e_1=0 single constraint:")
    print(f"   #{{p_1=0}} = {tot},  of which antipodal = {anti},  SPURIOUS(non-antipodal) = {tot-anti}")

# 2) Single p_L=0 vs consecutive window p_1..p_L=0, sweep at a small prize-ish prime
print("\n"+"-"*78)
print("single p_L=0  vs  consecutive window p_1..p_L=0   (which object stays char-uniform?)")
print("-"*78)
for n in [8,16]:
    a=n//2
    # control (char-0 proxy) and a small prize prime
    ctrl=next(q for q in range(10**7, 10**7+10**6) if (q-1)%n==0 and isprime(q))
    small=next(q for q in range(97, 5000) if (q-1)%n==0 and isprime(q))
    print(f"\nmu_{n}, a={a}: control q'={ctrl}, small q={small} (beta~{round(math.log(small)/math.log(n),2)})")
    print("  L | single p_L=0:   char0 -> charP   | window p_1..p_L=0: char0 -> charP")
    for L in range(1,a):
        s0=count_single(n,a,L,ctrl); sp=count_single(n,a,L,small)
        w0=count_window(n,a,L,ctrl); wp=count_window(n,a,L,small)
        sm = " *" if sp!=s0 else "  "
        wm = " *" if wp!=w0 else "  "
        print(f"  {L:2d} |   {s0:7d} -> {sp:7d}{sm} |        {w0:7d} -> {wp:7d}{wm}")
