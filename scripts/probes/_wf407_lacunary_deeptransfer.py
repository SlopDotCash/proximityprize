#!/usr/bin/env python3
"""
#407: where the lacunary relocation RE-COUPLES to the field (char-p transfer).
Test: at FIXED (n,a) sweep q; the lacBad value-count K(q) = #distinct e_a(S) over
the full-vanishing variety {S subset mu_n, |S|=a, e_1=..=e_{a-1}=0}.  Char-0 says
the multiset of e_a(S) values is fixed; q-dependence enters ONLY via collisions
mod p (two distinct char-0 values coincide mod p).  We count BOTH:
  - V0 = #distinct char-0 values e_a(S) computed over the COMPLEX subgroup (q-free)
  - K(q) = #distinct values mod p
If K(q) == V0 for all large p (no collisions), the relocation is genuinely
q-independent in this regime (char-0 rigidity wins).  If K(q) < V0 (collisions)
and the deficit depends on p, the field re-enters = same arithmetic wall.

We use the FULL symmetric vanishing e_1=..=e_{a-1}=0, so e_a(S) = (+/-) prod over
S of roots... actually with all lower e_i=0, S is a union of mu_a-cosets (tower
rigidity) in char 0, giving very few char-0 values -- the rigid regime.  To probe
the WINDOW (deep but not full vanishing) we instead fix t and read e_t with only
e_1..e_{t-1}=0, for a > t (the window shape).  We do a=t (full) AND a=t+1 (one slot
of freedom) to see freedom -> more values -> collision opportunity.
"""
import math, cmath, itertools
from sympy import isprime, primitive_root

def subgroup(p, n):
    g = primitive_root(p); base = pow(g, (p-1)//n, p)
    return [pow(base, k, p) for k in range(n)]

def esymm_mod(S, t, p):
    # elementary symmetric e_t of S mod p via product expansion of prod (X + x)
    coeffs = [1]
    for x in S:
        new = [0]*(len(coeffs)+1)
        for i in range(len(coeffs)):
            new[i] = (new[i] + coeffs[i]) % p
            new[i+1] = (new[i+1] + coeffs[i]*x) % p
        coeffs = new
    # coeffs[i] = e_i(S)
    return coeffs

def lacBad(p, H, a, t):
    """K = #distinct e_t(S) over S subset H,|S|=a, e_1=..=e_{t-1}=0 (mod p); also cnt."""
    vals=set(); cnt=0
    for S in itertools.combinations(H, a):
        c = esymm_mod(S, a, p)
        if all(c[i]==0 for i in range(1,t)):
            cnt+=1; vals.add(c[t])
    return len(vals), cnt

# char-0 reference value-set: use exact complex roots of unity, count distinct e_t up to tol
def lacBad_char0(n, a, t):
    z=[cmath.exp(2j*math.pi*k/n) for k in range(n)]
    vals=[]; cnt=0
    for S in itertools.combinations(z,a):
        # e_1..e_{t-1} ?= 0
        c=[1+0j]
        for x in S:
            new=[0j]*(len(c)+1)
            for i in range(len(c)):
                new[i]+=c[i]; new[i+1]+=c[i]*x
            c=new
        if all(abs(c[i])<1e-9 for i in range(1,t)):
            cnt+=1; vals.append(c[t])
    # dedup char-0 values
    uniq=[]
    for v in vals:
        if not any(abs(v-u)<1e-7 for u in uniq): uniq.append(v)
    return len(uniq), cnt

for (n,a,t) in [(8,5,3),(8,6,4),(16,5,3),(16,6,4)]:
    V0,cnt0 = lacBad_char0(n,a,t)
    print(f"--- n={n} a={a} t={t}: char-0 #distinct e_t = {V0} (cnt={cnt0}) ---")
    primes=[p for p in range(n+1, 4000) if isprime(p) and (p-1)%n==0][:14]
    devs=[]
    for p in primes:
        H=subgroup(p,n)
        K,cnt = lacBad(p,H,a,t)
        flag = "" if K==V0 else f"  <-- COLLISION deficit {V0-K}"
        if K!=V0: devs.append((p,V0-K))
        print(f"   p={p:5d} m={(p-1)//n:5d}  K(q)={K:4d}  cnt={cnt:4d}{flag}")
    if devs:
        print(f"   => FIELD-DEPENDENT: collisions at {[(p,d) for p,d in devs]} (relocation re-couples)")
    else:
        print(f"   => q-INDEPENDENT here: K==char0 {V0} for all swept p (char-0 rigidity holds)")
    print()
