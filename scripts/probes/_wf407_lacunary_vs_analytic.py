#!/usr/bin/env python3
"""
#407 route-unification, DECISIVE test of the ONE claimed-distinct route.

The DyadicLacunaryDeltaStar relocation claims the prize floor is governed by the
COMBINATORIAL incidence
    I(a,b) = #lacBad(mu_n, a, t) = #{ e_t(S) : S subset mu_n, |S|=a, e_1=..=e_{t-1}=0 },  t=a-b
which it asserts is "q-independent, finite, decidable, contains NO analytic input"
(i.e. NOT the analytic sup-norm B = max_b |sum_{x in mu_n} e_p(bx)|).

If that relocation is a GENUINE escape, then I(a,b) should be governed by char-0
cyclotomic rigidity and be (essentially) q-INDEPENDENT -- decoupled from B.
If instead I(a,b) carries the SAME content as the character sum (the campaign's
"field-dependent #orbits = same character-sum content"), then changing q at fixed n
should move I in step with the analytic/arithmetic structure -- i.e. it is NOT
decoupled, and the relocation is cosmetic (same wall).

We test the SHARPEST decidable proxy the file itself names: the t=2 fibre count
(simultaneous vanishing e_1(S)=0, read e_2(S)).  By Vieta, S subset mu_n with
e_1(S)=sum=0 and we count distinct e_2(S)=sum_{i<j} x_i x_j values.
We sweep q at FIXED n and measure:
  - K(q)   = #distinct e_2 values over { S subset mu_n : |S|=a, sum S = 0 }  (the lacBad size)
  - B(q)   = max_{b!=0} |sum_{x in mu_n} e_p(b x)|   (the analytic floor)
A genuine relocation predicts K(q) ~ const (q-independent).  Same-wall predicts K(q)
tracks the arithmetic of q (jumps when p-1 gains small torsion), exactly as B does.
"""
import math, cmath, itertools
from sympy import isprime, primitive_root

def subgroup(p, n):
    g = primitive_root(p); m = (p-1)//n
    base = pow(g, m, p)
    return [pow(base, k, p) for k in range(n)]

def B_floor(p, H):
    w = 2j*math.pi/p
    best = 0.0
    for b in range(1, p):
        s = abs(sum(cmath.exp(w*((b*x) % p)) for x in H))
        if s > best: best = s
    return best

def lacBad_t2(p, H, a):
    """#distinct e_2(S) over S subset H, |S|=a, e_1(S)=sum=0 (mod p)."""
    n = len(H)
    vals = set()
    cnt = 0
    for S in itertools.combinations(H, a):
        s = sum(S) % p
        if s != 0:
            continue
        cnt += 1
        # e_2 = (s^2 - p2)/2 ; with s=0, e_2 = -p2/2 mod p
        p2 = sum((x*x) % p for x in S) % p
        e2 = (-p2 * pow(2, p-2, p)) % p
        vals.add(e2)
    return len(vals), cnt

# fixed n, sweep several primes p with p = 1 mod n; small n,a so combinatorics is feasible.
n = 8
a = 4   # weight-a agreement sets; t = a-b with e_1=0 means b=a-... we use the t=a (full vanishing down to e_2): here we read e_2 directly with e_1=0, i.e. t up to a-?  Using a=4,e_1=0 -> count e_2.
primes = [p for p in [17,41,73,89,97,113,137,193,233,241,257,281,313,337,353,401,409,433,449,457,521,569,577,593,601,617,641,673,729+0,761,769,809,857,881,929,937,953,977,1009]
          if isprime(p) and (p-1)%n==0]
print(f"n={n}, a={a}; sweeping {len(primes)} primes p==1 mod {n}")
print(" p     m=(p-1)/n  small_tors(p-1/n odd-part)  K=#lacBad(t2)  cnt(e1=0)   B   B/sqrt(n ln m)")
rows=[]
for p in primes[:24]:
    H = subgroup(p, n)
    K, cnt = lacBad_t2(p, H, a)
    B = B_floor(p, H)
    m = (p-1)//n
    op = m
    while op % 2 == 0: op //= 2     # odd part of m
    lnm = math.log(m) if m>1 else 1.0
    rows.append((p, m, op, K, cnt, B, B/math.sqrt(n*lnm)))
    print(f"{p:5d}  {m:6d}   oddpart={op:4d}        K={K:4d}     cnt={cnt:4d}   B={B:6.3f}  {B/math.sqrt(n*lnm):.3f}")
Ks = [r[3] for r in rows]; Bs=[r[5] for r in rows]
print()
print(f"K (lacBad size) range: min={min(Ks)} max={max(Ks)} -> CV={ (max(Ks)-min(Ks)) }  (q-independent would be ~constant)")
print(f"B range: {min(Bs):.2f}..{max(Bs):.2f}")
# correlation of K with the arithmetic (odd-part torsion of m) and with B
import statistics
print("If K varies with the prime (not constant) and the variation aligns with small-torsion")
print("spikes of p-1, the lacunary incidence carries the SAME arithmetic content as B")
print("=> the 'relocation off the analytic wall' is cosmetic; same open object.")
