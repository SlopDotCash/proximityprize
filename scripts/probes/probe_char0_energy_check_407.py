#!/usr/bin/env python3
r"""
probe_char0_energy_check_407.py  (#407)

Sanity: compute E_r^C(mu_n) = #{(x,y) in [n]^{2r} : sum zeta^{x_i} = sum zeta^{y_i} in C},
zeta = exp(2pi i/n), EXACTLY by brute force, and compare to the claimed Lam-Leung baseline
(2r-1)!! n^r.  Also verify E_r^{F_q} >= E_r^C (every C-solution is a mod-q solution), which
the tower probe seemed to VIOLATE -- so the baseline formula must be checked.

We also report the TRUE defect D_r = E_r^{Fq} - E_r^C (using the brute-forced E_r^C),
which by the inclusion must be >= 0.
"""
import numpy as np, math, itertools, cmath

def is_prime(x):
    if x < 2: return False
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % w == 0: return x == w
    d,s=x-1,0
    while d%2==0: d//=2; s+=1
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        v=pow(w,d,x)
        if v in (1,x-1): continue
        for _ in range(s-1):
            v=v*v%x
            if v==x-1: break
        else: return False
    return True

def prime_1_mod_n_near(t,n):
    p=t-(t%n)+1
    if p>t: p-=n
    while p>n:
        if is_prime(p): return p
        p-=n
    return None

def dfac(k):
    r=1
    while k>1: r*=k; k-=2
    return r

def E_r_complex_brute(n, r):
    """exact #{(x,y): sum zeta^x_i = sum zeta^y_i in C}, zeta=exp(2pi i/n).
    Use integer fingerprint: represent sum_i zeta^{a_i} by its coefficient vector in
    Z^n (count of each residue), then sum zeta^a = sum zeta^b  iff  the vectors give equal
    complex value.  For 2^a roots, zeta^{j+n/2} = -zeta^j, so reduce coeff vector mod the
    relation zeta^{j+n/2}=-zeta^j to a vector in Z^{n/2}: c'_j = c_j - c_{j+n/2}.
    Two multisets are equal in C iff reduced vectors are equal (1,zeta,...,zeta^{n/2-1} are a
    Q-basis of Q(zeta_n) since [Q(zeta_{2^a}):Q]=2^{a-1}=n/2)."""
    half=n//2
    from collections import Counter
    # enumerate all r-multisets-with-order? we need ordered tuples for the energy count.
    # E_r counts ORDERED (x,y). Equivalent: for each ordered r-tuple x, its reduced vector v(x);
    # E_r = sum_v (#tuples mapping to v)^2.
    cnt=Counter()
    for x in itertools.product(range(n), repeat=r):
        v=[0]*half
        for a in x:
            if a<half: v[a]+=1
            else: v[a-half]-=1
        cnt[tuple(v)]+=1
    return sum(c*c for c in cnt.values())

def E_r_mod_q(p, H, r):
    """exact E_r over F_p by the same fingerprint but mod p: sum mod p."""
    from collections import Counter
    cnt=Counter()
    for x in itertools.product(H, repeat=r):
        cnt[sum(x)%p]+=1
    return sum(c*c for c in cnt.values())

print("Check char-0 energy vs (2r-1)!! n^r, and D_r = E_r^Fq - E_r^C >= 0.\n")
print(f"{'n':>4} {'r':>2} | {'E_r^C brute':>12} {'(2r-1)!!n^r':>12} {'match?':>7} | "
      f"{'E_r^Fq':>12} {'D_r=Fq-C':>10} {'D_r>=0?':>7}")
for a in (2,3,4):
    n=2**a
    for r in (1,2,3):
        if n**r > 200000:   # keep brute force tractable
            continue
        Ec = E_r_complex_brute(n, r)
        base = dfac(2*r-1)*n**r
        p = prime_1_mod_n_near(n**3, n)
        # build subgroup
        import sympy
        g=int(sympy.primitive_root(p)); h=pow(g,(p-1)//n,p)
        H=[]; x=1
        for _ in range(n): H.append(x); x=x*h%p
        Eq = E_r_mod_q(p,H,r)
        D = Eq-Ec
        print(f"{n:>4} {r:>2} | {Ec:>12} {base:>12} {str(Ec==base):>7} | "
              f"{Eq:>12} {D:>10} {str(D>=0):>7}")
