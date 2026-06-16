#!/usr/bin/env python3
r"""
probe_tower_descent_pdefect_407.py  (#407)

TECHNIQUE: additive combinatorics specific to 2^mu-th roots of unity.

THE OBJECT.  mu_n = <g>, g of multiplicative order n = 2^a in F_q* (q = 1 mod n prime).
A "p-defect" of order 2r is a sparse signed relation among the n-th roots of unity that
holds mod q but NOT in C:
     sum_{i=1..r} g^{x_i} - sum_{i=1..r} g^{y_i} == 0  (mod q),   but  != 0 in C
(equivalently the multiset {g^{x_i}} != {g^{y_i}} as complex numbers).
The char-0 ("baseline") solutions are the Wick/antipodal matchings counted by Lam-Leung:
E_r^C(mu_n) = (2r-1)!! n^r.  The defect count is
     D_r(q) := E_r^{F_q}(mu_n) - E_r^C(mu_n)   >= 0.
Prize floor (face 3) <=>  D_r(q) <= n^{2r}/q  (the random baseline) at r ~ ln q.

THE QUESTION I TEST HERE (the assigned descent idea).
The tower mu_n  superset  mu_{n/2}  superset ... :  g^2 generates mu_{n/2}.
Antipodality: g^{n/2} = -1, so g^{j + n/2} = -g^j.  A signed relation
  sum eps_i g^{x_i} == 0
splits by parity of the exponent x_i.  Write x_i = 2 u_i + b_i, b_i in {0,1}.
Even part lands in mu_{n/2} = <g^2>; odd part is g * (element of mu_{n/2}).
Since 1 and g are LINEARLY INDEPENDENT over Q(mu_{n/2}) (the tower is a degree-2 ext.),
in CHAR 0 a relation forces BOTH the even-block and odd-block to vanish separately
=> exact descent  mu_n -> mu_{n/2}  (this is the Lam-Leung mechanism, recursion depth a).
In CHAR p (mod q) the two blocks need only sum to 0 JOINTLY -> the descent LEAKS.
A "leak" is exactly a nonzero alpha = (even block) in Z[zeta_{n/2}] with
  alpha + g*beta == 0 (mod q),  alpha,beta in the mu_{n/2} relation lattice, NOT both 0 in C.

GOAL: measure whether the leak count is recursively controlled (a self-improving descent
giving a poly bound on D_r), or whether the leak count is itself the wall (no descent gain).

We measure, EXACTLY (FFT over Z_q), for tower levels a, a-1, ...:
  - E_r^{F_q}(mu_{2^level})  and the char-0 baseline (2r-1)!! (2^level)^r
  - the defect D_r and D_r / (n^{2r}/q)  (the face-3 ratio; <=1 is the prize floor)
  - the per-level defect RATIO D_r(2^level)/D_r(2^{level-1})  (is it ~ const? grows? shrinks?)
  - directly: the LEAK count = # split relations whose even/odd blocks are individually
    nonzero in C (a true char-p-only crossing), to see if the tower confines them.
"""
import numpy as np, math, sys

def is_prime(x):
    if x < 2: return False
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % w == 0: return x == w
    d, s = x-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for w in (2,3,5,7,11,13,17,19,23,29,31,37):
        v = pow(w, d, x)
        if v in (1, x-1): continue
        for _ in range(s-1):
            v = v*v % x
            if v == x-1: break
        else: return False
    return True

def prime_1_mod_n_near(target, n):
    p = target - (target % n) + 1
    if p > target: p -= n
    while p > n:
        if is_prime(p): return p
        p -= n
    return None

def gen_subgroup(p, n):
    for g in range(2, p):
        h = pow(g, (p-1)//n, p)
        s, x = [], 1
        seen=set()
        for _ in range(n):
            if x in seen: break
            seen.add(x); s.append(x); x = x*h % p
        if len(s) == n: return h, s
    return None, None

def double_factorial(k):  # (2r-1)!!
    r = 1
    while k > 1:
        r *= k; k -= 2
    return r

def E_r_via_fft(p, H, rmax):
    """Exact E_r = (1/p) sum_b |S(b)|^{2r}, S(b)=sum_{x in H} e_p(bx).  Integer."""
    f = np.zeros(p)
    for x in H: f[x] = 1.0
    S = np.fft.fft(f)
    a2 = np.abs(S)**2
    out = {}
    for r in range(1, rmax+1):
        out[r] = float(np.sum(a2**r) / p)
    return out

def main():
    rmax = 4
    print("=== TOWER-DESCENT p-DEFECT PROBE (#407) ===")
    print("regime p ~ n^3 (sparse, > n^2.5).  E_r exact via FFT over Z_p.\n")
    print(f"{'lvl':>3} {'2^lvl':>5} {'r':>2} | {'E_r^Fq':>12} {'baseline':>12} "
          f"{'D_r':>12} {'D_r/(N^2r/q)':>13} {'D_r ratio/prev':>15}")
    for a in (3,4,5,6,7):          # top n = 2^a
        n = 2**a
        p = prime_1_mod_n_near(n**3, n)
        if p is None or p > 5_000_000:
            continue
        # full tower from level a down to level 1
        prevD = {}
        for level in range(a, 0, -1):
            nn = 2**level
            # subgroup of order nn = <g^{(p-1)/nn}>
            h = pow(gen_for(p), (p-1)//nn, p)
            H, x = [], 1
            for _ in range(nn):
                H.append(x); x = x*h % p
            Es = E_r_via_fft(p, H, rmax)
            for r in range(1, rmax+1):
                base = double_factorial(2*r-1) * nn**r
                D = Es[r] - base
                rand = nn**(2*r) / p
                ratio = D / rand if rand > 0 else float('inf')
                pr = ""
                if (level+1, r) in prevD and prevD[(level+1,r)] > 1e-6:
                    pr = f"{D/prevD[(level+1,r)]:.4f}"
                prevD[(level, r)] = D
                if r in (2,3,4):
                    print(f"{level:>3} {nn:>5} {r:>2} | {Es[r]:>12.1f} {base:>12.0f} "
                          f"{D:>12.1f} {ratio:>13.4f} {pr:>15}")
        print(f"  (p={p}, n=2^{a}={n}, p/n^2.5={p/n**2.5:.2f})\n")

_GENCACHE={}
def gen_for(p):
    if p in _GENCACHE: return _GENCACHE[p]
    # primitive root
    import sympy
    g = int(sympy.primitive_root(p))
    _GENCACHE[p]=g
    return g

if __name__ == "__main__":
    main()
