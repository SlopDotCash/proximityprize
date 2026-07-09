#!/usr/bin/env python3
"""
probe_407_shortvector_count_law.py  --  #407: count short alpha in P, test the lattice heuristic.

The norm bound certifies defect=0 only for p > L2(alpha)^{phi/2}, and even the SHORTEST defect
(L2^2=2) needs p > 2^{phi/2} = 2^{n/4} -- astronomically above prize p~n^beta. So the per-alpha
norm bound is hopeless in regime; the only hope is a CUMULATIVE COUNT: bound the NUMBER of short
alpha in P and show defect = o(E_r^(0)).

LATTICE HEURISTIC (Minkowski / Gaussian heuristic for ideal lattices):
  P is an ideal of Z[zeta_n] (deg D=phi(n)) of norm N(P)=p, so covol(P) = p * covol(Z[zeta_n])
  = p * sqrt(|disc(Q(zeta_n))|). Under the Minkowski embedding, # nonzero lattice points of P in a
  centered convex body K of volume V is HEURISTICALLY ~ V / covol(P) (when V >> covol(P)), and is
  >= 1 forced only when V >= 2^D covol(P) (Minkowski). The defect alpha have BOUNDED coefficient
  L1/L2 length (<= 2r in group coords); the set of such alpha is a fixed convex body B_r INDEPENDENT
  of p (it lives in Z[zeta_n]). So:
       #defect-alpha(r,p) = #( B_r cap P )  ~  vol(B_r) / covol(P)  =  vol(B_r)/(p sqrt|disc|).
  Since vol(B_r) grows like (2r)^D / D! and is INDEPENDENT of p, this PREDICTS:
       #defect-alpha(r,p)  ~  C(r,n) / p   -> the defect-alpha count DECAYS like 1/p at fixed r.
  This probe TESTS that heuristic: does #defect-alpha(r,p) ~ const/p across primes? If yes, then
  summing the contribution to E_r and integrating r up to ln p gives the route a real shot.

We measure, at fixed (n,r), across many primes p=1 mod n:
   D(p) := number of DISTINCT defect classes (distinct nonzero alpha in P with the (x,y) realizable
           difference of length <= 2r), and W(p) := the WEIGHTED defect E_r(mod p)-E_r^(0) (tuples).
Then we regress D(p)*p and W(p)*p vs p to see if they are ~ constant (1/p law) or grow.

Run:  python scripts/probes/probe_407_shortvector_count_law.py
"""
import sys, math, itertools
from collections import Counter, defaultdict

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root
import sympy


def reduction_table(n):
    x = sympy.symbols('x')
    Phi = sympy.Poly(sympy.cyclotomic_poly(n, x), x)
    phi_n = Phi.degree()
    Phi_coeffs = [int(c) for c in Phi.all_coeffs()][::-1]
    redtab = [[0] * phi_n for _ in range(n)]
    for k in range(phi_n): redtab[k][k] = 1
    for k in range(phi_n, n):
        prev = redtab[k - 1]
        shifted = [0] * (phi_n + 1)
        for i in range(phi_n): shifted[i + 1] += prev[i]
        top = shifted[phi_n]
        for i in range(phi_n): shifted[i] -= top * Phi_coeffs[i]
        redtab[k] = shifted[:phi_n]
    return redtab, phi_n


def primes_1mod_n_in(n, lo, hi, cap=400):
    out = []
    c = ((lo + n - 1) // n) * n + 1
    while c <= hi and len(out) < cap:
        if is_prime(c) and odd_part((c - 1) // n) > 1:
            out.append(c)
        c += n
    return out


def measure(n, r, p, redtab, phi_n):
    """Return (W, D): W = weighted defect E_r(mod p)-E_r^(0); D = # distinct defect alpha classes.
       Method: group all r-tuples by (mod-p sum). Within each mod-p class, group by char-0 class
       (reduced power-basis vector). A class with >1 distinct char-0 vector contributes defect.
       W = sum over mod-p classes of (count^2 - sum_over_char0 subcount^2) ... actually
       E_r(mod p) = sum_s (size of mod-p class s)^2; E_r^(0) = sum_v (size of char-0 class v)^2.
       defect W = E_r(mod p) - E_r^(0) >= 0. D = #distinct nonzero alpha = differences of char-0
       vectors colliding mod p (we count distinct alpha = v_i - v_j up to the lattice)."""
    g = primitive_root(p); z = pow(g, (p - 1) // n, p)
    zpows = [pow(z, j, p) for j in range(n)]
    mod_classes = defaultdict(Counter)   # s -> Counter over char0 vector
    char0 = Counter()
    for tup in itertools.product(range(n), repeat=r):
        v = tuple(sum(redtab[t][i] for t in tup) for i in range(phi_n))
        s = 0
        for t in tup: s += zpows[t]
        s %= p
        mod_classes[s][v] += 1
        char0[v] += 1
    Er_mod = sum(sum(cc.values()) ** 2 for cc in mod_classes.values())
    Er_0 = sum(c * c for c in char0.values())
    W = Er_mod - Er_0
    # distinct defect alpha: differences of distinct char0 vectors that share a mod-p class
    alpha_set = set()
    for s, cc in mod_classes.items():
        vs = list(cc.keys())
        if len(vs) > 1:
            base = vs[0]
            for v in vs[1:]:
                a = tuple(v[i] - base[i] for i in range(phi_n))
                # canonicalize sign (alpha and -alpha are the same line, but count nonzero vectors)
                alpha_set.add(a)
                alpha_set.add(tuple(-x for x in a))
    D = len(alpha_set)
    return W, Er_0, D


def main():
    print("=" * 82)
    print(" #407 SHORT-VECTOR COUNT LAW:  does #defect-alpha(r,p) ~ const/p  (lattice heuristic)?")
    print("=" * 82)
    for n in (8, 16):
        redtab, phi_n = reduction_table(n)
        disc = abs(int(sympy.cyclotomic_poly(n).as_poly().discriminant())) if False else None
        for r in ((2, 3) if n == 8 else (2,)):
            print(f"\n n={n} (phi={phi_n}), r={r}:  prize regime p>=n^2={n*n}.")
            print(f"   {'p':>8} {'2^?':>6} {'E_r^(0)':>10} {'defectW':>10} {'W/E0':>9} "
                  f"{'#alpha D':>9} {'D*p/E0... W*p':>14}")
            lo = n * n  # start at prize boundary
            hi = lo * 64 if n ** r < 60000 else lo * 8
            ps = primes_1mod_n_in(n, lo, hi, cap=60 if n == 8 else 30)
            Wp_vals, Dp_vals = [], []
            for p in ps:
                if n ** r > 4_500_000: break
                W, E0, D = measure(n, r, p, redtab, phi_n)
                Wp_vals.append(W * p)
                Dp_vals.append(D * p)
                print(f"   {p:>8} {math.log2(p):6.2f} {E0:>10} {W:>10} {W/E0:>9.4f} "
                      f"{D:>9} {W*p:>14.3e}")
            if Wp_vals:
                import statistics
                # is W*p roughly constant (=> W ~ c/p, defect decays) or growing?
                first_half = Wp_vals[:len(Wp_vals)//2] or Wp_vals
                second_half = Wp_vals[len(Wp_vals)//2:] or Wp_vals
                m1 = statistics.mean(first_half); m2 = statistics.mean(second_half)
                print(f"   --> mean(W*p) first half = {m1:.3e}, second half = {m2:.3e}, "
                      f"ratio = {m2/m1 if m1 else float('nan'):.3f}  "
                      f"(~1 => W~c/p decay; >>1 => W decays SLOWER than 1/p)")
                d1 = statistics.mean(Dp_vals[:len(Dp_vals)//2] or Dp_vals)
                d2 = statistics.mean(Dp_vals[len(Dp_vals)//2:] or Dp_vals)
                print(f"   --> mean(D*p) first half = {d1:.3e}, second half = {d2:.3e}, "
                      f"ratio = {d2/d1 if d1 else float('nan'):.3f}")
    print("\nKEY: lattice heuristic predicts #alpha = vol(B_r)/(p sqrt|disc|) => D*p ~ const, W*p ~ const")
    print("(defect decays like 1/p at fixed r). If confirmed: defect(r,p)/E_r^(0) ~ C(n,r)/(p E_r^(0)),")
    print("which is TINY in prize regime -- the route's central quantitative claim. Then the open part")
    print("is summing over r up to ln p (deep r, where vol(B_r) explodes as (2r)^{phi}).")


if __name__ == "__main__":
    main()
