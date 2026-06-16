#!/usr/bin/env python3
"""
sweep_A12_phase_align.py  — Actionable A12 (#407 / merged 389-T03)

Tower-recursive phase alignment as a STRUCTURAL fact (worst-vs-average mechanism).

See the Lean brick `Sweep_A12_PhaseAlignmentTower.lean` header for the full statement.
Honesty: the DESCENT use of this alignment (M(n)^2 <= 2 M(n/2)^2) is REFUTED worst-case;
this probe re-confirms only the STRUCTURAL facts the brick formalizes.

Structural facts checked (n = 2^mu, mu_n = order-n subgroup of F_p^*, z = generator):
  mu_n = mu_{n/2}  U  z*mu_{n/2}  (disjoint),  A = S_b(mu_{n/2}),  B = S_{b z}(mu_{n/2}):
    [SPLIT]         S_b(mu_n)      = A + B                      (untwisted)
    [TWIST]         S_b^chi(mu_n)  = A - B                      (order-2 twist)
    [PARALLELOGRAM] |A+B|^2 + |A-B|^2 = 2(|A|^2 + |B|^2)        (EXACT, the backbone lemma)
    [ALIGN]         at worst b*, untwisted |A+B| realizes the max  <=>  Re(A conj B) >= 0
    [REAL]          A, B real (negation symmetry -1 = z^{n/2} in mu_n) => "cos=1" = same sign
    [PERSIST]       alignment persists one 2-adic level down
    [PROXY]         |S_b*(mu_{n/2})| vs B(mu_{n/2})  (worst-frequency faithfulness)

Efficiency: eta is CONSTANT on multiplicative cosets b*mu_n, so the distinct values of
b -> S_b(mu_n) number only m=(p-1)/n.  We scan one representative per coset (m reps), and
vectorize the inner sum with numpy.  Full O(p) scan avoided.
"""

import math
import numpy as np
from sympy import isprime, primitive_root


def find_prime(n, beta_target):
    target = int(round(n ** beta_target))
    p = target - (target % n) + 1
    if p <= target:
        p += n
    while not isprime(p):
        p += n
    return p


def subgroup_data(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)            # generator of mu_n (order n)
    H = np.array([pow(h, i, p) for i in range(n)], dtype=np.int64)
    return g, h, H


def coset_reps(p, n, g):
    """Representatives of F_p^* / mu_n: g^0, g^1, ..., g^{m-1} where m=(p-1)/n.
    eta is constant on each coset b*mu_n, so these m reps cover all distinct |S_b| values."""
    m = (p - 1) // n
    return np.array([pow(g, j, p) for j in range(m)], dtype=np.int64)


def Sb_vec(p, H, b):
    """S_b(H) = sum_{x in H} e_p(b x), vectorized."""
    ang = (2.0 * math.pi / p) * ((b * H) % p)
    return np.exp(1j * ang).sum()


def worst_b(p, n, g, H):
    """Worst frequency b* (max |S_b|) over the m coset reps."""
    reps = coset_reps(p, n, g)
    best_b, best = 0, -1.0
    for b in reps.tolist():
        if b == 0:
            continue
        v = abs(Sb_vec(p, H, b))
        if v > best:
            best, best_b = v, b
    return best_b, best


def analyze(n, p, verbose=True):
    g, h, H = subgroup_data(p, n)
    z = h
    half = n // 2
    Hhalf = np.array([pow(h, 2 * i, p) for i in range(half)], dtype=np.int64)
    zHhalf = (z * Hhalf) % p

    bstar, B_full = worst_b(p, n, g, H)

    A = Sb_vec(p, Hhalf, bstar)
    Bc = Sb_vec(p, zHhalf, bstar)           # = S_{b* z}(mu_{n/2})
    S_untwist = A + Bc
    S_twist = A - Bc
    S_full = Sb_vec(p, H, bstar)

    split_residual = abs(S_untwist - S_full)
    parallelogram_residual = abs((abs(S_untwist) ** 2 + abs(S_twist) ** 2)
                                 - 2 * (abs(A) ** 2 + abs(Bc) ** 2))
    denom = abs(A) * abs(Bc)
    cross = (A * Bc.conjugate()).real
    cos_align = cross / denom if denom > 1e-12 else float('nan')
    imag_mag = max(abs(A.imag), abs(Bc.imag), abs(S_full.imag))
    untwist_bigger = abs(S_untwist) >= abs(S_twist)

    if verbose:
        print(f"  n={n:3d}  p={p:>14d}  beta~{math.log(p)/math.log(n):.2f}  m=(p-1)/n={(p-1)//n}")
        print(f"     B(mu_n)=|S_b*|     = {B_full:.6f}  (b*={bstar})")
        print(f"     A=S_b*(mu_n/2)     = {A.real:+.6f} (im {A.imag:+.1e})")
        print(f"     B=S_b*(z mu_n/2)   = {Bc.real:+.6f} (im {Bc.imag:+.1e})")
        print(f"     cos(align A,B)     = {cos_align:+.6f}   untwist_bigger={untwist_bigger}")
        print(f"     |A+B|={abs(S_untwist):.6f}  |A-B|={abs(S_twist):.6f}")
        print(f"     SPLIT residual |A+B - S_full|  = {split_residual:.2e}  (=0)")
        print(f"     PARALLELOGRAM residual         = {parallelogram_residual:.2e}  (=0)")
        print(f"     max|Im| (negation sym => 0)    = {imag_mag:.2e}")
    return dict(n=n, p=p, bstar=bstar, B_full=B_full, cos_align=cos_align,
                untwist_bigger=bool(untwist_bigger), split_residual=split_residual,
                parallelogram_residual=parallelogram_residual, imag_mag=imag_mag)


def persistence_one_level(n, p):
    g, h, H = subgroup_data(p, n)
    quarter = n // 4
    if quarter < 1:
        return float('nan')
    bstar, _ = worst_b(p, n, g, H)
    w = pow(h, 2, p)                         # generator of mu_{n/2}
    Hq = np.array([pow(h, 4 * i, p) for i in range(quarter)], dtype=np.int64)
    wHq = (w * Hq) % p
    A2 = Sb_vec(p, Hq, bstar)
    B2 = Sb_vec(p, wHq, bstar)
    denom = abs(A2) * abs(B2)
    return (A2 * B2.conjugate()).real / denom if denom > 1e-12 else float('nan')


def proxy_faithfulness(n, p):
    g, h, H = subgroup_data(p, n)
    half = n // 2
    Hhalf = np.array([pow(h, 2 * i, p) for i in range(half)], dtype=np.int64)
    bf, _ = worst_b(p, n, g, H)
    bh, vh = worst_b(p, n // 2, g, Hhalf) if half >= 2 else (0, 1.0)
    A_at_full_worst = abs(Sb_vec(p, Hhalf, bf))
    return A_at_full_worst, vh, (A_at_full_worst / vh if vh > 0 else float('nan'))


def main():
    print("=" * 80)
    print("A12: tower-recursive phase alignment — structural fact re-confirmation")
    print("=" * 80)

    configs = []
    for n in [8, 16, 32, 64]:
        configs.append((n, 2.0))   # p ~ n^2  (small)
        configs.append((n, 4.0))   # p ~ n^4  (prize-shaped scaling)

    results = []
    for n, beta in configs:
        p = find_prime(n, beta)
        m = (p - 1) // n
        # coset-rep scan is O(m * n); cap to keep it fast
        if m * n > 60_000_000:
            print(f"\n[ n={n}, p~n^{beta}, p={p} ]  SKIPPED (m*n={m*n} too large)")
            continue
        print(f"\n[ n={n}, p~n^{beta} ]")
        r = analyze(n, p)
        r['persist_cos'] = persistence_one_level(n, p)
        pa, pt, pr = proxy_faithfulness(n, p)
        r['proxy_ratio'] = pr
        print(f"     persistence one level down: cos = {r['persist_cos']:+.6f}")
        print(f"     proxy faithfulness |S_b*(mu_n/2)|/B(mu_n/2) = {pr:.4f}  ({pa:.4f} vs {pt:.4f})")
        results.append(r)

    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"{'n':>4} {'p':>13} {'cos_align':>10} {'untw>':>6} {'parallelo':>11} "
          f"{'persist':>9} {'proxy':>7} {'maxIm':>9}")
    for r in results:
        print(f"{r['n']:>4} {r['p']:>13} {r['cos_align']:>+10.5f} {str(r['untwist_bigger'])[:1]:>6} "
              f"{r['parallelogram_residual']:>11.1e} {r['persist_cos']:>+9.5f} "
              f"{r['proxy_ratio']:>7.4f} {r['imag_mag']:>9.1e}")

    print("\nVERDICTS:")
    align = [r for r in results if not math.isnan(r['cos_align'])]
    print(f"  [A] worst-b half-sums aligned (cos>0.999):       "
          f"{all(r['cos_align'] > 0.999 for r in align)}  "
          f"(min cos = {min(r['cos_align'] for r in align):+.5f})")
    print(f"  [B] UNTWISTED |A+B| realizes the max at b*:      "
          f"{all(r['untwist_bigger'] for r in results)}")
    print(f"  [C] parallelogram identity exact (<1e-6):        "
          f"{all(r['parallelogram_residual'] < 1e-6 for r in results)}  "
          f"(max = {max(r['parallelogram_residual'] for r in results):.1e})")
    print(f"  [D] SPLIT exact (<1e-6):                         "
          f"{all(r['split_residual'] < 1e-6 for r in results)}  "
          f"(max = {max(r['split_residual'] for r in results):.1e})")
    pp = [r for r in results if not math.isnan(r['persist_cos'])]
    print(f"  [E] alignment PERSISTS one level (cos>0.999):    "
          f"{all(r['persist_cos'] > 0.999 for r in pp)}  "
          f"(min = {min(r['persist_cos'] for r in pp):+.5f})")
    print(f"  [F] negation symmetry: A,B real (maxIm<1e-9):    "
          f"{all(r['imag_mag'] < 1e-9 for r in results)}")
    print(f"  [G] proxy faithfulness ratio range:              "
          f"[{min(r['proxy_ratio'] for r in results):.4f}, "
          f"{max(r['proxy_ratio'] for r in results):.4f}]")


if __name__ == "__main__":
    main()
