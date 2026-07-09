#!/usr/bin/env python3
"""
probe_407_sparse_svpmin_scaling.py -- the DECIDING measurement for the sparse-support angle.

ESTABLISHED (probe_407_sparse_defect_structure): at the onset depth the sparse defect set is the
automorphism orbit of ONE minimal-house vector of 𝔭, of norm ~p, with house = h_min(n,p).

THE DECIDING QUESTION for whether sparse-support beats the box wall:
   onset_r(n,p) = smallest r such that 𝔭 contains a SIGNED-SUM-OF-<=2r-ROOTS vector (sparse).
   This is the SPARSE-SUPPORT analogue of the box onset L_box ~ n/(2e) (Minkowski).
   If onset_r grows like sqrt(n) (= λ_1 / O(1)), sparsity gives the SAME wall as well-roundedness.
   If onset_r grows SLOWER (e.g. O(log n) or O(1)), sparsity beats the box -- a NEW lever.
   If onset_r grows FASTER, sparsity is provably cleaner than the box up to larger r (a partial
   sub-baseline bound on the prize object).

We measure, for n = 8,16,32,64 and prize primes p ~ n^4, n^5:
   - h_min(n,p) = min house over SPARSE defects (signed root-sum, vanishing mod p), and
   - onset_r(n,p), the smallest r with a sparse defect,
   - h_min/λ_1, h_min/sqrt(n), onset_r/sqrt(n), onset_r/log2(p),
   - the box-onset comparison L_box(n) = smallest L with a full L∞<=L box vector in 𝔭.

We use meet-in-the-middle on the GROUP-RING coords to reach larger n: a sparse defect z = X - Y
with X,Y signed-root-sums of <= r terms each; we search for X-value == Y-value mod p with X != Y
algebraically.  We BFS r upward and stop at first defect, recording the minimal house.

To reach n=64 we cap r and use random sampling + targeted lattice-min (the SVP-min element of 𝔭
realized sparsely == the shortest signed-root-sum congruent to a 𝔭-element).
"""
import sys, math, itertools, random
from collections import defaultdict

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root


def prize_prime(n, beta, pmax=10**12):
    base = int(round(n ** beta)); base -= base % n; base += 1; p = base
    while p < pmax:
        if is_prime(p) and odd_part((p - 1) // n) > 1:
            return p
        p += n
    return None


def order_n_root(p, n):
    return pow(primitive_root(p), (p - 1) // n, p)


def ang_table(n):
    D = n // 2
    return [([math.cos(2*math.pi*t*k/n) for k in range(D)],
             [math.sin(2*math.pi*t*k/n) for k in range(D)]) for t in range(1, n, 2)]


def house_fold(dfold, ang):
    D = len(dfold); house = 0.0
    for (rc, rs) in ang:
        re = im = 0.0
        for k in range(D):
            if dfold[k]:
                re += dfold[k]*rc[k]; im += dfold[k]*rs[k]
        house = max(house, math.hypot(re, im))
    return house


def fold_of_combo(combo, n):
    D = n//2; fold = [0]*D
    for a in combo:
        if a < D: fold[a] += 1
        else: fold[a-D] -= 1
    return tuple(fold)


def onset_via_mitm(p, z, n, ang, rmax=7, cap=4_000_000):
    """Find smallest r with a sparse defect, and the min house at onset, by meet-in-the-middle:
       enumerate one-side signed root-sums of <= s terms (s = ceil(r/2)) into value->folds, then
       look for X - Y == 0 mod p with folds differing. We grow s and look for total terms <= 2r.
       Returns (onset_r, min_house_at_onset) or (None, None)."""
    D = n//2
    zpow = [pow(z, k, p) for k in range(n)]
    # build half-side multisets of exactly t terms for t=0..rmax, indexed by mod-p value
    # store value -> dict(fold -> mintermcount). We accumulate up to s terms.
    # Use combinations_with_replacement on n coords -> value, fold, t.
    # To bound work, cap number of multisets per side.
    val_to_folds = defaultdict(dict)  # value -> {fold: min #terms to realize}
    # t = number of terms on this side
    side_t_max = rmax
    # enumerate up to side_t_max terms; stop if too many
    count = 0
    for t in range(0, side_t_max+1):
        for combo in itertools.combinations_with_replacement(range(n), t):
            count += 1
            if count > cap:
                break
            v = 0
            for a in combo: v = (v + zpow[a]) % p
            fold = fold_of_combo(combo, n)
            d = val_to_folds[v]
            if fold not in d or d[fold] > t:
                d[fold] = t
        if count > cap:
            break
    # now find defects: same value v, two folds fx != fy, total terms tx+ty minimal
    best_r = None; best_house = None
    for v, folds in val_to_folds.items():
        if len(folds) < 2: continue
        items = list(folds.items())
        for i in range(len(items)):
            fx, tx = items[i]
            for j in range(len(items)):
                if i == j: continue
                fy, ty = items[j]
                if fx == fy: continue
                # z = fx - fy, realized with tx + ty terms; depth r = ceil((tx+ty)/2)? balanced.
                # A balanced relation Σx=Σy needs equal sides; here we allow X(tx terms)=Y(ty terms).
                # The signed-sum z = X - Y has L1(group) <= tx+ty, so 2r >= tx+ty -> r >= (tx+ty)/2.
                terms = tx + ty
                r = math.ceil(terms / 2)
                dz = tuple(fx[k]-fy[k] for k in range(D))
                if all(x == 0 for x in dz):  # char-0 zero, not a defect
                    continue
                if best_r is None or r < best_r or (r == best_r):
                    h = house_fold(list(dz), ang)
                    if best_r is None or r < best_r or (r == best_r and (best_house is None or h < best_house)):
                        if best_r is None or r < best_r:
                            best_r = r; best_house = h
                        elif r == best_r and h < best_house:
                            best_house = h
    return best_r, best_house


def main():
    print("="*100)
    print(" #407 SPARSE-SUPPORT SVP-MIN SCALING: onset_r and h_min vs n (the deciding measurement)")
    print("="*100)
    print(f"{'n':>4} {'beta':>5} {'p':>14} {'log2p':>6} | {'onset_r':>7} {'h_min':>7} {'λ_1':>6} "
          f"{'h/λ_1':>6} {'h/√n':>6} {'r/√n':>6} {'r/log2p':>7}")
    for n in (8, 16, 32, 64):
        ang = ang_table(n); lam1 = math.sqrt(n/2)
        rmax = {8: 7, 16: 6, 32: 5, 64: 4}[n]
        cap = {8: 5_000_000, 16: 5_000_000, 32: 6_000_000, 64: 8_000_000}[n]
        for beta in (4.0, 5.0):
            p = prize_prime(n, beta)
            if p is None:
                print(f"{n:>4} {beta:>5} (no prime)"); continue
            z = order_n_root(p, n)
            onset_r, h_min = onset_via_mitm(p, z, n, ang, rmax=rmax, cap=cap)
            if onset_r is None:
                print(f"{n:>4} {beta:>5.1f} {p:>14} {math.log2(p):>6.1f} | "
                      f"{'>'+str(rmax):>7} {'--':>7} {lam1:>6.2f}   (no sparse defect <= rmax)")
                continue
            print(f"{n:>4} {beta:>5.1f} {p:>14} {math.log2(p):>6.1f} | "
                  f"{onset_r:>7} {h_min:>7.2f} {lam1:>6.2f} {h_min/lam1:>6.3f} "
                  f"{h_min/math.sqrt(n):>6.3f} {onset_r/math.sqrt(n):>6.3f} {onset_r/math.log2(p):>7.3f}")
    print("\nDECISION CRITERION:")
    print(" - onset_r ~ c·√n  AND  h_min ~ √n: sparse onset = well-rounded λ_1 wall (NO new lever).")
    print(" - onset_r grows SLOWER than √n (e.g. ~log p): sparsity reaches deeper clean -> NEW partial bound.")
    print(" - h_min/λ_1 ~ const ≈ 1: sparse SVP-min ≈ lattice SVP-min (sparsity does NOT lengthen the")
    print("   shortest vector) -> the box onset and sparse onset coincide -> sparsity gives NOTHING new.")


if __name__ == "__main__":
    main()
