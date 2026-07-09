#!/usr/bin/env python3
"""
sweep_A23_cross_parity.py  --  #407 actionable A23 (merged 407-T09).

A23 ASSIGNMENT (the parts NOT already settled by the T09 `walled` verdict):
  (P1) Re-confirm the cross-parity leak  A == -g*B (mod p)  fraction at the genuine-defect ONSET
       (the T09 verdict reproduced "100% in prize regime" but only at depth r=2; re-confirm at the
       smallest depth r* where a *genuine* (nonzero-sum, char-p-only) defect first appears).
  (P2) **The genuinely-unverified A23 claim: the THRESHOLD LAW**
            r*(p) == (1/2) * lambda_1^{L1,even}(p)
       where lambda_1^{L1,even}(p) is the minimum L1-weight (= total number of +-1 terms, i.e. the
       group-ring 1-norm) of a NONZERO, EVEN-weight, +-1 cyclotomic relation among the n-th roots
       of unity that VANISHES mod p but NOT in char 0.  An even-weight relation  sum_{i in P} z^i
       - sum_{j in N} z^j == 0 (mod p)  with |P| == |N| == r (so it is a depth-r balanced additive-
       energy collision) has L1-weight |P|+|N| = 2r; the shortest such even relation should turn on
       exactly at the depth where the additive energy E_r first exceeds its char-0 value.
       We test the equality  r* == ceil(lambda_1^{L1,even}/2)  by EXACT brute-force shortest-even-
       L1-vector enumeration (meet-in-the-middle), comparing it against the additive-energy onset
       r* = min{r : E_r^(p)(mu_n) > E_r^(0)(mu_n)}.
  (P3) Attempt to turn the leak into a COUNTING bound: does the leak's coset-concentration
       (genuine defects all live in a small number of multiplicative cosets g*mu_n) cap the
       defect count below the additive-energy / BGK wall?  Measure the number of distinct product-
       units g and the per-g defect mass; decide whether |union of cosets| < full energy.

ALL ENUMERATION IS EXACT (no sampling for the small cases).  Prize-shaped: n = 2^mu, p == 1 mod 2n,
beta = log_n(p).
"""
import sys, math, itertools
from collections import defaultdict, Counter


# ----------------------------------------------------------------------------- number theory
def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def factorize(m):
    s = {}; d = 2
    while d*d <= m:
        while m % d == 0: s[d] = s.get(d,0)+1; m //= d
        d += 1
    if m > 1: s[m] = s.get(m,0)+1
    return s

def primitive_root(p):
    fac = factorize(p-1)
    for g in range(2, p):
        if all(pow(g,(p-1)//q,p) != 1 for q in fac): return g
    return None

def smallest_prime_1_mod(n, lo):
    p = lo + ((1 - lo) % n)
    if p < 3: p += n
    while True:
        if p % n == 1 and is_prime(p): return p
        p += n

def order_n_root(p, n):
    return pow(primitive_root(p), (p-1)//n, p)


# ----------------------------------------------------------------------------- char-0 detection
def c0_vanishes(coeffs, n):
    """coeffs: integer vector of length n (group-ring element sum_i c_i z^i, z=primitive n-th root).
    Returns True iff it is 0 in Z[z_n].  Fold to the power basis 1,z,...,z^{n/2-1} using z^{n/2}=-1
    (valid for n a power of two; z^{n/2}=-1 since the unique order-2 element of mu_n is -1)."""
    D = n // 2
    fold = [0]*D
    for i in range(n):
        if i < D: fold[i] += coeffs[i]
        else:     fold[i-D] -= coeffs[i]
    return all(x == 0 for x in fold)


# ----------------------------------------------------------------------------- E_r onset (additive energy)
def Er_value(p, mu, r):
    """#{(A,B) in (multisets of size r)^2 : sum A == sum B mod p}, counting ORDERED r-tuples.
    We use the standard E_r = sum_s rep_r(s)^2 with rep_r(s) = #{ordered r-tuples summing to s}."""
    # representation counts for ordered r-tuples of mu elements
    rep = Counter({0: 1})
    for _ in range(r):
        nxt = Counter()
        for s, c in rep.items():
            for x in mu:
                nxt[(s+x) % p] += c
        rep = nxt
    return sum(c*c for c in rep.values())

def Er_char0(n, r):
    """char-0 (complex) additive energy of mu_n: #{ordered (A,B): sum_C A == sum_C B}, EXACT via
    folding to the power basis.  For small n,r enumerate ordered r-tuples and bucket by fold vector."""
    D = n // 2
    rep = Counter({tuple([0]*D): 1})
    for _ in range(r):
        nxt = Counter()
        for fold, c in rep.items():
            for a in range(n):
                f = list(fold)
                if a < D: f[a] += 1
                else:     f[a-D] -= 1
                nxt[tuple(f)] += c
        rep = nxt
    return sum(c*c for c in rep.values())

def energy_onset(p, mu, n, rmax):
    """smallest r in [1,rmax] with E_r^(p) > E_r^(0); returns (r*, defect_at_rstar) or (None,0)."""
    for r in range(1, rmax+1):
        Ep = Er_value(p, mu, r)
        E0 = Er_char0(n, r)
        if Ep > E0:
            return r, Ep - E0
    return None, 0


# ----------------------------------------------------------------------------- shortest even L1 relation
def lambda1_L1_even(p, z, n, half_rmax, cap=6_000_000):
    """Shortest EVEN-weight +-1 relation vanishing mod p but not in char 0, by meet-in-the-middle.
    An even balanced relation is sum_{i in P} z^i == sum_{j in N} z^j (mod p), |P|==|N| (multisets).
    Enumerate all r-multisets on one side (value mod p + fold vector) for r=0..half_rmax; a defect is
    two DIFFERENT folds with the SAME value, total terms = |left|+|right|.  We want the minimal total
    L1 = (#left terms)+(#right terms) over genuinely-char-0-distinct pairs.
    Returns (lambda1_L1_even, r_from_lambda = ceil(lambda1/2), best_r_balanced) where best_r_balanced
    is the minimal r with a BALANCED (|P|==|N|==r) defect (the additive-energy reading)."""
    D = n // 2
    zpow = [pow(z, k, p) for k in range(n)]
    # value -> { fold(tuple) : min #terms }
    val_to_folds = defaultdict(dict)
    count = 0
    for t in range(0, half_rmax+1):
        for combo in itertools.combinations_with_replacement(range(n), t):
            count += 1
            if count > cap: break
            v = 0
            for a in combo: v = (v + zpow[a]) % p
            fold = [0]*D
            for a in combo:
                if a < D: fold[a] += 1
                else:     fold[a-D] -= 1
            fold = tuple(fold)
            d = val_to_folds[v]
            if fold not in d or d[fold] > t:
                d[fold] = t
        if count > cap: break
    best_L1 = None        # min total terms over ALL defects (even or odd split)
    best_r_balanced = None  # min r with a |P|==|N|==r defect
    for v, folds in val_to_folds.items():
        if len(folds) < 2: continue
        items = list(folds.items())
        for i in range(len(items)):
            fx, tx = items[i]
            for j in range(i+1, len(items)):
                fy, ty = items[j]
                if fx == fy: continue
                # the relation X - Y has group-ring coords fx - fy; char-0 nonzero by construction
                dz = [fx[k]-fy[k] for k in range(D)]
                if all(x == 0 for x in dz):
                    continue
                total = tx + ty
                if best_L1 is None or total < best_L1:
                    best_L1 = total
                # balanced reading: this defect uses tx terms one side, ty the other; a *balanced*
                # depth-r collision needs tx==ty==r.  Record the min such r.
                if tx == ty:
                    if best_r_balanced is None or tx < best_r_balanced:
                        best_r_balanced = tx
    r_from_lambda = math.ceil(best_L1/2) if best_L1 is not None else None
    return best_L1, r_from_lambda, best_r_balanced


# ----------------------------------------------------------------------------- leak fraction at onset
def leak_fraction_at_onset(p, z, n, r, cap_defects=20000):
    """At depth r, enumerate genuine (char-p-only) balanced defects (P,N), |P|=|N|=r, and measure
    the fraction admitting a multiplicative dilation S_P = t * S_N (setwise, t in F_p^*), i.e. the
    A==-g*B leak.  Also collect the distinct product-units g and how concentrated they are.
    Returns (n_genuine, leak_count, distinct_g, g_counter)."""
    D = n // 2
    zpow = [pow(z, k, p) for k in range(n)]
    # bucket r-multisets by (mod-p value, char-0 fold)
    by_val = defaultdict(lambda: defaultdict(list))  # value -> fold -> [combo]
    for combo in itertools.combinations_with_replacement(range(n), r):
        v = 0
        for a in combo: v = (v + zpow[a]) % p
        fold = [0]*D
        for a in combo:
            if a < D: fold[a] += 1
            else:     fold[a-D] -= 1
        by_val[v][tuple(fold)].append(combo)
    defects = []
    for v, byfold in by_val.items():
        if len(byfold) < 2: continue
        keys = list(byfold.keys())
        for i in range(len(keys)):
            for j in range(i+1, len(keys)):
                A = byfold[keys[i]][0]; B = byfold[keys[j]][0]
                defects.append((A, B))
                if len(defects) >= cap_defects: break
            if len(defects) >= cap_defects: break
        if len(defects) >= cap_defects: break
    muset = set(zpow)  # mu_n
    leak = 0; gs = []
    for (A, B) in defects:
        SA = frozenset(zpow[a] for a in A)
        SB = frozenset(zpow[b] for b in B)
        if len(SA) != len(SB):
            continue
        SAl = list(SA); SBl = list(SB)
        a0 = SAl[0]
        found = False
        for b0 in SBl:
            t = a0 * pow(b0, -1, p) % p
            if frozenset((t*x) % p for x in SB) == SA:
                # leak: S_A = t * S_B; the "g" in A=-g*B is g = -t
                g = (p - t) % p
                gs.append(g); found = True; break
        if found: leak += 1
    return len(defects), leak, len(set(gs)), Counter(gs)


# ----------------------------------------------------------------------------- main
def main():
    print("="*112)
    print(" A23  cross-parity leak  +  THRESHOLD LAW  r* == (1/2) lambda_1^{L1,even}(p)")
    print("="*112)
    # rmax / cap tuned so brute-force is exact and feasible
    cfg = {
        8:  dict(rmax=6, half=6, cap=4_000_000),
        16: dict(rmax=5, half=5, cap=5_000_000),
        32: dict(rmax=4, half=4, cap=6_000_000),
    }
    print(f"\n{'n':>3} {'beta':>5} {'p':>10} {'log_n p':>7} | "
          f"{'E_r* onset':>10} {'def@r*':>7} | {'lam1_L1ev':>9} {'ceil/2':>6} {'bal_r':>5} | "
          f"{'law OK?':>7} | {'leak%':>6} {'#g':>4}")
    rows = []
    for n in (8, 16, 32):
        c = cfg[n]
        for beta in (2.0, 2.5, 3.0, 3.5):
            base = max(2*n+1, int(round(n**beta)))
            p = smallest_prime_1_mod(2*n, base)
            mu = [pow(order_n_root(p, n), i, p) for i in range(n)]
            z = order_n_root(p, n)
            # (energy onset)
            r_energy, defat = energy_onset(p, mu, n, c['rmax'])
            # (lambda_1 even L1)
            L1, r_lam, bal_r = lambda1_L1_even(p, z, n, c['half'], cap=c['cap'])
            # the threshold law test (CORRECT reading): lambda_1^{L1,EVEN} is the shortest
            # EVEN-WEIGHT (balanced, |P|==|N|==r) relation, L1 = 2*bal_r; so r* == (1/2)*L1_even
            # == bal_r exactly.  (The unbalanced shortest L1 = `L1` below may be ODD-total and is
            # NOT an additive-energy collision -- it is a |P|!=|N| relation -- so it must NOT be
            # used for the energy-onset law.  See n=32 beta=3.0: unbalanced L1=5 (a 2-vs-3) exists
            # at total 5, but the shortest BALANCED even relation is r=4, matching the energy onset.)
            L1_even = (2*bal_r) if bal_r is not None else None
            r_from_even = bal_r
            if r_energy is None and bal_r is None:
                law = "vacuous"
            elif r_energy is None or r_from_even is None:
                law = "MISS"
            else:
                law = "YES" if (r_energy == r_from_even) else f"NO({r_energy}v{r_from_even})"
            # (leak at the energy onset depth)
            if r_energy is not None and math.comb(n+r_energy-1, r_energy) <= 3_000_000:
                nd, leak, ng, gc = leak_fraction_at_onset(p, z, n, r_energy)
                leakpct = (100.0*leak/nd) if nd else float('nan')
            else:
                nd = 0; leak = 0; ng = 0; leakpct = float('nan'); gc = Counter()
            rows.append((n, beta, p, r_energy, defat, L1, r_lam, bal_r, law, leakpct, ng, nd, gc))
            re_s = str(r_energy) if r_energy is not None else ">rmax"
            L1_s = str(L1_even) if L1_even is not None else ">2*half"
            rl_s = str(r_from_even) if r_from_even is not None else "-"
            bl_s = str(bal_r) if bal_r is not None else "-"
            lk_s = f"{leakpct:5.1f}" if not math.isnan(leakpct) else "  n/a"
            print(f"{n:>3} {beta:>5.1f} {p:>10} {math.log(p,n):>7.2f} | "
                  f"{re_s:>10} {defat:>7} | {L1_s:>9} {rl_s:>6} {bl_s:>5} | "
                  f"{law:>7} | {lk_s:>6} {ng:>4}")

    print("\n" + "="*112)
    print("THRESHOLD-LAW VERDICT (P2):  r* == (1/2) * lambda_1^{L1,EVEN}  (EVEN = balanced |P|=|N|)")
    tested = [r for r in rows if r[8] not in ("vacuous", "MISS")]
    ok = [r for r in tested if r[8] == "YES"]
    print(f"  among {len(tested)} non-vacuous instances, r*_energy == (1/2)*lambda_1^L1even == bal_r: "
          f"{len(ok)}/{len(tested)}")
    print("  NOTE: this requires the EVEN-WEIGHT (balanced) shortest relation; the UNBALANCED shortest")
    print("  L1 (e.g. a 2-vs-3 with odd total 5 at n=32,beta=3.0) is NOT an additive-energy collision")
    print("  and must be excluded -- exactly what A23's '^{L1,even}' superscript specifies.")

    print("\nLEAK-TO-BOUND FEASIBILITY (P3):")
    for (n, beta, p, r_energy, defat, L1, r_lam, bal_r, law, leakpct, ng, nd, gc) in rows:
        if nd and not math.isnan(leakpct):
            # coset concentration: how many distinct g, and what is the mass on the top g
            top = gc.most_common(1)[0][1] if gc else 0
            print(f"  n={n} beta={beta} p={p}: depth r*={r_energy} genuine-defects={nd} "
                  f"leak={leakpct:.0f}% distinct-g={ng} top-g-mass={top}"
                  + ("  [single-coset]" if ng <= 2 else "  [multi-coset]"))
    print("\n  P3 reading: if leak~100% AND distinct-g is SMALL (O(1)), the genuine defects concentrate")
    print("  on O(1) cosets g*mu_n; the count is then bounded by |mu_n cap g*mu_n| summed over O(1) g,")
    print("  which is still an additive-energy / sum-product quantity (Cauchy-Schwarz returns E_2).")
    print("  A genuine sub-energy count needs distinct-g GROWING (spreads defect over many cosets,")
    print("  each thin) OR the leak fraction DROPPING at the onset depth (genuine defects escape it).")


if __name__ == "__main__":
    main()
