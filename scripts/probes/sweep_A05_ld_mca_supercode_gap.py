#!/usr/bin/env python3
"""
sweep_A05_ld_mca_supercode_gap.py   (#407 sweep A05, 2026-06-14)

A05 deliverable: the LD/MCA gap probe attached to the super-code list bridge
(`SuperCodeListBridge.explainableScalars_card_le_superList`).

WHAT THE BRIDGE SAYS (in-tree, axiom-clean):
  For any linear code C and far direction u1 not in C, the far-line incidence
      I(u0,u1; delta) = #{ gamma : the line u0 + gamma*u1 (1-delta)n-agrees with some c in C }
  is bounded by the radius-(delta n) agreement list of the ONE-DIMENSION-LARGER super-code
      C+ := C (+) <u1>:
      I(u0,u1; delta)  <=  |list(C+, u0, delta n)|        (the injection gamma |-> c_gamma - gamma*u1).
  For RS[k] on mu_n the dilation symmetry pins the worst u1 to the monomial X^k, so
      C+ = RS[k] (+) <X^k> = RS[k+1].
  Hence the GRAND MCA CHALLENGE (bound I) reduces to the LIST-DECODING grand challenge of RS[k+1].

WHAT THIS PROBE MEASURES (exact arithmetic over F_q, no sampling on the codeword side):
  Prize-shaped instance: n = 16 = 2^4 (mu = 4),  q = 65537 (prime, q = 1 mod 16, q ~ n^4 so a=log_n q = 4),
  rate rho = 1/4 -> k = 4, super-code RS[k+1] = RS[5] (degree < 5).
  Two thresholds on the SAME super-code, as functions of the agreement parameter a = (1-delta)n:

   (LD side)  delta*_LD  -- the largest delta whose Johnson list cap is still a *constant* (= 1, i.e.
              unique decoding), i.e. the classical guaranteed-correct list-decoding radius of RS[k+1].
              n^2 / (a^2 - n*b) with b = n-d = (k+1)-1 = k.  Singleton at the Johnson radius.

   (MCA side) delta*_MCA -- the largest delta at which the worst far-line incidence I(delta) still
              fits the prize budget  I(delta) <= q * eps*.  Because eps* = 2^-128 << 1/q here, the
              honest finite-q surrogate budget is  I(delta) <= 1  (the strictest possible: NO bad
              scalar may exceed unique decoding of the LINE).  We compute I(delta) EXACTLY by
              enumerating every codeword of RS[k] (q^k of them is too many; we instead enumerate the
              super-code RS[k+1] decoding list of u0 and read off the gamma via the bridge injection,
              which is EXACT and equals I on the far stratum).

  The GAP is delta*_MCA vs delta*_LD measured as the ratio of *list sizes / incidences at the LD
  radius*: at the Johnson (unique-decoding) radius of the super-code the LD side guarantees list = 1,
  but the actual far-line incidence I there is much larger -- BEYOND-Johnson list size of RS[k+1].
  The headline number is  max_a  I_actual(a) / Johnson_cap(a)  at the prize agreement level,
  and the threshold gap  a_LD - a_MCA  (in agreement coordinates) / equivalently delta*_MCA - delta*_LD.

  Everything is EXACT: codewords of RS[k+1] decoding u0 are found by exhaustive (k+1)-subset
  interpolation of u0's coordinates (Lagrange), which is the standard exact list enumerator and is
  feasible for n=16,k+1=5  (C(16,5)=4368 interpolations per word).

This is EVIDENCE (a numeric gap measurement), never a substitute for proof.  Honesty: the bridge
inequality itself is the proven object; this probe only quantifies how far LD (Johnson) sits below
the true MCA incidence, i.e. why a NON-Johnson list bound is required.
"""
from itertools import combinations
from collections import defaultdict
from math import comb
import sys

# ---------- field utilities (prime field F_q) ----------
def inv(x, q): return pow(x % q, q - 2, q)

def order_n_element(q, n):
    assert (q - 1) % n == 0, f"need n | q-1: n={n} q={q}"
    # find a generator g of F_q^* then h = g^((q-1)/n) has order n
    # cheap: try small g, check it has order n exactly
    cof = (q - 1) // n
    for g in range(2, q):
        h = pow(g, cof, q)
        if h == 1:
            continue
        if all(pow(h, d, q) != 1 for d in range(1, n)):
            return h
    raise RuntimeError("no order-n element")

def mu_n(q, n):
    h = order_n_element(q, n)
    return [pow(h, i, q) for i in range(n)]

# ---------- RS evaluation ----------
def poly_eval(coeffs, x, q):
    # coeffs low->high; Horner
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % q
    return acc

def lagrange_through(points_x, points_y, q):
    """Exact polynomial (coeff list, low->high) through the given points (<= deg len-1).
    Returns coeffs of length len(points_x)."""
    m = len(points_x)
    # Newton / direct Lagrange in coefficient form
    coeffs = [0] * m
    for i in range(m):
        # basis poly L_i(x) = prod_{j!=i} (x - x_j)/(x_i - x_j)
        num = [1]  # poly = 1
        denom = 1
        for j in range(m):
            if j == i:
                continue
            # multiply num by (x - x_j)
            new = [0] * (len(num) + 1)
            for d, c in enumerate(num):
                new[d] = (new[d] - c * points_x[j]) % q
                new[d + 1] = (new[d + 1] + c) % q
            num = new
            denom = (denom * (points_x[i] - points_x[j])) % q
        scale = (points_y[i] * inv(denom, q)) % q
        for d, c in enumerate(num):
            coeffs[d] = (coeffs[d] + c * scale) % q
    return coeffs

def agreement_count(coeffs, D, word, q):
    return sum(1 for i in range(len(D)) if poly_eval(coeffs, D[i], q) == word[i])

# ---------- exact FULL list of RS[deg<m] decoding `word`, bucketed by agreement ----------
def rs_full_list(D, word, m, q):
    """ALL distinct codewords (coeff tuple len m) of RS[deg<m] agreeing with `word` on >= m points,
    each with its agreement count.  Exact via the standard subset-interpolation enumerator:
    every codeword agreeing on >= m points is the unique interpolation of SOME m of its agreement
    positions, so interpolating every m-subset and deduping finds them all.  C(n,m) interpolations.
    Returns dict coeff-tuple -> agreement."""
    n = len(D)
    found = {}
    for sub in combinations(range(n), m):
        xs = [D[i] for i in sub]
        ys = [word[i] for i in sub]
        coeffs = tuple(lagrange_through(xs, ys, q))
        if coeffs in found:
            continue
        found[coeffs] = agreement_count(coeffs, D, word, q)
    return found  # dict coeff-tuple -> agreement (>= m for all entries)

# ---------- the far-line incidence I(u0,u1;a) via the bridge, ALL agreements at once ----------
def far_line_incidence_curve(D, u0, k, q, a_values):
    """For u1 = X^k (monomial direction), compute the full RS[<k+1] super-list of u0 ONCE, then for
    each agreement threshold a return (I(a), |superlist(a)|).
    I(a) = #distinct gammas = -(degree-k coeff) over super-codewords with agreement >= a, EXACT and
    equal to the far-line incidence on the far stratum (FarCosetExplosion: every explainable scalar
    is bad).  The bridge gamma read-off uses that RS[<k] has no X^k term, so the degree-k coeff of
    the super-codeword e = c_gamma + gamma*X^k is exactly gamma (= -coeff under the c-gamma*u1 form)."""
    full = rs_full_list(D, u0, k + 1, q)   # RS[deg < k+1] = RS[k+1], coeff len k+1
    out = {}
    for a in a_values:
        gammas = set()
        nsl = 0
        for coeffs, ac in full.items():
            if ac >= a:
                nsl += 1
                gammas.add(coeffs[k])   # degree-k coefficient = the recovered direction scalar
        out[a] = (len(gammas), nsl)
    return out

# ---------- Johnson list cap of the super-code ----------
def johnson_cap(n, d, a):
    """L <= n^2 / (a^2 - n*(n-d)) when a^2 > n*(n-d) (Johnson gap); else +inf (no guarantee)."""
    b = n - d
    denom = a * a - n * b
    if denom <= 0:
        return float('inf')
    return (n * n) / denom

def johnson_unique_radius(n, d):
    """Smallest agreement a giving Johnson unique decoding L<=1 (a^2 - n b >= n^2 => guaranteed 1).
    Returns the integer agreement a_LD where the Johnson cap is < 2 (i.e. forces singleton)."""
    b = n - d
    a = 1
    while a <= n:
        denom = a * a - n * b
        if denom > 0 and (n * n) / denom < 2:
            return a
        a += 1
    return n

# ============================================================================
def run_instance(q, n, k, label):
    print(f"\n{'='*78}")
    print(f"INSTANCE {label}:  n={n} (mu={n.bit_length()-1}), q={q}, k={k}  "
          f"(rho={k}/{n}={k/n:.4f}, a=log_n q ~ {round((q.bit_length()-1)/(n.bit_length()-1),2)})")
    print(f"  super-code C+ = RS[k+1] = RS[{k+1}], far direction u1 = X^k = X^{k}")
    D = mu_n(q, n)
    # super-code RS[k+1]: degree < k+1, distance d_super = n - (k+1) + 1 = n - k
    d_super = n - (k + 1) + 1
    a_LD = johnson_unique_radius(n, d_super)
    print(f"  RS[k+1] distance d = n-(k+1)+1 = {d_super};  Johnson unique-decoding agreement a_LD = {a_LD}"
          f"  (delta*_LD = 1 - a_LD/n = {1 - a_LD/n:.4f})")

    # far u0: pick a worst-shaped offset.  Use a high monomial NOT in RS[k+1] to make u0 generic-far,
    # and u1 = X^k exactly so the bridge gamma-readoff is valid.
    # We will SCAN u0 over monomials X^e for e in [k+1 .. n-1] (the dilation-fundamental far family)
    # and take the worst (max incidence) per agreement -- the structural worst-over-directions.
    e_candidates = list(range(k + 1, n))
    a_values = list(range(3, n))
    print(f"\n  scanning far offsets u0 = X^e for e in {e_candidates}")
    # one super-list per direction; bucket by agreement
    per_dir = {}
    for e in e_candidates:
        u0 = [pow(x, e, q) for x in D]
        per_dir[e] = far_line_incidence_curve(D, u0, k, q, a_values)
    print(f"  {'a':>3} {'delta':>7} {'I_worst':>8} {'|superL|':>9} {'JohnsonCap':>11} "
          f"{'I/Cap':>8} {'arg e':>6} {'regime':>13}")
    rows = []
    for a in a_values:
        best_I, best_sl, best_e = 0, 0, None
        for e in e_candidates:
            I, sl = per_dir[e][a]
            if I > best_I:
                best_I, best_sl, best_e = I, sl, e
        cap = johnson_cap(n, d_super, a)
        delta = 1 - a / n
        # Johnson regime for the SUPER-code list-decoding:
        regime = "Johnson-LD" if a >= a_LD else "beyond-Johnson"
        ratio = (best_I / cap) if cap != float('inf') and cap > 0 else float('inf')
        rows.append((a, delta, best_I, best_sl, cap, ratio, best_e, regime))
        cap_s = f"{cap:.2f}" if cap != float('inf') else "inf"
        ratio_s = f"{ratio:.2f}" if ratio != float('inf') else "inf"
        print(f"  {a:>3} {delta:>7.3f} {best_I:>8} {best_sl:>9} {cap_s:>11} "
              f"{ratio_s:>8} {str(best_e):>6} {regime:>13}")
    return rows, a_LD, d_super

def report_gap(rows, a_LD, n, k, label):
    rows = sorted(rows)
    rho = k / n
    # prize window interior: delta in (1 - sqrt(rho), 1 - rho - small).  Use the closed endpoints.
    import math
    win_lo, win_hi = 1 - math.sqrt(rho), 1 - rho   # (Johnson, capacity); interior is strictly between
    # MCA threshold a_MCA = smallest agreement a (i.e. largest delta) with worst incidence I <= 1.
    a_MCA = next((a for (a, d, I, sl, cap, r, e, reg) in rows if I <= 1), None)
    delta_LD = 1 - a_LD / n
    delta_MCA = (1 - a_MCA / n) if a_MCA is not None else None
    print(f"\n  --- GAP VERDICT for {label} ---")
    print(f"    prize window interior: delta in ({win_lo:.3f}, {win_hi:.3f})  "
          f"= agreement a in ({n*rho:.1f}, {n*math.sqrt(rho):.1f}) [exclusive]")
    print(f"    delta*_LD  (Johnson unique-decoding radius of RS[k+1], a_LD={a_LD}) = {delta_LD:.4f}")
    if delta_MCA is not None:
        print(f"    delta*_MCA (radius where worst far-line incidence I drops to <=1, a_MCA={a_MCA}) "
              f"= {delta_MCA:.4f}")
        print(f"    THRESHOLD GAP: delta*_MCA - delta*_LD = {delta_MCA - delta_LD:+.4f}  "
              f"(={a_LD - a_MCA} agreement levels)")
    # The HONEST headline: in the prize window every Johnson list cap is VACUOUS (radius beyond the
    # Johnson radius), so the LD guarantee is "no bound" while the true far-line incidence is a
    # concrete super-linear number.  Report the in-window incidences and the largest finite-Johnson
    # ratio (the smallest-radius point where Johnson is still finite but already exceeded).
    in_window = [(a, d, I, sl, cap) for (a, d, I, sl, cap, r, e, reg) in rows
                 if win_lo < d < win_hi and I > 0]
    if in_window:
        print(f"    IN-WINDOW far-line incidences (Johnson cap = {'inf=vacuous' if all(c==float('inf') for *_,c in in_window) else 'see col'}):")
        for (a, d, I, sl, cap) in in_window:
            cap_s = "inf (vacuous)" if cap == float('inf') else f"{cap:.2f}"
            print(f"        a={a} delta={d:.3f}:  I={I}  super-list={sl}  Johnson-cap={cap_s}")
        Iw = max(I for (a, d, I, sl, cap) in in_window)
        print(f"      => peak IN-WINDOW far-line incidence = {Iw} (super-linear in n={n}: {Iw/n:.1f}*n), "
              f"vs the Johnson/LD guarantee = VACUOUS in-window.")
    # Largest finite-Johnson exceedance ratio (the ">24x"-style number where the comparison is fair).
    best_ratio = 0.0; best_at = None
    for (a, d, I, sl, cap, r, e, reg) in rows:
        if cap != float('inf') and cap > 0 and I > cap:
            ratio = I / cap
            if ratio > best_ratio:
                best_ratio = ratio; best_at = (a, d, I, cap)
    if best_at is not None:
        a, d, I, cap = best_at
        print(f"    LIST-SIZE EXCEEDANCE (finite-Johnson radius): at a={a} (delta={d:.3f}) "
              f"I={I} > Johnson cap {cap:.2f} by {best_ratio:.1f}x.")
    else:
        print(f"    LIST-SIZE EXCEEDANCE: at every radius where Johnson is FINITE the incidence has "
              f"already dropped to 0 -- i.e. the entire nonzero-incidence region is BEYOND Johnson "
              f"(Johnson is vacuous exactly where the MCA action is).")
    maxI = max((I for (a, d, I, sl, cap, r, e, reg) in rows), default=0)
    maxsl = max((sl for (a, d, I, sl, cap, r, e, reg) in rows), default=0)
    print(f"    (context) peak far-line incidence I_max = {maxI}, peak super-list |L|_max = {maxsl}")

if __name__ == "__main__":
    # PRIZE-SHAPED instance: mu_16, a=log_n q = 4  (q = 65537 = 2^16+1, q-1 = 2^16 so 16 | q-1; q ~ 16^4)
    rows, a_LD, d_super = run_instance(65537, 16, 4, "mu_16, rho=1/4, a=4 (PRIZE-SHAPED)")
    report_gap(rows, a_LD, 16, 4, "mu_16, rho=1/4, a=4")

    # cross-check rate 1/2 same domain
    rows2, a_LD2, _ = run_instance(65537, 16, 8, "mu_16, rho=1/2, a=4")
    report_gap(rows2, a_LD2, 16, 8, "mu_16, rho=1/2")

    # smaller domain sanity (mu_8) for q-independence cross-check
    rows3, a_LD3, _ = run_instance(65537, 8, 2, "mu_8, rho=1/4, a~5.3")
    report_gap(rows3, a_LD3, 8, 2, "mu_8, rho=1/4")

    print("\nNOTE: I is computed EXACTLY via the bridge (RS[k+1] list of u0, gamma read off the")
    print("degree-k coeff).  The bridge inequality I <= |superlist| is the PROVEN object")
    print("(SuperCodeListBridge.explainableScalars_card_le_superList).  This probe only quantifies")
    print("how far the Johnson (LD) guarantee sits below the true MCA incidence on the prize instance.")
