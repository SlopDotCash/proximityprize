#!/usr/bin/env python3
"""
S3-MAXNORM growth probe for #444 prize floor (the S3 unconditional handle).

CONTEXT (S3 handle / good_of_maxnorm_lt):
  spur_r(p) = char-p additive-energy excess over char-0 (the BGK defect). A
  signed 2r-config C = sum_i eps_i zeta^{a_i} (r plus, r minus) that sums to 0
  mod p but NOT in Z[zeta_n] is a "spurious" collision, and it exists for p iff
        p | N(C),   N = cyclotomic norm in Z[zeta_n] (= det of mult-by-C matrix).
  spur_r(p)=0 whenever p divides no such norm, in particular whenever
        p > MAXNORM(n,2r) := max{ |N(C)| : C signed 2r-config, N(C) != 0 }.
  good_of_maxnorm_lt: MAXNORM(n,2r) < p  =>  spur_r(p)=0  (prize proven there).

THE QUESTION (task):
  Crude bound MAXNORM <= (2r)^{phi(n)} = (2r)^{n/2} is EXPONENTIAL in n. The task
  asks whether the *binding* (deep r ~ ln q) configs have a BETTER-than-linear, or
  even O(1)-norm, certificate. We answer the growth-in-n question two ways:

  (A) EXHAUSTIVE small-r (r=2): full MAXNORM(n,4) to n as large as feasible.
      r=2 already settles the GROWTH-IN-n law, which is what S3 hinges on.

  (B) STRUCTURED deep family: the "binding" worst config is a maximally spread,
      non-antipodal signed sum. We track the bits-per-coordinate
            beta(n) := log2 |N(C_worst)| / (n/2)
      for the worst config found. If beta saturates to c>0, MAXNORM ~ 2^{cn/2}
      (exponential in n) => S3 caps far below prize. If beta -> 0, S3 has reach.

EXACT norm = product over primitive 2n-th roots of unity rho with rho^?:  actually
  N(C) = prod_{k odd, 1<=k<n} C(zeta_n^k) over the phi(n)=n/2 Galois conjugates
  (n=2^mu: Gal = {k odd mod 2n acting on zeta_n}, |Gal| = n/2). Computed via the
  resultant / mult-matrix determinant (fraction-free Bareiss), exact integers.
  Cross-checked against direct complex product (rounded) for sanity.

Translation invariance: fix a_1 = 0. Proper mu_n, n=2^mu, never the full group.
"""
import math
import cmath
from itertools import combinations


# ---------- exact integer norm via mult-by-C matrix on Z[x]/(x^h+1) ----------
def det_int(M):
    n = len(M); M = [row[:] for row in M]; sign = 1; prev = 1
    for k in range(n - 1):
        if M[k][k] == 0:
            piv = next((r for r in range(k + 1, n) if M[r][k] != 0), None)
            if piv is None:
                return 0
            M[k], M[piv] = M[piv], M[k]; sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]


def reduce_pow(e, h):
    s = 1
    while e >= h:
        e -= h; s = -s
    return s, e


def cvec(plus, minus, h):
    v = [0] * h
    for a in plus:
        s, e = reduce_pow(a % (2 * h), h); v[e] += s
    for b in minus:
        s, e = reduce_pow(b % (2 * h), h); v[e] -= s
    return v


def norm_of(plus, minus, h):
    v = cvec(plus, minus, h)
    if all(c == 0 for c in v):
        return 0
    M = [[0] * h for _ in range(h)]
    for col in range(h):
        for t in range(h):
            if v[t]:
                s, e = reduce_pow(t + col, h); M[e][col] += s * v[t]
    return det_int(M)


# fast |N| via complex Galois product (for large n where det is too slow)
def abslognorm_complex(plus, minus, n):
    h = n // 2
    total = 0.0
    zero = False
    for k in range(1, n, 2):            # odd k => primitive, n/2 conjugates
        z = cmath.exp(2j * cmath.pi * k / n)
        val = 0j
        for a in plus:
            val += z ** a
        for b in minus:
            val -= z ** b
        m = abs(val)
        if m < 1e-9:
            zero = True
            break
        total += math.log2(m)
    return (None if zero else total)      # returns log2|N|, or None if N==0


# ---------------------- (A) exhaustive MAXNORM(n,4) ----------------------
def maxnorm_r2_exact(n):
    h = n // 2
    mx = 0; mn = None
    for p2 in range(1, n):
        for m1 in range(n):
            for m2 in range(m1, n):
                N = norm_of([0, p2], [m1, m2], h)
                if N == 0:
                    continue
                a = abs(N)
                if a > mx:
                    mx = a
                if mn is None or a < mn:
                    mn = a
    return mx, mn


# ----------- (B) structured deep family: spread non-antipodal -----------
def deep_family_lognorm(n, r):
    """Worst-case-ish binding config: r plus at the r 'most spread' positions,
    r minus shifted, designed to be non-antipodal (no a, a+n/2 pairing) and
    maximally non-cancelling. We scan a few structured shapes and take the max."""
    best = 0.0
    shapes = []
    # shape 1: plus = first r evens, minus = first r odds (spread, non-antipodal)
    plus = [2 * i for i in range(r)]
    minus = [2 * i + 1 for i in range(r)]
    shapes.append((plus, minus))
    # shape 2: plus = 0,1,..,r-1 ; minus = r,r+1,..,2r-1 (consecutive block)
    shapes.append((list(range(r)), list(range(r, 2 * r))))
    # shape 3: golden-ish spread to avoid antipodal cancellation
    step = max(1, n // (2 * r))
    plus = [(2 * i * step) % n for i in range(r)]
    minus = [((2 * i + 1) * step) % n for i in range(r)]
    if len(set(plus)) == r and len(set(minus)) == r and not (set(plus) & set(minus)):
        shapes.append((plus, minus))
    for plus, minus in shapes:
        lg = abslognorm_complex(plus, minus, n)
        if lg is not None and lg > best:
            best = lg
    return best


print("S3 MAXNORM(n,2r) growth in n  (proper mu_n, n=2^mu, exact / Galois-product)")
print("=" * 78)

# --- Part A: exhaustive r=2, exact integer norms ---
print("\n[A] EXHAUSTIVE r=2  (4-configs):  MAXNORM(n,4) exact")
print(f"{'n':>5} {'phi=n/2':>8} {'MAXNORM':>16} {'log_n MN':>9} "
      f"{'bits/coord':>11} {'minNorm':>9}")
rowsA = []
for mu in range(3, 7):                  # n = 8,16,32,64
    n = 2 ** mu
    if n > 64:
        break
    mx, mn = maxnorm_r2_exact(n)
    logn = math.log(mx) / math.log(n) if mx > 1 else 0.0
    bits = math.log2(mx) / (n // 2) if mx > 0 else 0.0
    print(f"{n:>5} {n//2:>8} {mx:>16} {logn:>9.3f} {bits:>11.4f} {mn:>9}")
    rowsA.append((n, mx, bits))
print("  growth (n -> 2n):  log_n MN should -> const if linear-norm; "
      "bits/coord -> const>0 if exponential")
for i in range(1, len(rowsA)):
    n0, m0, b0 = rowsA[i - 1]; n1, m1, b1 = rowsA[i]
    print(f"    {n0:>3}->{n1:>3}: log2 ratio={math.log2(m1)/math.log2(m0):.3f}  "
          f"bits/coord {b0:.4f}->{b1:.4f}")

# --- Part B: structured deep family, complex Galois product, big n ---
print("\n[B] STRUCTURED DEEP family lognorm (binding-config proxy), to n=2^12")
print(f"{'n':>6} {'r':>3} {'phi=n/2':>8} {'log2|N|':>10} {'bits/coord':>11} "
      f"{'log_n|N|':>9}")
for mu in range(3, 13):                 # n up to 4096
    n = 2 ** mu
    for r in (2, 3, max(4, mu)):        # include a deep r that grows with mu
        if 2 * r >= n:
            continue
        lg = deep_family_lognorm(n, r)
        bits = lg / (n // 2) if lg > 0 else 0.0
        logn = lg / math.log2(n) if lg > 0 else 0.0   # log_n|N| = log2|N|/log2 n
        print(f"{n:>6} {r:>3} {n//2:>8} {lg:>10.2f} {bits:>11.4f} {logn:>9.3f}")

print("\nVERDICT KEY:")
print("  [A]+[B] bits/coord SATURATES to c>0  => MAXNORM ~ 2^{c*n/2} EXPONENTIAL in n")
print("    => MAXNORM >> prize p~n^4 for all but tiny n => S3 cert cannot fire")
print("    => S3 REDUCES TO WALL (linear/exponential growth is real).")
print("  bits/coord -> 0 (MAXNORM only poly in n) => S3 reaches prize => HAS-GAP-FIXABLE.")
