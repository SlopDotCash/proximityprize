#!/usr/bin/env python3
"""
G260: Origin-anchor gauge no-go for the #466 CORE frontier.

Self-contained, exact integer arithmetic, no FFT, no /tmp dependency.

Frontier after G258/G259: the only surviving prize face is the fixed-row weighted
covariance  C_r(W) = m * <W, R_r> - (sum W)(sum R_r)  at r = 5, 6, where W is the
sponsor weighted-relation quotient profile on Z/m and R_r is the rank-r indicator row.

G259 (Fable) showed the full bispectrum / all degree-k moments are translation invariant,
and a cyclic shift of the quotient origin reverses both covariances. Fable's Rank-1 open
target was: does a W-INTRINSIC, sponsor-uniform ORIGIN ANCHOR exist that recovers absolute
placement independent of R_r?

G260 answers NO, structurally. The quotient origin is a GAUGE. Every origin marker M
computable from W alone is translation-covariant and falls into exactly one class:

  (INV)  invariant:     M(shift(W,c)) = M(W)        (autocorrelation values, |DFT|,
                        value multiset, any degree-k moment). Gives identity and a
                        sign-reversing shift the SAME value; cannot separate them.
  (EQ)   equivariant:   M(shift(W,c)) = M(W) + c     (argmax of a unique extremum, any
                        "pick a distinguished residue" rule; DFT phases advance linearly).
                        "Align M to 0" is a GAUGE FIXING: it maps every member of the shift
                        orbit to ONE canonical profile, so it cannot tell R_r which
                        physical origin to use.

Because the target covariance is shift-NON-invariant (and sign-reversing shifts are
abundant and persistent as support thins to prize scale), neither class pins the sign.

This script:
  (1) exhibits the exact small Z/7 witness kernel-checked in the Lean companion;
  (2) verifies universally (exhaustive over the shift orbit) that the argmax gauge
      collapses the whole orbit to one canonical form;
  (3) shows sign-reversing shifts persist at ~25% of shifts as support/m -> 0.03.

The rank weight is the standard structural surrogate used across G245-G259 (not the literal
G245 Newton coefficient). The tested property -- gauge covariance of every W-marker vs
shift-non-invariance of the target -- is structural and stable across the surrogate, per lane
convention. It is a route no-go, not a Jacobi covariance estimate and not a prize closure.
"""

def cov(W, R, m):
    s = m * sum(w * r for w, r in zip(W, R)) - sum(W) * sum(R)
    return s

def roll(W, c):
    m = len(W)
    return [W[(i - c) % m] for i in range(m)]

def unique_argmax(W):
    mx = max(W)
    if W.count(mx) != 1:
        return None
    return W.index(mx)

def sign(x):
    return (x > 0) - (x < 0)

print("=== G260 ORIGIN-ANCHOR GAUGE NO-GO (exact integer) ===\n")

# (1) exact Z/7 witness (matches the Lean file)
m = 7
W = [2, 0, 1, 1, 1, 1, 0]
R = [0, 0, 0, 1, 1, 1, 0]
c = 2
Wc = roll(W, c)
base = cov(W, R, m)
cc = cov(Wc, R, m)
a = unique_argmax(W)
ac = unique_argmax(Wc)
print("(1) exact Z/7 witness (Lean companion):")
print(f"    W        = {W}   argmax = {a}")
print(f"    shift W c = {Wc}   argmax = {ac} = ({a}+{c}) mod {m} = {(a + c) % m}")
print(f"    R        = {R}")
print(f"    C(W,R)        = {m}*{sum(w*r for w,r in zip(W,R))} - {sum(W)}*{sum(R)} = {base}  (> 0)")
print(f"    C(shift W c,R)= {m}*{sum(w*r for w,r in zip(Wc,R))} - {sum(W)}*{sum(R)} = {cc}  (< 0)")
canon0 = roll(W, -a)
canonC = roll(Wc, -ac)
print(f"    gauge canonical roll(W,-a)      = {canon0}")
print(f"    gauge canonical roll(shiftWc,-ac)= {canonC}")
assert base > 0 and cc < 0, "witness must sign-reverse"
assert canon0 == canonC, "gauge canonical forms must coincide"
assert ac == (a + c) % m, "argmax must be equivariant"
print("    OK: sign reversal + argmax equivariance + identical gauge-canonical form.\n")

# (2) universal gauge collapse: whole shift orbit -> one canonical form
import random
rng = random.Random(7)
collapse_ok = True
checked = 0
for _ in range(4000):
    mm = rng.randint(5, 40)
    Wr = [rng.randint(0, 4) for _ in range(mm)]
    if Wr.count(max(Wr)) != 1:
        continue
    aa = unique_argmax(Wr)
    canon = roll(Wr, -aa)
    for cc2 in range(mm):
        Wcc = roll(Wr, cc2)
        acc = unique_argmax(Wcc)
        if acc != (aa + cc2) % mm or roll(Wcc, -acc) != canon:
            collapse_ok = False
            break
    checked += 1
    if not collapse_ok:
        break
print(f"(2) universal argmax-gauge collapse over shift orbit "
      f"({checked} random profiles, all shifts): {collapse_ok}\n")

# (3) persistence of simultaneous sign-reversing shifts as support/m -> 0
print("(3) simultaneous (r5&r6) sign-reversing shift persistence as support thins:")
for (mm, supp) in [(101, 50), (211, 64), (401, 64), (809, 80), (1601, 96), (3203, 100)]:
    rng2 = random.Random(supp + mm)
    idx = rng2.sample(range(mm), supp)
    Wp = [0] * mm
    for i in idx:
        Wp[i] = rng2.randint(1, 3)

    def row(seed):
        rr = [0] * mm
        rloc = random.Random(seed + mm)
        for i in rloc.sample(range(mm), mm // 3):
            rr[i] = 1
        return rr

    R5 = row(5)
    R6 = row(6)
    b5 = cov(Wp, R5, mm)
    b6 = cov(Wp, R6, mm)
    both = 0
    for cc3 in range(1, mm):
        Wr = roll(Wp, cc3)
        v5 = cov(Wr, R5, mm)
        v6 = cov(Wr, R6, mm)
        if (b5 and sign(v5) != sign(b5) and v5) and (b6 and sign(v6) != sign(b6) and v6):
            both += 1
    print(f"    m={mm:5d} supp/m={supp/mm:.3f}: simultaneous reversing shifts = {both:4d} "
          f"({100.0*both/(mm-1):.1f}% of nontrivial shifts)")

print("\nVERDICT: the quotient origin is a gauge; every W-intrinsic marker is invariant or")
print("equivariant and cannot select the physical origin R_r uses. No origin anchor pins the")
print("covariance sign. The missing datum is ABSOLUTE row placement = the original joint")
print("sponsor-prime BGK/Paley covariance. CORE OPEN / ON-BGK.")
