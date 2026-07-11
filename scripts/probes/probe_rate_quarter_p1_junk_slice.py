#!/usr/bin/env python3
"""Junk-slice ledger: does the fiber-Chebyshev constraint improve the
five-pencil master budget?  Exact decomposition + calibration.

Composition audit: a rider of a margined pencil needs >= b = T - A votes,
split into (foreign-region votes: <= k-1 per region, quadratically constrained
across riders) + (junk votes: globally disjoint).  The constraint can lower a
rider cap only when the demand b exceeds the total foreign fiber capacity:
  * five-cover geometry: 4 foreign regions -> capacity 4(k-1) = 1073741820 > T:
    NEVER forcing (any sub-T demand fits in fiber caps alone);
  * two-capacity-region geometry: capacity 2(k-1) = 536870910; forcing needs
    b > 2(k-1) i.e. A < T - 2(k-1) = 55924056 — but pair-pencils always have
    A >= 2T - N = 111848108: the crossover range is EMPTY for pair-pencil
    families.  The master's margin demand (13) is 7 orders below the cap.
VERDICT: the composition does NOT improve the master ledger; its real content
is the decomposition theorem + the empty-crossover calibration.

Probe: measure own/foreign/junk vote splits for the census dual family's
extremal riders at mu_256 (expect 1 foreign vote, 0 junk — quadratic
constraint non-binding in practice, matching the calibration).
"""

import numpy as np

q, Nn, T, k = 1031, 256, 142, 64
dom = list(range(Nn))
V = np.array([[pow(x, j, q) for j in range(k)] for x in dom], dtype=np.int64)
rng = np.random.default_rng(424242)


def modinv(a):
    return pow(int(a) % q, q - 2, q)


# dual two-pencil construction (as in the census)
ov = list(range(Nn - (T - 1), T - 1))
dc = rng.integers(0, q, k - 2 - len(ov))
dc[-1] = max(1, int(dc[-1]))
d = np.zeros(Nn, dtype=np.int64)
for i in range(Nn):
    zv = 1
    for r in ov:
        zv = zv * (i - r) % q
    cv = 0
    for cc in reversed(dc):
        cv = (cv * i + int(cc)) % q
    d[i] = zv * cv % q
v01 = (V @ rng.integers(0, q, k)) % q
v11 = (V @ rng.integers(0, q, k)) % q
xd = (np.arange(Nn) * d) % q
v02, v12 = (v01 + xd) % q, (v11 + d) % q
A1 = set(range(0, T - 1))
A2 = set(range(Nn - (T - 1), Nn))
u0, u1 = np.zeros(Nn, dtype=np.int64), np.zeros(Nn, dtype=np.int64)
for i in range(Nn):
    if i in A1:
        u0[i], u1[i] = v01[i], v11[i]
    elif i in A2:
        u0[i], u1[i] = v02[i], v12[i]
junk = [i for i in range(Nn) if i not in A1 and i not in A2]

print("=" * 78)
print("Vote-location split for the extremal dual family's riders (mu_256)")
print("=" * 78)
splits = {"foreign": 0, "junk": 0, "riders": 0}
for (vv0, vv1, own, other) in ((v01, v11, A1, A2), (v02, v12, A2, A1)):
    a = (u0 - vv0) % q
    b = (u1 - vv1) % q
    for i in range(Nn):
        if b[i] != 0 and i not in own:
            g = (-int(a[i]) * modinv(b[i])) % q
            # this coordinate hosts rider g's vote for this pencil
            agr = sum(1 for y in range(Nn)
                      if (vv0[y] + g * vv1[y]) % q == (u0[y] + g * u1[y]) % q)
            if agr >= T:
                splits["riders"] += 1
                if i in other:
                    splits["foreign"] += 1
                else:
                    splits["junk"] += 1
print(f"  riders (vote-coords with agreement >= T): {splits['riders']};"
      f" foreign-region votes: {splits['foreign']}; junk votes:"
      f" {splits['junk']}")
print(f"  per-rider foreign votes = 1 << k-1 = {k-1}: the quadratic constraint")
print("  is FAR from binding on extremal families (matches the calibration).")

print("\n" + "=" * 78)
print("Calibration at prize constants (exact)")
print("=" * 78)
N, Tp, kp = 2**30, 592794966, 2**28
print(f"  four foreign regions: 4(k-1) = {4*(kp-1)} >= T = {Tp}:"
      f" {4*(kp-1) >= Tp}  -> five-cover fiber capacity hosts ANY sub-T demand")
print(f"  two-region crossover: T - 2(k-1) = {Tp - 2*(kp-1)} <"
      f" pair floor 2T-N = {2*Tp - N}: {Tp - 2*(kp-1) < 2*Tp - N}"
      f"  -> crossover range EMPTY for pair-pencil families")
print(f"  master margin demand 13 vs fiber cap k-1 = {kp-1}: ratio"
      f" {13/(kp-1):.2e}  -> the margin-13 caps CANNOT be improved this way")
print("  VERDICT: no improvement to the five-pencil master ledger; the")
print("  composition's honest content = the vote-decomposition theorem +")
print("  junk-forced rider count (binding only above 2(k-1) demand, an empty")
print("  range for pair-pencil-generated families) + these calibrations.")
