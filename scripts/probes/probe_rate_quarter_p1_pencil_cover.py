#!/usr/bin/env python3
"""Pencil-cover statistics for extremal stall families (residual (c)).

Every pair of bad scalars rides its divided-difference pencil (cover EXISTENCE);
distinct pencils share <= 1 rider, so pencils partition the ordered pairs:
    B(B-1) = Sum_pi m_pi (m_pi - 1),   m_pi <= c := N - T + 1.
Pigeonhole: a pair-cover by P pencils forces B^2 <= P c^2; at P = 4 this gives
B <= 2c = 961893718 <= N at prize scale (the margin-free 4-pencil budget).

This probe measures the pair-pencil distribution of the census's extremal
family (dual two-pencil at mu_256/q=1031, B = 230 = 2c') and verifies the
partition identity and the trade-off exactly.
"""

import numpy as np
from collections import Counter

q, N, T, k = 1031, 256, 142, 64
c_cap = N - T + 1  # 115


def modinv(a):
    return pow(int(a) % q, q - 2, q)


dom = list(range(N))
V = np.array([[pow(x, j, q) for j in range(k)] for x in dom], dtype=np.int64)
rng = np.random.default_rng(424242)
ov = list(range(N - (T - 1), T - 1))
deg_c = k - 2 - len(ov)
cvec = rng.integers(0, q, deg_c + 1)
cvec[-1] = max(1, int(cvec[-1]))
d = np.zeros(N, dtype=np.int64)
for i in range(N):
    zv = 1
    for r in ov:
        zv = zv * (i - r) % q
    cv = 0
    for cc in reversed(cvec):
        cv = (cv * i + int(cc)) % q
    d[i] = zv * cv % q
assert all(d[i] != 0 for i in range(N) if i not in ov)
v01 = (V @ rng.integers(0, q, k)) % q
v11 = (V @ rng.integers(0, q, k)) % q
xd = (np.arange(N) * d) % q
v02, v12 = (v01 + xd) % q, (v11 + d) % q
A1 = list(range(0, T - 1))
A2 = list(range(N - (T - 1), N))
u0, u1 = np.zeros(N, dtype=np.int64), np.zeros(N, dtype=np.int64)
for i in A1:
    u0[i], u1[i] = v01[i], v11[i]
for i in A2:
    if i >= T - 1:
        u0[i], u1[i] = v02[i], v12[i]

# bad scalars + witnesses (as in the census dual construction)
bad = {}  # gamma -> pf evaluation vector
for (v0, v1) in ((v01, v11), (v02, v12)):
    a = (u0 - v0) % q
    b = (u1 - v1) % q
    base = int(((a == 0) & (b == 0)).sum())
    for i in np.where(b != 0)[0]:
        g = (-int(a[i]) * modinv(b[i])) % q
        if base + 1 >= T and g not in bad:
            bad[g] = (v0 + g * v1) % q
B = len(bad)
print(f"extremal dual family: B = {B} (= 2c' = {2 * c_cap}), budget N = {N}")

# pair-pencil fingerprints: dir = (pf' - pf)/(g' - g); base = pf - g*dir
gs = sorted(bad)
pencil_of_pair = {}
for i1 in range(B):
    for i2 in range(i1 + 1, B):
        g1, g2 = gs[i1], gs[i2]
        inv = modinv(g2 - g1)
        dirv = tuple(int((int(bad[g2][t]) - int(bad[g1][t])) * inv % q)
                     for t in range(0, N, 16))
        basev = tuple(int((int(bad[g1][t]) - g1 * dirv[ti]) % q)
                      for ti, t in enumerate(range(0, N, 16)))
        pencil_of_pair[(g1, g2)] = (dirv, basev)
cnt = Counter(pencil_of_pair.values())
m = Counter()
for pencil, npairs in cnt.items():
    # m_pi from pair count: npairs = C(m,2)
    mm = int((1 + (1 + 8 * npairs) ** 0.5) / 2 + 0.5)
    assert mm * (mm - 1) // 2 == npairs
    m[mm] += 1
print(f"distinct pair-pencils: {len(cnt)}")
print(f"rider-multiplicity distribution (m: #pencils): {dict(sorted(m.items()))}")
tot = sum(mm * (mm - 1) * count for mm, count in m.items())
print(f"partition identity Sum m(m-1) = {tot} vs B(B-1) = {B * (B - 1)}:"
      f" {tot == B * (B - 1)}")
mx = max(m)
print(f"max riders on one pencil = {mx} <= c' = {c_cap}: {mx <= c_cap}")
P4 = 4
print(f"pigeonhole: pair-cover by {P4} pencils forces B^2 <= 4c'^2 ->"
      f" B <= {2 * c_cap}; this family needs {len(cnt)} pencils (>> 4),"
      f" so the 4-cover theorem does not apply to it — and indeed B = 2c'.")
c = 480946859
print(f"prize constants: c = N-T+1 = {c}; 2c = {2 * c} <= N = {2**30}:"
      f" {2 * c <= 2**30};  5c^2 vs (N+1)^2: 5c^2 = {5 * c * c},"
      f" (N+1)^2 = {(2**30 + 1)**2} -> 5-cover would allow B ~ sqrt5*c ="
      f" {int(5**0.5 * c)} > N: pigeonhole route caps at 4 pencils")
print(f"pair-pencil aligned floor: 2T - N = {2 * T - N} (scaled),"
      f" prize: {2 * 592794966 - 2**30}")
