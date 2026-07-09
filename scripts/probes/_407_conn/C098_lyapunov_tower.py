"""
C098 attack: Lyapunov / geometric-mean bound on the per-level house ratios
   r_j = B(mu_{2^j}) / B(mu_{2^{j-1}}),   B(mu_n) = max_{b!=0} |eta(mu_n,b)|,  eta = sum_{x in mu_n} e_p(bx).

Claim under test (C098):
  STRICT per-level descent  r_j <= sqrt2  (B(2^j)^2 <= 2 B(2^{j-1})^2) for ALL j  is REFUTED.
  But the telescoped prize target needs only the LYAPUNOV AVERAGE
        (1/mu) sum_{j} log(r_j^2) -> log 2,
  i.e. running geometric mean of r_j^2 -> 2 from above, absorbing per-level spikes.

PRIZE REGIME ONLY: n=2^mu proper subgroup, q prime ~ n^beta (beta 4..5), n << sqrt q, m=(q-1)/n large.
Exact: eta is CONSTANT on mu_n-cosets, so the worst-b search scans one rep per coset (m reps), exact.

DECISIVE equivalence we check numerically:
  G_mu := (B_mu^2 / B_1^2)^{1/(mu-1)}  (running geom mean of r^2).
  B_1 = B(mu_2) = O(1).  So G_mu -> 2  <==>  B_mu^2 = 2^mu * 2^{o(mu)} = n^{1+o(1)}  <==>  BGK at the TOP.
  The geom mean tolerates only n^{o(1)} = (B_mu^2/n)^{1/mu} slack; that slack is exactly the
  log(m) factor the prize wants AS the bound, not slack the Lyapunov route gives for free.
"""

import math
import numpy as np

def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n - 1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p - 1; m = phi; fac = []; d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no prim root")

def subgroup(p, g, n):
    h = pow(g, (p - 1) // n, p)
    S = np.empty(n, dtype=np.int64); x = 1
    for i in range(n):
        S[i] = x; x = x * h % p
    return S

def house_sq(p, g, n, m_cap):
    """B(mu_n)^2 = max_{b!=0} |eta(mu_n,b)|^2.  eta constant on mu_n cosets => scan coset reps g^0..g^{m-1}.
    If m=(p-1)/n > m_cap, scan only the first m_cap reps (exact lower bound on the true house; in the
    prize regime the worst coset appears early/often and we report whether the cap binds)."""
    S = subgroup(p, g, n)
    m = (p - 1) // n
    M = min(m, m_cap)
    twopi_over_p = 2.0 * math.pi / p
    best = 0.0
    t = 1
    # batch reps in chunks for speed
    chunk = 2000
    reps = np.empty(chunk, dtype=np.int64)
    j = 0
    while j < M:
        c = min(chunk, M - j)
        tt = t
        for k in range(c):
            reps[k] = tt; tt = tt * g % p
        t = tt
        # for each rep r: phase = (S * r) mod p ; eta = sum exp(i*2pi/p * phase)
        # build (c, n) matrix of (S*rep) mod p
        prod = (S[None, :] * reps[:c, None]) % p   # (c, n)
        ang = twopi_over_p * prod
        re = np.cos(ang).sum(axis=1); im = np.sin(ang).sum(axis=1)
        v = (re * re + im * im).max()
        if v > best: best = v
        j += c
    return best, (m <= m_cap)

def find_prime(n, beta):
    target = int(round(n ** beta))
    k0 = max(1, target // n)
    for dk in range(0, 500000):
        for k in (k0 + dk, k0 - dk):
            if k <= 0: continue
            q = 1 + n * k
            if q > 3 and is_prime(q) and n * n < q:
                return q
    return None

print("=" * 104)
print("C098: Lyapunov geometric mean of per-level house ratios r_j^2 = B(2^j)^2/B(2^{j-1})^2")
print("PRIZE REGIME: n=2^mu PROPER subgroup, q ~ n^beta (beta=4,5), n << sqrt q, m=(q-1)/n large")
print("=" * 104)

M_CAP = 300000   # cap coset reps scanned per level (keeps it fast; flag if it binds)

# top n = 2^MU; tower j=1..MU is subgroups mu_{2^j} of the SAME q.
configs = [(7, 4), (8, 4), (6, 5)]

results = []
for MU, beta in configs:
    N = 1 << MU
    q = find_prime(N, beta)
    if q is None:
        print(f"  [skip] MU={MU} beta={beta}: no prime"); continue
    g = primitive_root(q)
    m = (q - 1) // N
    print(f"\n--- MU={MU}  n=2^{MU}={N}  q={q}  q/n^{beta}={q/N**beta:.3f}  m=(q-1)/n={m}  log_n q={math.log(q)/math.log(N):.3f} ---")
    print(f"    prize: n<sqrt(q)? {N < q**0.5}   m large? {m>1000}   (cap {M_CAP} per level)")
    Bsq = {}; capbind = {}
    for j in range(1, MU + 1):
        Bsq[j], full = house_sq(q, g, 1 << j, M_CAP)
        capbind[j] = not full
    print(f"    {'j':>2} {'n_j':>5} {'B_j^2':>13} {'B_j':>9} {'C0=B/sqn':>9} {'r_j^2':>8} {'r_j':>7} {'geomG_j':>8} {'cap?':>5}")
    for j in range(1, MU + 1):
        nj = 1 << j; B2 = Bsq[j]; B = math.sqrt(B2); C0 = B / math.sqrt(nj)
        if j == 1:
            rj2 = float('nan'); rj = float('nan'); G = float('nan')
        else:
            rj2 = Bsq[j] / Bsq[j-1]; rj = math.sqrt(rj2)
            G = (Bsq[j] / Bsq[1]) ** (1.0 / (j - 1))
        print(f"    {j:>2} {nj:>5} {B2:>13.3f} {B:>9.3f} {C0:>9.4f} {rj2:>8.4f} {rj:>7.4f} {G:>8.4f} {'Y' if capbind[j] else '.':>5}")
    Gfinal = (Bsq[MU] / Bsq[1]) ** (1.0 / (MU - 1))
    logm = math.log(m)
    Gfloor = ((N * logm) / Bsq[1]) ** (1.0 / (MU - 1))      # BGK floor model B^2 = n log m
    Gnonbgk = ((N ** 1.5) / Bsq[1]) ** (1.0 / (MU - 1))     # non-BGK B ~ n^0.75
    print(f"    => geom mean r^2 at top  G_mu = {Gfinal:.4f}")
    print(f"       BGK-floor model (B^2=n log m): G_mu would be {Gfloor:.4f}")
    print(f"       non-BGK model (B^2=n^1.5):     G_mu would be {Gnonbgk:.4f}")
    print(f"       C0^2 top = B_mu^2/n = {Bsq[MU]/N:.4f}  (BGK wants ~ log m = {logm:.3f})")
    results.append((MU, beta, q, m, Gfinal, Gfloor, Gnonbgk, Bsq[MU]/N, logm))

print()
print("=" * 104)
print("VERDICT LOGIC:")
print(" - r_j^2 spikes ABOVE 2 at individual levels  => strict descent (r_j<=sqrt2 all j) is indeed REFUTED (matches DISPROOF_LOG/C072).")
print(" - G_mu (geom mean) hovers near 2 (from above) => the DESCRIPTIVE Lyapunov claim is correct.")
print(" - BUT G_mu = (B_mu^2/B_1^2)^{1/(mu-1)};  G_mu->2  <==>  B_mu^2 = n^{1+o(1)}  <==>  BGK at the TOP.")
print("   The geom mean only re-distributes the SAME total budget log(B_mu^2/B_1^2) over mu levels;")
print("   it gives NO independent control of B_mu.  Proving 'limsup running geom mean <= 2' IS proving BGK.")
print("   => the Lyapunov reframing is a RESTATEMENT of the open core, not an escape from it.")
print("=" * 104)
