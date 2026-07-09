#!/usr/bin/env python3
"""_wf_Ek-randomlike_0.py  (#407 prize — Ek-randomlike, replicate 1/2, INDEPENDENT method)

QUESTION (settle it):
  Is the 2r-th additive energy E_r(mu_n) RANDOM-LIKE in the prize CONSTANT-INDEX regime?
  i.e. does  excess := E_r(mu_n) - n^{2r}/p  satisfy  excess <= C^r r! n^r  with C bounded
  as n grows at FIXED index m = (p-1)/n ?

WHY IT MATTERS (the moment arrow):
  B = max_{b!=0}|S(b)| <= (q*E_r)^{1/2r}  is PROVEN.  If E_r is random-like to depth r~log q,
  then B <= sqrt(n log q) closes the prize.  If C grows in n or r, the arrow overshoots -> wall.

DEFINITIONS (exact, integer):
  mu_n = order-n=2^a multiplicative subgroup of F_p, p = m*n + 1 (m = index, kept SMALL/fixed).
  S(b) = sum_{x in mu_n} e_p(b x).
  E_r = (1/p) sum_{b in F_p} |S(b)|^{2r}  =  #{ x_1+...+x_r = y_1+...+y_r mod p : x,y in mu_n }.
  This is an INTEGER (it counts r-against-r additive matchings). Computed exactly via integer
  FFT-free convolution counts AND cross-checked by the float FFT moment for small cases.

  The "random / Gaussian" comparison value for the FULL E_r (incl. b=0 main term) is:
        E_r ~ n^{2r}/p  +  r! * n^r        (main term + diagonal Gaussian term).
  So we isolate  excess = E_r - n^{2r}/p  and normalize by the diagonal  r! n^r:
        ratio_r(n) = (E_r - n^{2r}/p) / (r! * n^r)        [ = C^r if excess = C^r r! n^r ]
        c_r(n)     = ratio_r(n) ** (1/r)                  [ effective per-moment constant ]
  RANDOM-LIKE  <=>  c_r(n) bounded (ideally ->1) in BOTH n and r.

INDEPENDENCE FROM TWIN:
  - Twin (probe_moment_growth_law_407.py) uses SPARSE p ~ n^3 (index m ~ n^2, GROWING).
  - THIS probe uses CONSTANT small index m in {8,16,32} (p ~ n only) and pushes n to 512+.
    The constant-index regime is the one the prize cares about (m = (q-1)/n is the structural
    knob; "fixed index, growing n" is the clean asymptotic the swarm disagreed on).
  - Exact integer counting (no float FFT for the headline numbers); float FFT used only as a
    cross-check on the smallest case to catch a coding bug.

METHOD for E_r exactly at moderate p:
  Build the r-fold sumset multiplicity vector N_r over Z_p by repeated integer convolution of the
  indicator of mu_n (mod p). Then E_r = sum_b N_r[b]^2 (Plancherel: #matchings = sum of squares of
  the r-fold convolution multiplicities). p = m*n+1 is small here (<= ~16400 for n=512,m=32) so the
  length-p convolutions are cheap.
"""
import numpy as np
import sympy
import math

def smallest_prime_index_at_least(n, m_min):
    """smallest index m >= m_min with p = m*n + 1 prime; returns (m, p)."""
    m = m_min
    while True:
        p = m * n + 1
        if sympy.isprime(p):
            return m, p
        m += 1

def subgroup_indicator(p, n):
    """indicator (length p, int) of the order-n multiplicative subgroup of F_p."""
    g = int(sympy.primitive_root(p))
    h = pow(g, (p - 1) // n, p)
    ind = np.zeros(p, dtype=np.int64)
    x = 1
    seen = 0
    for _ in range(n):
        if ind[x] == 0:
            ind[x] = 1
            seen += 1
        x = x * h % p
    assert seen == n, f"subgroup size {seen} != {n}"
    return ind

def cyclic_conv_mod(a, b, p):
    """exact integer cyclic convolution of two length-p int vectors, result mod-p indexed.
    Uses numpy float FFT then rounds; values are small enough (<= n^{2r} ~ fits double for our
    range) but to be SAFE for the headline E_r we do exact int convolution via np.convolve on
    the sparse support when one operand is the n-sparse indicator."""
    # b is dense multiplicity (the running r-fold sum), a is the sparse indicator (n ones).
    supp = np.nonzero(a)[0]
    out = np.zeros(p, dtype=object)  # python ints: exact, no overflow
    bl = b.tolist()
    for s in supp.tolist():
        # add b shifted by s (mod p)
        # out[(i+s)%p] += b[i]
        out[s:] += np.array(bl[:p - s], dtype=object)
        if s > 0:
            out[:s] += np.array(bl[p - s:], dtype=object)
    return out

def Er_exact(p, n, rmax):
    """exact E_r for r=1..rmax via repeated sparse convolution; returns dict r->E_r (python int)."""
    ind = subgroup_indicator(p, n)
    res = {}
    cur = ind.astype(object).copy()  # N_1 = indicator
    # r=1
    res[1] = int(sum(int(v) * int(v) for v in cur))
    for r in range(2, rmax + 1):
        cur = cyclic_conv_mod(ind, cur, p)  # N_r = ind * N_{r-1}
        res[r] = int(sum(int(v) * int(v) for v in cur))
    return res

def Er_fft_check(p, n, rmax):
    """float-FFT cross check: E_r = (1/p) sum_b |S(b)|^{2r}."""
    f = np.zeros(p)
    ind = subgroup_indicator(p, n)
    f[ind == 1] = 1.0
    S = np.fft.fft(f)
    a2 = np.abs(S) ** 2
    return {r: float(np.sum(a2 ** r) / p) for r in range(1, rmax + 1)}

fac = [math.factorial(r) for r in range(0, 12)]

print("=" * 100)
print("CROSS-CHECK (small n): exact integer E_r  vs  float-FFT E_r  (must agree)")
print("=" * 100)
m0, p0 = smallest_prime_index_at_least(16, 8)
exact = Er_exact(p0, 16, 4)
chk = Er_fft_check(p0, 16, 4)
print(f"n=16 p={p0} index={m0}")
for r in range(1, 5):
    print(f"  r={r}: exact={exact[r]:>12d}   fft={chk[r]:>16.1f}   match={abs(exact[r]-chk[r])<0.5}")

print()
print("=" * 100)
print("CONSTANT-INDEX SWEEP:  ratio_r(n) = (E_r - n^{2r}/p)/(r! n^r),  c_r(n)=ratio_r^{1/r}")
print("RANDOM-LIKE <=> c_r(n) bounded (->1) in BOTH n and r.")
print("=" * 100)

for m_target in (8, 16, 32):
    print(f"\n--- target index m ~ {m_target}  (actual index shown per row; constant regime) ---")
    print(f"{'n':>5} {'idx':>5} {'p':>9} | " +
          "  ".join(f"r={r}: ratio (c_r)" for r in range(2, 6)))
    for a in range(3, 10):           # n = 8,16,32,64,128,256,512
        n = 1 << a
        m, p = smallest_prime_index_at_least(n, m_target)
        rmax = 5
        res = Er_exact(p, n, rmax)
        cells = []
        for r in range(2, rmax + 1):
            main = n ** (2 * r) / p          # float main term (huge); excess = E_r - main
            excess = res[r] - main
            ratio = excess / (fac[r] * n ** r)
            c_r = ratio ** (1.0 / r) if ratio > 0 else float('nan')
            cells.append(f"{ratio:8.3f}({c_r:5.3f})")
        print(f"{n:>5} {m:>5} {p:>9} | " + "  ".join(cells))

print()
print("=" * 100)
print("GROWTH IN r AT FIXED (n, small index):  c_r for r=2..7  (does c_r climb with r?)")
print("=" * 100)
for a in (6, 7, 8):
    n = 1 << a
    m, p = smallest_prime_index_at_least(n, 16)
    res = Er_exact(p, n, 7)
    cells = []
    for r in range(2, 8):
        main = n ** (2 * r) / p
        excess = res[r] - main
        ratio = excess / (fac[r] * n ** r)
        c_r = ratio ** (1.0 / r) if ratio > 0 else float('nan')
        cells.append(f"c_{r}={c_r:5.3f}")
    print(f" n={n:>4} idx={m:>3} p={p:>8}: " + "  ".join(cells))

print()
print("=" * 100)
print("MOMENT-ARROW TEST: best B-bound min_r (p*E_r)^{1/2r}  vs  true B=max_{b!=0}|S(b)|")
print("  and vs the clean law sqrt(n*log2(p/n)).  Does arrow/trueB stay bounded?")
print("=" * 100)
print(f"{'n':>5} {'idx':>5} {'p':>9} | {'trueB':>8} {'sqrt(nL)':>9} | {'arrowMin':>9} {'@r':>3} {'arrow/B':>8}")
for a in range(3, 10):
    n = 1 << a
    m, p = smallest_prime_index_at_least(n, 16)
    f = np.zeros(p)
    ind = subgroup_indicator(p, n)
    f[ind == 1] = 1.0
    S = np.fft.fft(f)
    a2 = np.abs(S) ** 2
    a2[0] = 0.0
    trueB = math.sqrt(float(np.max(a2)))
    L = math.log2(p / n)
    snl = math.sqrt(n * L)
    rmax = min(16, max(2, int(2 * math.log2(p))))
    best = None; bestr = None
    for r in range(1, rmax + 1):
        Er = float(np.sum((a2 + (0 if r == 1 else 0)) ** r) / p)  # a2[0]=0 already removed main term
        # NOTE: with a2[0]=0, this is E_r MINUS the n^{2r}/p main term contribution from b=0
        bound = (p * Er) ** (1.0 / (2 * r)) if Er > 0 else float('inf')
        if best is None or bound < best:
            best, bestr = bound, r
    print(f"{n:>5} {m:>5} {p:>9} | {trueB:8.2f} {snl:9.2f} | {best:9.2f} {bestr:3d} {best/trueB:8.3f}")

print()
print("READ:")
print("  - c_r(n) -> ~1 and FLAT in n at fixed index  => random-like => moment arrow CLOSES.")
print("  - c_r(n) grows in n (even slowly)            => sqrt(log n)-type overshoot.")
print("  - c_r climbs with r                          => deep-moment inflation (the wall).")
print("  - arrow/trueB bounded                        => moments reach the true sup (good).")
