#!/usr/bin/env python3
"""
probe_466_d4_structure.py -- LANE F2: CENSUS the 92 in-window K-bad primes at n=32.

Follow-up to probe_466_d4_scanner.py (run3: n=32 exhaustive window scan found 92 K-bad
in-window primes, max W4/K-margin ratio 2.14 -- the depth-4 face DIVERGES from D3).

QUESTION: are the K-bad primes ALL structured (high-v2 / generalized-Fermat / near the
window floor beta~4 / smooth-cofactor), or is there a GENERIC (unstructured) K-bad prime?
  - If ALL structured  -> the D4 divisor structure conjecture is stateable; good supply survives.
  - If a GENERIC one exists -> the T4=O(n^4) good-prime-supply hypothesis fails on positive
    density -> the bilinear n^{7/8} route DIES.

Method: recompute E4(mu_32, p) exactly for every p == 1 mod 32 in the window
[32^4, 4*32^4] = [1048576, 4194304] (sparse autocorrelation, same as the scanner, E4-only),
flag K-BAD (A4 = E4(p) - n^8/p > 1.05*E4^0), and profile each K-bad prime:
    v2(p-1); generalized-Fermat form p = b^(2^s)+1; largest prime factor of odd part of p-1
    (smooth-cofactor test); beta = log_n(p) (window-floor proximity); W4 and K-margin ratio.

Anchor cross-check FIRST: n=16 p=65537 -> W4 = +4480 (dossier), else abort.
"""
import sys, time
import numpy as np

T0 = time.time()
N = 32
K_THRESH = 1.05
LO, HI = N**4, 4 * N**4          # [1048576, 4194304]
E4_0 = 105 * N**4 - 630 * N**3 + 1435 * N**2 - 1155 * N   # = 90889120
DC_N8 = N**8                      # numerator of DC term n^8/p
KMARGIN = 0.05 * E4_0            # W4 threshold ~ (approx; exact uses +n^8/p)


def log(m=""):
    print(m, flush=True)


def sieve(limit):
    b = np.ones(limit + 1, dtype=bool)
    b[:2] = False
    for q in range(2, int(limit**0.5) + 1):
        if b[q]:
            b[q * q:: q] = False
    return b


def v2(m):
    k = 0
    while m % 2 == 0:
        m //= 2
        k += 1
    return k


def largest_prime_factor(m):
    """m modest (< 4.2M); trial division."""
    lpf = 1
    d = 2
    while d * d <= m:
        while m % d == 0:
            lpf = d
            m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        lpf = max(lpf, m)
    return lpf


def is_perfect_power_base(m, e):
    """return integer b with b**e == m, else None."""
    if m < 1:
        return None
    b = round(m ** (1.0 / e))
    for c in (b - 1, b, b + 1):
        if c >= 1 and c**e == m:
            return c
    return None


def gf_form(p):
    """generalized-Fermat p = b^(2^s)+1 ? return (b, s) with s>=1 minimal exponent-tower,
    i.e. p-1 = b^(2^s), b>=2, requiring the exponent to be a 2-power >= 2. Also return the
    plain 'p-1 is a 2^k power of a base' info. We report the LARGEST 2^s for which p-1 is a
    perfect (2^s)-th power (s>=1)."""
    m = p - 1
    best = None
    s = 1
    while 2**s <= 40:  # exponent up to 2^5=32 covers window range
        b = is_perfect_power_base(m, 2**s)
        if b is not None and b >= 2:
            best = (b, s)
        s += 1
    return best


def mu_subgroup(p, n):
    q = (p - 1) // n
    h = None
    for a in range(2, p):
        cand = pow(a, q, p)
        if cand != 1 and pow(cand, n // 2, p) == p - 1:
            h = cand
            break
    if h is None:
        raise RuntimeError("no order-%d elt for p=%d" % (n, p))
    xs = np.empty(n, dtype=np.int64)
    cur = 1
    for i in range(n):
        xs[i] = cur
        cur = (cur * h) % p
    return xs


def E4_char_p(p, n, xs):
    """Exact E_4 = sum_t N4(t)^2 via sparse autocorrelation (E4-only; no depth-3 pass)."""
    s2 = (xs[:, None] + xs[None, :]) % p
    vals, cnts = np.unique(s2.ravel(), return_counts=True)
    cnts = cnts.astype(np.int64)
    s4 = ((vals[:, None] + vals[None, :]) % p).ravel()
    w4 = (cnts[:, None] * cnts[None, :]).astype(np.float64).ravel()
    _, inv = np.unique(s4, return_inverse=True)
    N4 = np.rint(np.bincount(inv, weights=w4)).astype(np.int64)
    assert int(N4.sum()) == n**4
    return int(np.dot(N4, N4))


# ---- anchor cross-check (n=16, p=65537, W4 must be +4480)
def anchor_check():
    E4_0_16 = 105 * 16**4 - 630 * 16**3 + 1435 * 16**2 - 1155 * 16  # 4649680
    xs = mu_subgroup(65537, 16)
    w4 = E4_char_p(65537, 16, xs) - E4_0_16
    log("[ANCHOR] n=16 p=65537: W4 = %+d (dossier requires +4480) -> %s"
        % (w4, "PASS" if w4 == 4480 else "FAIL"))
    assert w4 == 4480, "anchor mismatch, aborting"


log("probe_466_d4_structure.py -- census of n=32 in-window K-bad primes")
log("window [n^4,4n^4] = [%d,%d];  E4^0(32)=%d;  K=%.2f;  K-margin(approx)=%.0f"
    % (LO, HI, E4_0, K_THRESH, KMARGIN))
anchor_check()

IS_P = sieve(HI + 8)
window_primes = [int(p) for p in np.nonzero(IS_P[LO:HI + 1])[0] + LO if (p + LO) % N == 1]
# fix off-by: recompute cleanly
window_primes = [p for p in range(LO, HI + 1) if IS_P[p] and p % N == 1]
log("window primes == 1 mod %d: %d" % (N, len(window_primes)))

kbad = []
t_s = time.time()
maxW4 = 0
for i, p in enumerate(window_primes):
    if (i + 1) % 1000 == 0:
        log("  ... %d/%d (%.0fs)" % (i + 1, len(window_primes), time.time() - t_s))
    xs = mu_subgroup(p, N)
    E4p = E4_char_p(p, N, xs)
    W4 = E4p - E4_0
    A4 = E4p - DC_N8 / p
    maxW4 = max(maxW4, W4)
    if A4 > K_THRESH * E4_0:
        kbad.append((p, W4, A4))

log("")
log("=" * 96)
log("RESULT: %d K-bad in-window primes (max in-window W4 = %d, K-margin ~ %.0f)"
    % (len(kbad), maxW4, KMARGIN))
log("=" * 96)

# ---- census
import math
rows = []
for p, W4, A4 in sorted(kbad, key=lambda t: t[0]):
    m = p - 1
    v = v2(m)
    odd = m // (2**v)
    lpf = largest_prime_factor(odd) if odd > 1 else 1
    gf = gf_form(p)
    beta = math.log(p) / math.log(N)
    exact_margin = KMARGIN + DC_N8 / p
    rows.append(dict(p=p, v2=v, odd=odd, lpf=lpf, gf=gf, beta=beta, W4=W4,
                     A4E=A4 / E4_0, ratio=W4 / exact_margin))

log("")
log("%-9s %-4s %-6s %-10s %-14s %-8s %-11s %-6s %-7s"
    % ("p", "v2", "beta", "GF b^(2^s)+1", "odd part p-1", "lpf(odd)", "W4", "A4/E4^0", "W4/marg"))
log("-" * 96)
structured = 0
generic = []
for r in rows:
    gf = r["gf"]
    gfstr = "b=%d,s=%d" % gf if gf else "-"
    # structured := high-v2 (v2>=13, i.e. >= scanner threshold) OR GF OR near floor (beta<4.05)
    # OR smooth odd cofactor (lpf small relative to sqrt) -- we record the raw fields and
    # decide 'structured' by: GF, or v2 unusually high, or beta near window floor.
    is_struct = (gf is not None) or (r["v2"] >= 13) or (r["beta"] < 4.02)
    tag = "STRUCT" if is_struct else "GENERIC?"
    if is_struct:
        structured += 1
    else:
        generic.append(r)
    log("%-9d %-4d %-6.3f %-10s %-14d %-8d %-11d %-6.3f %-7.3f  %s"
        % (r["p"], r["v2"], r["beta"], gfstr, r["odd"], r["lpf"], r["W4"],
           r["A4E"], r["ratio"], tag))

log("")
log("=" * 96)
log("CENSUS SUMMARY")
log("=" * 96)
log("total K-bad in-window: %d" % len(rows))
log("  generalized-Fermat (p=b^(2^s)+1): %d" % sum(1 for r in rows if r["gf"]))
log("  v2(p-1) >= 13 (high 2-adic): %d" % sum(1 for r in rows if r["v2"] >= 13))
log("  beta < 4.02 (near window floor): %d" % sum(1 for r in rows if r["beta"] < 4.02))
log("  beta < 4.05: %d" % sum(1 for r in rows if r["beta"] < 4.05))
log("  beta < 4.10: %d" % sum(1 for r in rows if r["beta"] < 4.10))
if rows:
    log("  beta range of K-bad set: [%.4f, %.4f]"
        % (min(r["beta"] for r in rows), max(r["beta"] for r in rows)))
    log("  v2 range of K-bad set: [%d, %d]"
        % (min(r["v2"] for r in rows), max(r["v2"] for r in rows)))
# v2 histogram
from collections import Counter
vh = Counter(r["v2"] for r in rows)
log("  v2 histogram: %s" % dict(sorted(vh.items())))
# largest-p K-bad (deepest into window = least 'floor-structured')
if rows:
    deepest = max(rows, key=lambda r: r["p"])
    log("  DEEPEST K-bad (largest beta): p=%d beta=%.4f v2=%d gf=%s lpf=%d"
        % (deepest["p"], deepest["beta"], deepest["v2"], deepest["gf"], deepest["lpf"]))
log("")
log("GENERIC (unstructured) K-bad primes: %d" % len(generic))
for r in generic:
    log("  p=%d v2=%d beta=%.4f odd=%d lpf=%d W4=%d ratio=%.3f"
        % (r["p"], r["v2"], r["beta"], r["odd"], r["lpf"], r["W4"], r["ratio"]))

log("")
log("VERDICT: %s" % (
    "ALL K-bad primes STRUCTURED (GF or high-v2 or window-floor) -> D4 structure conj holds"
    if not generic else
    "GENERIC K-bad prime(s) EXIST -> n^{7/8} T4 supply hypothesis FAILS on positive density"))
log("total elapsed %.1fs" % (time.time() - T0))
