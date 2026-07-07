#!/usr/bin/env python3
"""
probe_466_rogers_siegel_tail.py  --  LANE L3 (#466, dossier v3 section 6 Tier-2):
the D2 Rogers-Siegel DECISION probe.

QUESTION (decidable, empirical): over the ensemble of primes p = 1 mod n in the dyadic
window [n^4, 4n^4], how does M(n,p) = max_{b != 0} |eta_b| distribute, where
eta_b = sum_{x in mu_n} e_p(b x) and mu_n is THE order-n subgroup of F_p^x?
In particular: is the LOWER tail (unusually small M) heavy or thin, and does the
normalized statistic x = M / sqrt(n log(p/n)) concentrate?

IID GAUSSIAN BENCHMARK: eta_b is constant on cosets of mu_n (m = (p-1)/n cosets) and
REAL (since n is even, -1 in mu_n).  Parseval: sum over coset reps of eta^2 = p - n,
i.e. per-coset variance sigma^2 = (p-n)/m ~ n.  The iid model (m iid N(0, sigma^2),
max of |.|) predicts M/sigma ~ a_N + b_N * Gumbel with N = 2m,
a_N = sqrt(2 ln N) - (ln ln N + ln 4pi)/(2 sqrt(2 ln N)), b_N = 1/sqrt(2 ln N):
x concentrates near sqrt(2) with fluctuations O(1/log m), and the LOWER tail of a max
is doubly-exponentially thin: P(Gumbel < -1) = exp(-e) = 0.0660,
P(Gumbel < -2) = exp(-e^2) = 6.18e-4.

DECISION RULE (from the lane brief):
  CONCENTRATION (both tails thin, variance shrinking with n)
      => the exists-form ("some rare prize prime has anomalously small M") gains
         NOTHING over the forall-form => final no-go note for the D2 sliver.
  HEAVY LOWER TAIL (a positive fraction of primes with x << median)
      => name the anomaly class (v2(p-1)? generalized-Fermat? smooth cofactor?)
      => genuinely new exists-form lever.

REGIME DISCIPLINE: mu_n proper (m >= n^3 >> 1, never n = p-1), p >= n^4, two sizes
n = 16 and n = 32, generalized-Fermat primes p = b^(2^s)+1 FLAGGED and stats reported
both with and without them (known resonant family -- but note GF resonance is an
UPPER-tail phenomenon; the lower tail is the object here).

Exactness: at both n we do the FULL coset scan (all m coset reps, one exact n-term
cosine sum each -- this enumerates every distinct value of |eta_b|, so the argmax is
exact, no sampling error in M).  At n = 32 the PRIME ensemble is sampled (~2000 evenly
spaced out of ~13k) plus ALL structured primes (GF, v2 >= 12); at n = 16 all primes.
Internal check per prime: Parseval sum_reps eta^2 = p - n to 1e-6 relative.
"""

import math
import time
import numpy as np

EULER_GAMMA = 0.5772156649015329


# ---------------------------------------------------------------- primes / algebra

def sieve(limit):
    bs = bytearray([1]) * (limit + 1)
    bs[0:2] = b"\x00\x00"
    for i in range(2, int(limit ** 0.5) + 1):
        if bs[i]:
            bs[i * i:: i] = bytearray(len(bs[i * i:: i]))
    return bs


def prime_factors(x, small_primes):
    fac = set()
    for q in small_primes:
        if q * q > x:
            break
        while x % q == 0:
            fac.add(q)
            x //= q
    if x > 1:
        fac.add(x)
    return fac


def find_generator(p, small_primes):
    fac = prime_factors(p - 1, small_primes)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no generator")


def v2(x):
    return (x & -x).bit_length() - 1


def gf_level(p):
    """Largest s >= 1 with p = b^(2^s) + 1, b >= 2; 0 if not generalized-Fermat."""
    x = p - 1
    best = 0
    for s in range(1, 24):
        e = 1 << s
        if 2 ** e > x:
            break
        b = round(x ** (1.0 / e))
        for bb in (b - 1, b, b + 1):
            if bb >= 2 and bb ** e == x:
                best = s
    return best


def least_prime_factor(x, small_primes):
    for q in small_primes:
        if q * q > x:
            return x
        if x % q == 0:
            return q
    return x


# ---------------------------------------------------------------- the exact statistic

def exact_M(p, n, g):
    """Full coset scan: exact M(n,p), plus Parseval check value."""
    m = (p - 1) // n
    gm = pow(g, m, p)
    mu = np.empty(n, dtype=np.int64)
    v = 1
    for i in range(n):
        mu[i] = v
        v = v * gm % p
    assert v == 1, "subgroup order mismatch"
    # coset reps g^0 .. g^(m-1): baby-step / giant-step to avoid a python loop of m
    c = 4096
    nblk = (m + c - 1) // c
    baby = np.empty(c, dtype=np.int64)
    v = 1
    for i in range(c):
        baby[i] = v
        v = v * g % p
    gc = pow(g, c, p)
    giant = np.empty(nblk, dtype=np.int64)
    v = 1
    for j in range(nblk):
        giant[j] = v
        v = v * gc % p
    reps = ((giant[:, None] * baby[None, :]) % p).reshape(-1)[:m]
    prod = (reps[:, None] * mu[None, :]) % p          # < p^2 < 2^44, int64 safe
    eta = np.cos((2.0 * np.pi / p) * prod).sum(axis=1)
    parseval = float(eta @ eta)                        # should be p - n
    M = float(np.abs(eta).max())
    return M, m, parseval


# ---------------------------------------------------------------- gumbel benchmark

def gumbel_loc_scale(m, sigma):
    N = 2 * m                       # max of |.| over m symmetric values
    L = math.log(N)
    aN = math.sqrt(2 * L) - (math.log(L) + math.log(4 * math.pi)) / (2 * math.sqrt(2 * L))
    bN = 1.0 / math.sqrt(2 * L)
    return sigma * aN, sigma * bN


# ---------------------------------------------------------------- ensemble runner

def run_ensemble(n, sample_target, small_primes, isprime, out):
    lo, hi = n ** 4, 4 * n ** 4
    allp = [p for p in range(lo + 1, hi + 1, n)
            if isprime[p]]                       # p = 1 mod n, p in (n^4, 4 n^4]
    out(f"\n{'=' * 78}")
    out(f"n = {n}: window ({lo}, {hi}], primes p = 1 mod {n}: {len(allp)} total")

    # structured primes: generalized-Fermat and high 2-adic valuation
    structured = [p for p in allp if gf_level(p) > 0 or v2(p - 1) >= 12]
    if len(allp) <= sample_target:
        chosen = list(allp)
    else:
        step = len(allp) / sample_target
        chosen = sorted(set([allp[int(i * step)] for i in range(sample_target)]
                            + structured))
    out(f"scanned: {len(chosen)} primes ({'full ensemble' if len(chosen) == len(allp) else 'evenly sampled'}), "
        f"structured (GF or v2>=12) forced in: {len(structured)}")

    rows = []
    t0 = time.time()
    for k, p in enumerate(chosen):
        g = find_generator(p, small_primes)
        M, m, parseval = exact_M(p, n, g)
        rel = abs(parseval - (p - n)) / (p - n)
        assert rel < 1e-6, f"Parseval failed at p={p}: {parseval} vs {p - n}"
        sigma = math.sqrt((p - n) / m)
        x = M / math.sqrt(n * math.log(p / n))
        loc, scale = gumbel_loc_scale(m, sigma)
        z = (M - loc) / scale
        rows.append((p, m, M, x, z, v2(p - 1), gf_level(p),
                     least_prime_factor(m, small_primes)))
        if (k + 1) % 500 == 0:
            out(f"  ... {k + 1}/{len(chosen)} primes, {time.time() - t0:.0f}s")
    out(f"scan done in {time.time() - t0:.0f}s")

    dt = np.dtype([("p", np.int64), ("m", np.int64), ("M", np.float64),
                   ("x", np.float64), ("z", np.float64), ("v2", np.int64),
                   ("gf", np.int64), ("lpf", np.int64)])
    arr = np.array(rows, dtype=dt)

    def stats(tag, a):
        x = a["x"]
        z = a["z"]
        qs = np.percentile(x, [0, 1, 5, 10, 25, 50, 75, 90, 95, 99, 100])
        out(f"\n-- {tag}  (N = {len(a)}) --")
        out(f"x = M/sqrt(n log(p/n)):  mean {x.mean():.4f}  std {x.std():.4f}  "
            f"skew {float(((x - x.mean()) ** 3).mean() / x.std() ** 3):+.3f}")
        out("x quantiles  min/1/5/10/25/50/75/90/95/99/max:")
        out("   " + "  ".join(f"{q:.3f}" for q in qs))
        out(f"lower tail:  P(x<1.0) = {np.mean(x < 1.0):.5f}   "
            f"P(x<0.9) = {np.mean(x < 0.9):.5f}   "
            f"P(x<1.1) = {np.mean(x < 1.1):.5f}   P(x<1.2) = {np.mean(x < 1.2):.5f}")
        out(f"upper tail:  P(x>1.8) = {np.mean(x > 1.8):.5f}   "
            f"P(x>2.0) = {np.mean(x > 2.0):.5f}   P(x>2.5) = {np.mean(x > 2.5):.5f}")
        out(f"Gumbel-standardized z = (M - loc)/scale (iid benchmark: mean {EULER_GAMMA:.4f}, "
            f"std {math.pi / math.sqrt(6):.4f}):")
        out(f"   observed mean {z.mean():.4f}  std {z.std():.4f}")
        out(f"   P(z<-1) obs {np.mean(z < -1):.5f} vs Gumbel {math.exp(-math.e):.5f}   "
            f"P(z<-2) obs {np.mean(z < -2):.6f} vs Gumbel {math.exp(-math.e ** 2):.6f}")
        out(f"   P(z>2)  obs {np.mean(z > 2):.5f} vs Gumbel {1 - math.exp(-math.exp(-2)):.5f}   "
            f"P(z>4)  obs {np.mean(z > 4):.5f} vs Gumbel {1 - math.exp(-math.exp(-4)):.5f}")
        return qs

    stats("ALL primes", arr)
    non_gf = arr[arr["gf"] == 0]
    if len(non_gf) < len(arr):
        stats("NON-GF primes only (regime discipline)", non_gf)
        gf = arr[arr["gf"] > 0]
        out(f"\n-- GF primes p = b^(2^s)+1 in window: {len(gf)} --")
        for r in gf:
            out(f"   p={r['p']}  s={r['gf']}  v2={r['v2']}  x={r['x']:.4f}  z={r['z']:+.3f}")

    # structure of the lower tail
    order = np.argsort(arr["x"])
    out("\n-- 15 SMALLEST-x primes (the lower tail; anomaly-class scan) --")
    out("   p        m      v2  GF  lpf(m)     x       z")
    for i in order[:15]:
        r = arr[i]
        out(f"   {r['p']:<8} {r['m']:<6} {r['v2']:<3} {r['gf']:<3} {r['lpf']:<9} "
            f"{r['x']:.4f}  {r['z']:+.3f}")
    out("-- 10 LARGEST-x primes (upper tail) --")
    for i in order[-10:][::-1]:
        r = arr[i]
        out(f"   {r['p']:<8} {r['m']:<6} {r['v2']:<3} {r['gf']:<3} {r['lpf']:<9} "
            f"{r['x']:.4f}  {r['z']:+.3f}")

    # anomaly-class correlation: does v2 / GF / smooth-m predict small x?
    out("\n-- mean x by v2(p-1) --")
    for v in sorted(set(arr["v2"].tolist())):
        sel = arr[arr["v2"] == v]
        out(f"   v2={v:<3} N={len(sel):<5} mean x = {sel['x'].mean():.4f}  "
            f"min x = {sel['x'].min():.4f}")
    med = np.median(arr["x"])
    tail = arr[arr["x"] < 0.85 * med]
    out(f"\nprimes with x < 0.85 * median ({0.85 * med:.3f}): {len(tail)} "
        f"({len(tail) / len(arr):.5f} of ensemble)")
    return arr


def main():
    outpath = "scripts/probes/_out_466_rogers_siegel_tail.txt"
    fh = open(outpath, "w", encoding="utf-8")

    def out(s=""):
        print(s)
        fh.write(s + "\n")
        fh.flush()

    out("LANE L3 / D2 Rogers-Siegel decision probe -- M(n,p) distribution over the")
    out("prime ensemble p = 1 mod n in [n^4, 4n^4].  x = M/sqrt(n log(p/n)).")
    out("iid Gumbel benchmark: x ~= sqrt(2) = 1.4142 with O(1/log m) fluctuations;")
    out("lower tail of a max is doubly-exponentially thin.")

    limit = 4 * 32 ** 4 + 10
    isprime = sieve(limit)
    small_primes = [i for i in range(2, 3000) if isprime[i]]

    a16 = run_ensemble(16, 10 ** 9, small_primes, isprime, out)   # full ensemble
    a32 = run_ensemble(32, 2000, small_primes, isprime, out)

    out(f"\n{'=' * 78}")
    out("CONCENTRATION TEST (variance across n):")
    for n, a in ((16, a16), (32, a32)):
        an = a[a["gf"] == 0]
        out(f"  n={n}: std(x) all = {a['x'].std():.4f}, non-GF = {an['x'].std():.4f}, "
            f"median = {np.median(a['x']):.4f}, mean log m = "
            f"{np.mean(np.log(a['m'].astype(float))):.2f}")
    out("Gumbel prediction: std(x) ~ (pi/sqrt(6)) / sqrt(2 log(2m) * log(p/n));")
    for n, a in ((16, a16), (32, a32)):
        pred = np.mean(math.pi / math.sqrt(6) /
                       np.sqrt(2 * np.log(2 * a["m"].astype(float))
                               * np.log(a["p"].astype(float) / n)))
        out(f"  n={n}: predicted std(x) = {pred:.4f}")
    fh.close()


if __name__ == "__main__":
    main()
