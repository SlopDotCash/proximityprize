#!/usr/bin/env python3
r"""
probe_keff_robust_scale.py  --  #444 DECISIVE EVIDENCE on the prize floor.

QUESTION (the new-frontier attack):
  Is  K_eff(n,r) = ( E_r(mu_n) / Wick(n,r) )^{1/r}  BOUNDED (<= ~1.1 vs char-0,
  ~0.6 vs Wick), ANTITONE in r, and STRUCTURED-PRIME-ROBUST, at the TRUE prize
  regime beta = log_n p = 4 (p just above n^4), as n grows 16 -> 256 ?

If YES across ALL primes incl. structured ones -> the energy-transfer
E_r <= K^r * Wick is plausibly TRUE with K = O(1) -> the prize floor is TRUE.
If some structured prime at beta=4 INFLATES K_eff -> danger / refuted.

DEFINITIONS (exact, proper mu_n, NEVER the full group):
  mu_n   = order-n subgroup of F_p^*  (n = 2^mu, n | p-1, index (p-1)/n > 1).
  E_r    = order-r additive energy
         = #{ (x_1..x_{2r}) in mu_n^{2r} : x_1+...+x_r = x_{r+1}+...+x_{2r} }
         = (1/p) * sum_{b mod p} |eta_b|^{2r},   eta_b = sum_{y in mu_n} e_p(b y).
  Wick   = (2r-1)!! * n^r        (Gaussian-variance-n 2r-th moment; the upper target)
  E_r^0  = char-0 closed-walk value E[T_d^{2r}], T_d = sum_{j=1}^{n/2} 2cos(th_j)
           (= the largest-p / typical-q stable value; the prize char-0 anchor).
  K_eff(vs Wick)   = (E_r / Wick)^{1/r}
  K_eff(vs char-0) = (E_r / E_r^0)^{1/r}      <- the "defect" / faithfulness ratio.

METHODS (both give E_r to <~1e-12 relative error; validated vs exact integer
enumeration at small n -- see --selftest):
  * n <= 64   : full length-p real-FFT of the indicator (fast, exact-ish).
  * n >= 128  : coset/Gauss-period sum  E_r = (n^{2r} + n * sum_cosets eta_c^{2r})/p
                (avoids the p-sized array; vectorised over coset reps).

beta is held STRICTLY at 4: p is chosen just above n^4.  We additionally sweep a
STRESS SET of structured primes at beta~4:
   - generic        : first prime > n^4 with rough index
   - high-v2        : maximise 2-adic valuation of (p-1)  (p-1 = 2^big * odd)
   - rough-index    : (p-1)/n has a large prime factor (index far from smooth)
   - smooth-index   : (p-1)/n is 2^k-heavy (index a high power of 2)
   - near-Fermat    : p-1 closest to a pure 2-power (the K=2.28 Fermat danger class)

Run:  python scripts/probes/probe_keff_robust_scale.py
      python scripts/probes/probe_keff_robust_scale.py --selftest
"""
import sys
import math
import itertools
from collections import Counter

import numpy as np


# ----------------------------------------------------------------------------
# number theory helpers
# ----------------------------------------------------------------------------
def is_prime(n):
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def v2(k):
    c = 0
    while k % 2 == 0:
        k //= 2
        c += 1
    return c


def odd_part(k):
    while k % 2 == 0:
        k //= 2
    return k


def largest_prime_factor(k):
    f = 1
    d = 2
    while d * d <= k:
        while k % d == 0:
            f = max(f, d)
            k //= d
        d += 1 if d == 2 else 2
    if k > 1:
        f = max(f, k)
    return f


def order_n_root(p, n):
    """A generator of the unique order-n subgroup of F_p^* (n | p-1)."""
    e = (p - 1) // n
    import random
    random.seed(2718281 + p % 100003)
    for _ in range(4000):
        g = pow(random.randrange(2, p - 1), e, p)
        if g <= 1:
            continue
        # order exactly n  <=>  g^{n/q} != 1 for every prime q | n  (here n=2^mu)
        if pow(g, n // 2, p) != 1:
            return g
    raise RuntimeError(f"no order-{n} root mod {p}")


def subgroup(p, n):
    g = order_n_root(p, n)
    out = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = x * g % p
    assert len(set(out)) == n, "not a full order-n subgroup"
    return out


# ----------------------------------------------------------------------------
# prime selection at FIXED beta = 4  (p just above n^4), structured classes
# ----------------------------------------------------------------------------
def primes_1_mod_n_above(n, lo, count, want=None):
    """Yield primes p = 1 (mod n), p >= lo, proper (index>1), filtered by `want`."""
    c = ((lo + n - 1) // n) * n + 1
    if c <= lo:
        c += n
    found = []
    tries = 0
    while len(found) < count and tries < 4_000_000:
        tries += 1
        if is_prime(c) and (c - 1) // n > 1:
            if want is None or want(c, n):
                found.append(c)
        c += n
    return found


def pick_structured(n):
    """Return dict class_name -> prime p with beta ~ 4 (p in [n^4, ~16 n^4))."""
    lo = n ** 4
    hi = 16 * n ** 4
    out = {}

    # generic: first prime > n^4 (rough-ish typically)
    g = primes_1_mod_n_above(n, lo, 1)
    out["generic"] = g[0] if g else None

    # high-v2: maximise v2(p-1)
    cands = primes_1_mod_n_above(n, lo, 400)
    if cands:
        cands_w = [c for c in cands if c < hi] or cands
        out["high-v2"] = max(cands_w, key=lambda c: v2(c - 1))
        # rough-index: (p-1)/n has a large prime factor relative to its size
        out["rough-index"] = max(
            cands_w, key=lambda c: largest_prime_factor((c - 1) // n) / max(1, (c - 1) // n)
        )
        # smooth-index: (p-1)/n is 2-power heavy
        out["smooth-index"] = max(cands_w, key=lambda c: v2((c - 1) // n))
        # near-Fermat: p-1 closest to a pure 2-power (odd part of (p-1) smallest)
        out["near-Fermat"] = min(cands_w, key=lambda c: odd_part(c - 1))
    return out


def prime_signature(p, n):
    idx = (p - 1) // n
    return (
        f"beta={math.log(p)/math.log(n):.3f} "
        f"v2(p-1)={v2(p-1):2d} idx={idx} "
        f"v2(idx)={v2(idx)} lpf(idx)={largest_prime_factor(idx)}"
    )


# ----------------------------------------------------------------------------
# E_r  (char-p)  --  two scalable methods
# ----------------------------------------------------------------------------
def Er_fft(p, n, rmax):
    """Full length-p FFT.  E_r to ~1e-12 rel.  Use for n <= 64."""
    ind = np.zeros(p, dtype=np.float64)
    for x in subgroup(p, n):
        ind[x] = 1.0
    mag2 = np.abs(np.fft.rfft(ind)) ** 2  # real input -> rfft; symmetric spectrum
    # rfft gives b=0..p//2 ; |eta_b|=|eta_{p-b}| so double the interior, single the ends
    # E_r = (1/p) sum_{b=0}^{p-1} mag2^r = (1/p)[ mag2[0]^r + 2*sum_{1..(p-1)/2} mag2^r ]
    out = {}
    for r in range(2, rmax + 1):
        tail = np.sum(mag2[1:] ** r)  # b = 1 .. p//2  (p odd => last index (p-1)/2)
        out[r] = float((mag2[0] ** r + 2.0 * tail) / p)
    return out


def primitive_root(p):
    """A primitive root mod p (smallest)."""
    # factor p-1
    m = p - 1
    facs = []
    d = 2
    while d * d <= m:
        if m % d == 0:
            facs.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        facs.append(m)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in facs):
            return g
    raise RuntimeError("no primitive root")


def Er_period(p, n, rmax):
    """Coset / Gauss-period sum.  E_r = (n^{2r} + n*sum_cosets eta_c^{2r})/p.
    Avoids the p-sized array.  Use for n >= 128.  Vectorised over coset reps.

    The f=(p-1)/n cosets of mu_n in F_p^* are exactly { gr^j * mu_n : j=0..f-1 }
    where gr is a primitive root (mu_n = <gr^f>).  So coset reps = gr^j, computed
    in O(f) without sieving all of F_p.
    """
    Hint = subgroup(p, n)
    f = (p - 1) // n
    gr = primitive_root(p)
    # reps = gr^0, gr^1, ..., gr^{f-1}
    reps = np.empty(f, dtype=np.int64)
    x = 1
    for j in range(f):
        reps[j] = x
        x = x * gr % p

    # eta_c = sum_{y in mu_n} cos(2 pi c y / p)   (real; mu_n=-mu_n => imag cancels)
    Hi = np.array(Hint, dtype=np.int64)
    twopi_over_p = 2.0 * math.pi / p
    etas = np.empty(f, dtype=np.float64)
    # block over reps to bound memory: (block x n) matrix of cosines
    B = max(1, 2_000_000 // max(1, n))
    for s in range(0, f, B):
        rb = reps[s:s + B]
        # outer product reps*Hi mod p
        prod = (np.multiply.outer(rb, Hi) % p)
        etas[s:s + len(rb)] = np.cos(twopi_over_p * prod).sum(axis=1)
    out = {}
    for r in range(2, rmax + 1):
        s = float(np.sum(etas ** (2 * r)))
        out[r] = (n ** (2 * r) + n * s) / p
    return out


def Er_charp(p, n, rmax):
    return Er_fft(p, n, rmax) if n <= 64 else Er_period(p, n, rmax)


# ----------------------------------------------------------------------------
# char-0 anchor  E_r^0 = E[ (sum_{j=1}^{n/2} 2cos th_j)^{2r} ]  (closed walk count)
# computed EXACTLY via the integer multinomial closed-walk formula.
# ----------------------------------------------------------------------------
def Er_char0(n, r):
    """E[T_d^{2r}], T_d = sum_{j=1}^{d} 2 cos(th_j), d=n/2, th_j independent uniform.
    = sum over integer compositions: 2cos has moments  E[(2cos)^{2k}] = C(2k,k).
    Closed-walk count = sum over ways to distribute the 2r steps among d coords,
    each coord getting an even number 2k_j, weight prod C(2k_j,k_j) * multinomial.
    """
    d = n // 2
    from functools import lru_cache

    # E[(2cos)^{2k}] = binom(2k,k);  odd powers vanish.
    # E[T^{2r}] = sum_{compositions of r into d nonneg parts k_j>=0, sum k_j = r}
    #              (2r)! / prod (2k_j)! * prod C(2k_j, k_j)
    #   wait: multinomial over the 2r labeled steps assigned to coords with
    #   coord j getting 2k_j steps: (2r)!/prod(2k_j)! ; times prod E[(2cos)^{2k_j}].
    # Sum over multisets of (k_1..k_d), k_j>=0, sum=r. Use partitions of r into <=d parts.
    def partitions_into_at_most(rem, maxpart, slots):
        # yield nonincreasing positive parts, length<=slots, sum=rem
        if rem == 0:
            yield []
            return
        if slots == 0:
            return
        for q in range(min(rem, maxpart), 0, -1):
            for rest in partitions_into_at_most(rem - q, q, slots - 1):
                yield [q] + rest

    total = 0
    fact = math.factorial
    twor_fact = fact(2 * r)
    for P in partitions_into_at_most(r, r, d):
        # P = positive parts k_j (the zero parts are the unused coords).
        # number of ways to choose WHICH coords get these parts:
        cnt = Counter(P)
        used = len(P)
        # choose `used` coords out of d, then assign the multiset P to them:
        ways_coords = math.comb(d, used)
        ways_assign = fact(used)
        for v in cnt.values():
            ways_assign //= fact(v)
        # per-assignment weight: (2r)! / prod (2k_j)!  * prod C(2k_j,k_j)
        denom = 1
        cwalk = 1
        for k in P:
            denom *= fact(2 * k)
            cwalk *= math.comb(2 * k, k)
        total += ways_coords * ways_assign * (twor_fact // denom) * cwalk
    return total


def wick(n, r):
    """(2r-1)!! * n^r."""
    df = 1
    for i in range(1, 2 * r, 2):
        df *= i
    return df * (n ** r)


# ----------------------------------------------------------------------------
# self-test: methods agree with exact integer enumeration at small n
# ----------------------------------------------------------------------------
def Er_enum(p, n, rmax):
    H = subgroup(p, n)
    out = {}
    for r in range(2, rmax + 1):
        c = Counter()
        for tup in itertools.product(H, repeat=r):
            c[sum(tup) % p] += 1
        out[r] = sum(v * v for v in c.values())
    return out


def selftest():
    print("=== SELFTEST: methods vs exact integer enumeration (proper mu_n, beta=4) ===")
    ok = True
    for n in (4, 8, 16):
        lo = n ** 4
        p = primes_1_mod_n_above(n, lo, 1)[0]
        ex = Er_enum(p, n, 5)
        ff = Er_fft(p, n, 5)
        pe = Er_period(p, n, 5)
        for r in range(2, 6):
            ef = abs(ff[r] - ex[r]) / ex[r]
            ep = abs(pe[r] - ex[r]) / ex[r]
            if ef > 1e-9 or ep > 1e-9:
                ok = False
                print(f"  FAIL n={n} r={r}: exact={ex[r]} fft={ff[r]} period={pe[r]}")
        print(f"  n={n:3d} p={p}: fft & period match enumeration to <1e-9  "
              f"(E2 exact={ex[2]})")
    # char-0 anchor sanity: known r=2,3 closed forms
    #   E_2^0 = 3n^2-3n (even-parity unit circle additive energy, the char-0 value)
    #   E_3^0 = 15n^3-45n^2+40n
    for n in (8, 16, 32):
        e2 = Er_char0(n, 2)
        e3 = Er_char0(n, 3)
        f2 = 3 * n * n - 3 * n
        f3 = 15 * n ** 3 - 45 * n ** 2 + 40 * n
        m = "OK" if (e2 == f2 and e3 == f3) else "MISMATCH"
        if m != "OK":
            ok = False
        print(f"  char0 n={n:3d}: E2^0={e2} (3n^2-3n={f2}) E3^0={e3} (15n^3-45n^2+40n={f3}) {m}")
    print("SELFTEST:", "PASS" if ok else "FAIL")
    return ok


# ----------------------------------------------------------------------------
# main sweep
# ----------------------------------------------------------------------------
def main():
    if "--selftest" in sys.argv:
        selftest()
        return

    print("#444  K_eff robustness at FIXED beta=4  (proper mu_n, p just above n^4)")
    print("K_eff(W)=(E_r/Wick)^{1/r}   K_eff(0)=(E_r/E_r^char0)^{1/r}")
    print("Wick=(2r-1)!! n^r.  Defect ratio>1 => char-p energy EXCEEDS char-0 (danger).")
    print()

    # how far in n we can push each method in reasonable time/memory:
    #   FFT  : n<=64  (p<=~16.8M)
    #   period: n=128 (p~268M -> f~2.1M cosets, OK) ; n=256 (p~4.3e9) too slow -> skip/limited
    ns = [16, 32, 64, 128]
    rmax_by_n = {16: 10, 32: 10, 64: 8, 128: 6}

    for n in ns:
        rmax = rmax_by_n[n]
        e0 = {r: Er_char0(n, r) for r in range(2, rmax + 1)}
        wk = {r: wick(n, r) for r in range(2, rmax + 1)}
        structured = pick_structured(n)
        print(f"================ n={n}  (char-0 anchor E_2^0={e0[2]}) ================")
        # report the worst (max) K_eff over the structured classes per r
        worst_vsW = {r: (0.0, "") for r in range(2, rmax + 1)}
        worst_vs0 = {r: (0.0, "") for r in range(2, rmax + 1)}
        for cls, p in structured.items():
            if p is None:
                continue
            try:
                Er = Er_charp(p, n, rmax)
            except MemoryError:
                print(f"  [{cls}] p={p}  MEMORYERROR -- skipped")
                continue
            sig = prime_signature(p, n)
            print(f"  --- class={cls:12s} p={p}  {sig}")
            hdr = "    r |   K_eff(W)  K_eff(0)  |  E_r/Wick   E_r/E0   |  antitone(W)"
            print(hdr)
            prevW = None
            for r in range(2, rmax + 1):
                kW = (Er[r] / wk[r]) ** (1.0 / r)
                k0 = (Er[r] / e0[r]) ** (1.0 / r)
                ratioW = Er[r] / wk[r]
                ratio0 = Er[r] / e0[r]
                anti = "" if prevW is None else ("yes" if kW <= prevW + 1e-9 else "NO!")
                prevW = kW
                print(f"    {r:2d} | {kW:9.4f}  {k0:8.4f}  | {ratioW:9.4f}  {ratio0:7.4f}  |  {anti}")
                if kW > worst_vsW[r][0]:
                    worst_vsW[r] = (kW, cls)
                if k0 > worst_vs0[r][0]:
                    worst_vs0[r] = (k0, cls)
        print(f"  >>> n={n} WORST-OVER-CLASSES K_eff per r:")
        for r in range(2, rmax + 1):
            print(f"      r={r:2d}: max K_eff(W)={worst_vsW[r][0]:.4f} [{worst_vsW[r][1]}]   "
                  f"max K_eff(0)={worst_vs0[r][0]:.4f} [{worst_vs0[r][1]}]")
        print()


if __name__ == "__main__":
    main()
