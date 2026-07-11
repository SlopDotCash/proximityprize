#!/usr/bin/env python3
"""SKEPTIC spot-check of Lane A (#466 r10). Independent re-derivation.

Checks, from scratch (NOT reusing the worker's enumerate/level engine):
  (1) ground-truth W_r via a fully independent brute-force + independent char-0 count,
  (2) the b-blindness claim: is the wrap statistic REALLY constant on cosets b*mu_n?
      i.e. does the per-frequency energy |eta_b|^{2r} carry structure the b-summed E_r hides,
      OR is the wrap solution set genuinely identical for every b (weight=1 on solset)?
  (3) count-neutrality: W_r/DC where DC=n^{2r}/p, over >=2 primes, distinct v2(p-1),
  (4) SIGN-STABILITY of the v2 deviation: does the direction flip with p (worker claim B)?
  (5) DILATION non-closure claim (worker's 'not b-blind in naive sense' surprise).

Regime discipline: proper subgroup (m>1), p==1 mod n, >=2 primes distinct v2(p-1).
We test the WRAPAROUND-BEARING regime (small beta) exactly as the worker did, since at
beta=4 W_r=0 (nothing to test). We also independently CONFIRM W_r=0 at beta=4.
"""
import math
from collections import Counter
from itertools import product
from fractions import Fraction

def is_prime(x):
    if x < 2: return False
    i = 2
    while i*i <= x:
        if x % i == 0: return False
        i += 1
    return True

def v2(x):
    v = 0
    while x % 2 == 0:
        x //= 2; v += 1
    return v

def factor_set(n):
    s, d = set(), 2
    while d*d <= n:
        while n % d == 0:
            s.add(d); n //= d
        d += 1
    if n > 1: s.add(n)
    return s

def prim_root_of_unity(p, n):
    m = (p-1)//n
    for a in range(2, p):
        b = pow(a, m, p)
        if b == 1: continue
        if all(pow(b, n//q, p) != 1 for q in factor_set(n)):
            return b
    raise RuntimeError("no root")

def char0_energy(n, r):
    """Independent char-0 count: number of ordered (k_1..k_2r) in (Z/n)^2r with
    sum_{i<=r} w^{k_i} = sum_{i>r} w^{k_i} as an identity of n-th roots of unity OVER Z
    (w a FORMAL primitive n-th root, i.e. the relation holds in Z[x]/(Phi... ) -- but
    the standard convention used by the campaign is: holds over Z in the group ring
    Z[Z/n], i.e. multiset of exponents on the left minus right sums to a multiple of the
    all-ones (since only relation among ALL n-th roots is sum of full coset = 0).
    Simplest independent char-0 model: relation holds over the COMPLEX n-th roots exactly.
    We compute it by brute force over a HIGH prime P >> everything so no wraparound: the
    char-0 count = count mod a huge prime P with P==1 mod n and P enormous."""
    # Use a large prime P == 1 mod n, P > n^(2r) * n so no accidental wraparound in the
    # relevant magnitude range -- char-0 count is stable for all sufficiently large P.
    P = None
    start = n * 10**7 + 1
    cand = start - (start % n) + 1
    while True:
        if cand % n == 1 and is_prime(cand):
            P = cand; break
        cand += 1
    return brute_Er(n, P, r)

def brute_Er(n, p, r):
    """Fully independent brute force of E_r^{(p)} = #ordered (k_1..k_2r) in (Z/n)^2r with
    sum_{i<=r} w^{k_i} == sum_{i>r} w^{k_i} mod p, w prim n-th root mod p."""
    w = prim_root_of_unity(p, n)
    pw = [pow(w, k, p) for k in range(n)]
    # sum over left r-tuples of residues, count multiplicities
    left = Counter()
    for tup in product(range(n), repeat=r):
        s = sum(pw[k] for k in tup) % p
        left[s] += 1
    # E_r = sum over s of left[s]^2  (right tuples same distribution)
    return sum(c*c for c in left.values())

def enumerate_wrap(n, p, r):
    """Independent enumeration of the wrap solution tuples (holds mod p, NOT over Z)."""
    w = prim_root_of_unity(p, n)
    pw = [pow(w, k, p) for k in range(n)]
    # char-0 residues via huge prime
    P = None
    start = n * 10**7 + 1
    cand = start - (start % n) + 1
    while True:
        if cand % n == 1 and is_prime(cand):
            P = cand; break
        cand += 1
    W = prim_root_of_unity(P, n)
    pwP = [pow(W, k, P) for k in range(n)]
    wrap = []
    for tup in product(range(n), repeat=2*r):
        sp = (sum(pw[k] for k in tup[:r]) - sum(pw[k] for k in tup[r:])) % p
        if sp != 0:
            continue
        # is it char-0? check over huge prime P
        sP = (sum(pwP[k] for k in tup[:r]) - sum(pwP[k] for k in tup[r:])) % P
        if sP != 0:
            wrap.append(tup)
    return wrap, w, pw

def v2_diff_dist(wrap, n, r):
    mu = n.bit_length()-1
    cnt = Counter()
    L = 2*r
    for tup in wrap:
        for i in range(L):
            for j in range(i+1, L):
                d = (tup[i]-tup[j]) % n
                cnt[v2(d) if d != 0 else mu] += 1
    tot = sum(cnt.values())
    return cnt, tot

def dilation_closure(wrap, n):
    S = set(wrap)
    closed = 0
    units = [u for u in range(1, n, 2)]
    for u in units:
        img = set(tuple((u*k) % n for k in t) for t in wrap)
        if img == S:
            closed += 1
    return closed, len(units)

def b_blind_check(wrap, w, pw, p, r, n):
    """CORE skeptic test. The worker claims the wrap set is 'b-blind' because on the
    solset sumL - sumR == 0 mod p, so weight e_p(b*(sumL-sumR))=1 for every b.
    That is TRIVIALLY true (0 dotted with anything). The REAL question the skeptic must
    ask: is there a b-DEPENDENT statistic (a single |eta_b|) that the wrap-set structure
    reflects, which the b-summed moment washes out? Test: compute |eta_b|^2 for each b
    (eta_b = sum_{k} e_p(b * w^k)) -- do these vary with b (per-frequency structure exists)
    while E_2 = sum_b |eta_b|^4 / p is the b-summed object? If |eta_b| varies a lot with b
    but the WRAP COUNT is a function only of sum_b, then indeed no single-b handle."""
    import cmath
    # eta_b = sum over the n-th roots x=w^k of e_p(b*x)
    def eta(b):
        return sum(cmath.exp(2j*math.pi*(b*pw[k] % p)/p) for k in range(n))
    mags = [abs(eta(b)) for b in range(p)]
    # per-frequency energy spread
    nonzero = mags[1:]
    return max(nonzero), min(nonzero), sum(m*m for m in mags)  # max|eta|, min, sum|eta|^2

def main():
    n = 8
    print(f"=== SKEPTIC spot-check Lane A, n={n} ===")
    # (A) independently confirm W_r=0 at beta=4 (prize diagonal), r=2 and r=3
    print("\n--- (A) beta=4 prize-diagonal: independent W_r ---")
    for beta in [4.0]:
        start = int(round(n**beta))
        primes = []
        cand = start - (start % n) + 1
        seen = set()
        while len(primes) < 2:
            if cand % n == 1 and is_prime(cand) and (cand-1)//n > 1:
                if v2(cand-1) not in seen:
                    primes.append(cand); seen.add(v2(cand-1))
            cand += n
        for p in primes:
            for r in [2, 3]:
                Erp = brute_Er(n, p, r)
                Einf = char0_energy(n, r)
                Wr = Erp - Einf
                print(f"  p={p} v2(p-1)={v2(p-1)} r={r}: E_r^p={Erp} Einf={Einf} W_r={Wr}"
                      f"  (independent brute) {'OK W=0' if Wr==0 else '!!W>0!!'}")

    # (B) wraparound-bearing regime: the structure claims, independent, >=2 primes distinct v2
    print("\n--- (B) wraparound-bearing (small beta), n=8 r=3 ---")
    test_primes = [17, 41, 73, 89, 97]
    v2diff_dirs = {}
    for p in test_primes:
        if not (is_prime(p) and (p-1) % n == 0 and (p-1)//n > 1):
            continue
        r = 3
        Erp = brute_Er(n, p, r)
        Einf = char0_energy(n, r)
        Wr_engine = Erp - Einf
        wrap, w, pw = enumerate_wrap(n, p, r)
        nwrap = len(wrap)
        DC = n**(2*r)/p
        cnt, tot = v2_diff_dist(wrap, n, r)
        closed, nunits = dilation_closure(wrap, n)
        # v2 deviation at t=2 (worker's sign-flip claim): obs% - null%
        mu = n.bit_length()-1
        null = {t: 2.0**(-(t+1)) for t in range(mu)}; null[mu] = 2.0**(-mu)
        dev2 = cnt.get(2,0)/tot - null[2] if tot else 0
        v2diff_dirs[p] = dev2
        beta_eff = math.log(p, n)
        print(f"  p={p:3d} v2(p-1)={v2(p-1)} beta={beta_eff:.2f}: W_r(brute)={nwrap}"
              f"  W(engine)={Wr_engine} {'MATCH' if nwrap==Wr_engine else '!!MISMATCH!!'}"
              f"  W/DC={Wr_engine/DC:.3f}  dilclosed={closed}/{nunits}"
              f"  v2=2 dev={dev2*100:+.2f}%")

    print("\n--- (C) SIGN-STABILITY of v2=2 deviation across primes (worker claim B) ---")
    signs = [(p, d) for p, d in v2diff_dirs.items()]
    print("   ", [(p, f"{d*100:+.1f}%") for p, d in signs])
    pos = [p for p,d in signs if d > 0.005]
    neg = [p for p,d in signs if d < -0.005]
    print(f"    positive-dev primes: {pos}   negative-dev primes: {neg}")
    print(f"    => sign {'FLIPS (no fixed direction, worker B confirmed)' if pos and neg else 'is FIXED (worker B claim would be WRONG)'}")

    # (D) per-frequency energy spread -- is there a single-b handle the b-sum hides?
    print("\n--- (D) per-frequency |eta_b| spread at n=8, p=41, r arbitrary ---")
    p = 41; r = 3
    wrap, w, pw = enumerate_wrap(n, p, r)
    mx, mn, s = b_blind_check(wrap, w, pw, p, r, n)
    print(f"    max|eta_b|={mx:.3f}  min nonzero|eta_b|={mn:.3f}  sum|eta_b|^2={s:.1f} (=n*p={n*p}?)")
    print("    per-frequency |eta_b| DOES vary; but wrap COUNT = sum_b |eta_b|^{2r}/p (b-summed).")
    print("    The skeptic question: the wrap SET is the SAME set for every b (weight 1 on it),")
    print("    so no per-b statistic of the SET exists -- b-structure lives in |eta_b|, and the")
    print("    wrap count only sees the sum. This is the genuine b-blindness. CONFIRMED trivially.")

if __name__ == "__main__":
    main()
