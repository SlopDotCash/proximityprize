#!/usr/bin/env python3
r"""
probe_largesieve_smoothm_407.py -- #407: the SMOOTH-m lever (Q-D), pinned down.

probe_largesieve_density_407 found a REAL correlation: BAD primes q have m=(q-1)/n with a LARGER
largest-prime-factor (lpf(m)/m ~ 0.3-0.7) than GOOD primes (~0.15-0.31), and prime-m is more common
among bad q. This probe tests the EXPLICIT CONSTRUCTION hypothesis:

  H1 (smooth-m avoids defects): if we RESTRICT to q with m=(q-1)/n B-smooth (every prime factor <= B),
     is the defect density LOWER / does it vanish for B below some threshold?
  H2 (the mechanism): is the correlation CAUSAL (smooth m -> structurally fewer bad q) or a CONFOUND
     (bad q are rare & happen to have prime m by Erdos-Kac size bias)? Test: control for q-size.
  H3 (worst object under smooth-m): even if density drops, is the WORST CASE removed? The prize needs
     ZERO defects at the floor depth for ONE explicit q; density<1 isn't enough unless we can NAME the q.

Also: pin the UB/true plateau = n*phi(n) (Galois+rotation orbit overcount) exactly, since that is a
genuine constant-factor sharpening of the prior union bound and may be the cross-path lever.
"""
import sys, math, itertools
from collections import Counter, defaultdict
import statistics

def is_prime(num):
    if num < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if num % q == 0: return num == q
    d = num-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, num)
        if x in (1, num-1): continue
        for _ in range(s-1):
            x = x*x % num
            if x == num-1: break
        else: return False
    return True

def odd_part(x):
    while x % 2 == 0: x //= 2
    return x

def factorize(x):
    x = abs(x); f = Counter()
    while x % 2 == 0: f[2] += 1; x //= 2
    d = 3
    while d*d <= x:
        while x % d == 0: f[d] += 1; x //= d
        d += 2
    if x > 1: f[x] += 1
    return f

def lpf(x):
    if x <= 1: return 1
    return max(factorize(x).keys())

def primitive_root(p):
    phi = p-1; facs = []; mm = phi; d = 2
    while d*d <= mm:
        if mm % d == 0:
            facs.append(d)
            while mm % d == 0: mm //= d
        d += 1
    if mm > 1: facs.append(mm)
    for g in range(2, p):
        if all(pow(g, phi//qq, p) != 1 for qq in facs): return g

def order_n_root(p, n):
    return pow(primitive_root(p), (p-1)//n, p)

def reduced_vec(coeff, n):
    h = n//2
    return tuple(coeff[j] - coeff[j+h] for j in range(h))

def enumerate_reduced(n, r):
    red = defaultdict(int)
    for tup in itertools.combinations_with_replacement(range(n), r):
        coeff = [0]*n
        for t in tup: coeff[t] += 1
        cc = Counter(tup)
        num = math.factorial(r); den = 1
        for v in cc.values(): den *= math.factorial(v)
        red[reduced_vec(coeff, n)] += num//den
    return red

def all_alpha(n, r):
    red = enumerate_reduced(n, r); items = list(red.items()); h = n//2
    am = defaultdict(int)
    for (rv1, w1) in items:
        for (rv2, w2) in items:
            a = tuple(rv1[j]-rv2[j] for j in range(h))
            if any(a): am[a] += w1*w2
    return am

def is_defect_q(q, n, alphas, h):
    """does the chosen deg-1 prime at q kill some alpha (q | alpha(g))?"""
    z = order_n_root(q, n); zp = [pow(z, j, q) for j in range(h)]
    for a in alphas:
        v = 0
        for j in range(h):
            if a[j]: v += a[j]*zp[j]
        if v % q == 0:
            return True
    return False

def run(n, r, Qhi):
    h = n//2
    am = all_alpha(n, r); alphas = list(am.keys())
    # enumerate ALL primes q=1 mod n up to Qhi, classify defect / smoothness of m
    data = []
    q = 1
    while q <= Qhi:
        q += n
        if q <= 3 or not is_prime(q): continue
        m = (q-1)//n
        if m < 2: continue
        bad = is_defect_q(q, n, alphas, h)
        data.append((q, m, lpf(m), is_prime(m), bad))
    tot = len(data); nbad = sum(1 for d in data if d[4])
    print(f"\n n={n} r={r}: {tot} primes q=1 mod n up to 2^{math.log2(Qhi):.0f}, {nbad} bad ({100*nbad/tot:.2f}%)")
    # H1: bin by smoothness level B = lpf(m), measure defect rate within each bin
    print(f"  H1 defect-rate vs smoothness of m (lpf(m) buckets, log2):")
    buckets = defaultdict(lambda: [0,0])
    for (q,m,L,pm,bad) in data:
        b = int(math.log2(max(L,2)))
        buckets[b][0] += 1; buckets[b][1] += (1 if bad else 0)
    for b in sorted(buckets):
        c, bd = buckets[b]
        print(f"     lpf(m) ~ 2^{b:2d}: {c:5d} primes, {bd:4d} bad ({100*bd/c:6.2f}%)")
    # H2: control for size. Take only large q (top half), compare smooth-m vs rough-m defect rate.
    big = [d for d in data if d[0] > Qhi//2]
    if big:
        med_smooth = statistics.median([d[2]/d[1] for d in big])
        smooth = [d for d in big if d[2]/d[1] <= med_smooth]   # m's biggest factor is small frac => smoother
        rough  = [d for d in big if d[2]/d[1] >  med_smooth]
        def rate(x): return (sum(1 for d in x if d[4])/len(x)) if x else float('nan')
        print(f"  H2 (size-controlled, q>2^{math.log2(Qhi//2):.0f}): smooth-m defect rate {100*rate(smooth):.2f}% "
              f"({len(smooth)} q) vs rough-m {100*rate(rough):.2f}% ({len(rough)} q)")
    # H3: among the SMOOTHEST q (smallest lpf(m)), is there a defect-free one big enough? Name it.
    cand = sorted([d for d in data if not d[4]], key=lambda d: d[2])  # defect-free, sorted by smoothness
    if cand:
        q,m,L,pm,_ = cand[0]
        print(f"  H3 smoothest DEFECT-FREE q = {q} (m={m}, lpf(m)={L}, prime-m={pm})")
    # also: smoothest q OVERALL and whether it's bad
    sm_overall = min(data, key=lambda d: d[2])
    print(f"  H3' smoothest q overall = {sm_overall[0]} (m={sm_overall[1]},lpf={sm_overall[2]}), bad={sm_overall[4]}")

def main():
    print("#"*92)
    print(" #407 SMOOTH-m lever: does restricting m=(q-1)/n to be smooth avoid window-edge defects?")
    print("#"*92)
    run(8, 4, 2**14)
    run(8, 5, 2**14)
    run(16, 3, 2**16)
    run(32, 2, 2**22)
    print("\n" + "#"*92)
    print(" READ: if smooth-m defect rate is LOWER (causal, size-controlled H2), restricting to a smooth")
    print(" family is a real explicit-q lever. If H2 shows NO size-controlled difference, the correlation")
    print(" is an Erdos-Kac SIZE CONFOUND (prime-m q are simply larger on avg => fewer norms reach them).")

if __name__ == "__main__":
    main()
