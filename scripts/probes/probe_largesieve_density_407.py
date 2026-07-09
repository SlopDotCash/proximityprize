#!/usr/bin/env python3
r"""
probe_largesieve_density_407.py -- #407 avg-over-q, the GENUINELY NEW questions.

The prior session refuted the FIRST/SECOND MOMENT UNION BOUND: #bad q in [Q,2Q] <= n^{2r} phi log(2r)/log Q
is vacuous at prize depth r ~ ln q because n^{2r} is astronomical. That bound asks "is the bad SET
empty?" (covering). This probe asks the strictly weaker and possibly-true questions:

  Q-A. DENSITY (not covering): does the bad-prime DENSITY  d_r(Q) = #{bad q in [Q,2Q]} / #{q in [Q,2Q]}
       go to 0 as Q->inf at FIXED depth r?  (a good q exists iff d_r < 1, MUCH weaker than empty.)
       The union bound gives d_r <= n^{2r} phi log(2r) / Q  -- this ->0 in Q for FIXED r,n. The prize
       needs r ~ ln q growing WITH q though. So the real question: at the prize DIAGONAL r=ln Q,n=2^40,
       can ANY method beat the union bound's collapse?

  Q-B. The SINGLE-alpha density is the heart: a FIXED sparse alpha with norm N(alpha) is "bad for q"
       iff the deg-1 prime q|alpha. By Chebotarev/Galois closure, density of such q among primes =1 mod n
       is EXACTLY (number of prime ideals of K=Q(zeta_n) above q that divide alpha)/phi averaged ... but
       for a FIXED alpha this is governed by the prime factorization of the FIXED integer N(alpha): the
       bad q are precisely the prime factors of N(alpha) that are =1 mod n and split-compatibly. A FIXED
       integer has FINITELY many prime factors => density of bad-q FOR ONE alpha is ZERO. The union over
       infinitely-many alpha (as r->inf) is what bites. So the avg-over-q question = ANALYTIC RANK of the
       FAMILY {N(alpha)}_alpha: how fast does the union of their prime factors fill the primes =1 mod n?

  Q-C. The KEY NEW computation: among primes q=1 mod n in a window, what is the TRUE bad density as a
       function of (window scale Q, depth r)? Fit d_r(Q) ~ C * (something). Prior measured "defect-free
       fraction" -> this probe measures the LAW d_r(Q) precisely and checks if it's ~ A_r/Q (union, the
       wall) or genuinely smaller (heavy clustering / shared-factor structure that the union misses).

  Q-D. SMOOTH-q RESTRICTION: restrict to q with q-1 having a controlled factorization (q-1 = n*m, m
       SMOOTH or m PRIME). Does forcing m structured remove defects? (the Gauss-sum phases depend on the
       m-th-power residue structure; a structured m might flatten or might resonate.)
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

def smooth_bound(x):
    """largest prime factor of x (smoothness)."""
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

def norm_exact(alpha, n):
    h = len(alpha); prod = 1.0
    for t in range(1, n, 2):
        z = complex(math.cos(2*math.pi*t/n), math.sin(2*math.pi*t/n))
        val = sum(alpha[i]*z**i for i in range(h))
        prod *= abs(val)
    return round(prod)

def all_alpha(n, r):
    red = enumerate_reduced(n, r)
    items = list(red.items()); h = n//2
    am = defaultdict(int)
    for (rv1, w1) in items:
        for (rv2, w2) in items:
            a = tuple(rv1[j]-rv2[j] for j in range(h))
            if any(a): am[a] += w1*w2
    return am

# ---- Q-C: the bad-density LAW, measured exactly, with smooth/prime-m split ----
def density_law(n, r):
    h = n//2
    am = all_alpha(n, r)
    alphas = list(am.keys())
    norms = {a: norm_exact(a, n) for a in alphas}
    # set of all odd primes p=1 mod n that divide some N(alpha) AND split-divide some alpha
    # (=the actual bad primes). Build by factoring all norms, then verifying the embedding.
    cand = set()
    for a in alphas:
        for p in factorize(odd_part(norms[a])):
            if p % n == 1 and p > 3:
                cand.add(p)
    # verify each candidate is genuinely bad (the SPECIFIC deg-1 prime divides some alpha)
    bad = set()
    for q in cand:
        if not is_prime(q): continue
        z = order_n_root(q, n); zp = [pow(z, j, q) for j in range(h)]
        for a in alphas:
            v = 0
            for j in range(h):
                if a[j]: v += a[j]*zp[j]
            if v % q == 0:
                bad.add(q); break
    cap = max(bad) if bad else 1
    print(f"\n n={n} r={r}: phi={h}, #alpha={len(alphas)}, #bad primes (all scales)={len(bad)}, "
          f"cap=2^{math.log2(max(cap,1)):.1f}")
    # measure density across log-windows up to the cap
    edges = [2**k for k in range(int(math.log2(2*n))+1, int(math.log2(max(cap,4)))+2)]
    rows = []
    for i in range(len(edges)-1):
        Qlo, Qhi = edges[i], edges[i+1]
        prs = [q for q in range(Qlo - Qlo%n + 1, Qhi+1, n) if q > 3 and is_prime(q)]
        if not prs: continue
        b = sum(1 for q in prs if q in bad)
        dens = b/len(prs)
        # union-bound prediction at this scale: sum_alpha #{prime factors of N(alpha) in [Qlo,Qhi]} / #prs
        ub_hits = 0
        for a in alphas:
            for p, e in factorize(odd_part(norms[a])).items():
                if Qlo <= p <= Qhi and p % n == 1: ub_hits += 1
        ub_dens = ub_hits/len(prs)
        rows.append((Qlo, Qhi, len(prs), b, dens, ub_dens))
    print(f"  {'window':>22} {'#q':>6} {'#bad':>6} {'density':>9} {'unionUB':>9} {'UB/true':>8}")
    for (Qlo,Qhi,npr,b,dens,ub) in rows:
        ratio = ub/dens if dens > 0 else float('inf')
        print(f"  [2^{math.log2(Qlo):4.1f},2^{math.log2(Qhi):4.1f}] {npr:6d} {b:6d} {dens:9.4f} {ub:9.4f} "
              f"{('inf' if ratio==float('inf') else f'{ratio:7.2f}')}")
    # Q-D: smooth vs prime m=(q-1)/n among the GOOD and BAD primes -- is structure correlated with badness?
    good = [q for q in (range(2*n, min(cap*2, 2**20))) if q % n == 1 and is_prime(q) and q not in bad]
    badl = sorted(bad)
    def m_profile(qs):
        sm = []; pm = 0
        for q in qs[:5000]:
            m = (q-1)//n
            if m <= 1: continue
            sm.append(smooth_bound(m)/m)  # 1.0 if m prime; small if smooth
            if is_prime(m): pm += 1
        if not sm: return (float('nan'), 0, 0)
        return (statistics.mean(sm), pm, len(sm))
    g_sm, g_pm, g_ct = m_profile(good); b_sm, b_pm, b_ct = m_profile(badl)
    print(f"  Q-D smooth-m: GOOD primes mean(lpf(m)/m)={g_sm:.3f} (prime-m frac {g_pm/max(g_ct,1):.3f}); "
          f"BAD {b_sm:.3f} (prime-m frac {b_pm/max(b_ct,1):.3f})")


def main():
    print("#"*92)
    print(" #407 avg-over-q DENSITY LAW (not covering): does bad-density beat the union bound?")
    print("#"*92)
    for (n,r) in [(8,3),(8,4),(8,5),(16,2),(16,3),(32,2)]:
        density_law(n, r)
    print("\n" + "#"*92)
    print(" READ: if UB/true >> 1 and GROWS with scale, clustering makes the TRUE density far below the")
    print(" union bound -> avg-over-q could certify a good q where the union bound is vacuous. If UB/true")
    print(" ~ 1 (no clustering at scale), the union bound IS the truth and the route is dead (prior verdict).")

if __name__ == "__main__":
    main()
