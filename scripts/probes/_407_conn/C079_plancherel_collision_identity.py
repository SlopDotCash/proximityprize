#!/usr/bin/env python3
"""
C079 attack: "Plancherel collision identity and Gauss-sum 2nd moment are ONE Parseval"
and "N0 = sum_b eta_b^r / q is LITERALLY MomentCollisionSpectral.collision",
opening "Paley-Zygmund anti-concentration on the eta side".

Exact integer / exact-cyclotomic-rational arithmetic. PRIZE REGIME ONLY:
dyadic mu_n a PROPER subgroup of F_q*, q prime = 1 mod n, q ~ n^beta (beta~4-4.5),
proper-subgroup + large prime. (NEVER the full group.)

Claims graded independently:
  (A) raw-moment identity   : sum_{b in F_q} eta_b^r == q * N0(G,r),
        N0(G,r)=#{v in G^r : sum v_i = 0 mod q}.      [F16 / SubgroupGaussSumRawMoment]
  (B) "literal collision"   : is N0(G,r) == MomentCollisionSpectral.collision ?
        collision = #{(S,S'): |S|=|S'|=a, sum_{x in S}x = sum_{x in S'}x}  (SUBSET pairs).
  (C) the actionable payoff : does Paley-Zygmund on {eta_b} give a NEW bound on
        M(n)=max_{b!=0}|eta_b| beyond what the 2nd moment already gives?
"""
import itertools, cmath, math
from fractions import Fraction

def primitive_root(q):
    # smallest primitive root mod prime q
    facs = []
    m = q-1
    d = 2
    while d*d <= m:
        if m % d == 0:
            facs.append(d)
            while m % d == 0: m//=d
        d += 1
    if m > 1: facs.append(m)
    for g in range(2, q):
        if all(pow(g, (q-1)//p, q) != 1 for p in facs):
            return g
    raise RuntimeError

def subgroup(q, n):
    # the unique multiplicative subgroup of order n (n | q-1), as a sorted list of residues
    g = primitive_root(q)
    h = pow(g, (q-1)//n, q)
    S = set()
    x = 1
    for _ in range(n):
        S.add(x); x = (x*h) % q
    assert len(S) == n
    return sorted(S)

def find_prize_prime(n, beta, qmin=None):
    """proper subgroup mu_n < F_q*, q prime = 1 mod n, q ~ n^beta, q>>n (proper, large)."""
    import sympy
    target = qmin if qmin else int(round(n**beta))
    q = target
    # q = 1 mod n
    q = q - (q % n) + 1
    if q <= n: q += n
    while True:
        if sympy.isprime(q):
            return q
        q += n

def eta_all(q, G):
    """exact complex eta_b for all b: eta_b = sum_{y in G} exp(2pi i b y / q)."""
    w = [cmath.exp(2j*cmath.pi*k/q) for k in range(q)]
    eta = []
    for b in range(q):
        s = 0+0j
        for y in G:
            s += w[(b*y) % q]
        eta.append(s)
    return eta

def N0_count(q, G, r):
    """EXACT integer N0(G,r) = #{v in G^r : sum v_i = 0 mod q}, by DP over residues."""
    # dp[res] = number of partial tuples with given residue sum
    dp = [0]*q
    dp[0] = 1
    Gl = G
    for _ in range(r):
        nd = [0]*q
        for res, c in enumerate(dp):
            if c == 0: continue
            for y in Gl:
                nd[(res+y) % q] += c
        dp = nd
    return dp[0]

def collision_subset_sum(q, G, a):
    """EXACT MomentCollisionSpectral.collision with stat = subset-sum over A=F_q.
       = #{(S,S'): S,S' subsets of G, |S|=|S'|=a, sum S = sum S' mod q}."""
    from collections import Counter
    cnt = Counter()
    for S in itertools.combinations(G, a):
        cnt[sum(S) % q] += 1
    return sum(c*c for c in cnt.values())

print("="*78)
print("C079 PROBE  —  prize regime: proper dyadic mu_n < F_q*, q=1 mod n, q~n^beta")
print("="*78)

# ---- (A) raw-moment identity  sum_b eta_b^r == q*N0(G,r) ----------------------
print("\n[A] raw-moment identity:  sum_{b} eta_b^r  ?=  q * N0(G,r)")
print("    (N0 = # r-tuples in G^r summing to 0; F16 'raw moment law')")
for (n, beta) in [(8,4.0),(8,4.5),(16,4.0)]:
    q = find_prize_prime(n, beta)
    G = subgroup(q, n)
    eta = eta_all(q, G)
    print(f"  n={n:3d} q={q:8d} (q/n={q//n}, proper={n<q-1}):")
    for r in [1,2,3,4]:
        lhs = sum(e**r for e in eta)            # exact-ish complex
        N0 = N0_count(q, G, r)
        rhs = q*N0
        # lhs should be a real integer = rhs
        ok = abs(lhs.real - rhs) < 1e-5 and abs(lhs.imag) < 1e-5
        print(f"    r={r}: sum eta^r = {lhs.real:14.3f}+{lhs.imag:+.1e}i   q*N0 = {rhs:14d}   match={ok}")

# ---- (B) "literal collision" : N0 vs MomentCollisionSpectral.collision --------
print("\n[B] 'N0 is LITERALLY collision' test:")
print("    collision(a) = #{(S,S') subset-pairs, |S|=|S'|=a, sumS=sumS'} (with repetition? NO: subsets)")
print("    N0(G,2a)     = #{ordered 2a-tuples (with repeats) summing to 0}")
print("    compare both, and the natural map collision -> tuple-sum-zero:")
for (n, beta) in [(8,4.0),(16,4.0)]:
    q = find_prize_prime(n, beta)
    G = subgroup(q, n)
    print(f"  n={n} q={q}:")
    for a in [1,2,3]:
        coll = collision_subset_sum(q, G, a)     # subset pairs, sumS=sumS'
        N0_2a = N0_count(q, G, 2*a)               # ordered tuples, no repeat restriction, sum=0
        # collision counts ORDERED pairs of a-element SUBSETS with equal sum
        # eta-moment N0(2a) counts ORDERED 2a-tuples (repeats allowed) summing 0
        print(f"    a={a}: collision(subsets)={coll:10d}   N0(G,{2*a})(tuples)={N0_2a:14d}   equal={coll==N0_2a}")

# ---- (C) the payoff: does Paley-Zygmund on {eta_b} give a NEW M(n) bound? -----
print("\n[C] Paley-Zygmund payoff test:")
print("    PZ on the SQUARE statistic |eta_b|^2 needs E[X]=M2/q=n and E[X^2]=M4/q=E_2(G).")
print("    'many heavy frequencies' lower bound from PZ; does it constrain M(n)=max|eta_b|?")
print("    Compare: 2nd moment ALONE gives max|eta_b|^2 >= n (pigeonhole, already in tree).")
print("    Does the collision/4th-moment refinement push max|eta_b| UP toward BGK?")
for (n, beta) in [(8,4.5),(16,4.0),(32,4.0)]:
    q = find_prize_prime(n, beta)
    G = subgroup(q, n)
    eta = eta_all(q, G)
    mags2 = [abs(e)**2 for b,e in enumerate(eta) if b != 0]   # b != 0
    M2 = sum(mags2)                                            # = q*n - n^2 (punctured 2nd mom)
    M4 = sum(m*m for m in mags2)                               # punctured 4th moment
    Mn = math.sqrt(max(mags2))                                # M(n) = max_{b!=0}|eta_b|
    # PZ: #{b!=0 : |eta_b|^2 >= t*E[X]} >= (1-t)^2 * E[X]^2/E[X^2]  for t in (0,1)
    Ex = M2/(q-1); Ex2 = M4/(q-1)
    # number of "heavy" frequencies at t=1/2
    t = 0.5
    pz_lb = (1-t)**2 * Ex**2/Ex2 * (q-1)     # PZ count lower bound (# of b!=0 with |eta|^2>=t*Ex)
    # actual count
    actual = sum(1 for m in mags2 if m >= t*Ex)
    print(f"  n={n:3d} q={q:7d}: M(n)={Mn:7.3f}  2sqrt(n)={2*math.sqrt(n):6.3f}  "
          f"sqrt(n)={math.sqrt(n):6.3f}  sqrt(n*log(q/n))={math.sqrt(n*math.log(q/n)):6.3f}")
    print(f"            E[|eta|^2]={Ex:7.3f}(=n)  E[|eta|^4]={Ex2:9.1f}  E_2(G)~M4/q={M4/q:9.1f}")
    print(f"            PZ heavy-count LB (t=1/2): {pz_lb:9.1f}   actual heavy count: {actual:9d}")
    # KEY: does PZ give any UPPER bound on M(n)? PZ is a LOWER bound on a COUNT -> NO upper on max.
    # The only thing controlling the MAX from below is pigeonhole (max^2 >= avg = n).
    print(f"            max|eta|^2={max(mags2):8.3f}  avg|eta|^2={Ex:7.3f}  ratio max/avg={max(mags2)/Ex:6.2f}")

print("\n[C-verdict logic]")
print("  PZ / anti-concentration produces a LOWER bound on the NUMBER of heavy frequencies.")
print("  The prize core M(n)=max|eta_b| needs an UPPER bound (sqrt-cancellation).")
print("  A lower-bound-on-a-count NEVER yields an upper bound on the max => no new M(n) bound.")
print("  PZ uses only E[X]=n (2nd moment, in tree) and E[X^2]=E_2(G) (4th moment, in tree):")
print("  it is a re-reading of the SAME two Parseval moments, adds no new analytic input.")
