#!/usr/bin/env python3
"""G95 probe: irreducible-cyclic-code weight-distribution dictionary vs the prize Gauss periods.

Checks, for dyadic toy instances (n = 8,16,32,64; p = 1 mod n, beta ~ 4):
  (P1) value multiset of {eta_b : b in F_p^*}: exactly m = (p-1)/n distinct values, each multiplicity n
       (the maximally-many-valued theorem -- the anti-Schmidt-White orientation).
  (P2) irrationality / NO lattice quantization: min/max nearest-neighbor gaps of the distinct values,
       ratio spread; compare with what an integer-lattice (McEliece-quantized) distribution would force.
  (P3) power-sum integrality (the transferred "weights are integers" mechanism):
       P_r = sum over DISTINCT values v of v^r  is a rational integer, with
       n*P_r = p*N_r - n^r,  N_r = #{(x_1..x_r) in mu_n^r : sum = 0}.  Report v_2(P_r) pattern.
  (P4) the extension-field CONTRAST (semiprimitive two-valued collapse): F_16 / index 5 (2^2 = -1 mod 5)
       periods take exactly 2 distinct values -- the regime ALL exact literature evaluations live in,
       and which (P1) proves impossible over the prime field.
  (P5) does quantization alone force M >= c sqrt(n log p)? measure M, Parseval floor, and the
       "distinct-values + L2 mass" lower bound max^2 >= (p-n)/m  (= Parseval floor; distinctness adds
       no archimedean gain -- honest negative).
"""
import math, cmath
from fractions import Fraction

def is_prime(x):
    if x < 2: return False
    for q in range(2, int(x**0.5)+1):
        if x % q == 0: return False
    return True

def good_prime(n, beta=4.0):
    # smallest p = 1 mod n with v2(p-1) = v2(n) (prize-representative) and p ~ n^beta
    target = int(n**beta)
    p = (target // n) * n + 1
    while True:
        if is_prime(p) and ((p-1)//n) % 2 == 1 or True:
            # require v2(p-1) == log2(n): (p-1)/n odd
            if is_prime(p) and ((p-1)//n) % 2 == 1:
                return p
        p += n

def subgroup(n, p):
    # mu_n subset F_p^*: solutions of x^n = 1; via generator
    g = None
    for cand in range(2, p):
        # check cand is a generator (p small)
        ord_ok = True
        for q in set(factorize(p-1)):
            if pow(cand, (p-1)//q, p) == 1:
                ord_ok = False; break
        if ord_ok:
            g = cand; break
    h = pow(g, (p-1)//n, p)
    G = set()
    x = 1
    for _ in range(n):
        G.add(x); x = (x*h) % p
    assert len(G) == n
    return sorted(G), g

def factorize(x):
    fs = []
    d = 2
    while d*d <= x:
        while x % d == 0:
            fs.append(d); x //= d
        d += 1
    if x > 1: fs.append(x)
    return fs

def periods(n, p, G):
    """exact-ish eta_b for all b; also exact power sums via integer counting."""
    etas = {}
    for b in range(1, p):
        s = 0.0
        for x in G:
            s += math.cos(2*math.pi*((b*x) % p)/p)
        # imaginary part vanishes for -1 in G; keep real
        etas[b] = s
    return etas

def N_r(G, p, r):
    """#{(x_1..x_r) in G^r : sum = 0 mod p} by DP over Z/p."""
    from collections import defaultdict
    cnt = {0: 1}
    for _ in range(r):
        nxt = defaultdict(int)
        for s, c in cnt.items():
            for x in G:
                nxt[(s+x) % p] += c
        cnt = nxt
    return cnt.get(0, 0)

def main():
    print("=== G95 dictionary probe ===")
    for n in [8, 16, 32, 64]:
        p = good_prime(n)
        G, g = subgroup(n, p)
        m = (p-1)//n
        etas = periods(n, p, G)
        vals = sorted(etas.values())
        # group values with tolerance
        tol = 5e-10 * max(1.0, max(abs(v) for v in vals))
        groups = []
        cur = [vals[0]]
        for v in vals[1:]:
            if v - cur[-1] < tol:
                cur.append(v)
            else:
                groups.append(cur); cur = [v]
        groups.append(cur)
        mults = [len(gp) for gp in groups]
        distinct = [sum(gp)/len(gp) for gp in groups]
        M = max(abs(v) for v in vals)
        # nearest-neighbor gaps among distinct values
        gaps = [distinct[i+1]-distinct[i] for i in range(len(distinct)-1)]
        mn_gap, mx_gap = min(gaps), max(gaps)
        # power sums over distinct values
        P1 = sum(distinct); P2 = sum(v*v for v in distinct)
        # exact via counting
        N2 = N_r(G, p, 2); N3 = N_r(G, p, 3); N4 = N_r(G, p, 4)
        P2_exact = (p*N2 - n**2)//n
        P3_exact = (p*N3 - n**3)//n
        P4_exact = (p*N4 - n**4)//n
        floor = math.sqrt(n*(p-n)/(p-1))
        prize = math.sqrt(n*math.log(p/n))
        print(f"\n n={n} p={p} m={m}  (beta={math.log(p)/math.log(n):.2f})")
        print(f"  #distinct values = {len(groups)}  (predicted m = {m}): {'OK' if len(groups)==m else 'FAIL'}")
        print(f"  multiplicities: min={min(mults)} max={max(mults)} (predicted n = {n}): "
              f"{'OK' if set(mults)=={n} else 'FAIL'}")
        print(f"  P1 = {P1:+.6f} (predicted -1)   P2 = {P2:.4f} (predicted p-n = {p-n}, exact {P2_exact})")
        print(f"  P3 exact = {P3_exact} (v2 = {v2(P3_exact)}), P4 exact = {P4_exact} (v2 = {v2(P4_exact)});"
              f" N2={N2} (pred n), N3={N3}, N4={N4}")
        print(f"  M = {M:.4f};  Parseval floor sqrt(n(p-n)/(p-1)) = {floor:.4f};  sqrt(n log(p/n)) = {prize:.4f}")
        print(f"  distinct-value gaps: min = {mn_gap:.3e}, max = {mx_gap:.3e}, spread = {mx_gap/mn_gap:.1f}x")
        print(f"  lattice test: if values lay in a+d*Z, d <= min gap; span/min_gap = "
              f"{(distinct[-1]-distinct[0])/mn_gap:.1f} but #values-1 = {len(distinct)-1} "
              f"=> lattice would need span >= (m-1)*d: {'consistent only if gaps ~equal; spread says NO' if mx_gap/mn_gap > 3 else 'ambiguous'}")

    # (P4) extension-field contrast: F_16, subgroup of index 5 (order 3), semiprimitive 2^2 = -1 mod 5
    print("\n=== (P4) extension-field contrast: F_16, index-5 subgroup (semiprimitive) ===")
    # F_16 = F_2[t]/(t^4+t+1); elements as 4-bit ints; multiplication via carryless mod poly 0b10011
    def gf16_mul(a, b):
        r = 0
        for i in range(4):
            if (b >> i) & 1:
                r ^= a << i
        for i in range(7, 3, -1):
            if (r >> i) & 1:
                r ^= 0b10011 << (i-4)
        return r
    # generator: t = 2
    elems = []
    x = 1
    for _ in range(15):
        elems.append(x); x = gf16_mul(x, 2)
    assert len(set(elems)) == 15
    # subgroup of order 3: powers of g^5
    H = [1]
    h = elems[4]  # g^5 is elems[4]? elems[0]=g^1... careful: elems[0]=1? no
    # rebuild: elems[i] = g^i with elems[0] = 1
    elems = [1]
    x = 2
    for _ in range(14):
        elems.append(x); x = gf16_mul(x, 2)
    h = elems[5]
    H = [1, h, gf16_mul(h, h)]
    # trace F_16 -> F_2: Tr(x) = x + x^2 + x^4 + x^8
    def gf16_pow(a, k):
        r = 1
        for _ in range(k): r = gf16_mul(r, a)
        return r
    def tr(x):
        return (x ^ gf16_pow(x, 2) ^ gf16_pow(x, 4) ^ gf16_pow(x, 8)) & 1
    # periods eta_b = sum_{x in H} (-1)^{Tr(bx)} for b in F_16^*
    per = {}
    for b in elems:
        s = sum((-1)**tr(gf16_mul(b, x)) for x in H)
        per[b] = s
    dv = sorted(set(per.values()))
    from collections import Counter
    cnt = Counter(per.values())
    print(f"  F_16, |H| = 3, index 5: distinct period values = {dv} with multiplicities {dict(cnt)}")
    print(f"  => {len(dv)} distinct values over 5 cosets: two-valued collapse = "
          f"{'CONFIRMED (semiprimitive; Frobenius identifies cosets)' if len(dv) == 2 else 'NOT seen'}")

def v2(x):
    x = abs(x)
    if x == 0: return 'inf'
    k = 0
    while x % 2 == 0:
        x //= 2; k += 1
    return k

main()
