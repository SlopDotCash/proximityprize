"""
C025 follow-up: in the ACTUAL prize regime (p ~ n^beta, beta=4-5, proper subgroup, FAR below
the (n/2*|A|^2)^(n/2) threshold), does the char-p surplus e2=0 layer survive at a PRODUCTION
dim |A| = 2 mod 4 ?  If yes, the parity/threshold kill is SILENT exactly where the prize lives.

This is the decisive prize-relevance test: the parity law only empties the char-0 layer;
the threshold theorem only transfers char-0 emptiness to char-p ABOVE its threshold. Below
the threshold (= the whole prize regime) the char-p layer is governed by the BGK/antipodal
wall, NOT by parity. We check whether |A|=2 mod 4 production subsets with e2=0, e1!=0 exist
at a real prize-regime proper-subgroup prime.
"""
import itertools
from sympy import isprime, primitive_root

def find_prime_with_subgroup(n, beta_lo, beta_hi):
    lo = int(n ** beta_lo); hi = int(n ** beta_hi)
    p = lo - (lo % n) + 1
    if p < lo: p += n
    while p <= hi:
        if isprime(p) and (p - 1) % n == 0 and n < p - 1:
            return p
        p += n
    return None

def primitive_2m_root(p, n):
    gr = primitive_root(p)
    g = pow(gr, (p - 1) // n, p)
    assert pow(g, n, p) == 1 and pow(g, n // 2, p) != 1
    return g

def scan_production_dim(m, beta_lo, beta_hi, asize, max_subsets=400000):
    n = 1 << m
    p = find_prime_with_subgroup(n, beta_lo, beta_hi)
    if p is None:
        print(f"  m={m} n={n}: no proper-subgroup prime in n^[{beta_lo},{beta_hi}]")
        return
    g = primitive_2m_root(p, n)
    beta = __import__("math").log(p, n)
    npairs = asize * (asize - 1) // 2
    parity = "ODD(2or3 mod4)" if npairs % 2 else "even(0or1 mod4)"
    # |A| mod 4
    amod4 = asize % 4
    # threshold for reference
    half = 1 << (m - 1)
    log2_thr = half * __import__("math").log2(half * asize * asize)
    log2_p = __import__("math").log2(p)
    zero = 0; zero_e1 = 0; checked = 0
    for S in itertools.combinations(range(n), asize):
        tot = 0
        for i in range(asize):
            for j in range(i + 1, asize):
                tot += pow(g, (S[i] + S[j]) % n, p)
        if tot % p == 0:
            zero += 1
            e1 = sum(pow(g, e, p) for e in S) % p
            if e1 != 0:
                zero_e1 += 1
        checked += 1
        if checked >= max_subsets:
            break
    print(f"  m={m} n={n} p={p} beta={beta:.2f} |A|={asize}(|A|%4={amod4}) pairs={npairs}({parity})")
    print(f"      log2(threshold)={log2_thr:.1f}  log2(p)={log2_p:.1f}  below-threshold={log2_p<log2_thr}")
    print(f"      e2=0 subsets={zero}, of those e1!=0 (REAL bad scalars)={zero_e1}  (checked {checked})")

if __name__ == "__main__":
    print("=== Prize-regime (proper subgroup, below threshold) PRODUCTION-DIM e2=0 census ===")
    # production dim: |A| = k+2 = 2 mod 4 (k=0 mod 4). smallest: |A|=6 (k=4).
    # m=4 (n=16): exhaustive over C(16,6)=8008 subsets, beta~4-5
    scan_production_dim(4, 4.0, 5.0, 6)
    # m=5 (n=32): |A|=6, C(32,6)=906192 subsets (cap)
    scan_production_dim(5, 4.0, 5.0, 6, max_subsets=906192)
    # m=4, larger production agreement |A|=10 (k=8, also 2 mod 4), C(16,10)=8008
    scan_production_dim(4, 4.0, 5.0, 10)
    # control: a NON-production dim |A|=4 (k=2, 0 mod... |A|%4=0 -> even pairs) to show the layer is generically nonempty
    print("  --- control (|A|%4=0, even pair count, NOT production dim) ---")
    scan_production_dim(4, 4.0, 5.0, 4)
