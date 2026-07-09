"""
C025 decisive test: BELOW the threshold (prize regime), parity is a CHAR-0 argument and gives
NO obstruction to a char-p surplus e2=0. Does the char-p surplus layer at a PRODUCTION dim
(|A| = 2 mod 4, odd pair count) actually appear at some prize-regime prime?

If YES at even ONE proper-subgroup prime below threshold -> the parity kill is genuinely
SILENT in the prize regime (it governs only the char-0 layer / above-threshold primes).

We sweep many proper-subgroup primes p = 1 mod n in n^[4,5], n=16, |A|=6 (k=4, production),
counting subsets with e2(A,g)=0, e1!=0 (REAL depth-1 bad scalars at agreement k+2).
"""
import itertools
from sympy import isprime, primitive_root
import math

def primitive_2m_root(p, n):
    gr = primitive_root(p)
    g = pow(gr, (p - 1) // n, p)
    assert pow(g, n, p) == 1 and pow(g, n // 2, p) != 1
    return g

def count_bad(m, p, asize):
    n = 1 << m
    g = primitive_2m_root(p, n)
    zero_e1 = 0; zero = 0
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
    return zero, zero_e1

if __name__ == "__main__":
    m = 4; n = 1 << m; asize = 6  # production dim |A|=6 = 2 mod 4
    half = 1 << (m - 1)
    log2_thr = half * math.log2(half * asize * asize)
    print(f"n={n}, production |A|={asize} (|A|%4=2, ODD pair count=15), log2(threshold)={log2_thr:.1f}")
    print("Sweeping proper-subgroup primes p=1 mod n in n^[4,5] (= [65536, 1048576]); all BELOW threshold:")
    print(f"  {'p':>10} {'beta':>6} {'log2 p':>8} {'#e2=0':>7} {'#bad(e1!=0)':>12}")
    lo, hi = int(n**4), int(n**5)
    p = lo - (lo % n) + 1
    if p < lo: p += n
    found_nonempty = False
    tested = 0
    while p <= hi and tested < 40:
        if isprime(p) and (p - 1) % n == 0 and n < p - 1:
            z, ze = count_bad(m, p, asize)
            beta = math.log(p, n)
            flag = "  <-- NONEMPTY char-p surplus!" if ze > 0 else ""
            print(f"  {p:>10} {beta:>6.2f} {math.log2(p):>8.1f} {z:>7} {ze:>12}{flag}")
            if ze > 0:
                found_nonempty = True
            tested += 1
        p += n
    print()
    print("RESULT:", "char-p surplus at production dim IS nonempty at some prize prime"
          if found_nonempty else
          "char-p surplus at production dim EMPTY at every prize prime swept "
          "(parity-aligned even below threshold)")
