import sys
from canon_badprimes import canon_bad
from math import log

def smallest_bad_and_height(n):
    det = canon_bad(n)
    A = abs(det)
    bits = A.bit_length()
    # smallest bad prime in the primitive-root lane: trial primes p ≡ 1 mod n, p | det
    p = n + 1
    smallest = None
    # simple primality
    def isp(m):
        if m < 2: return False
        i = 2
        while i*i <= m:
            if m % i == 0: return False
            i += 1
        return True
    cnt = 0
    while smallest is None and cnt < 200000:
        if isp(p) and A % p == 0:
            smallest = p
        p += n
        cnt += 1
    return smallest, bits

if __name__ == "__main__":
    for m in range(4, int(sys.argv[1]) + 1):
        n = 1 << m
        sm, bits = smallest_bad_and_height(n)
        lnmax_approx = bits * log(2)  # upper bound proxy for ln|Res|; per-prime height differs
        print(f"n={n:5d}  smallest_bad={sm}  (smallestPrime(1 mod n)?)  |Res| bits={bits}  ln|Res|/n={bits*log(2)/n:.3f}")
