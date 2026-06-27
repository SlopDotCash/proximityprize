import sys
from math import gcd

# Compute canonicalRatioBadPrimes(n) for n a power of two, n>=16:
#   f(X) = (X^4+1)^n - (X^2+1)^n,  Phi_n(X) = X^(n/2) + 1
#   Res(Phi_n, f) = ± det( mult-by-(f mod Phi_n) ) in Z[X]/(Phi_n),  Phi_n irreducible.
# Ring R = Z[X]/(X^d + 1), d = n/2 : negacyclic, X^d = -1.

def ring_mul(u, v, d):
    # negacyclic convolution length d:  X^d = -1
    res = [0]*d
    for i, ui in enumerate(u):
        if ui == 0:
            continue
        for j, vj in enumerate(v):
            if vj == 0:
                continue
            k = i + j
            if k < d:
                res[k] += ui*vj
            else:
                res[k-d] -= ui*vj
    return res

def ring_pow(base, e, d):
    result = [0]*d; result[0] = 1
    b = base[:]
    while e:
        if e & 1:
            result = ring_mul(result, b, d)
        e >>= 1
        if e:
            b = ring_mul(b, b, d)
    return result

def mult_matrix(g, d):
    # column j = coeffs of g * X^j mod X^d+1  (shift with sign wrap)
    cols = []
    cur = g[:]
    for j in range(d):
        cols.append(cur[:])
        # multiply cur by X:  new[k]=cur[k-1], new[0] = -cur[d-1]
        nxt = [0]*d
        nxt[0] = -cur[d-1]
        for k in range(1, d):
            nxt[k] = cur[k-1]
        cur = nxt
    # matrix M[i][j] = cols[j][i]
    return [[cols[j][i] for j in range(d)] for i in range(d)]

def bareiss_det(M):
    M = [row[:] for row in M]
    n = len(M); sign = 1; prev = 1
    for k in range(n-1):
        if M[k][k] == 0:
            sw = None
            for i in range(k+1, n):
                if M[i][k] != 0:
                    sw = i; break
            if sw is None:
                return 0
            M[k], M[sw] = M[sw], M[k]; sign = -sign
        for i in range(k+1, n):
            for j in range(k+1, n):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j])//prev
        prev = M[k][k]
    return sign*M[n-1][n-1]

def pollard_rho(n):
    if n % 2 == 0:
        return 2
    import random
    while True:
        x = random.randrange(2, n-1); y = x; c = random.randrange(1, n-1); d = 1
        while d == 1:
            x = (x*x + c) % n
            y = (y*y + c) % n; y = (y*y + c) % n
            d = gcd(abs(x-y), n)
        if d != n:
            return d

def is_prime(n):
    if n < 2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n % p == 0: return n == p
    d = n-1; r = 0
    while d % 2 == 0: d//=2; r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else:
            return False
    return True

def factor(n):
    n = abs(n); fac = {}
    def go(m):
        if m == 1: return
        if is_prime(m):
            fac[m] = fac.get(m,0)+1; return
        d = pollard_rho(m)
        go(d); go(m//d)
    # strip small primes first
    for p in range(2, 100000):
        while n % p == 0:
            fac[p] = fac.get(p,0)+1; n//=p
        if p*p > n: break
    go(n)
    return fac

def canon_bad(n):
    d = n//2
    # X^2+1 and X^4+1 as ring elements
    a = [0]*d; a[4 % d] += 1; a[0] += 1   # X^4+1 (4<d for n>=16 -> d>=8)
    b = [0]*d; b[2] += 1; b[0] += 1        # X^2+1
    A = ring_pow(a, n, d)
    B = ring_pow(b, n, d)
    g = [A[i]-B[i] for i in range(d)]
    M = mult_matrix(g, d)
    det = bareiss_det(M)
    return det

if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv)>1 else 64
    det = canon_bad(n)
    fac = factor(det)
    primes = sorted(fac)
    print(f"n={n}  |Res| has {len(str(abs(det)))} digits")
    print("prime factors:", primes)
    # primitive-root lane: primes p with n | p-1
    prim_lane = [p for p in primes if (p-1) % n == 0]
    print(f"primes with {n} | p-1 (primitive-root lane):", prim_lane)
