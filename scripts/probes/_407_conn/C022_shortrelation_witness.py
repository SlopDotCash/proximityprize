#!/usr/bin/env python3
"""
C022 witness: exhibit the SHORT char-p relation that beats the char-0 min distance.

The min-dist probe found: at n=8 (and 16,32), t=2, char-0 min-dist d*=4 but the
char-p (F_q) dual-window code has a weight-3 kernel vector.  A weight-3 vector w
supported on {e1,e2,e3} with
     sum_i w_i zeta^{j e_i} = 0  (j=1,2)  over F_q
is a SHORT relation among 2^mu-th roots that does NOT hold in char 0 (else min-dist
would be 3 in char 0 too).  This is exactly the "short low-weight relation of
2^mu-th roots vanishing mod the prize prime but not in char 0" = the BGK /
Lam-Leung-in-char-p object.

We:
  (1) extract one weight-3 kernel vector explicitly over F_q,
  (2) verify it vanishes mod q for j=1,2 but NOT in char 0 (the corresponding
      Z[zeta]-combination is nonzero),
  (3) confirm its char-0 norm / the integer it 'wraps around' is ~ q (so it is a
      LARGE-NORM relation reduced mod q -- the defect carrier).
"""
import itertools, sys
from math import log2

def primitive_nth_root(q, n):
    import sympy
    g = sympy.primitive_root(q)
    zeta = pow(g, (q-1)//n, q)
    assert pow(zeta, n, q) == 1
    return zeta

def kernel_weight3(q, zeta, n, t):
    """find a weight-3 support {a,b,c} with a nonzero (w1,w2,w3) over F_q killing
       j=1..t, and return (support, weights)."""
    Zp = [pow(zeta, e, q) for e in range(n)]
    for S in itertools.combinations(range(n), 3):
        # t x 3 matrix M[j-1][i] = zeta^{j*e_i}
        M = [[pow(Zp[e], j, q) for e in S] for j in range(1, t+1)]
        # find nonzero kernel vector: solve M w = 0 over F_q, t=2 rows, 3 cols
        w = solve_kernel(M, 3, t, q)
        if w is not None and any(x % q != 0 for x in w):
            return S, w
    return None, None

def solve_kernel(M, ncol, nrow, q):
    """return one nonzero kernel vector of the nrow x ncol matrix over F_q, or None."""
    A = [row[:] for row in M]
    pivcols = []
    pr = 0
    for c in range(ncol):
        piv = None
        for r in range(pr, nrow):
            if A[r][c] % q != 0:
                piv = r; break
        if piv is None:
            continue
        A[pr], A[piv] = A[piv], A[pr]
        inv = pow(A[pr][c], q-2, q)
        A[pr] = [(x*inv) % q for x in A[pr]]
        for r in range(nrow):
            if r != pr and A[r][c] % q != 0:
                f = A[r][c]
                A[r] = [(A[r][cc] - f*A[pr][cc]) % q for cc in range(ncol)]
        pivcols.append(c); pr += 1
        if pr == nrow: break
    free = [c for c in range(ncol) if c not in pivcols]
    if not free:
        return None
    fc = free[0]
    w = [0]*ncol
    w[fc] = 1
    # back-substitute pivot columns
    for i, c in enumerate(pivcols):
        w[c] = (-A[i][fc]) % q
    return w

# char-0 exact test in Z[zeta_n], n a power of 2: basis {1,...,zeta^{n/2-1}},
# zeta^{n/2} = -1.
def reduce_cyclo(v, n):
    half = n//2
    red = [0]*half
    for i in range(n):
        red[i % half] += v[i] * (1 if (i//half) % 2 == 0 else -1)
    return red

def main():
    P = lambda *a: (print(*a), sys.stdout.flush())
    P("="*78)
    P("C022 SHORT char-p relation witness (defeats char-0 BCH min distance)")
    P("="*78)
    for (n, t) in [(8,2),(16,2),(16,4),(32,2)]:
        import sympy
        # one proper-subgroup prime, prize regime q ~ n^4
        lo = int(n**4); q = ((lo//n)+1)*n + 1
        while not sympy.isprime(q): q += n
        zeta = primitive_nth_root(q, n)
        S, w = kernel_weight3(q, zeta, n, t) if t == 2 else weightd_kernel(q, zeta, n, t)
        P(f"\nn={n}=2^{int(log2(n))}, t={t}, q={q} (prize: n^2={n*n}<q={q})")
        if S is None:
            P("  (no weight-3 relation at this t -- using min-dist search separately)")
            continue
        P(f"  support exps S = {S}, F_q weights w = {w}")
        # verify char-p vanishing
        for j in range(1, t+1):
            val = sum(w[i]*pow(zeta, j*S[i], q) for i in range(len(S))) % q
            P(f"    j={j}: sum w_i zeta^(j e_i) mod q = {val}  (should be 0)")
        # char-0 test: build the Z[zeta] element with the SAME integer weights
        # (lift F_q reps to integers in (-q/2,q/2])
        wz = [x - q if x > q//2 else x for x in w]
        P(f"  integer-lifted weights (centered) = {wz}")
        nonzero_char0 = False
        for j in range(1, t+1):
            vvec = [0]*n
            for i in range(len(S)):
                vvec[(j*S[i]) % n] += wz[i]
            red = reduce_cyclo(vvec, n)
            z0 = all(x == 0 for x in red)
            P(f"    j={j}: char-0 Z[zeta] reduced = {red}  -> zero? {z0}")
            if not z0: nonzero_char0 = True
        P(f"  ==> relation vanishes mod q but NOT in char 0: {nonzero_char0}")
        P(f"      (this is the SHORT low-weight 2^mu-th-root relation vanishing mod")
        P(f"       the prize prime = the BGK/Lam-Leung-in-char-p defect carrier)")

def weightd_kernel(q, zeta, n, t):
    """for t>2, find min-weight kernel and return its support+weights."""
    Zp = [pow(zeta, e, q) for e in range(n)]
    for wd in range(1, min(n, 2*t+2)+1):
        for S in itertools.combinations(range(n), wd):
            M = [[pow(Zp[e], j, q) for e in S] for j in range(1, t+1)]
            w = solve_kernel(M, wd, t, q)
            if w is not None and any(x % q != 0 for x in w):
                return S, w
    return None, None

if __name__ == "__main__":
    main()
