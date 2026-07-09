"""
C096 v2 -- corrected involution + non-degenerate regime.

KEY FIX over v1: the in-tree automorphism is the TWISTED inversion  M(u)(x) = x^{k-1} u(1/x)
(coefficient reversal / GRS duality), NOT plain x->1/x. On a degree-e monomial (e<k):
    M(x^e) = x^{k-1} (x^{-e}) = x^{k-1-e}.
So the GENUINE involution on monomial-direction labels is  e -> (k-1-e),  i.e. on a pair
direction (a,b) it is (a,b) -> (k-1-a, k-1-b)  (reflection through (k-1)/2),  NOT (-a,-b).

The "self-dual / fixed" set is then a == (k-1-a) mod n and b == (k-1-b) mod n.

We test, at PROPER-subgroup primes:
  TEST1: badcount invariant under the GENUINE involution (a,b)->(k-1-a,k-1-b)?  (sanity)
  TEST3: is the argmax FORCED to lie in the involution-fixed set?  (the C096 inference)

We work with monomial directions where the EVALUATION code is degree < k, and choose a
non-trivial radius delta so badcount is not saturated. We also include monomials of degree
>= k for u0/u1 indexing the direction *labels* a,b in 0..k-1 (the legitimate code-domain
degrees the duality acts on).
"""
from itertools import combinations
import math, sympy

def gauss_solve(M, y, mod):
    M = [row[:] + [y[r]] for r, row in enumerate(M)]
    m = len(M); ncol = len(M[0]) - 1
    r = 0
    for c in range(ncol):
        piv = next((rr for rr in range(r, m) if M[rr][c] % mod != 0), None)
        if piv is None: return None
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], mod - 2, mod)
        M[r] = [(x * inv) % mod for x in M[r]]
        for rr in range(m):
            if rr != r and M[rr][c] % mod != 0:
                f = M[rr][c]
                M[rr] = [(a - f * b) % mod for a, b in zip(M[rr], M[r])]
        r += 1
        if r == m: break
    return [M[i][ncol] for i in range(ncol)]

def run(n, q, k, delta):
    assert sympy.isprime(q) and (q - 1) % n == 0
    gF = sympy.primitive_root(q)
    g0 = pow(gF, (q - 1) // n, q)
    mu = [pow(g0, i, q) for i in range(n)]
    # check inversion-closed (needed for twisted inversion to permute the domain): mu is a group -> yes
    inv_closed = all(pow(x, q - 2, q) in set(mu) for x in mu)
    pts = mu
    dn, dd = delta
    need = max(math.ceil((dd - dn) * n / dd), k)
    subsets = [S for r in range(need, n + 1) for S in combinations(range(n), r)]

    def monvec(e):                      # x^e on mu : index i -> g0^(i*e)
        e %= n
        return tuple(pow(mu[i], e, q) for i in range(n))

    def interp_ok(vals, Sl):
        base = Sl[:k]
        M = [[pow(pts[base[r]], c, q) for c in range(k)] for r in range(k)]
        coeff = gauss_solve(M, [vals[base[r]] for r in range(k)], q)
        if coeff is None: return False
        for idx in Sl:
            ev = 0; xp = 1
            for c in range(k):
                ev = (ev + coeff[c] * xp) % q; xp = xp * pts[idx] % q
            if ev != vals[idx]: return False
        return True

    def badcount(a, b):
        u0 = monvec(a); u1 = monvec(b); cnt = 0
        for gamma in range(q):
            line = [(u0[i] + gamma * u1[i]) % q for i in range(n)]
            if any(interp_ok({i: line[i] for i in S}, list(S)) for S in subsets):
                cnt += 1
        return cnt

    # restrict labels to 0..k-1 (genuine code-degree directions the duality acts on),
    # plus we still vary over 0..n-1 to see the global argmax.
    bc = {(a, b): badcount(a, b) for a in range(n) for b in range(n)}

    invol = lambda a: (k - 1 - a) % n
    t1 = all(bc[(a, b)] == bc[(invol(a), invol(b))] for a in range(n) for b in range(n))
    is_fixed = lambda d: invol(d[0]) == d[0] and invol(d[1]) == d[1]

    mx = max(bc.values())
    argmax = [d for d in bc if bc[d] == mx]
    nonfixed = [d for d in argmax if not is_fixed(d)]
    # also exclude the trivial saturated band: report the max badcount value and whether saturated
    saturated = (mx == q)

    print(f"--- n={n} q={q} idx={(q-1)//n} (proper={n<q-1}, inv-closed={inv_closed}), "
          f"k={k}, delta={dn}/{dd}, need={need}/{n}, |subsets|={len(subsets)} ---")
    print(f"  TEST1 genuine twisted-inv invariance (a,b)->(k-1-a,k-1-b): {'HOLDS' if t1 else 'FAILS'}")
    print(f"  max badcount={mx} (saturated={saturated}); #argmax={len(argmax)}; "
          f"self-dual argmax={len([d for d in argmax if is_fixed(d)])}; NON-self-dual argmax={len(nonfixed)}")
    if nonfixed:
        print(f"  *** NON-self-dual maximizers: {sorted(nonfixed)[:6]} => forcing inference REFUTED ***")
    else:
        print(f"  argmax all self-dual here")
    if n <= 8:
        for a in range(n):
            print("    ", [bc[(a, b)] for b in range(n)])
    return t1, mx, nonfixed

if __name__ == "__main__":
    # non-degenerate radius: delta=3/8 (need=5 of 8) so badcount is NOT saturated.
    for q in [113, 257, 1153]:
        run(8, q, k=4, delta=(3, 8))
    print("==== n=4, k=3, delta=1/2 ====")
    for q in [1009, 1013]:
        run(4, q, k=3, delta=(1, 2))
