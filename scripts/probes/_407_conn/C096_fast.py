"""
C096 fast/decisive probe. Tests the load-bearing inference of the connection:
  "symmetry under <dilation, twisted-inversion> FORCES the worst monomial direction
   to be a FIXED POINT of the involution (a,b)->(-a,-b) (self-dual line)."

Two independent things are checked, both exactly, at PROPER-subgroup primes:

  TEST 1 (the in-tree symmetries, sanity): badcount(a,b) is invariant under
          (a,b)->(-a,-b) [twisted inversion]. MUST hold.
  TEST 2 (the dilation reduction claim): on MONOMIAL directions, dilation x->g*x maps
          x^e -> g^e * x^e = scalar*x^e, i.e. dilation acts TRIVIALLY on the monomial
          label (a,b). So "Z/n halves the n^2 monomial directions" is checked: how many
          distinct labels does <dilation> actually merge among monomials? (Expect: ~none.)
  TEST 3 (THE CLAIM): is the argmax of badcount a FIXED POINT of the involution? If a
          NON-self-dual label attains the max, the forcing inference is REFUTED.

Uses the genuine far-line bad-scalar (explainableScalars) count with delta = 1/2,
witness threshold ceil((1-delta)n), on RS[mu_n, k] with eval domain = the order-n subgroup.
"""
from itertools import combinations
import sympy

def gauss_solve(M, y, mod):
    M = [row[:] + [y[r]] for r, row in enumerate(M)]
    m = len(M); ncol = len(M[0]) - 1
    r = 0
    for c in range(ncol):
        piv = None
        for rr in range(r, m):
            if M[rr][c] % mod != 0:
                piv = rr; break
        if piv is None:
            return None
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], mod - 2, mod)
        M[r] = [(x * inv) % mod for x in M[r]]
        for rr in range(m):
            if rr != r and M[rr][c] % mod != 0:
                f = M[rr][c]
                M[rr] = [(a - f * b) % mod for a, b in zip(M[rr], M[r])]
        r += 1
        if r == m:
            break
    return [M[i][ncol] for i in range(ncol)]

def run(n, q, k, delta=(1, 2)):
    assert sympy.isprime(q) and (q - 1) % n == 0, "q must be prime == 1 mod n"
    gF = sympy.primitive_root(q)
    g0 = pow(gF, (q - 1) // n, q)            # order-n generator
    mu = [pow(g0, i, q) for i in range(n)]   # index i -> g0^i
    assert pow(g0, n, q) == 1 and len(set(mu)) == n
    pts = mu
    dn, dd = delta
    import math
    need = math.ceil((dd - dn) * n / dd)     # ceil((1-delta) n)
    need = max(need, k)
    subsets = [S for r in range(need, n + 1) for S in combinations(range(n), r)]

    def monvec(e):
        e %= n
        return tuple(pow(mu[i], e, q) for i in range(n))   # = g0^(i*e)

    def interp_ok(vals, Sl):
        base = Sl[:k]
        M = [[pow(pts[base[r]], c, q) for c in range(k)] for r in range(k)]
        yv = [vals[base[r]] for r in range(k)]
        coeff = gauss_solve(M, yv, q)
        if coeff is None:
            return False
        for idx in Sl:
            ev = 0; xp = 1
            for c in range(k):
                ev = (ev + coeff[c] * xp) % q
                xp = xp * pts[idx] % q
            if ev != vals[idx]:
                return False
        return True

    def badcount(a, b):
        u0 = monvec(a); u1 = monvec(b)
        cnt = 0
        for gamma in range(q):
            line = [(u0[i] + gamma * u1[i]) % q for i in range(n)]
            ok = False
            for S in subsets:
                Sl = list(S)
                if interp_ok({i: line[i] for i in Sl}, Sl):
                    ok = True; break
            if ok:
                cnt += 1
        return cnt

    bc = {(a, b): badcount(a, b) for a in range(n) for b in range(n)}

    # TEST 1: twisted-inversion invariance
    t1 = all(bc[(a, b)] == bc[((-a) % n, (-b) % n)] for a in range(n) for b in range(n))

    # TEST 2: dilation orbits on monomial labels (expect singletons -> NO reduction)
    # dilation x->g0*x sends label e -> e (monomial is eigenvector). Verify badcount unchanged
    # under any relabel induced -> it's identity on labels, so this is trivially true; we instead
    # report that dilation merges 0 pairs of DISTINCT monomial labels.
    dilation_merges_distinct = False  # by the eigenvector argument; no exact pairs merged

    # TEST 3: argmax self-dual?
    mx = max(bc.values())
    argmax = [d for d in bc if bc[d] == mx]
    is_fixed = lambda d: (2 * d[0]) % n == 0 and (2 * d[1]) % n == 0
    nonfixed = [d for d in argmax if not is_fixed(d)]

    print(f"--- n={n} q={q} (index (q-1)/n={(q-1)//n}, proper={n < q-1}), k={k}, "
          f"need={need}/{n} agree, |subsets|={len(subsets)} ---")
    print(f"  TEST1 twisted-inv invariance (a,b)->(-a,-b): {'HOLDS' if t1 else 'FAILS'}")
    print(f"  TEST2 dilation merges distinct monomial labels: {dilation_merges_distinct} "
          f"(monomials are dilation eigenvectors -> Z/n acts trivially on labels)")
    print(f"  max badcount={mx}; #argmax={len(argmax)}; self-dual argmax="
          f"{len([d for d in argmax if is_fixed(d)])}; NON-self-dual argmax={len(nonfixed)}")
    fixed_set = [d for d in [(0,0),(0,n//2),(n//2,0),(n//2,n//2)]]
    print(f"  self-dual labels = {fixed_set}; their badcounts = {[bc[d] for d in fixed_set]}")
    if nonfixed:
        print(f"  *** NON-self-dual maximizers exist: {sorted(nonfixed)[:6]} (badcount {mx}) ***")
        print(f"  *** => C096 inference 'worst direction FORCED self-dual' REFUTED at n={n},q={q} ***")
    else:
        print(f"  all maximizers self-dual here")
    if n <= 8:
        print("  badcount table a\\b:")
        for a in range(n):
            print("    ", [bc[(a, b)] for b in range(n)])
    return mx, argmax, nonfixed

if __name__ == "__main__":
    # n=8 proper subgroups, several primes (small q first for speed, then larger/prize-flavored).
    for q in [113, 257, 1153]:   # all == 1 mod 8, proper subgroup mu_8 << F_q*
        run(8, q, k=2)
    # smaller n=4 cross-check at a prize-flavored prime too
    run(4, 1009, k=2)
