"""
C096 attack: "twisted-inversion folds the worst-line search mod an involution
-> worst monomial direction is FORCED self-dual (fixed point of (a,b)->(-a,-b))."

Setup (PRIZE-FLAVORED, proper subgroup):
  - dyadic mu_n, n = 2^mu, a PROPER subgroup of F_q*, q prime == 1 mod n, q ~ n^beta.
  - RS code on the eval domain = mu_n (the subgroup), degree < k.
  - Monomial line directions: u1 = x^b, offset u0 = x^a (monomials), a,b in Z/n indexing.
    Actually we sweep ALL pairs (a,b) of monomial *evaluations* on mu_n.
  - far-line / bad-scalar count = explainableScalars count:
        #{ gamma in F_q : exists codeword agreeing with u0 + gamma*u1 on >= (1-delta)*n coords }.

What C096 ASSERTS (the load-bearing step in attack_plan):
  (a) badcount is invariant under  dilation x->g*x  (proven in-tree)         -> Z/n symmetry on (a,b)
  (b) badcount is invariant under  twisted inversion (GRS-duality involution) -> involution (a,b)->(k-1-a? / -a,-b)
  (c) THEREFORE the worst (max badcount) direction is a FIXED POINT of the involution (self-dual line).

We test (a),(b) exactly (must hold = the in-tree theorems), then test (c):
  Is the argmax of badcount necessarily a fixed point of the involution? If a NON-self-dual
  direction attains the max, claim (c) is REFUTED (symmetry does not force the max to a fixed pt).
"""
import sys
from itertools import combinations, product

def find_subgroup_prime(n, beta_lo=4.0, beta_hi=5.5):
    """Find prime q == 1 mod n with q ~ n^beta, beta in [beta_lo, beta_hi]."""
    lo = int(n**beta_lo); hi = int(n**beta_hi)
    # search q = 1 + n*t
    import sympy
    t = lo // n
    while True:
        q = 1 + n*t
        if q > hi: return None
        if sympy.isprime(q):
            return q
        t += 1

def main(n, beta_lo, beta_hi, k, delta_num, delta_den, max_dirs=None, verbose=True):
    import sympy
    q = find_subgroup_prime(n, beta_lo, beta_hi)
    if q is None:
        print(f"no prime for n={n} in beta range"); return
    # generator of F_q*, then g0 = generator of the order-n subgroup
    gF = sympy.primitive_root(q)
    g0 = pow(gF, (q-1)//n, q)            # order-n element
    mu = [pow(g0, i, q) for i in range(n)]  # subgroup elements; index i -> g0^i
    assert len(set(mu)) == n
    assert pow(g0, n, q) == 1

    # eval domain = mu (index i in 0..n-1 holds point mu[i] = g0^i).
    # RS codewords: polynomials of degree < k, evaluated on mu.
    # A monomial direction u_e = (x^e for x in mu) = mu[i]^e ; as i-vector: mu[(i*e)%? ] no:
    #   mu[i]^e = (g0^i)^e = g0^(i*e) = mu[(i*e) % n].  So x^e on the subgroup is just a CYCLIC
    #   reindex of the all-ones? No: mu[i]^e = g0^(i*e mod n). So the vector x^e is determined by e mod n.
    # Thus monomial directions are indexed by e in Z/n. Good (matches "n monomial directions").
    def monvec(e):
        e = e % n
        return tuple(pow(mu[i], e, q) for i in range(n))   # = g0^(i*e mod n)

    # witness threshold: agreement on >= ceil((1-delta)*n) coords.
    # delta = delta_num/delta_den.
    need = -(-( (delta_den-delta_num)*n) // delta_den)   # ceil((1-delta)*n) integer
    need = max(need, k)  # any k coords determine a unique deg<k poly; below k everything agrees -> trivial

    # Precompute: for each subset S of size in {need, ..., n}, the codeword that could match.
    # For a far line u0 + gamma*u1 to agree with SOME codeword on S (|S|>=need>=k means at most one poly),
    # we just need: does the restriction to S interpolate a degree<k polynomial?
    # Equivalent: pick any k coords in S, interpolate, check it matches on all of S.
    subsets = [S for r in range(need, n+1) for S in combinations(range(n), r)]

    pts = mu  # evaluation points by index

    from functools import lru_cache
    # Lagrange / Vandermonde solve over F_q for given k points -> coeffs, then eval.
    def interp_and_check(vals_on_S, S):
        # vals_on_S: dict index->value. S sorted. Need |S|>=k.
        Sl = list(S)
        # build poly via Newton/Vandermonde on first k points, then verify on the rest.
        base = Sl[:k]
        # Vandermonde solve
        # matrix M[r][c] = pts[base[r]]^c, r,c in 0..k-1 ; solve M coeff = y
        M = [[pow(pts[base[r]], c, q) for c in range(k)] for r in range(k)]
        y = [vals_on_S[base[r]] for r in range(k)]
        coeff = gauss_solve(M, y, q)
        if coeff is None:
            return False
        for idx in Sl:
            ev = 0
            xp = 1
            for c in range(k):
                ev = (ev + coeff[c]*xp) % q
                xp = (xp * pts[idx]) % q
            if ev != vals_on_S[idx]:
                return False
        return True

    def gauss_solve(M, y, mod):
        M = [row[:] + [y[r]] for r, row in enumerate(M)]
        m = len(M); ncol = len(M[0])-1
        r = 0
        for c in range(ncol):
            piv = None
            for rr in range(r, m):
                if M[rr][c] % mod != 0:
                    piv = rr; break
            if piv is None: return None
            M[r], M[piv] = M[piv], M[r]
            inv = pow(M[r][c], mod-2, mod)
            M[r] = [(x*inv) % mod for x in M[r]]
            for rr in range(m):
                if rr != r and M[rr][c] % mod != 0:
                    f = M[rr][c]
                    M[rr] = [(a - f*b) % mod for a, b in zip(M[rr], M[r])]
            r += 1
            if r == m: break
        return [M[i][ncol] for i in range(ncol)]

    def line_explainable_on_S(u0, u1, gamma, S):
        vals = {i: (u0[i] + gamma*u1[i]) % q for i in S}
        return interp_and_check(vals, S)

    def badcount(a, b):
        """worst-line bad-scalar count for direction u0=x^a, u1=x^b."""
        u0 = monvec(a); u1 = monvec(b)
        cnt = 0
        for gamma in range(q):
            ok = False
            for S in subsets:
                if line_explainable_on_S(u0, u1, gamma, S):
                    ok = True; break
            if ok: cnt += 1
        return cnt

    # ---- This is expensive (q can be large). Keep n small (8) and beta moderate. ----
    dirs = [(a, b) for a in range(n) for b in range(n)]
    if max_dirs:
        dirs = dirs[:max_dirs]

    print(f"n={n} q={q} (q/n^? : beta={ (q.bit_length()/n.bit_length()):.2f} log2), k={k}, "
          f"delta={delta_num}/{delta_den}, need={need} agree-coords, |subsets|={len(subsets)}, q scalars")
    print(f"  mu_n is a PROPER subgroup: n={n} | q-1={q-1}, index={ (q-1)//n }")

    bc = {}
    for (a, b) in dirs:
        bc[(a, b)] = badcount(a, b)

    # ---- (a) dilation invariance: x->g0*x permutes mu by index shift i->i+1.
    #      On monomial x^e: dilation sends x^e -> (g0 x)^e = g0^e x^e = scalar * x^e.
    #      Scalar*direction: u1 -> c*u1 just rescales gamma; badcount invariant. Also u0->c*u0 is an offset
    #      change. The DIRECTION index (a,b) is *unchanged* by dilation (monomials are dilation eigenvectors).
    #      So Z/n acts trivially on monomial (a,b) labels -> dilation gives NO reduction among monomials.
    #      (This is already a crack in the plan; record it.)

    # ---- (b) twisted inversion: x->1/x on mu permutes index i->-i; on x^e -> x^{-e}.
    #      So the involution on monomial labels is (a,b) -> (-a, -b) mod n.  Test invariance:
    inv_ok = True
    for (a, b) in dirs:
        if bc[(a, b)] != bc[((-a) % n, (-b) % n)]:
            inv_ok = False
    print(f"(b) twisted-inversion invariance (a,b)->(-a,-b): {'HOLDS' if inv_ok else 'FAILS'}")

    # ---- (c) THE CLAIM: is the argmax a fixed point of the involution?  Fixed pts: (-a,-b)==(a,b)
    #      i.e. 2a==0 and 2b==0 mod n  -> a,b in {0, n/2}.  (the 'self-dual' set)
    mx = max(bc.values())
    argmax = [d for d in dirs if bc[d] == mx]
    def is_fixed(d):
        a, b = d
        return ( (2*a) % n == 0 ) and ( (2*b) % n == 0 )
    fixed_argmax = [d for d in argmax if is_fixed(d)]
    nonfixed_argmax = [d for d in argmax if not is_fixed(d)]
    print(f"max badcount = {mx} over {len(dirs)} monomial directions")
    print(f"  #argmax dirs = {len(argmax)};  self-dual(fixed) among them = {len(fixed_argmax)}; "
          f"NON-self-dual among them = {len(nonfixed_argmax)}")
    print(f"  argmax sample: {argmax[:8]}")
    if nonfixed_argmax:
        print(f"  *** A NON-SELF-DUAL direction attains the max: {nonfixed_argmax[:5]} ***")
        print(f"  => claim (c) 'worst direction FORCED self-dual' is REFUTED at n={n}, q={q}.")
    else:
        print(f"  all argmax dirs are self-dual at n={n}, q={q} (consistent with (c) here)")
    # full table if small
    if verbose and n <= 8:
        print("  badcount table (rows a=0..n-1, cols b=0..n-1):")
        for a in range(n):
            print("   ", [bc[(a, b)] for b in range(n)])
    return mx, argmax, nonfixed_argmax

if __name__ == "__main__":
    # n=8, proper subgroup, q ~ n^4..n^5 (n=8 -> q in [4096, 32768]); pick beta so q stays small enough
    # to sweep all q scalars. n=8 with q~8^4=4096 .. keep it tractable.
    main(n=8, beta_lo=4.0, beta_hi=4.6, k=2, delta_num=1, delta_den=2)
