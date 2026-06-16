"""
Probe for connection C016 (#407): "The exact genericity gap is the degree-collapse map d -> d mod n;
LovettUnionDegreesInjective is stated at the WRONG quotient for mu_n."

We test, with EXACT integer arithmetic at PROPER-SUBGROUP large primes (prize regime n << sqrt(q)):

  (claim 1) The generalized-Vandermonde minor det[ pts_i^{degs_j} ] with pts a FULL n-element
            generating set of mu_n (a primitive root + powers, M i j = zeta^(e_j * i)) is nonzero
            IFF the exponents e_j are pairwise distinct MOD n. (matches genVandermonde_rootsOfUnity_det_ne_zero_iff)

  (claim 2) The IN-TREE Lovett residual condition is "distinct AS NATURALS" of vAbs(V_i)+e.
            For mu_n the faithful condition is "distinct MOD n". So the gap is exactly d -> d % n.
            We exhibit configs that ARE distinct-as-naturals but NOT distinct-mod-n -> det = 0
            on a full mu_n point set. (The _wf407_nvm.lean countermodel uses a 3-pt SUBSET that
            happens to lie in mu_4, conflating "mod n" with "mod n/gcd"; we check the cleaner
            full-mu_n statement.)

  (claim 3 / honesty test) Does pinning the mod-n condition WIN anything for the prize?
            We check whether the determinant value (modulus, the prize quantity B) carries any
            info beyond the 0/nonzero dichotomy. The nonvanishing criterion is ALGEBRAIC/0-1;
            the prize floor B = max|eta_b| is ARCHIMEDEAN. So even the corrected mod-n condition
            is silent on B. (W-genericity wall: the NVM statement is the wrong category.)
"""

import itertools, math

def find_prime_with_subgroup(n, beta_lo=4, beta_hi=6, max_tries=200000):
    """Find a prime q == 1 mod n with n << sqrt(q), i.e. q ~ n^beta, beta in [beta_lo, beta_hi]."""
    target_lo = n**beta_lo
    target_hi = n**beta_hi
    # q = 1 + k*n
    k0 = max(1, target_lo // n)
    q = 1 + k0 * n
    tries = 0
    while q <= target_hi and tries < max_tries:
        if is_prime(q):
            return q
        q += n
        tries += 1
    return None

def is_prime(m):
    if m < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % p == 0:
            return m == p
    d = m - 1; r = 0
    while d % 2 == 0:
        d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x == 1 or x == m-1: continue
        for _ in range(r-1):
            x = (x*x) % m
            if x == m-1: break
        else:
            return False
    return True

def primitive_nth_root(q, n):
    """A primitive n-th root of unity zeta in F_q (q == 1 mod n)."""
    assert (q-1) % n == 0
    cof = (q-1)//n
    for g in range(2, q):
        z = pow(g, cof, q)
        # check primitive order n
        if z == 1: continue
        ok = True
        # zeta^(n/p) != 1 for each prime p | n
        for p in prime_factors(n):
            if pow(z, n//p, q) == 1:
                ok = False; break
        if ok:
            return z
    raise RuntimeError("no primitive root found")

def prime_factors(n):
    fs = set(); d = 2
    while d*d <= n:
        while n % d == 0:
            fs.add(d); n//=d
        d += 1
    if n > 1: fs.add(n)
    return fs

def det_mod(M, q):
    """Exact determinant mod q (Bareiss / fraction-free over F_q via Gaussian elim)."""
    M = [row[:] for row in M]
    n = len(M)
    det = 1
    for col in range(n):
        piv = None
        for r in range(col, n):
            if M[r][col] % q != 0:
                piv = r; break
        if piv is None:
            return 0
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            det = (-det) % q
        inv = pow(M[col][col], q-2, q)
        det = (det * M[col][col]) % q
        for r in range(col+1, n):
            f = (M[r][col] * inv) % q
            if f:
                for c in range(col, n):
                    M[r][c] = (M[r][c] - f*M[col][c]) % q
    return det % q

def full_minor_det(zeta, exps, q, n):
    """det of M[i][j] = zeta^(exps[j]*i), i over Fin n, j over the chosen exps (len n)."""
    M = [[pow(zeta, (exps[j]*i) % (q-1), q) for j in range(len(exps))] for i in range(n)]
    return det_mod(M, q)

def report(n):
    q = find_prime_with_subgroup(n)
    if q is None:
        print(f"  n={n}: no prime found in range"); return
    beta = math.log(q)/math.log(n)
    zeta = primitive_nth_root(q, n)
    print(f"\n=== n={n}, q={q} (q ~ n^{beta:.2f}, proper subgroup, n<<sqrt(q)={n < math.isqrt(q)}) ===")
    # CLAIM 1: full mu_n minor nonzero IFF exps distinct mod n
    # sample many strictly-increasing exponent vectors (as naturals), record det==0 vs distinct-mod-n.
    import random
    random.seed(12345)
    mismatch = 0; total = 0; collapse_naturals_distinct = 0
    examples = []
    for _ in range(3000):
        # pick n distinct-AS-NATURALS exponents from [0, 3n)
        pool = random.sample(range(0, 3*n), n)
        exps = sorted(pool)  # strictly increasing naturals
        distinct_mod_n = len(set(e % n for e in exps)) == n
        det = full_minor_det(zeta, exps, q, n)
        nonzero = (det != 0)
        total += 1
        if nonzero != distinct_mod_n:
            mismatch += 1
        if (not distinct_mod_n) and (det == 0):
            collapse_naturals_distinct += 1
            if len(examples) < 3:
                examples.append((exps, [e%n for e in exps]))
    print(f"  CLAIM1 (det!=0 <=> distinct mod n): {total-mismatch}/{total} agree, {mismatch} mismatch")
    print(f"  CLAIM2 (distinct-as-naturals but NOT mod-n => det=0): {collapse_naturals_distinct} such configs found")
    for ex in examples:
        print(f"     example exps(naturals, all distinct)={ex[0]}  ->  mod {n}={ex[1]}  => det=0 (collapse)")
    return q, zeta

# CLAIM 3 (honesty): the corrected mod-n NVM is still 0/1, silent on B = max|eta_b|.
def claim3_archimedean(n):
    q = find_prime_with_subgroup(n)
    zeta = primitive_nth_root(q, n)
    g = None
    for cand in range(2, q):
        if is_prime(q) and pow(cand,(q-1)//2,q)!=1:  # ensure generator-ish; just need a generator of F_q*
            # check order
            ok=True
            for p in prime_factors(q-1):
                if pow(cand,(q-1)//p,q)==1: ok=False;break
            if ok: g=cand; break
    # mu_n = {zeta^j}
    mu = [pow(zeta, j, q) for j in range(n)]
    # additive character psi(x) = e^{2pi i x / q}; eta_b = sum_{y in mu_n} psi(b*y)
    B = 0.0
    import cmath
    for b in range(1, q):
        s = sum(cmath.exp(2j*math.pi*((b*y) % q)/q) for y in mu)
        B = max(B, abs(s))
    sqrtn = math.sqrt(n)
    print(f"\n=== CLAIM3 honesty: n={n}, q={q} ===")
    print(f"  B = max_b |eta_b| = {B:.4f},  sqrt(n)={sqrtn:.4f},  B/sqrt(n)={B/sqrtn:.4f}")
    print(f"  (full mu_n Vandermonde det is NONZERO -- distinct mod n trivially -- yet B varies;")
    print(f"   the nonvanishing 0/1 criterion is BLIND to this archimedean modulus B = the prize floor.)")

if __name__ == "__main__":
    for n in (8, 16, 32):
        report(n)
    for n in (8, 16):
        claim3_archimedean(n)
