#!/usr/bin/env python3
"""
C056 attack: "Schur vanishing h_{b-k}(x_S)=0 <=> esymm-fiber membership; multiplier
c=g^{b-a} is homogeneity degree of the controlling complete-homogeneous polynomial."

We attack the THREE legs of the claim at PRIZE-REGIME proper-subgroup dyadic primes
(n=2^mu a PROPER subgroup of F_q*, q prime = n^beta, beta~4-5, n << sqrt(q)):

  LEG 1 (residual ratio = h_{b-a} reduced).  For the monomial stack (x^a, x^b) and a
         (k+1)-subset S=T, the boundary residual ratio  gamma_T = -residual(x^b)/residual(x^a)
         equals  -[ X^b mod prod_{i in T}(X-x_i) ] expressed in the k-th-power column.
         Connection asserts: this controlling object is the complete-homogeneous
         h_{b-a}(x_T) (Jacobi-Trudi cofactor), generalizing the ladder b=k+1, a=k
         where ratio = -e_1 = -h_1.  We test the SHARP version: is the residual ratio
         exactly  (-1)*<the reduced coeff of X^k in (X^b mod coreVanish)> / <same for X^a>,
         and does that equal -h_{b-a}(x_T) ONLY in the ladder/a=k case, or generally?

  LEG 2 (homogeneity).  h_j(g*x_T) = g^j * h_j(x_T)  -- a pure algebraic identity. PROVABLE.

  LEG 3 (orbit multiplier).  c = g^{b-a}; orbit size = n/gcd(b-a,n).  The in-tree fibration
         (MonomialGammaFibration) proves c = g^b*(g^a)^{-1} = g^{b-a} (for the smooth
         rotation domain) and ord(c) = n/gcd(b-a,n).  The connection claims this c is the
         HOMOGENEITY WEIGHT of h_{b-a}.  We test:  does badSet = c*badSet hold with
         c=g^{b-a}, AND does the residual ratio transform as gamma(g*T) = c * gamma(T)
         consistently with "ratio = homogeneous-degree-(b-a) function"?
"""
import itertools
from sympy import isprime

def matdet(M, p):
    # fraction-free / plain modular determinant via Gaussian-style cofactor (small sizes)
    n = len(M)
    M = [row[:] for row in M]
    det = 1
    for col in range(n):
        piv = None
        for r in range(col, n):
            if M[r][col] % p != 0:
                piv = r; break
        if piv is None:
            return 0
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            det = (-det) % p
        inv = pow(M[col][col], p-2, p)
        det = (det * M[col][col]) % p
        for r in range(col+1, n):
            f = (M[r][col] * inv) % p
            if f:
                for c in range(col, n):
                    M[r][c] = (M[r][c] - f*M[col][c]) % p
    return det % p

def residual(dom, k, T, expo, p):
    """residual of value column y_i = x_i^expo against power columns 1..x^{k-1}.
    borderedMatrix: columns b<k -> x^b, last column -> x^expo. (k+1)x(k+1)."""
    M = []
    for i in T:
        x = dom[i]
        row = [pow(x, b, p) for b in range(k)] + [pow(x, expo, p)]
        M.append(row)
    return matdet(M, p)

def poly_mod_coreVanish(b, roots, p):
    """Return X^b reduced modulo prod_{x in roots}(X - x) as a coeff list (low->high),
    degree < len(roots)=t."""
    t = len(roots)
    # core vanish poly coeffs (monic, degree t)
    cv = [1]  # represents prod, build up; coeffs high->low we'll do low->high
    # build prod (X - x): start [ -x0, 1 ] ...
    poly = [1]  # constant 1, low->high
    for x in roots:
        # multiply by (X - x): new[j] = old[j-1] - x*old[j]
        new = [0]*(len(poly)+1)
        for j in range(len(poly)):
            new[j]   = (new[j]   - x*poly[j]) % p
            new[j+1] = (new[j+1] + poly[j]) % p
        poly = new
    # poly is core vanish, low->high, length t+1, monic leading.
    # reduce X^b: represent X^b as [0..0,1] length b+1; do schoolbook reduction
    rem = [0]*(b+1); rem[b] = 1
    cv = poly
    # reduce degrees >= t
    for deg in range(b, t-1, -1):
        if deg < len(rem) and rem[deg] % p != 0:
            coef = rem[deg]
            # subtract coef * X^{deg-t} * cv
            for j in range(len(cv)):
                idx = deg - t + j
                rem[idx] = (rem[idx] - coef*cv[j]) % p
    return [c % p for c in rem[:t]]  # degree < t

def h_complete(j, xs, p):
    """complete homogeneous symmetric polynomial h_j of variables xs, mod p."""
    if j == 0: return 1
    # generating function 1/prod(1-x_i*t); compute coeff of t^j by DP
    coeffs = [0]*(j+1); coeffs[0] = 1
    for x in xs:
        # multiply current series by 1/(1-x t) = sum x^m t^m  -> running convolution
        new = [0]*(j+1)
        for d in range(j+1):
            s = 0
            xm = 1
            for m in range(d+1):
                s = (s + coeffs[d-m]*xm) % p
                xm = (xm*x) % p
            new[d] = s
        coeffs = new
    return coeffs[j] % p

def find_dyadic_prime(mu, beta_lo=4, beta_hi=5):
    """find prime q ~ n^beta with q = 1 mod n, n=2^mu PROPER subgroup."""
    n = 1 << mu
    lo = n**beta_lo; hi = n**beta_hi
    # search q = 1 mod n
    q = ((lo // n) + 1) * n + 1
    while q <= hi:
        if isprime(q):
            return q
        q += n
    return None

def primitive_subgroup_gen(q, n):
    """find g of order exactly n in F_q*."""
    # find a generator of F_q* then raise to (q-1)/n
    import random
    phi = q-1
    facs = factorize(phi)
    def is_gen(a):
        for pr in facs:
            if pow(a, phi//pr, q) == 1:
                return False
        return True
    a = 2
    while not is_gen(a):
        a += 1
    g = pow(a, (q-1)//n, q)
    assert pow(g, n, q) == 1 and all(pow(g, n//pr, q) != 1 for pr in factorize(n))
    return g

def factorize(m):
    facs = set(); d = 2
    while d*d <= m:
        while m % d == 0:
            facs.add(d); m//=d
        d += 1
    if m > 1: facs.add(m)
    return facs

def multiplicative_order(c, q):
    if c % q == 0: return 0
    o = 1; x = c % q
    while x != 1:
        x = (x*c) % q; o += 1
    return o

# ============================================================
print("="*70)
print("C056: Schur/h_{b-a} homogeneity -> orbit multiplier, PROPER-SUBGROUP regime")
print("="*70)

# Use proper-subgroup dyadic primes. n=2^mu, q ~ n^beta, n << sqrt(q).
configs = []
for mu in (3, 4, 5):
    n = 1 << mu
    q = find_dyadic_prime(mu, 4, 5) or find_dyadic_prime(mu, 3, 6)
    if q is None:
        print(f"  (no prime found for mu={mu})"); continue
    configs.append((q, n, mu))

for (q, n, mu) in configs:
    g = primitive_subgroup_gen(q, n)
    dom = [pow(g, i, q) for i in range(n)]
    assert len(set(dom)) == n, "domain not injective (g order < n)"
    print(f"\n--- q={q} (={n}^{round(__import__('math').log(q,n),2)}), n={n}=2^{mu}, "
          f"g={g} (ord {n}), n^2={n*n} << q={q}: proper subgroup, large prime ---")

    # LEG 2 first: homogeneity of h_j  (pure identity check)
    leg2_ok = True
    import random
    for _ in range(200):
        t = random.randint(2, min(n, 6))
        xs = random.sample(dom, t)
        j = random.randint(0, 5)
        lhs = h_complete(j, [(g*x) % q for x in xs], q)
        rhs = (pow(g, j, q) * h_complete(j, xs, q)) % q
        if lhs != rhs:
            leg2_ok = False
            print(f"  LEG2 FAIL j={j} xs={xs}")
            break
    print(f"  LEG2 homogeneity h_j(g*x)=g^j h_j(x): {'OK' if leg2_ok else 'FAIL'} (200 rand)")

    # LEG 1: residual ratio vs h_{b-a} reduced, for several (k,a,b)
    # boundary radius t=k+1 subsets; residual ratio gamma_T = -res(x^b)/res(x^a).
    # Claim core: ratio is governed by h_{b-a}(x_T) reduced mod coreVanish.
    print("  LEG1 residual-ratio vs (X^b mod coreVanish) coeff & vs h_{b-a}:")
    for (k, a, b) in [(2,2,3),(2,2,4),(2,1,3),(3,3,4),(3,2,4),(2,0,2),(3,3,6)]:
        t = k+1
        if t > n: continue
        matches_reduced = 0
        matches_hba = 0
        tot = 0
        gamma_examples = []
        for T in itertools.combinations(range(n), t):
            ra = residual(dom, k, T, a, q)
            rb = residual(dom, k, T, b, q)
            if ra % q == 0:
                continue
            tot += 1
            gam = (-rb) * pow(ra, q-2, q) % q
            roots = [dom[i] for i in T]
            xs = roots
            # reduced X^b and X^a mod coreVanish; ratio of their X^k coeffs is the residual ratio
            redb = poly_mod_coreVanish(b, roots, q)
            reda = poly_mod_coreVanish(a, roots, q)
            # the residual ratio should equal -(redb[k]/reda[k]) because residual reads off
            # the X^k component against the k-th power column (the value column slot is degree k)
            # Actually residual uses power cols 0..k-1 and the value col; the determinant
            # extracts the coefficient of x^k in the reduced value (Cramer). So:
            if reda[k] % q != 0:
                pred = (-redb[k]) * pow(reda[k], q-2, q) % q
                if pred == gam:
                    matches_reduced += 1
            # h_{b-a} comparison: the connection's headline. ratio = -h_{b-a}(x_T)?  (only when a=k)
            hba = h_complete(b-a, xs, q)
            if gam == (-hba) % q:
                matches_hba += 1
            if len(gamma_examples) < 1:
                gamma_examples.append((T, gam, (-hba)%q, redb[k], reda[k]))
        print(f"    (k={k},a={a},b={b}) t={t}: residual-ratio==-(redCoeff_b/redCoeff_a): "
              f"{matches_reduced}/{tot} | ratio==-h_{{{b-a}}}: {matches_hba}/{tot}")

    # LEG 3: orbit multiplier c=g^{b-a}; ratio(g.T) = c*ratio(T); orbit size n/gcd(b-a,n)
    print("  LEG3 orbit multiplier c=g^{b-a} & ratio(rotate)=c*ratio:")
    import math
    for (k, a, b) in [(2,2,3),(2,1,3),(2,0,2),(3,3,4),(2,2,4)]:
        t = k+1
        if t > n: continue
        c = pow(g, (b-a) % n, q)   # g^{b-a}; note b-a taken mod n since g^n=1
        ok_rot = True
        ok_count = 0; cnt = 0
        for T in itertools.combinations(range(n), t):
            ra = residual(dom, k, T, a, q); rb = residual(dom, k, T, b, q)
            if ra % q == 0: continue
            gam = (-rb)*pow(ra, q-2, q) % q
            # rotate T by +1 mod n
            Trot = tuple(sorted((i+1) % n for i in T))
            ra2 = residual(dom, k, Trot, a, q); rb2 = residual(dom, k, Trot, b, q)
            if ra2 % q == 0:
                continue
            gam2 = (-rb2)*pow(ra2, q-2, q) % q
            cnt += 1
            if gam2 == (c*gam) % q:
                ok_count += 1
            else:
                ok_rot = False
        orbit = n // math.gcd((b-a) % n if (b-a)%n!=0 else n, n)
        print(f"    (k={k},a={a},b={b}): c=g^{{{b-a}}}; ratio(g.T)=c*ratio(T): "
              f"{ok_count}/{cnt} {'(all)' if ok_rot and cnt>0 else ''}; "
              f"ord(c)={ multiplicative_order(c, q) }; n/gcd(b-a,n)={orbit}")
