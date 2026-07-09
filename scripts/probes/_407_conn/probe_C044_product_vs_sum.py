"""
Probe for C044 (issue #407): is the bad scalar gamma at the SMALLEST live gap t=2^L
a PRODUCT of coset-rep 2^L-powers (the C044 claim) -- or a SUM?

Prize regime: mu_n a PROPER dyadic subgroup of F_q^*, n=2^mu, q prime ==1 mod n,
q ~ n^beta (n << sqrt q). Coset-union S = union_i x_i * mu_{2^L}, m cosets, |S| = m*2^L.
Smallest live gap t = 2^L: loc(S) = prod_i (X^{2^L} - x_i^{2^L}) is a poly in Y=X^{2^L},
so e_j(S)=0 for 0<j<2^L and the first nonzero esymm is e_{2^L}.

C044 claims  e_{2^L}(S) = +- prod_i x_i^{2^L} * (unit)  -- a PRODUCT of class values.
Actual algebra: writing c_i = x_i^{2^L}, loc(S) = prod_i (Y - c_i) = Y^m - e1(c)Y^{m-1}+...
so coeff of X^{|S|-2^L} = coeff of Y^{m-1} = -e1(c) = -SUM_i c_i, i.e.
   e_{2^L}(S) = +- e_1(class set) = +- SUM_i c_i   (a SUM, not a product).
The PRODUCT prod_i c_i = e_m(c) appears at the TOP gap t = m*2^L = |S|.

We verify EXACTLY (mod q) which the smallest live gap produces, at proper-subgroup primes.
e_t computed via the polynomial coeffs of prod(X - s) mod q  -- O(|S|^2), exact.
"""

import itertools

def isprime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0: return False
        d += 2
    return True

def all_esymm(vals, q):
    """coeffs of prod_x (X - x) mod q.  poly[k] = coeff of X^k.
    e_t(vals) = (-1)^t * poly[N-t]  where N=len(vals)."""
    poly = [1]  # constant poly 1
    for x in vals:
        new = [0] * (len(poly) + 1)
        for i, c in enumerate(poly):
            new[i]   = (new[i]   + c * (-x)) % q   # multiply by (X - x): -x * c at degree i
            new[i+1] = (new[i+1] + c) % q          # + c at degree i+1
        poly = new
    return poly  # poly[k] = coeff X^k, length N+1

def esymm_from_poly(poly, t, q, N):
    return (pow(-1, t, q) * poly[N - t]) % q

def find_prime(n, beta=4):
    target = n ** beta
    q = target - (target % n) + 1
    while not (isprime(q) and (q - 1) % n == 0):
        q += n
    return q

def find_generator_of_unit_group(q):
    m = q - 1
    facs = set(); mm = m; d = 2
    while d * d <= mm:
        while mm % d == 0: facs.add(d); mm //= d
        d += 1
    if mm > 1: facs.add(mm)
    for h in range(2, q):
        if all(pow(h, m // p, q) != 1 for p in facs):
            return h
    raise RuntimeError("no generator")

def run(n, L, m, beta=4):
    q = find_prime(n, beta)
    h = find_generator_of_unit_group(q)
    g = pow(h, (q - 1) // n, q)           # generator of mu_n
    d = 2 ** L
    assert d < n, f"need proper subgroup d=2^L<n; d={d},n={n}"
    step = n // d
    mu_d = [pow(g, (step * j) % n, q) for j in range(d)]
    reps = [pow(g, i, q) for i in range(m)]
    classes = [pow(r, d, q) for r in reps]
    assert len(set(classes)) == m, "reps not in distinct cosets"
    S = set()
    for r in reps:
        for u in mu_d:
            S.add((r * u) % q)
    S = list(S)
    a = len(S)
    assert a == m * d, f"coset union size {a} != m*d={m*d} (overlap)"
    t = d
    poly = all_esymm(S, q)
    e_t = esymm_from_poly(poly, t, q, a)
    sum_classes = sum(classes) % q
    prod_classes = 1
    for c in classes: prod_classes = (prod_classes * c) % q
    e_top = esymm_from_poly(poly, a, q, a)
    return dict(n=n, L=L, d=d, m=m, q=q, a=a, t=t, e_t=e_t,
        sum_classes=sum_classes, prod_classes=prod_classes,
        e_t_eq_sum=(e_t in (sum_classes, (-sum_classes) % q)),
        e_t_eq_prod=(e_t in (prod_classes, (-prod_classes) % q)),
        e_top=e_top,
        e_top_eq_prod=(e_top in (prod_classes, (-prod_classes) % q,
                                 *( (x, (-x) % q) for x in [pow(prod_classes, d, q)] ))))

def vary_reps_count_lacbad(n, L, m, beta=4, sample=200):
    """Empirically: over many m-coset choices, how many distinct e_t (=lacBad) values?
    C044 says #lacBad <= n/gcd(t,n) <= n. With t=d|n, gcd(t,n)=d, bound = n/d.
    Check the coset-union FAMILY only (a sub-family of full vanishingVariety)."""
    q = find_prime(n, beta)
    h = find_generator_of_unit_group(q)
    g = pow(h, (q - 1) // n, q)
    d = 2 ** L
    step = n // d
    mu_d = [pow(g, (step * j) % n, q) for j in range(d)]
    # coset classes available: g^i for i in 0..step-1 raised to d give the n/d distinct classes
    rep_indices = list(range(n // d))  # one rep per coset
    seen = set()
    cnt = 0
    for combo in itertools.combinations(rep_indices, m):
        cnt += 1
        if cnt > sample: break
        reps = [pow(g, (i * d) % n, q) for i in combo]  # actually use class reps; but rep arbitrary in coset doesn't change e_t since e_t(S) depends only on S
        # build S from representative g^i (i = combo index times anything in its coset); use g^{i} as rep
        reps2 = [pow(g, i, q) for i in combo]
        S = set()
        for r in reps2:
            for u in mu_d:
                S.add((r * u) % q)
        S = list(S)
        poly = all_esymm(S, q)
        e_t = esymm_from_poly(poly, d, q, len(S))
        seen.add(e_t)
    return dict(n=n, L=L, d=d, m=m, q=q, distinct_e_t=len(seen),
                bound_n_over_gcd=n // d, samples=min(cnt, sample))

if __name__ == "__main__":
    print("=== Part 1: is e_t at smallest live gap a SUM or a PRODUCT of class values? ===")
    cases = [(8,1,2),(8,1,3),(8,2,2),(16,1,2),(16,1,3),(16,2,2),(16,2,3),(16,3,2),
             (32,1,3),(32,2,2),(32,2,3),(32,4,2),(64,2,2),(64,4,2)]
    print(f"{'n':>3}{'L':>3}{'d':>4}{'m':>3}{'q':>12}{'a':>4}{'t':>4} | e_t==SUM  e_t==PROD | e_t  sum  prod")
    for (n,L,m) in cases:
        try:
            r = run(n,L,m)
            print(f"{r['n']:>3}{r['L']:>3}{r['d']:>4}{r['m']:>3}{r['q']:>12}{r['a']:>4}{r['t']:>4} |   "
                  f"{str(r['e_t_eq_sum']):>5}     {str(r['e_t_eq_prod']):>5}  | "
                  f"{r['e_t']} {r['sum_classes']} {r['prod_classes']}")
        except AssertionError as ex:
            print(f"{n:>3}{L:>3}  skip: {ex}")
    print()
    print("=== Part 2: #lacBad over the COSET-UNION family vs C044 bound n/gcd(t,n)=n/d ===")
    print(f"{'n':>3}{'L':>3}{'d':>4}{'m':>3}{'q':>12} | distinct e_t (lacBad)  vs bound n/d  vs n")
    for (n,L,m) in [(16,1,2),(16,2,2),(16,1,3),(32,2,2),(32,1,2),(32,2,3),(64,2,2)]:
        v = vary_reps_count_lacbad(n,L,m)
        print(f"{v['n']:>3}{v['L']:>3}{v['d']:>4}{v['m']:>3}{v['q']:>12} | distinct={v['distinct_e_t']:>4} (over {v['samples']} unions)   n/d={v['bound_n_over_gcd']:>4}   n={v['n']}")
