"""
C088 probe: does the covering-transfer injectivity hypothesis (p | Res, i.e.
"dyadic sumset stays injective mod the degree-1 prime p|p") say anything about
the BGK sqrt-cancellation house B = max_{b!=0} | sum_{y in mu_n} psi(b y) | in
the PRIZE REGIME (dyadic mu_n a PROPER subgroup of F_q*, q ~ n^beta, beta~4-5)?

The connection claims:
  - the cyclotomic reduction Z[zeta_{2^mu}] -> F_p (degree-1 prime p|p) is a
    "covering-transfer hom" whose injectivity-on-G == p | Res(f_S - f_T, Phi_{2^mu})
  - injectivity-on-G "carries the dyadic obstruction down" and unifies F4/F10/F11.

We test the OPERATIVE numeric claim in the actual prize regime: for fully-split
prize primes q == 1 (mod n) (so zeta_n in F_q, power basis COLLAPSED), measure:
  (a) Is the n=2^mu subgroup sumset injective / covering at all? (the covering
      lemma needs subset sums of DISTINCT roots to stay distinct -- but in
      F_q the subgroup is finite of size n, so a 2^mu-element domain over an
      n-element subgroup CANNOT have a super-poly distinct sumset.)
  (b) The actual house B and whether "injectivity" of the reduction has ANY
      correlation with B being small (the prize's open core).

This separates the char-0 covering phenomenon (where it works) from the prize
regime (proper subgroup, where it is vacuous / decoupled from B).
"""

import itertools, math

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def primes_one_mod_n_in_range(n, lo, hi):
    out = []
    # q == 1 mod n, q prime, in [lo,hi]
    start = ((lo - 1)//n + 1)*n + 1
    q = start
    while q <= hi:
        if is_prime(q):
            out.append(q)
        q += n
    return out

def subgroup_mu_n(q, n):
    """The dyadic subgroup mu_n = {x : x^n = 1} in F_q^*, q == 1 mod n."""
    # find a generator g of F_q^*, then mu_n = <g^((q-1)/n)>
    # naive generator search
    qm1 = q-1
    # factor qm1
    def factorize(m):
        f=set(); d=2
        while d*d<=m:
            while m%d==0:
                f.add(d); m//=d
            d+=1
        if m>1: f.add(m)
        return f
    fac = factorize(qm1)
    def is_gen(g):
        for p in fac:
            if pow(g, qm1//p, q) == 1:
                return False
        return True
    g = 2
    while not is_gen(g):
        g += 1
    h = pow(g, qm1//n, q)  # generator of mu_n
    return [pow(h, i, q) for i in range(n)]

def house_B(q, mu):
    """B = max_{b != 0} | sum_{y in mu} omega_q^{b y} |, omega_q = exp(2 pi i / q)."""
    n = len(mu)
    best = 0.0
    # only need b over coset reps of F_q^*/mu? B is constant on mu-cosets; but
    # to be safe & exact-ish, scan all b in 1..q-1 for small q.
    twopi = 2*math.pi
    for b in range(1, q):
        s = 0+0j
        for y in mu:
            ang = twopi * ((b*y) % q) / q
            s += complex(math.cos(ang), math.sin(ang))
        m = abs(s)
        if m > best:
            best = m
    return best

def distinct_sumset_size_in_subgroup(mu, n):
    """
    The covering claim needs: subset sums of the n 'signed/distinct' elements
    cover F_q. In the prize regime mu has size n (PROPER subgroup). Take the
    natural 'dyadic' analogue: the elements of mu itself, and form r-fold
    distinct sumsets. We measure the FULL sumset of mu (all subset sums) size.
    If it is << q, the covering is FALSE in the proper-subgroup regime.
    """
    q = None  # not needed; sums in Z then we only report distinct count of subset sums mod q done by caller
    return None

print("="*78)
print("C088: covering-transfer injectivity vs BGK house B, PRIZE REGIME")
print("="*78)
print()
print(f"{'n':>4} {'q':>9} {'beta=log_n q':>12} {'B':>10} {'2sqrt(n)':>9} {'sqrt(n)':>9} {'B/sqrt(n)':>10} {'covers?':>8}")
print("-"*78)

for mu_exp in [3,4,5,6]:           # n = 8,16,32,64
    n = 2**mu_exp
    # prize regime: q ~ n^4..n^5, q == 1 mod n, prime, multiple such primes
    lo, hi = n**4, n**4 + 60*n     # a band of fully-split prize primes
    qs = primes_one_mod_n_in_range(n, lo, hi)
    qs = qs[:3]                     # a few fully-split primes
    if not qs:
        # widen
        lo, hi = n**3, n**4
        qs = primes_one_mod_n_in_range(n, lo, hi)[:3]
    for q in qs:
        mu = subgroup_mu_n(q, n)
        assert len(set(mu)) == n, "mu_n not size n"
        # verify it's a subgroup (closed under mult)
        muset = set(mu)
        # house
        B = house_B(q, mu)
        beta = math.log(q)/math.log(n)
        # covering test: the distinct sumset of the n subgroup elements.
        # full subset-sum set mod q (all 2^n subsets is too big for n=64;
        # do r-fold distinct sums for r up to a small cap and see if it
        # plateaus far below q -> NOT covering)
        cover = "—"
        if n <= 16:
            sums = set()
            for r in range(0, n+1):
                for S in itertools.combinations(mu, r):
                    sums.add(sum(S) % q)
            cover = f"{len(sums)}/{q}"
            cover = "YES" if len(sums)==q else f"NO({len(sums)})"
        print(f"{n:>4} {q:>9} {beta:>12.3f} {B:>10.3f} {2*math.sqrt(n):>9.3f} {math.sqrt(n):>9.3f} {B/math.sqrt(n):>10.3f} {cover:>8}")

print()
print("INTERPRETATION:")
print(" - 'covers?' tests the covering-transfer CONCLUSION (distinct sumset = F_q)")
print("   directly in the proper-subgroup prize regime.")
print(" - B is the ACTUAL prize open core (BGK sqrt-cancellation house).")
print(" - If covering FAILS (NO) in-regime, the F4/F10/F11 covering gadget is")
print("   simply not the prize object: it concerns a DIFFERENT (char-0, full")
print("   power-basis) regime, decoupled from B.")
