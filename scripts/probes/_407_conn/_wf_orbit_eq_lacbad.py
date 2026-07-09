"""
C058 probe: Is the Chai-Fan action-orbit count K (F9) literally equal to
#lacBad / (coset size) (F10), i.e. are the F9 orbit action and the F10
lacunary-coset action THE SAME <g^{b-a}>-coset action?

C058 claim (identity part):
  - F9 (Chai-Fan): bad-alpha set for monomial pencil h_alpha(z)=z^a + alpha z^b
    is a union of <g^{b-a}>-orbits because h_alpha(mu z) = mu^a h_{alpha mu^{b-a}}(z).
  - F10 (DyadicLacunary): lacBad(G,a,t) = { e_t(S) : S subset G, |S|=a, e_1..e_{t-1}=0 }
    is closed under gamma -> g^t * gamma (lacBad_smul_closed), a union of cosets of
    <g^t> = mu_{n/gcd(t,n)}.
  - With t = a-b (gap) and g^{b-a} = g^{-t}, these are the SAME cyclic subgroup.
  => #lacBad = K * (coset size) = K * (n/gcd(t,n)).

We test on PROPER subgroups mu_n < F_q* (prize regime: n=2^mu, q prime =1 mod n,
n << sqrt(q)). We compute, for monomial direction (a,b) with gap t=a-b:

  (A) Direct list-decode bad set: alpha bad <=> z^a + alpha z^b is within agreement
      w = a (i.e. distance n-a) of RS[k] with k=b, on D=mu_n.  By the Vieta pin,
      at the cleanest radius delta = 1 - a/n, agreement = a, the bad scalars are
      exactly gamma = (-1)^t e_t(S) over S subset mu_n, |S|=a, e_1=...=e_{t-1}=0.
      We compute lacBad directly from the esymm definition (this IS the in-tree object).

  (B) The orbit / coset structure of lacBad under multiplication by g^t.
      coset_size = order of g^t in F_q* = n/gcd(t,n).
      #orbits K  = number of <g^t>-orbits inside lacBad.
      Caveat (issue #407 line 933): 0 is its own singleton orbit if 0 in lacBad.

  Test: is #lacBad == K_nonzero * coset_size + (1 if 0 in lacBad else 0) ?
        i.e. nonzero part of lacBad is an EXACT union of full <g^t>-cosets,
        each of size coset_size, so K = #lacBad_nonzero / coset_size is an integer.

This verifies the *identity* (same coset action). It does NOT verify K=O(1)
(that is the open count = BGK, already refuted at window interior).
"""
import itertools
from sympy import isprime

def primitive_root(p):
    # find a generator of F_p*
    factors = factorize(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//f, p) != 1 for f in factors):
            return g
    raise RuntimeError("no prim root")

def factorize(n):
    fs = set()
    d = 2
    while d*d <= n:
        while n % d == 0:
            fs.add(d); n//=d
        d += 1
    if n > 1: fs.add(n)
    return fs

def subgroup_mu_n(p, n):
    """multiplicative subgroup of order n in F_p* (n | p-1)."""
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # element of order n
    elems = []
    x = 1
    for _ in range(n):
        elems.append(x)
        x = (x*h) % p
    assert len(set(elems)) == n
    return elems, h  # h is a generator of mu_n

def esymm(S, t, p):
    """e_t of a list S of field elements mod p."""
    if t == 0:
        return 1 % p
    if t > len(S):
        return 0
    acc = 0
    for T in itertools.combinations(S, t):
        prod = 1
        for x in T:
            prod = (prod * x) % p
        acc = (acc + prod) % p
    return acc % p

def lacBad(mu, a, t, p):
    """{ e_t(S) : S subset mu, |S|=a, e_1=...=e_{t-1}=0 }  (the in-tree object)."""
    vals = set()
    for S in itertools.combinations(mu, a):
        ok = all(esymm(S, j, p) == 0 for j in range(1, t))
        if ok:
            vals.add(esymm(S, t, p))
    return vals

def coset_orbits(vals, gt, p):
    """partition vals into <gt>-orbits under x -> gt*x. Returns list of orbit sizes."""
    vals = set(vals)
    orbits = []
    seen = set()
    for v in sorted(vals):
        if v in seen:
            continue
        orb = []
        x = v
        while x not in seen:
            seen.add(x)
            orb.append(x)
            x = (x * gt) % p
        orbits.append(orb)
    return orbits

def order_of(x, p):
    if x == 0:
        return 0
    o = 1
    y = x % p
    while y != 1:
        y = (y*x) % p
        o += 1
    return o

def run_case(p, n, a, t):
    mu, h = subgroup_mu_n(p, n)   # h generator of mu_n
    gt = pow(h, t, p)             # g^t, g = h a generator of mu_n
    coset_size = order_of(gt, p)  # = n/gcd(t,n)
    g = h
    import math
    expect_size = n // math.gcd(t, n)
    vals = lacBad(mu, a, t, p)
    has_zero = (0 in vals)
    nz = vals - {0}
    orbits = coset_orbits(nz, gt, p)
    sizes = [len(o) for o in orbits]
    all_full = all(s == coset_size for s in sizes) if coset_size > 0 else (len(nz)==0)
    K_nz = len(orbits)
    # identity check: #lacBad_nonzero == K_nz * coset_size  (exact union of full cosets)
    identity_ok = (len(nz) == K_nz * coset_size) if coset_size > 0 else (len(nz)==0)
    return {
        'p': p, 'n': n, 'a': a, 'b': a-t, 't': t,
        'gcd(t,n)': math.gcd(t,n),
        'coset_size': coset_size, 'expect_n/gcd': expect_size,
        'coset_size_ok': coset_size == expect_size,
        '#lacBad': len(vals), 'has_zero': has_zero, '#nonzero': len(nz),
        'K(#orbits_nz)': K_nz, 'orbit_sizes': sorted(set(sizes)),
        'all_cosets_full': all_full,
        'IDENTITY #lacBad_nz==K*coset': identity_ok,
    }

# Prize-regime-shaped cases: proper subgroups mu_n < F_q*, q prime, q ~ n^beta, n<<sqrt(q)
# n in {8,16,32}, multiple proper-subgroup large-ish primes.
CASES = []
# choose primes p = 1 mod n, p >> n (proper subgroup, several primes per n)
def find_primes(n, count, start):
    out = []
    p = start
    while len(out) < count:
        if p % n == 1 and isprime(p):
            out.append(p)
        p += 1
    return out

import math
for n in (8, 16):
    primes = find_primes(n, 4, n*n*4)  # p ~ several*n^2 and up (proper subgroup, large-ish)
    for p in primes:
        # several monomial directions: vary gap t and degree a
        for (a, t) in [(n//2, 1), (n//2, 2), (n//2+1, 2), (n//2, 3), (3*n//4, 2)]:
            if a <= n and a-t >= 1 and t >= 1:
                CASES.append((p, n, a, t))

# n=32 is heavier (C(32,16) huge) -> restrict to small a or small gap to stay fast
for n in (32,):
    primes = find_primes(n, 2, n*n*8)
    for p in primes:
        for (a, t) in [(3, 2), (4, 2), (4, 3), (5, 2)]:
            CASES.append((p, n, a, t))

print(f"{'p':>10} {'n':>3} {'a':>3} {'b':>3} {'t':>2} {'g(t,n)':>6} {'cos':>4} {'cos_ok':>6} "
      f"{'#lac':>5} {'z':>2} {'#nz':>5} {'K':>4} {'sizes':>10} {'full':>5} {'IDENT':>6}")
all_ok = True
for (p, n, a, t) in CASES:
    r = run_case(p, n, a, t)
    line = (f"{r['p']:>10} {r['n']:>3} {r['a']:>3} {r['b']:>3} {r['t']:>2} "
            f"{r['gcd(t,n)']:>6} {r['coset_size']:>4} {str(r['coset_size_ok']):>6} "
            f"{r['#lacBad']:>5} {str(r['has_zero'])[0]:>2} {r['#nonzero']:>5} "
            f"{r['K(#orbits_nz)']:>4} {str(r['orbit_sizes']):>10} "
            f"{str(r['all_cosets_full'])[0]:>5} {str(r['IDENTITY #lacBad_nz==K*coset'])[0]:>6}")
    print(line)
    if not (r['coset_size_ok'] and r['all_cosets_full'] and r['IDENTITY #lacBad_nz==K*coset']):
        all_ok = False

print()
print("ALL identity+coset-quantization checks pass:", all_ok)
