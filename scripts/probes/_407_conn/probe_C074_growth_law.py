"""
C074 part 2: the GROWTH of the sum-spectrum orbit count, and the FREENESS mechanism.

Question 1 (FREENESS root cause): when is a nonzero subset-sum s = sum_{x in S} x
fixed by dilation, i.e. g^j * s = s for some 0<j<n?  That requires g^j=1 (impossible
for 0<j<n since g has order n) OR s=0.  So for s != 0 the orbit {g^j s} has exactly n
distinct values  ==>  every nonzero orbit has size exactly n, UNCONDITIONALLY.
This is a rigorous identity, not a probe coincidence.  We just re-verify the count.

Question 2 (does the SUM spectrum collapse like the PRODUCT spectrum to ~n?  NO):
the product spectrum = e_{Sigma a_i mod n} so #prod = n always (one value per exponent
residue).  The sum spectrum has #orbits = K*n orbits.  We test whether K (= #orbits)
is BOUNDED/poly or grows like C(n,t)/n.  For the PRIZE-relevant ladder badSet the radius
sits at the *small live gap*; but the connection's collapse claim is global.

We measure K(n,t) = #sum-orbits and compare to:
   - C(n,t)/n  (the generic Sidon-like upper expectation: distinct sums / orbit size)
   - n         (the product-spectrum value)
to decide poly-vs-superpoly. We also fit log K / log n at fixed small t.
"""
import itertools
from math import comb, log

def isprime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True

def find_prime(n, beta=5):
    target = n ** beta
    q = target - (target % n) + 1
    while not (isprime(q) and (q-1) % n == 0):
        q += n
    return q

def find_generator(q):
    m = q-1
    facs = set(); mm = m; d = 2
    while d*d <= mm:
        while mm % d == 0: facs.add(d); mm //= d
        d += 1
    if mm > 1: facs.add(mm)
    for h in range(2, q):
        if all(pow(h, m//p, q) != 1 for p in facs):
            return h
    raise RuntimeError

def mu_n(q, n):
    g = pow(find_generator(q), (q-1)//n, q)
    return [pow(g, i, q) for i in range(n)], g

def sum_orbits(n, t, q, g, D):
    Sig = set(sum(c) % q for c in itertools.combinations(D, t))
    nz = [s for s in Sig if s != 0]
    # verify every orbit size == n
    rem = set(nz); sizes = []
    while rem:
        s0 = next(iter(rem)); x = s0; cnt = 0
        while True:
            rem.discard(x); cnt += 1; x = (x*g) % q
            if x == s0: break
        sizes.append(cnt)
    return len(Sig), len(nz), sizes

print("=== C074 growth law: #sum-orbits K vs C(n,t)/n vs product-value n ===\n")
print(f"{'n':>3} {'t':>2} {'#sum':>7} {'#orbits':>8} {'allsize=n?':>10} "
      f"{'C(n,t)/n':>10} {'orbit/[C(n,t)/n]':>16} {'#prod':>6}")
for n in [8,16,32,64,128]:
    q = find_prime(n, 5)
    D, g = mu_n(q, n)
    tmax = min(n, 6 if n <= 32 else 4)
    for t in range(2, tmax+1):
        if comb(n,t) > 6_000_000:  # keep enumeration cheap
            continue
        nsum, nnz, sizes = sum_orbits(n, t, q, g, D)
        alln = all(s == n for s in sizes)
        norb = len(sizes)
        cnt_over = comb(n,t)/n
        print(f"{n:>3} {t:>2} {nsum:>7} {norb:>8} {str(alln):>10} "
              f"{cnt_over:>10.1f} {norb/cnt_over:>16.4f} {n:>6}")

print("\n=== Interpretation ===")
print("If 'allsize=n?' is True everywhere => freeness PROVEN (orbit size always exactly n).")
print("orbit/[C(n,t)/n] ~ 1 => sum spectrum is NEAR-MAXIMAL (almost all sums distinct),")
print("   i.e. ~C(n,t) distinct sums, SUPER-poly in n at fixed growing t -- the OPPOSITE of")
print("   the product collapse to n.  K = #orbits is NOT bounded by any poly that the prize")
print("   would need from a single ladder pencil's full subset-sum set.")
