"""
Probe for C074 (issue #407): the DILATION-ORBIT bridge between the additive
subset-SUM spectrum (open, F15 ladder badSet) and the multiplicative subset-PRODUCT
spectrum (proven <= n) on the SAME smooth domain mu_n.

PRIZE REGIME: mu_n = <g> a PROPER dyadic subgroup of F_q^*, n=2^mu, q prime ==1 mod n,
q ~ n^beta (beta 4-5), n << sqrt q, multiple primes. (Full-group / small-prime = #400 trap.)

C074's load-bearing claims (the NEW content beyond C044, which already showed
sum-spectrum = e_1-of-class SUM and refuted the single-product <= n bound):

  (A) PRODUCT spectrum of mu_n at size t = exactly n  (Lean-proven; reconfirm numerically).
  (B) DILATION ORBIT: g*(subset-sum over S subset mu_n) = subset-sum over g*S, and
      g*S is again a t-subset of mu_n (mu_n is closed under mult by g). So the SUM
      spectrum Sigma_t = { sum_{x in S} x : S in C(mu_n, t) } is INVARIANT under mult by g.
      Therefore Sigma_t is a UNION of mu_n-orbits under multiplication, plus possibly {0}.
      CLAIM TO TEST:  is the action FREE (so #Sigma_t \ {0} is a multiple of n)?
                      i.e. is  #Sigma_t = n * (#nonzero orbits) + [0 in Sigma_t] ?
                      Equivalently #(Sigma_t \ {0}) ≡ 0  (mod n).
  (C) The size law: is #Sigma_t polynomial in n (prize survives) or super-poly?
      Measure K = #Sigma_t / n across n=8..64 and across t.

We compute EXACTLY mod q.  Subset sums by exact integer combinatorics.
"""
import itertools
from math import comb

def isprime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True

def find_prime(n, beta=4):
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
    raise RuntimeError("no generator")

def mu_n(q, n):
    g = pow(find_generator(q), (q-1)//n, q)
    return [pow(g, i, q) for i in range(n)], g

def subset_sums(D, t, q):
    return set(sum(c) % q for c in itertools.combinations(D, t))

def subset_products(D, t, q):
    S = set()
    for c in itertools.combinations(D, t):
        p = 1
        for x in c: p = (p*x) % q
        S.add(p)
    return S

def orbit_decompose(Sigma, g, q):
    """Decompose Sigma \\ {0} into orbits under x -> g*x (mod q). Return list of orbit sizes."""
    rem = set(s for s in Sigma if s != 0)
    sizes = []
    while rem:
        s0 = next(iter(rem))
        orb = []
        x = s0
        while True:
            orb.append(x); rem.discard(x)
            x = (x*g) % q
            if x == s0: break
            if x in orb:  # safety (should not happen for free action up to period)
                break
        sizes.append(len(orb))
    return sizes

print("=== C074: PRODUCT spectrum == n  AND  SUM-spectrum dilation-orbit law ===\n")
print(f"{'n':>3} {'q':>10} {'t':>2} | {'#PROD':>6} {'==n?':>5} | {'#SUM':>6} {'0in?':>5} "
      f"{'#nz':>6} {'nz%n':>5} {'#orbits':>7} {'orbit-sizes(distinct)':>22} {'K=#SUM/n':>9}")
cases = [(8,2),(8,3),(8,4),(16,2),(16,3),(16,4),(16,5),(16,6),(32,2),(32,3),(32,4),
         (64,2),(64,3)]
betas = [4,5]
for beta in betas:
    print(f"\n--- beta={beta} (q ~ n^{beta}) ---")
    for (n,t) in cases:
        q = find_prime(n, beta)
        D, g = mu_n(q, n)
        # PRODUCT spectrum
        P = subset_products(D, t, q)
        prod_eq_n = (len(P) == n)
        # SUM spectrum
        Sig = subset_sums(D, t, q)
        zero_in = (0 in Sig)
        nz = len([s for s in Sig if s != 0])
        sizes = orbit_decompose(Sig, g, q)
        distinct_sizes = sorted(set(sizes))
        K = len(Sig)/n
        print(f"{n:>3} {q:>10} {t:>2} | {len(P):>6} {str(prod_eq_n):>5} | "
              f"{len(Sig):>6} {str(zero_in):>5} {nz:>6} {nz % n:>5} {len(sizes):>7} "
              f"{str(distinct_sizes):>22} {K:>9.3f}")
