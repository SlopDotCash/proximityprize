"""
Probe for C025 (rank 25): "Parity obstruction kills the char-0 e2=0 layer at k=0 mod 4".

The connection claims (via comment-40 reduction):
  bad alpha at agreement a=k+2  <=>  exists (k+2)-subset S of mu_n with e2(S)=0, e1(S)!=0, alpha=-1/e1(S).
  C025: for production dim k=0 mod 4  (so |A|=k+2 = 2 mod 4), the parity law forces
        e2Folded != 0, and ABOVE THE THRESHOLD (2^(m-1) |A|^2)^(2^(m-1)) < p
        there is NO subset with e2(S)=0  ->  depth-1 bad scalar set EMPTY.

TWO honesty checks:
  (1) MATH: is the parity law + threshold theorem actually TRUE?
      - verify e2Folded mod-2 coeff-sum == #upperPairs  (parity identity)
      - verify "above threshold => char-0 vanishing" by exact search: for |A| with odd pair
        count, confirm NO subset S of mu_n has e2(S, g) == 0 mod p, for p above threshold.
      - and (control) for |A| with EVEN pair count, char-0 solutions CAN exist.
  (2) PRIZE RELEVANCE: is the threshold reachable in the prize regime (p ~ n^beta, beta=4-5)?
      Compare threshold (n/2 * |A|^2)^(n/2) vs prize prime n^5.  This is the decisive trap.
"""

import itertools
from sympy import isprime, primitive_root, factorint

# ---------------------------------------------------------------------------
# helpers: build mu_n = <g> with g a primitive 2^m-th root of unity mod p
# ---------------------------------------------------------------------------
def find_prime_with_subgroup(n, beta_lo, beta_hi):
    """Find a prime p with p = 1 mod n, n^beta_lo <= p <= n^beta_hi, p PROPER (n < p-1)."""
    lo = int(n**beta_lo)
    hi = int(n**beta_hi)
    p = lo - (lo % n) + 1
    if p < lo:
        p += n
    while p <= hi:
        if isprime(p) and (p - 1) % n == 0 and n < p - 1:
            return p
        p += n
    return None

def primitive_2m_root(p, n):
    """g of exact order n=2^m mod p."""
    gr = primitive_root(p)
    g = pow(gr, (p - 1) // n, p)
    assert pow(g, n, p) == 1
    assert pow(g, n // 2, p) != 1, "order not exactly n"
    return g

def e2_of_subset(S_exps, g, p, n):
    """e2(A,g) = sum_{i<j in A} g^(exp_i+exp_j) mod p, A = {g^e : e in S_exps}."""
    tot = 0
    L = list(S_exps)
    for i in range(len(L)):
        for j in range(i + 1, len(L)):
            tot = (tot + pow(g, (L[i] + L[j]) % n, p)) % p
    return tot

def e1_of_subset(S_exps, g, p, n):
    return sum(pow(g, e % n, p) for e in S_exps) % p

# ---------------------------------------------------------------------------
# CHECK 1a: parity identity  coeff-sum(e2Folded) == #upperPairs mod 2
# ---------------------------------------------------------------------------
def e2folded_coeffsum_and_pairs(S_exps, m):
    n = 1 << m
    half = 1 << (m - 1)
    L = list(S_exps)
    pairs = [(L[i], L[j]) for i in range(len(L)) for j in range(i + 1, len(L))]
    npairs = len(pairs)
    coeff = [0] * half
    for (a, b) in pairs:
        r = (a + b) % n
        if r < half:
            coeff[r] += 1
        else:
            coeff[r - half] -= 1
    csum = sum(coeff)
    return csum, npairs

def check_parity_identity():
    print("=== CHECK 1a: parity identity coeff-sum == #upperPairs MOD 2 (the Lean claim) ===")
    ok = True
    nfail = 0
    for m in [3, 4, 5]:
        n = 1 << m
        for asize in range(2, min(n, 9) + 1):
            cnt = 0
            for S in itertools.combinations(range(n), asize):
                csum, npairs = e2folded_coeffsum_and_pairs(S, m)
                if (csum % 2) != (npairs % 2):
                    ok = False
                    nfail += 1
                    if nfail <= 10:
                        print(f"  FAIL m={m} A={S}: csum={csum} npairs={npairs} (mod2 {csum%2} vs {npairs%2})")
                cnt += 1
                if cnt >= 60:
                    break
    print("  parity identity mod 2:", "HOLDS on all sampled" if ok else f"FAILED ({nfail})")
    return ok

# ---------------------------------------------------------------------------
# CHECK 1b: threshold theorem -> char-0 emptiness for ODD-pair-count sizes.
# For sizes |A| = 2 or 3 mod 4 the pair count is odd; claim: NO subset has e2=0
# at primes above the threshold.  We test at SMALL m where exhaustive search is feasible,
# using a prime ABOVE the threshold.
# ---------------------------------------------------------------------------
def check_emptiness_above_threshold():
    print("\n=== CHECK 1b: above-threshold char-0 emptiness for odd-pair-count sizes ===")
    for m in [3]:
        n = 1 << m
        half = 1 << (m - 1)
        for asize in range(3, min(n, 7) + 1):
            npairs = asize * (asize - 1) // 2
            parity = "ODD" if npairs % 2 == 1 else "even"
            threshold = (half * asize * asize) ** half  # (2^(m-1)*|A|^2)^(2^(m-1))
            # find a prime above threshold with the subgroup
            p = None
            cand = threshold - (threshold % n) + 1
            while cand <= threshold:
                cand += n
            tries = 0
            while tries < 2_000_000:
                if isprime(cand) and (cand - 1) % n == 0 and n < cand - 1:
                    p = cand
                    break
                cand += n
                tries += 1
            if p is None:
                print(f"  m={m} |A|={asize}: no prime found above threshold {threshold}")
                continue
            g = primitive_2m_root(p, n)
            # exhaustive search for e2=0 subsets of size asize
            zero_subs = 0
            zero_with_e1 = 0
            checked = 0
            for S in itertools.combinations(range(n), asize):
                if e2_of_subset(S, g, p, n) == 0:
                    zero_subs += 1
                    if e1_of_subset(S, g, p, n) != 0:
                        zero_with_e1 += 1
                checked += 1
            print(f"  m={m} n={n} |A|={asize} pairs={npairs}({parity}) "
                  f"thr={threshold} p={p}: e2=0 subsets={zero_subs}, "
                  f"of-those e1!=0={zero_with_e1}  (checked {checked})")

# ---------------------------------------------------------------------------
# CHECK 2: the DECISIVE trap. Is the threshold reachable in the prize regime?
# prize: p ~ n^beta, beta in [4,5].  threshold = (n/2 * |A|^2)^(n/2).
# For production dim, |A| = k+2 with k = O(n)  (say k ~ rho*n, rho in {1/2,1/4,1/8,1/16}).
# ---------------------------------------------------------------------------
def check_prize_regime_threshold():
    print("\n=== CHECK 2: is the threshold REACHABLE in the prize regime? (decisive) ===")
    print("    threshold = (2^(m-1) * |A|^2)^(2^(m-1));  prize prime ~ n^beta, beta<=5")
    print("    Need threshold < p for the theorem to apply.")
    print()
    print(f"  {'mu=m':>5} {'n':>10} {'|A|~k+2':>10} {'log2(threshold)':>16} {'log2(prize p=n^5)':>18} {'theorem applies?':>18}")
    import math
    for m in [3, 4, 5, 8, 16, 30]:
        n = 1 << m
        half = 1 << (m - 1)
        # production dim: take the LARGEST relevant rate rho=1/2 (k=n/2), |A|=k+2
        k = n // 2
        A = k + 2
        log2_threshold = half * math.log2(half * A * A)  # log2((2^(m-1)*A^2)^(2^(m-1)))
        log2_prize = 5 * math.log2(n)  # p = n^5 (top of prize beta range)
        applies = log2_threshold < log2_prize
        print(f"  {m:>5} {n:>10} {A:>10} {log2_threshold:>16.1f} {log2_prize:>18.1f} {str(applies):>18}")
    print()
    print("  (Also try the SMALLEST production |A|: smallest k=0 mod 4 with k>=4, i.e. |A|=6 const.)")
    print(f"  {'mu=m':>5} {'n':>10} {'|A|':>6} {'log2(threshold)':>16} {'log2(prize p=n^5)':>18} {'applies?':>10}")
    for m in [3, 4, 5, 8, 16, 30]:
        n = 1 << m
        half = 1 << (m - 1)
        A = 6  # |A| = k+2 with k=4 (smallest production dim) -> CONSTANT agreement size
        log2_threshold = half * math.log2(half * A * A)
        log2_prize = 5 * math.log2(n)
        applies = log2_threshold < log2_prize
        print(f"  {m:>5} {n:>10} {A:>6} {log2_threshold:>16.1f} {log2_prize:>18.1f} {str(applies):>10}")

if __name__ == "__main__":
    check_parity_identity()
    check_emptiness_above_threshold()
    check_prize_regime_threshold()
