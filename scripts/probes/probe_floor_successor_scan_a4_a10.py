#!/usr/bin/env python3
"""
LANE A3 — falsify-first successor scan for the floor-localization route.

The Lean scanner (FloorClosureSuccessorScanner / _FloorClosureContract) is parametrized by an
ABSTRACT `FloorBad : ℕ → ℕ → Prop`; `CandidateListExactAt FloorBad a` is NOT a concrete decidable
predicate inside Lean (it depends on FloorBad's content, which is the external F_p-rank /
resultant computation, never formalized). So a genuine Lean `verifiedOn_Icc` certificate cannot
be produced from inside Lean alone.

This probe supplies the missing CONCRETE content numerically, using the in-tree canonical
resultant predicate as the operational floor-bad predicate:

  canonicalRatioPoly(n) = (X^4+1)^n - (X^2+1)^n
  canonicalRatioBadPrimes(n) = prime factors of Res(Φ_n, canonicalRatioPoly(n))

For n = 2^a, a prime p ≡ 1 mod n is "floor-bad" (canonical sense) iff there exists a primitive
n-th root ζ in F_p with (ζ^4+1)^n ≡ (ζ^2+1)^n (mod p), i.e. Φ_n and the obstruction poly share a
root mod p. We compute, per rung a:

  least  := smallest prime ≡ 1 mod 2^a
  badsplit := the set of split primes (≡ 1 mod 2^a, up to a bound) that ARE canonical-floor-bad

CandidateListExactAt holds at rung a  <=>  badsplit == {least}   (singleton least-prime rule exact).

A single (exact at a) AND (not exact at a+1) pair KILLS the uniform-floor-localization route.
A clean verified prefix a=4..10 is honest evidence (NOT proof; the uniform ∀a step stays open).
"""

def is_prime(m):
    if m < 2: return False
    if m < 4: return True
    if m % 2 == 0: return False
    d = 3
    while d * d <= m:
        if m % d == 0: return False
        d += 2
    return True

def primes_1_mod_n(n, bound):
    """All primes p with p % n == 1 and p <= bound, ascending."""
    out = []
    p = n + 1
    while p <= bound:
        if is_prime(p):
            out.append(p)
        p += n
    return out

def has_primitive_nth_root_obstruction(p, n):
    """True iff exists ζ in F_p of multiplicative order exactly n with
       (ζ^4+1)^n == (ζ^2+1)^n  (mod p).  p ≡ 1 mod n assumed."""
    # generator-free: enumerate elements of order dividing n = the n-th roots of unity,
    # which form the unique subgroup of order n (since n | p-1). Build it from a generator g.
    g = None
    for cand in range(2, p):
        if pow(cand, (p - 1) // 2, p) != 1:  # quick non-residue-ish; find a generator properly below
            pass
    # find a primitive root mod p (p prime)
    g = find_primitive_root(p)
    h = pow(g, (p - 1) // n, p)  # h has order exactly n
    # primitive n-th roots are h^k with gcd(k,n)=1
    from math import gcd
    z = h
    found = False
    cur = h
    for k in range(1, n + 1):
        if gcd(k, n) == 1:
            zk = pow(h, k, p)
            lhs = pow((pow(zk, 4, p) + 1) % p, n, p)
            rhs = pow((pow(zk, 2, p) + 1) % p, n, p)
            if lhs == rhs:
                found = True
                break
    return found

def find_primitive_root(p):
    if p == 2: return 1
    phi = p - 1
    # factor phi
    fac = factorize(phi)
    for g in range(2, p):
        ok = True
        for q in fac:
            if pow(g, phi // q, p) == 1:
                ok = False
                break
        if ok:
            return g
    raise RuntimeError("no primitive root")

def factorize(m):
    fs = set()
    d = 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d); m //= d
        d += 1
    if m > 1: fs.add(m)
    return fs

def candidate_exact_at(a, split_bound):
    n = 1 << a
    splits = primes_1_mod_n(n, split_bound)
    if not splits:
        return None
    least = splits[0]
    badsplit = [p for p in splits if has_primitive_nth_root_obstruction(p, n)]
    exact = (badsplit == [least])
    return dict(n=n, least=least, n_splits=len(splits), badsplit=badsplit,
                exact=exact, splits_bound=split_bound)

def main():
    print("LANE A3 falsify-first successor scan (canonical-resultant floor-bad predicate)\n")
    # bound: scan enough split primes per rung to have a meaningful exactness test.
    # split density ~ 1/(phi(n) log) so use a generous multiple of n.
    results = {}
    for a in range(4, 11):
        n = 1 << a
        bound = max(50 * n, 20000)
        # cap heavy rungs: order-n subgroup enumeration is O(n) per prime; for a=10 n=1024 fine
        r = candidate_exact_at(a, bound)
        results[a] = r
        if r is None:
            print(f"a={a:2d} n={n:5d}  NO split primes <= {bound}")
            continue
        tag = "EXACT" if r['exact'] else "NOT-EXACT"
        print(f"a={a:2d} n={n:5d}  least={r['least']:6d}  #splits<= {bound}={r['n_splits']:4d}  "
              f"badsplit={r['badsplit'][:8]}{'...' if len(r['badsplit'])>8 else ''}  => {tag}")

    print("\n--- successor-pair verdict (exact at a AND not-exact at a+1) ---")
    killer = None
    for a in range(4, 10):
        ra, rb = results.get(a), results.get(a + 1)
        if ra is None or rb is None: continue
        if ra['exact'] and not rb['exact']:
            killer = (a, a + 1)
            print(f"KILLER PAIR: CandidateListExactAt {a} holds, CandidateListExactAt {a+1} FAILS "
                  f"-> uniform-floor-localization route REFUTED at rung {a}->{a+1}")
    if killer is None:
        # report prefix verdict
        exacts = [a for a in range(4, 11) if results.get(a) and results[a]['exact']]
        print(f"No exact-then-failing adjacent pair found in a=4..10.")
        print(f"Rungs where singleton least-prime rule is EXACT (within scanned split bound): {exacts}")
        nonexact = [a for a in range(4, 11) if results.get(a) and not results[a]['exact']]
        print(f"Rungs NOT exact (extra bad split primes appear): {nonexact}")

if __name__ == "__main__":
    main()
