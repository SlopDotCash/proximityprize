"""
C018 follow-up: WHERE does the unconstrained r-subset-sum census reach I_infty?
Test the connection's central caveat that prize-regime (p ~ n^beta, n << sqrt(q)) is
"FAR BELOW threshold so census exactness FAILS".

We sweep ALL primes p = 1 mod n from small to ~n^3, recording census_p vs I_infty,
and report the LAST prime at which census_p != I_infty (the true onset of exactness),
to compare against:
  - the resultant threshold (2^mu)^{2^{mu-1}}  (the Lean SUFFICIENT condition),
  - n^2 (the "small prime / #400-trap" boundary; prize requires n << sqrt(q) i.e. p > n^2),
  - the prize regime p ~ n^4..n^5.

If the true onset is at or below ~n^2, then in the prize regime (p > n^2) the unconstrained
census ALREADY equals I_infty -- i.e. delta* = I_infty^{-1}(n) is q-independent IN the prize
regime, and the connection's claim that exactness fails in-prize is FALSE for the
unconstrained census.
"""
from math import comb
from itertools import combinations


def feas_set(half, r):
    js = []
    for j in range(0, r // 2 + 1):
        if (r - 2 * j) >= 0 and (r - j) <= half:
            js.append(j)
    return js


def I_infty(mu, r):
    half = 2 ** (mu - 1)
    return sum((2 ** (r - 2 * j)) * comb(half, r - 2 * j) for j in feas_set(half, r))


def is_prime(x):
    if x < 2:
        return False
    if x % 2 == 0:
        return x == 2
    i = 3
    while i * i <= x:
        if x % i == 0:
            return False
        i += 2
    return True


def root_of_order(p, order):
    if (p - 1) % order != 0:
        return None
    cof = (p - 1) // order
    for base in range(2, p):
        g = pow(base, cof, p)
        if g != 1 and pow(g, order // 2, p) != 1:
            return g
    return None


def census_p(p, mu, r):
    n_sub = 2 ** mu
    g = root_of_order(p, n_sub)
    if g is None:
        return None
    elems = [pow(g, i, p) for i in range(n_sub)]
    sums = set()
    for S in combinations(elems, r):
        s = 0
        for x in S:
            s = (s + x) % p
        sums.add(s)
    return len(sums)


def sweep(mu, r, p_hi):
    n = 2 ** mu
    Ii = I_infty(mu, r)
    thr = n ** (2 ** (mu - 1))
    last_bad = None
    bad_list = []
    p = n + 1
    while p <= p_hi:
        if (p - 1) % n == 0 and is_prime(p):
            c = census_p(p, mu, r)
            if c is not None and c != Ii:
                last_bad = p
                bad_list.append((p, c, c - Ii))
        p += 1
    print(f"\nmu={mu} n={n} r={r}: I_infty={Ii}  resultant_thr={thr}  n^2={n*n}  n^3={n**3}")
    print(f"  primes p=1 mod {n} up to {p_hi} where census != I_infty: {len(bad_list)} of them")
    for (p, c, d) in bad_list:
        marker = "  <-- > n^2 !!" if p > n * n else ""
        print(f"     p={p:<7} census={c:<6} surplus={d:+d}{marker}")
    if last_bad is None:
        print(f"  ===> census == I_infty for EVERY tested prime (true onset below {n+1})")
    else:
        print(f"  ===> last deviation at p={last_bad}  (={last_bad/(n*n):.2f} * n^2);"
              f"  exactness for all p>{last_bad}")
        print(f"       resultant threshold {thr} is {thr/last_bad:.3e}x larger than true onset")
    return last_bad


def main():
    print("############ unconstrained r-subset-sum census: true onset of q-independence ############")
    # n=8: sweep generously past n^3=512, even to ~5000 to confirm nothing reappears
    for r in [3, 4, 5, 6]:
        sweep(3, r, 5000)
    # n=16: sweep to a few * n^3 = 4096; n^2 = 256.  (heavier: C(16,r))
    for r in [3, 4, 5]:
        sweep(4, r, 4000)


if __name__ == "__main__":
    main()
