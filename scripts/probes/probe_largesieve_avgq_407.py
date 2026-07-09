#!/usr/bin/env python3
r"""
probe_largesieve_avgq_407.py  --  #407: the LARGE-SIEVE / AVERAGE-OVER-q route to the floor.

THE SETUP (the residual, defect form #3):
  Fix n=2^a, depth r. A pair (x,y) in mu_n^{2r} is a p-DEFECT for prime q iff
        S(x) := sum_i x_i  ==  S(y)  (mod q)   but   S(x) != S(y) in C  (i.e. in Z[zeta_n]).
  Equivalently the difference alpha = S(x)-S(y) is a nonzero element of Z[zeta_n], a sparse sum of
  <= 2r roots of unity, and the chosen degree-1 prime q | alpha (q = 1 mod n splits completely;
  pick ONE embedding zeta_n -> g, g a fixed primitive n-th root mod q; then "q | alpha" means
  alpha(g) == 0 mod q -- ONE residue condition mod q, NOT q | N(alpha)).
  The floor  kappa_r <= 1  is (essentially)   #defects(q) <= baseline ~ n^{2r}/q.

THE PRIZE ALLOWS CHOOSING q (explicit code). So we need ONE good q in [Q,2Q], Q ~ 2^168.
We test whether ALMOST ALL such q are good, via moments over q.

THE OBSTRUCTION (recorded): the FIRST moment over q,
      E_q[#defects] = sum_{alpha != 0, sparse} #{q in [Q,2Q], q=1 mod n : alpha(g_q) == 0 mod q}
  is HUGE because rare q where g_q hits a common zero of many alpha dominate.

THIS PROBE tests, with EXACT small-scale enumeration over real primes q:
  (1) the per-q defect count D(q) and its distribution over q in a window (mean, median, max, tail);
  (2) whether the BAD q (D(q) > baseline) are RARE -- i.e. does a good q exist with room to spare;
  (3) the FIRST-moment structure: which alpha drive E_q[D] (heavy-tail diagnosis);
  (4) the SECOND moment Var_q[D] and whether a Chebyshev/large-sieve bound separates good from bad;
  (5) the key large-sieve quantity directly: sum_q |sum_alpha a_alpha e_q(...)|^2 vs the diagonal.

We work at sizes where we can enumerate mu_n^{2r} differences AND scan many primes q exactly.
n in {8,16}, r in {2,3}; q over a real window of primes = 1 mod n.
"""
import sys, math, itertools
from collections import Counter, defaultdict

sys.path.insert(0, 'scripts/probes')

def is_prime(num):
    if num < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if num % q == 0: return num == q
    d = num-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, num)
        if x in (1, num-1): continue
        for _ in range(s-1):
            x = x*x % num
            if x == num-1: break
        else: return False
    return True

def odd_part(x):
    while x % 2 == 0: x //= 2
    return x

def primitive_root(p):
    phi = p-1; facs = []; mm = phi; d = 2
    while d*d <= mm:
        if mm % d == 0:
            facs.append(d)
            while mm % d == 0: mm //= d
        d += 1
    if mm > 1: facs.append(mm)
    for g in range(2, p):
        if all(pow(g, phi//qq, p) != 1 for qq in facs): return g

def order_n_root(p, n):
    """A fixed primitive n-th root of unity mod p (the chosen embedding zeta_n -> z)."""
    g = primitive_root(p)
    z = pow(g, (p-1)//n, p)
    return z

def primes_window(n, Q, count):
    """First `count` primes q == 1 mod n with q >= Q (deep-sparse: odd_part((q-1)/n)>1)."""
    out = []
    q = Q - (Q % n) + 1
    if q < Q: q += n
    while len(out) < count:
        if q > 3 and is_prime(q) and odd_part((q-1)//n) > 1:
            out.append(q)
        q += n
    return out

# ---------------------------------------------------------------------------
# The char-0 difference set: alpha = S(x) - S(y), x,y in mu_n^r, as a vector in
# the group-ring coords Z^n (coeff c_j = #{i: x_i = zeta^j} - #{i: y_i = zeta^j}).
# alpha is "char-0 nonzero" iff this coeff vector, reduced mod Phi_n, is nonzero.
# For n=2^a, reduction mod Phi_n = X^{n/2}+1 is: fold the top half with a sign:
#   c_j (j>=n/2)  ->  subtract from c_{j-n/2}.  So the reduced vector r_j = c_j - c_{j+n/2}, j<n/2.
# alpha char-0 == 0  iff  r_j = 0 for all j < n/2  iff  c_j = c_{j+n/2} for all j.
# ---------------------------------------------------------------------------

def reduced_vec(coeff, n):
    h = n//2
    return tuple(coeff[j] - coeff[j+h] for j in range(h))

def enumerate_sumclasses(n, r):
    """For each multiset of r elements of {0..n-1} (the exponents), the group-ring coeff vector.
       Returns list of (coeff_tuple_len_n, reduced_tuple_len_n/2). Enumerate ORDERED then reduce by
       coeff (multiset) to keep it exact but compact."""
    classes = {}
    for tup in itertools.combinations_with_replacement(range(n), r):
        coeff = [0]*n
        for t in tup: coeff[t] += 1
        # multiplicity of this ordered-count among r-tuples:
        # number of orderings = r! / prod(mult!)
        mult = 1
        cc = Counter(tup)
        num = math.factorial(r)
        den = 1
        for v in cc.values(): den *= math.factorial(v)
        mult = num // den
        key = tuple(coeff)
        classes[key] = classes.get(key, 0) + mult
    return classes  # coeff_tuple -> number of ORDERED r-tuples giving it


def main():
    print("="*92)
    print(" #407 LARGE-SIEVE / AVERAGE-OVER-q ROUTE: are almost all primes q good for the floor?")
    print("="*92)

    for (n, r) in [(8, 2), (8, 3), (16, 2)]:
        h = n//2
        print(f"\n{'#'*88}\n n={n}, r={r}  (depth 2r={2*r} roots of unity; phi(n)={h})\n{'#'*88}")

        # char-0 sum classes at depth r: coeff vector -> #ordered r-tuples
        classes = enumerate_sumclasses(n, r)
        coeffs = list(classes.keys())
        weights = [classes[c] for c in coeffs]   # # ordered r-tuples
        Ntup = sum(weights)                       # = n^r
        assert Ntup == n**r, (Ntup, n**r)
        # group classes by their REDUCED vector (char-0 sum value).
        # E_r^char0 = sum over reduced-classes of (#ordered tuples in class)^2
        red_groups = defaultdict(int)             # reduced_vec -> # ordered r-tuples
        for c, w in zip(coeffs, weights):
            red_groups[reduced_vec(c, n)] += w
        Er0 = sum(v*v for v in red_groups.values())
        # baseline #defects ~ (n^{2r} - Er0)/q ... actually defect = pairs equal mod q but not in C.
        # Total pairs N^2 = n^{2r}. Equal-in-C pairs = Er0. So "off-diagonal" pairs = n^{2r}-Er0.
        # Each off-diagonal pair (x,y) is a defect for q iff alpha(g_q)==0 mod q.
        offdiag = n**(2*r) - Er0
        print(f"  char-0 energy E_r^0 = {Er0}  ((2r-1)!!*n^r = {math.prod(range(1,2*r,2))*n**r}); "
              f"off-diagonal pairs n^2r - E0 = {offdiag}")

        # Build the list of DISTINCT nonzero char-0 differences alpha = c_x - c_y (reduced),
        # with their multiplicity = #{ordered (x,y) pairs giving this alpha}.
        # alpha lives in Z^{h} (reduced coords). #defects(q) = sum over alpha!=0 of mult(alpha)*[alpha(g_q)==0 mod q].
        # mult(alpha) = sum_{cx,cy : red(cx)-red(cy)=alpha} w(cx)*w(cy).
        # Compute via convolution of reduced-class histogram.
        # red_hist: reduced_vec -> total ordered tuples
        red_items = list(red_groups.items())
        # alpha multiplicities:
        alpha_mult = defaultdict(int)
        for (rv1, w1) in red_items:
            for (rv2, w2) in red_items:
                alpha = tuple(rv1[j]-rv2[j] for j in range(h))
                if any(alpha):
                    alpha_mult[alpha] += w1*w2
        # sanity: sum over alpha!=0 of mult = offdiag
        assert sum(alpha_mult.values()) == offdiag, (sum(alpha_mult.values()), offdiag)
        n_distinct_alpha = len(alpha_mult)
        print(f"  distinct nonzero char-0 differences alpha: {n_distinct_alpha}  "
              f"(total mult {offdiag})")

        # window of primes q (deep-sparse, q ~ n^4..n^5 ish but kept enumerable)
        # choose Q so q in prize-ish depth but we can scan ~a few hundred primes
        for beta in [4.0]:
            Q = int(round(n**beta))
            qs = primes_window(n, Q, 400)
            print(f"\n  --- window: {len(qs)} primes q>= {Q} (~n^{beta}), q==1 mod n, deep-sparse ---")
            print(f"      q from {qs[0]} to {qs[-1]} (2^{math.log2(qs[0]):.1f}..2^{math.log2(qs[-1]):.1f})")

            # For each q, choose the embedding z = order-n root, evaluate alpha(z) mod q for all alpha,
            # D(q) = sum of mult(alpha) over alpha with alpha(z)==0 mod q.
            # baseline = offdiag / q  (random heuristic: each alpha vanishes mod q w.p. 1/q).
            Dvals = []
            # precompute alpha list as arrays
            alphas = list(alpha_mult.keys())
            mults = [alpha_mult[a] for a in alphas]
            for q in qs:
                z = order_n_root(q, n)
                zpows = [pow(z, j, q) for j in range(h)]   # z^0..z^{h-1}
                D = 0
                for a, m in zip(alphas, mults):
                    val = 0
                    for j in range(h):
                        if a[j]: val += a[j]*zpows[j]
                    if val % q == 0:
                        D += m
                Dvals.append(D)
            Dvals.sort()
            import statistics
            baseline = offdiag / qs[len(qs)//2]
            mean = statistics.mean(Dvals)
            median = statistics.median(Dvals)
            mx = max(Dvals)
            n_good = sum(1 for d in Dvals if d <= baseline)
            n_zero = sum(1 for d in Dvals if d == 0)
            print(f"      baseline (offdiag/q) ~ {baseline:.4f}")
            print(f"      D(q):  min={Dvals[0]}  median={median}  mean={mean:.3f}  max={mx}")
            print(f"      #q with D==0 (NO defect at all): {n_zero}/{len(qs)}  ({100*n_zero/len(qs):.1f}%)")
            print(f"      #q with D<=baseline (GOOD):      {n_good}/{len(qs)}  ({100*n_good/len(qs):.1f}%)")
            # tail
            tail = Counter(Dvals)
            print(f"      D distribution (value:count, top 8): "
                  + ", ".join(f"{v}:{c}" for v,c in sorted(tail.items())[:8]))
            # first moment check: E_q[D] should ~ offdiag * E_q[1/q]*(harmonic over alpha hits)
            print(f"      FIRST MOMENT: mean D = {mean:.3f} vs naive baseline {baseline:.4f}  "
                  f"(ratio {mean/baseline:.2f})")
            # the question: is mean dominated by rare large D? compare mean vs median
            print(f"      heavy-tail diagnosis: mean/median = {mean/max(median,1e-9):.2f}, "
                  f"max/mean = {mx/max(mean,1e-9):.2f}")


if __name__ == "__main__":
    main()
