"""
sweep_A33_realizability.py  —  Actionable A33 (merged 407-T05).

QUESTION (the one untried R-thin lever).
  R-thin: a *ragged* agreement set S of a GENUINE monomial line  L_gamma(x) = x^a + gamma*x^b
  on mu_n (n = 2^mu),  d = gcd(a-b, n) >= 2,  s = n/d, satisfies  |S| <= sqrt(n*k)  (rho = k/n).

  All MOMENT / SPECTRAL / PSD / FOLD levers were proven EMPTY by the prior #407 work:
  the LP over autocorrelations  v_t = |S cap omega^t S|  with the full PSD cone
  collapses to LP(orbit-incidence-only) at every prize direction d = n/s
  -> only the lowest Fourier mode lambda_0 = sum_t v_t binds; higher moments add NOTHING.
  Residual gap to sqrt(n*k) is a CONSTANT ~ s/2, char-free, that the circulant-of-counts
  cannot remove.

  THE ONE UNTRIED LEVER = REALIZABILITY.  The autocorrelation profile v is NOT free:
  S is the agreement set of ONE degree-<k polynomial c (curve-decodability), and the
  L = d twist codewords  c_omega(x) = omega^{-a} c(omega x)  all share that single c
  (a global Toeplitz / Hankel rank-<=k constraint the circulant-of-counts discards).

  We TEST whether a realizability-aware count beats sqrt(n*k) at intermediate d
  (Kambire worst direction d ~ n/s), n = 16, 32 (and 64 sampled), char-free.

WHAT WE COMPUTE (all EXACT over a finite field F_q, q = 1 mod n so mu_n subset F_q*):
  For each genuine direction (a,b) [equivalently d = gcd(a-b,n), worst = intermediate d]:
   (i)  TRUE-REALIZABLE max |S| :
          max over deg-<k polys c of  |{ x in mu_n : c(x) = x^a + gamma*x^b for some gamma }|.
        Equivalently: how many points of mu_n can lie on the curve  y = c(x)  AND on the
        line family  y = x^a + gamma*x^b.  Since gamma is free (one scalar), the agreement
        condition on a candidate set T (|T|>=2) is:
            the map  x -> (c(x) - x^a) / x^b   is CONSTANT (= gamma) on T,
        i.e.  (c(x) - x^a) = gamma * x^b  for all x in T.
        So  c(x) - x^a - gamma*x^b = 0 on T  for a single deg-<k c and single gamma.
        We enumerate the LARGEST T subset of mu_n on which there EXIST c (deg<k) and gamma
        making  c(x) = x^a + gamma*x^b  for all x in T.  This is exactly:
            x^a + gamma*x^b  restricted to T  is interpolated by a deg-<k poly.
        Realizability = a Vandermonde/Hankel rank test: the values w_x = x^a + gamma*x^b on T
        are the evaluations of a deg-<k poly  <=>  every (k+1)-subset of (x, w_x) has the
        deg-<k interpolation consistency (RS code membership), one free param gamma.
   (ii) ORBIT-INCIDENCE relaxation bound  |S| <= sqrt(n*k) + Theta(s)   (the proven-loose LP cap).
   (iii) sqrt(n*k)  (the R-thin / Johnson target).

  VERDICT criterion:  does (i)  TRUE-REALIZABLE max  <  sqrt(n*k)  at intermediate d
  (i.e. does realizability BEAT the target), and by how much, char-free across several q?

Self-contained: pure-python finite-field linear algebra; numpy only for tabulation.
Run:  python sweep_A33_realizability.py
"""

import itertools
import math

# ----------------------------------------------------------------------------
# minimal exact F_q linear algebra (q prime)
# ----------------------------------------------------------------------------

def inv_mod(a, q):
    return pow(a % q, q - 2, q)

def find_primitive_root(q):
    # q prime
    if q == 2:
        return 1
    phi = q - 1
    # factor phi
    fac = {}
    m = phi
    d = 2
    while d * d <= m:
        while m % d == 0:
            fac[d] = fac.get(d, 0) + 1
            m //= d
        d += 1
    if m > 1:
        fac[m] = fac.get(m, 0) + 1
    for g in range(2, q):
        ok = True
        for pf in fac:
            if pow(g, phi // pf, q) == 1:
                ok = False
                break
        if ok:
            return g
    raise RuntimeError("no primitive root")

def mu_n_elements(n, q):
    """The n-th roots of unity in F_q (requires n | q-1). Returns list of field elements,
       ordered as zeta^0, zeta^1, ..., zeta^{n-1} where zeta = g^{(q-1)/n}."""
    assert (q - 1) % n == 0, f"n={n} does not divide q-1={q-1}"
    g = find_primitive_root(q)
    zeta = pow(g, (q - 1) // n, q)
    return [pow(zeta, j, q) for j in range(n)], zeta

def rank_mod(rows, q):
    """rank of a matrix (list of rows) over F_q via Gaussian elimination."""
    rows = [r[:] for r in rows]
    if not rows:
        return 0
    ncols = len(rows[0])
    r = 0
    for c in range(ncols):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][c] % q != 0:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        invp = inv_mod(rows[r][c], q)
        rows[r] = [(x * invp) % q for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % q != 0:
                f = rows[i][c]
                rows[i] = [(rows[i][j] - f * rows[r][j]) % q for j in range(ncols)]
        r += 1
        if r == len(rows):
            break
    return r

def interpolable_deg_lt_k(points, q, k):
    """points: list of (x, y) in F_q^2 with DISTINCT x. Returns True iff there is a poly
       of degree < k with c(x)=y for all points. RS membership: build Vandermonde
       [1,x,...,x^{k-1} | y] and check rank(V) == rank(V|y)."""
    if len(points) <= k:
        return True  # k points always interpolated by deg<k
    V = []
    Vy = []
    for (x, y) in points:
        row = [pow(x, j, q) for j in range(k)]
        V.append(row)
        Vy.append(row + [y % q])
    return rank_mod(V, q) == rank_mod(Vy, q)

# ----------------------------------------------------------------------------
# TRUE realizable max ragged |S| for a genuine direction (a,b)
# ----------------------------------------------------------------------------

def true_realizable_max(n, k, a, b, q, mu, max_T=None):
    """Largest T subset of mu_n (as exponent set on zeta) such that there EXIST a deg-<k
       poly c and a scalar gamma with  c(zeta^j) = zeta^{a j} + gamma*zeta^{b j}  for all j in T.

       For a CANDIDATE exponent set Texp (subset of 0..n-1) we must check: does there exist
       gamma and deg-<k c with the agreement holding on all of Texp?
       Equivalently, the points (x_j, w_j) with w_j = x_j^a + gamma*x_j^b lie on a deg-<k poly.
       gamma is one free scalar. We search:
         for |Texp| <= k+1: ALWAYS realizable for SOME gamma (under-determined / free) -> not ragged-interesting.
         The binding regime is |Texp| >= k+2.
       We test realizability as: there exists gamma s.t. the |Texp| points (x, x^a+gamma x^b)
       lie on one deg-<k poly. The set of (c, gamma) is a linear system; we test feasibility
       by checking whether  [Vandermonde_k(x) | -x^b]  spans the vector  (x^a)  -- i.e. solve
            V * c_coeffs - gamma * (x^b vector) = (x^a vector)   over Texp,  unknowns (c_coeffs[k], gamma).
       Feasible  <=>  rank(M) == rank(M | rhs),  M = [V | -x^b], rhs = x^a.
    """
    half = n // 2
    if max_T is None:
        max_T = n
    mu_elts, zeta = mu_n_elements(n, q)
    # x_j = zeta^j ; x_j^a = zeta^{a j}, etc.
    def realizable(Texp):
        # build M = [ V_k(x) | -x^b ]  rhs = x^a ,  rows over Texp
        M = []
        Mr = []
        for j in Texp:
            x = mu_elts[j % n]
            vrow = [pow(x, t, q) for t in range(k)]
            xb = pow(x, b, q)
            xa = pow(x, a, q)
            row = vrow + [(-xb) % q]          # unknowns: c_0..c_{k-1}, gamma
            M.append(row)
            Mr.append(row + [xa % q])
        return rank_mod(M, q) == rank_mod(Mr, q)

    # find the largest realizable Texp. Exhaustive is C(n, t); we search t downward and
    # use a greedy/branch with exact verification. For n<=16 fully exhaustive is fine;
    # for n=32,64 we do a randomized + greedy-extension search with many restarts.
    import random
    best = 0
    best_set = None
    if n <= 16:
        # exhaustive over all subset sizes from large to small, stop at first realizable size
        for t in range(n, k + 1, -1):
            found = None
            for Texp in itertools.combinations(range(n), t):
                if realizable(Texp):
                    found = Texp
                    break
            if found is not None:
                return t, list(found)
        return k + 1, list(range(k + 1))  # trivially realizable
    else:
        # heuristic: greedy maximal realizable set with many random seeds
        seeds = 4000
        for _ in range(seeds):
            order = list(range(n))
            random.shuffle(order)
            cur = []
            for j in order:
                if realizable(cur + [j]):
                    cur.append(j)
            if len(cur) > best:
                best = len(cur)
                best_set = cur[:]
        return best, best_set

# ----------------------------------------------------------------------------
# main sweep
# ----------------------------------------------------------------------------

def primes_1_mod_n(n, count, start):
    out = []
    cand = start
    if cand % n != 1:
        cand += (n - (cand - 1) % n) % n
        cand = ((cand - 1) // n) * n + 1
    cand = ((start - 1) // n) * n + 1
    while cand <= start:
        cand += n
    while len(out) < count:
        if cand > 1 and is_prime(cand):
            out.append(cand)
        cand += n
    return out

def is_prime(m):
    if m < 2:
        return False
    if m % 2 == 0:
        return m == 2
    d = 3
    while d * d <= m:
        if m % d == 0:
            return False
        d += 2
    return True

def run_for_n(n, rhos, q_list, mu):
    print("=" * 84)
    print(f"n = {n} = 2^{mu}")
    print("=" * 84)
    for rho in rhos:
        k = int(round(rho * n))
        if k < 1:
            continue
        target = math.sqrt(n * k)  # sqrt(n*k) = Johnson / R-thin target
        print(f"\n  rho = {rho}, k = {k},  sqrt(n*k) = {target:.3f},  Johnson 1-sqrt(rho) agree band ~ {target:.1f}")
        # directions: GENUINE monomial line  x^a + gamma*x^b  with a,b NOT in the code
        # (a,b >= k so the line is genuinely outside RS[k]) and d = gcd(a-b, n).
        # worst (Kambire) = intermediate d. enumerate distinct achievable d with a,b>=k.
        ds = sorted(set(math.gcd(abs(aa - bb), n)
                        for aa in range(k, n) for bb in range(k, n) if aa != bb))
        header = f"    {'d':>4} {'s=n/d':>6} {'(a,b)':>9} {'q':>9} | {'true|S|':>8} {'sqrt(nk)':>9} {'beats?':>7} {'orbit-inc':>10}"
        print(header)
        for d in ds:
            if d == n:
                continue
            s = n // d
            # a representative GENUINE direction with gcd(a-b,n)=d and a,b>=k
            a, b = None, None
            for bb in range(k, n):
                aa = bb + d
                if aa < n and math.gcd(aa - bb, n) == d:
                    a, b = aa, bb
                    break
            if a is None:
                continue
            # orbit-incidence relaxation:  |S| <= n/(2d) + sqrt((n/2d)^2 + n*(d-1)*(k-1)/d)
            t1 = n / (2.0 * d)
            orbit_inc = t1 + math.sqrt(t1 * t1 + n * (d - 1) * (k - 1) / d)
            for q in q_list:
                if (q - 1) % n != 0:
                    continue
                tS, _ = true_realizable_max(n, k, a, b, q, mu)
                beats = "YES" if tS < target - 1e-9 else "no"
                ab = f"({a},{b})"
                print(f"    {d:>4} {s:>6} {ab:>9} {q:>9} | {tS:>8} {target:>9.3f} {beats:>7} {orbit_inc:>10.2f}")
                break  # one prime per d for the table; multi-q char-test below

def char_dependence_test(n, rho, mu, q_list):
    """For the WORST (intermediate-d) direction, check true|S| across several primes q=1 mod n."""
    k = int(round(rho * n))
    target = math.sqrt(n * k)
    ds = sorted(set(math.gcd(abs(aa - bb), n)
                    for aa in range(k, n) for bb in range(k, n) if aa != bb
                    if math.gcd(abs(aa - bb), n) not in (1, n)))
    if not ds:
        return
    # Kambire worst is intermediate d; scan the d closest to sqrt(n)
    target_d = min(ds, key=lambda dd: abs(dd - max(2, int(round(n ** 0.5)))))
    a, b = None, None
    for bb in range(k, n):
        aa = bb + target_d
        if aa < n and math.gcd(aa - bb, n) == target_d:
            a, b = aa, bb
            break
    if a is None:
        return
    print(f"\n  [char-dependence @ n={n}, rho={rho}, k={k}] worst-ish d={target_d}, s={n//target_d}, (a,b)=({a},{b}), sqrt(nk)={target:.3f}")
    vals = []
    for q in q_list:
        if (q - 1) % n != 0:
            continue
        tS, _ = true_realizable_max(n, k, a, b, q, mu)
        vals.append((q, tS))
        print(f"      q={q:>9}  true|S|={tS}  beats sqrt(nk)={'YES' if tS<target-1e-9 else 'no'}")
    uniq = set(v for _, v in vals)
    print(f"      -> char-{'INDEPENDENT' if len(uniq)==1 else 'DEPENDENT'} (values {sorted(uniq)})")

if __name__ == "__main__":
    # n=8 (mu=3), n=16 (mu=4) exhaustive ; n=32 (mu=5) heuristic
    # primes q = 1 mod n, several, to test char-(in)dependence.
    print("\n### A33 REALIZABILITY PROBE: does the deg-<k (Hankel/rank) constraint beat sqrt(n*k)?\n")

    # n = 8
    q8 = [p for p in primes_1_mod_n(8, 6, 17)]
    run_for_n(8, [0.5, 0.25], q8, 3)
    char_dependence_test(8, 0.25, 3, q8)

    # n = 16
    q16 = [p for p in primes_1_mod_n(16, 6, 97)]
    run_for_n(16, [0.5, 0.25, 0.125], q16, 4)
    char_dependence_test(16, 0.25, 4, q16)

    # n = 32 (heuristic search for true|S|)
    q32 = [p for p in primes_1_mod_n(32, 3, 193)]
    run_for_n(32, [0.25], q32, 5)
    char_dependence_test(32, 0.25, 5, q32)

    print("\n### DONE.")
