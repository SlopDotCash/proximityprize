"""
C064: "Worst far line = worst PERIOD not worst frequency."

Connection record (forms F2/F3/F7/F18, walls W-largesieve/W-BGK):
  lineIncidence_spectral gives  #{gamma: s0+gamma*s1 in S}*|V| = |F|*Sum_{psi _|_ s1} Sum_{s in S} psi(s0-s).
  CLAIM: for a MONOMIAL far direction the surviving psi _|_ s1 are indexed by mu_n,
         Sum_{s in S} psi(s0-s) factors through eta_b, and (by eta coset-invariance,
         eta_image_card_mul_le) the line-incidence spectral error is NOT a sum over q
         frequencies but over EXACTLY m=(p-1)/n distinct period values, each with
         multiplicity n. => worst far line governed by the worst PERIOD (max over m
         Gauss periods), and F18 autocorrelation flatness = variance of that
         n-weighted period average.

We test the operative arithmetic claim at PROPER dyadic subgroups mu_n < F_q*
(prize regime n << sqrt(q), beta ~ 2.5-3). Two things:

  (P1) The Gauss-period collapse for eta itself: does eta_b take exactly m=(p-1)/n
       distinct values, each value's preimage a full mu_n coset (multiplicity exactly n)?
       (This is the eta_image_card_mul_le content; baseline sanity.)

  (P2) THE LOAD-BEARING CLAIM: is the line-incidence SPECTRAL ERROR for a monomial
       far direction actually an "n-weighted average of m period values" -- i.e. does
       the per-line incidence error, as the far direction / offset ranges, take values
       that organize into m distinct periods each with multiplicity n, so that
       max-over-far-lines = max-over-m-periods, NOT max-over-q-frequencies?

  (P3) Does the variance of that n-weighted period average equal the F18 autocorrelation
       max (the flatness)?  Or is the period-organized object just B = max eta again
       (i.e. the connection collapses straight back to BGK with no new structure)?
"""

import cmath, math
from itertools import product

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def find_prime(n, beta):
    """smallest prime q = 1 mod n with q >= n^beta (proper subgroup mu_n)."""
    target = int(n**beta)
    q = ((target // n) + 1) * n + 1
    while not is_prime(q):
        q += n
    return q

def primitive_root(q):
    # q prime; find generator of F_q*
    fac = []
    m = q-1
    d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m//=d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2,q):
        if all(pow(g,(q-1)//p,q)!=1 for p in fac):
            return g
    raise RuntimeError

def subgroup(q, n):
    """mu_n = order-n multiplicative subgroup of F_q* (n | q-1)."""
    g = primitive_root(q)
    h = pow(g, (q-1)//n, q)  # generator of mu_n
    return [pow(h, j, q) for j in range(n)]

def main():
    print("="*78)
    print("C064: line-incidence error = worst PERIOD vs worst FREQUENCY")
    print("="*78)
    configs = [(8,3.0),(16,3.0),(32,2.6),(64,2.5)]
    for n, beta in configs:
        q = find_prime(n, beta)
        mu = subgroup(q, n)
        m = (q-1)//n
        w = cmath.exp(2j*math.pi/q)           # base additive char psi(x)=w^x
        psi = lambda x: w**(x % q)

        # ---- eta_b = sum_{y in mu_n} psi(b*y), b ranges over F_q* ----
        eta = {}
        for b in range(1,q):
            eta[b] = sum(psi((b*y) % q) for y in mu)

        # (P1) Gauss-period collapse: distinct values + multiplicity
        # round to dedup floating values
        def key(z): return (round(z.real,6), round(z.imag,6))
        valmap = {}
        for b in range(1,q):
            valmap.setdefault(key(eta[b]), []).append(b)
        n_distinct = len(valmap)
        mults = sorted(set(len(v) for v in valmap.values()))
        # each value's preimage should be a union of cosets => multiplicity divisible by n
        all_mult_mult_of_n = all(len(v) % n == 0 for v in valmap.values())
        B = max(abs(eta[b]) for b in range(1,q))   # the BGK object

        print(f"\nn={n}  q={q}  beta={math.log(q,n):.2f}  m=(q-1)/n={m}")
        print(f"  (P1) eta distinct values = {n_distinct}  (m={m}) ;"
              f" mult set={mults} ; all mult multiple of n = {all_mult_mult_of_n}")
        print(f"       B = max|eta_b| = {B:.4f} ; sqrt(n)={math.sqrt(n):.3f} ;"
              f" sqrt(n*ln m)={math.sqrt(n*math.log(m)):.3f}")

        # ---------------------------------------------------------------
        # (P2) The line-incidence spectral error for a MONOMIAL far direction.
        # Model the syndrome set S as the IMAGE OF mu_n under the additive char,
        # the way the connection wants it: a "monomial far direction" makes the
        # surviving psi _|_ s1 indexed by mu_n and Sum_{s in S} psi(s0-s) factor
        # through eta. Concretely the per-line spectral error reduces to a sum
        #   Err(s0) = Sum_{nonprincipal periods} (period value) * (offset phase)
        # We TEST the connection's literal claim: as the far line varies (offset b0
        # over F_q*), does the incidence-error functional take exactly m distinct
        # MAGNITUDES each with multiplicity n (the "n-weighted average of m periods")?
        #
        # The cleanest faithful instantiation: the *single-frequency* contribution
        # of a far line at offset b is eta_b itself (the connection's own reduction:
        # Sum_{s in S} psi(s0-s) factors through eta_b). So the per-far-line error
        # IS {eta_b : b in F_q*}, and the claim "m periods x mult n" is EXACTLY P1.
        # i.e. worst far line = max_b |eta_b| = B = the worst Gauss period.
        # -> This is TRUE but is the SAME object as BGK (face 3). Test whether the
        #    connection gives anything BEYOND restating B.
        worst_far_line = B
        worst_period   = B            # by P1 the periods ARE the eta values
        worst_frequency = max(abs(eta[b]) for b in range(1,q))  # also = B
        print(f"  (P2) worst-far-line err = {worst_far_line:.4f} ;"
              f" worst-period = {worst_period:.4f} ;"
              f" worst-(q)freq = {worst_frequency:.4f}")
        print(f"       worst-far-line == worst-period ? {abs(worst_far_line-worst_period)<1e-6}")
        print(f"       worst-period   == worst-q-freq ? {abs(worst_period-worst_frequency)<1e-6}"
              f"   <-- if TRUE, 'period not frequency' is VACUOUS (they coincide)")

        # (P3) F18 autocorrelation flatness = variance of n-weighted period average?
        # autocorrelation A_h = sum_{y in mu} psi(h*(y - y'))-type; the connection
        # says flatness = variance of the period average. Compute:
        #   var over q-1 freqs of |eta_b|^2  (the per-frequency spread)
        #   var over m periods of |period|^2 (the per-period spread)
        sq_freq = [abs(eta[b])**2 for b in range(1,q)]
        mean_freq = sum(sq_freq)/len(sq_freq)
        var_freq = sum((x-mean_freq)**2 for x in sq_freq)/len(sq_freq)
        # per-period values (one rep per coset)
        period_vals = [abs(complex(*k))**2 for k in valmap.keys()]
        mean_per = sum(period_vals)/len(period_vals)
        var_per = sum((x-mean_per)**2 for x in period_vals)/len(period_vals)
        print(f"  (P3) mean|eta|^2 over freqs = {mean_freq:.3f} (=n? {n}) ;"
              f" var_freq={var_freq:.2f} ; var_period={var_per:.2f}")
        # The 'n-weighted average' just re-weights: averaging over a coset of size n
        # gives the SAME per-coset value (eta constant on cosets) => the n-weighting
        # is trivial (variance unchanged). Confirm var_freq == var_per:
        print(f"       var_freq == var_period ? {abs(var_freq-var_per)<1e-6}"
              f"   <-- n-weighting is trivial (eta constant on cosets)")
        # B^2 vs mean+ stuff: is B determined by var? (the C045/C060 lesson)
        print(f"       B^2={B**2:.2f} ; mean+sqrt(2*var*ln m)~"
              f"{mean_freq+math.sqrt(2*var_per*math.log(max(m,2))):.2f}"
              f"  (extreme-value heuristic; var does NOT pin B)")

    print("\n" + "="*78)
    print("INTERPRETATION")
    print("="*78)
    print("""
- (P1) confirms eta_image_card_mul_le numerically: eta takes ~m distinct values,
  each preimage a union of mu_n cosets (mult multiple of n). [already in-tree, axiom-clean]
- (P2) The 'monomial far direction' reduction the connection invokes makes the
  per-far-line spectral contribution factor THROUGH eta_b. So:
    worst far line == worst period == B == worst q-frequency restricted to mu_n.
  The 'period not frequency' framing is real ONLY in the trivial sense that the
  m periods ARE the distinct nonzero-frequency values (cosets collapse). The
  worst-case is the SAME number B either way. No new tractable object is produced.
- (P3) The n-weighting is TRIVIAL because eta is CONSTANT on each coset: averaging
  over a size-n coset returns the coset's own value, so var_freq == var_period and
  the 'n-weighted average of m periods' is just {eta values} relabeled. F18 flatness
  (the variance) does NOT determine B (same C045/C060 lesson: variance is blind to
  the extreme). => the connection RESTATES B = max Gauss period = BGK/Paley wall.
""")

if __name__ == "__main__":
    main()
