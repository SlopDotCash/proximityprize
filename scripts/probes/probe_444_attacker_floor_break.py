#!/usr/bin/env python3
"""
probe_444_attacker_floor_break.py  (#444 ATTACKER — try to BREAK the beyond-Johnson floor)

The floor (docs/kb/deltastar-444-beyond-johnson-floor.md) claims:
  For eta > eta_crit = (log s)/(2 log p), the worst-case far-line incidence
    #bad gamma = #{size-s subsets S of mu_n : p_1(S)=...=p_c(S)=0 mod p},  c = s-k = eta*n,
  equals the char-0 coset count (= O(1), NO defect), so delta* >= (1-rho) - eta_crit > Johnson.

DECISIVE TESTS:
  (T1) EXACT worst-case incidence at accessible n in {16,32,64} at radii with eta just ABOVE
       eta_crit. Compute lacunary count, char-0 coset count, and DEFECT = lacunary - coset.
       Floor predicts DEFECT == 0 whenever eta > eta_crit.
  (T2) COUNTEREXAMPLE HUNT: search for ANY defect (non-coset S with vanishing power sums mod p)
       with eta > eta_crit. A single defect with eta > eta_crit REFUTES the floor.
       We hunt over MANY small primes p = 1 mod n (NOT prize-shape), letting p be SMALL so the
       norm ceiling p <= s^{1/(2eta)} can be VIOLATED. If a defect appears below the ceiling, OK;
       if a non-coset defect appears with eta > eta_crit(this p,s), floor is broken.
  (T3) eta_crit sanity + capacity-eta_crit > Johnson for every prize rate.

Power sums vs elem-sym: equivalent via Newton when c < p (always true here). We use POWER SUMS
directly (the actual condition in the argument). For a size-s subset S, condition is
  sum_{x in S} x^j == 0 mod p  for j=1..c.
"""
import itertools, cmath, math
from math import comb, log
from sympy import isprime, primitive_root

# ---------- subgroup ----------
def subgroup_vals_idx(n, p):
    g = primitive_root(p); zeta = pow(g, (p-1)//n, p)
    vals = []; x = 1
    for i in range(n):
        vals.append((x, i)); x = (x*zeta) % p
    return vals  # list of (value, index)

# ---------- char-0 coset count (deep mu_tau coset unions) ----------
def coset_structure(n, p, s):
    """
    A char-0 'coset union' surviving S: union of cosets of some subgroup mu_tau of mu_n,
    where tau | s and tau is the relevant 2-power granularity. The cleanest enumeration:
    the surviving char-0 sets (Lam-Leung rigidity) are exactly unions of mu_tau-cosets with
    tau = least 2-power >= (c+1)-ish. But to be SAFE and EXACT we DEFINE the char-0 coset count
    operationally as: subsets S that are a union of full cosets of mu_tau for the LARGEST tau
    such that all required power sums vanish identically (char-0). We instead compute it directly:
    the char-0 lacunary subsets = those whose vanishing holds over Q (i.e. beta_S = 0 as complex,
    AND structurally a coset-union). We enumerate cosets of every 2-power subgroup and count
    s-sized unions. Returns set of frozensets (by index) that are mu_tau-coset-unions of size s.
    """
    # cosets of mu_tau (tau a divisor of n that is a power of 2)
    coset_unions = set()
    taus = [t for t in range(1, n+1) if n % t == 0 and (t & (t-1)) == 0]  # 2-power divisors
    for tau in taus:
        if s % tau != 0:
            continue
        # cosets of mu_tau: partition indices into n/tau classes mod (n/tau)
        step = n // tau  # mu_tau = {indices that are multiples of step}? mu_tau has tau elements
        # mu_tau = elements of order dividing tau = indices i with i*tau ≡ 0 mod n => i multiple of n/tau
        # cosets: {i0 + (n/tau)*j : j=0..tau-1}
        ncoset = n // tau
        cosets = []
        for i0 in range(ncoset):
            cosets.append(frozenset((i0 + step*j) % n for j in range(tau)))
        cosets = list(dict.fromkeys(cosets))
        need = s // tau
        if need > len(cosets):
            continue
        for combo in itertools.combinations(cosets, need):
            U = frozenset().union(*combo)
            if len(U) == s:
                coset_unions.add(U)
    return coset_unions

# ---------- exact lacunary count (power sums vanish) ----------
def lacunary_subsets(n, p, s, c):
    """All size-s subsets (by index) of mu_n with p_1..p_c == 0 mod p. Returns set of frozensets."""
    vals = subgroup_vals_idx(n, p)
    out = set()
    # precompute powers x^j for j=1..c
    powtab = [[pow(v, j, p) for j in range(1, c+1)] for v, _ in vals]
    for combo in itertools.combinations(range(n), s):
        ok = True
        for j in range(c):
            t = 0
            for i in combo:
                t += powtab[i][j]
            if t % p != 0:
                ok = False; break
        if ok:
            out.add(frozenset(combo))
    return out

def beta_char0_abs(idxs, n):
    z = 2j*math.pi/n
    return abs(sum(cmath.exp(z*i) for i in idxs))

def is_antipodal_free(idxs, n):
    half = n//2; s = set(idxs)
    # antipodal-free core = no pair {i, i+n/2} both present
    return not any(((i+half) % n) in s for i in idxs)

# =========================================================================
# T1: exact worst-case incidence at eta just above eta_crit
# =========================================================================
def find_prize_like_prime(n, beta=4.0, idx_min=2):
    target = int(n**beta); base = target - (target % n) + 1; p = base
    while True:
        if p > n and isprime(p) and (p-1) % n == 0 and (p-1)//n >= idx_min:
            return p
        p += n

def T1(n, p, rates):
    print(f"\n=== T1  n={n}  p={p}  (log2 p={math.log2(p):.2f}) ===", flush=True)
    print(f"{'rho':>6} {'k':>3} {'s':>3} {'c':>3} {'eta':>7} {'etacrit':>8} {'eta>ec?':>8} "
          f"{'lacun':>7} {'coset0':>7} {'DEFECT':>7}", flush=True)
    for rho in rates:
        k = round(rho*n)
        if k < 1: continue
        # pick s so that eta = (s/n - rho) is just above eta_crit
        for s in range(k+1, n//2 + 1):
            c = s - k
            if c < 1: continue
            eta = s/n - rho
            eta_crit = math.log(s)/(2*math.log(p)) if s > 1 else 0.0
            if eta <= eta_crit:
                continue
            # only the FIRST s past the threshold (eta just above), to keep cheap
            if comb(n, s) > 3_000_000:
                continue
            lac = lacunary_subsets(n, p, s, c)
            cos = coset_structure(n, p, s)
            cos_in_lac = set(U for U in cos if U in lac)  # cosets that actually satisfy mod p
            defect = lac - cos
            print(f"{rho:>6.4f} {k:>3} {s:>3} {c:>3} {eta:>7.4f} {eta_crit:>8.4f} "
                  f"{'YES':>8} {len(lac):>7} {len(cos_in_lac):>7} {len(defect):>7}", flush=True)
            if defect:
                for D in list(defect)[:3]:
                    di = sorted(D)
                    print(f"        !!! DEFECT idx={di} antipodal_free={is_antipodal_free(di,n)} "
                          f"|beta|={beta_char0_abs(di,n):.4f}", flush=True)
            break  # just the first eta above eta_crit for this rate

# =========================================================================
# T2: counterexample hunt over SMALL primes (norm ceiling violable)
# =========================================================================
def primes_1_mod_n(n, count, idx_min=2, pmin=None):
    out = []; pp = (pmin or 0)
    pp = pp - (pp % n) + 1
    if pp <= n: pp = n + 1
    while len(out) < count:
        if isprime(pp) and (pp-1) % n == 0 and (pp-1)//n >= idx_min:
            out.append(pp)
        pp += n
    return out

def T2(n, s, c, primes, max_report=8):
    """
    Hunt for non-coset defects with vanishing power sums. For each prime, eta = c/n is FIXED,
    eta_crit = log(s)/(2 log p) VARIES (small p -> large eta_crit -> we want eta > eta_crit, i.e.
    LARGE p; but small p makes the norm ceiling p <= s^{1/(2eta)} violable, which is where a defect
    'should' live). We report: for each defect, whether eta > eta_crit(p) (=> REFUTES floor) and
    whether p <= ceiling (=> consistent with norm bound).
    """
    eta = c / n
    ceil = s ** (1.0/(2*eta)) if eta > 0 else float('inf')
    print(f"\n=== T2 HUNT  n={n} s={s} c={c}  eta={eta:.4f}  norm-ceiling p<=s^(1/2eta)={ceil:.4g} ===",
          flush=True)
    cos_template = None
    total_defect = 0; refuting = 0; reported = 0
    for p in primes:
        cos = coset_structure(n, p, s)  # index-only, p-independent structure
        lac = lacunary_subsets(n, p, s, c)
        cos_in_lac = set(U for U in cos if U in lac)
        defect = lac - cos
        eta_crit = math.log(s)/(2*math.log(p))
        if defect:
            total_defect += len(defect)
            above = eta > eta_crit
            belowceil = p <= ceil
            if above:
                refuting += len(defect)
            if reported < max_report:
                reported += 1
                D = sorted(next(iter(defect)))
                af = is_antipodal_free(D, n); bz = beta_char0_abs(D, n)
                tag = "<<< REFUTES FLOOR (eta>eta_crit)" if above else ""
                print(f"  p={p:7d} idx={(p-1)//n:5d} #lac={len(lac):4d} #coset={len(cos_in_lac):3d} "
                      f"#DEFECT={len(defect):4d} eta_crit={eta_crit:.4f} eta>ec?{above} "
                      f"p<=ceil?{belowceil} ex={D} af={af} |b|={bz:.3f} {tag}", flush=True)
    print(f"  --- total defects={total_defect}, REFUTING (eta>eta_crit)={refuting} "
          f"over {len(primes)} primes ---", flush=True)
    return refuting

# =========================================================================
# T3: eta_crit sanity + capacity - eta_crit > Johnson
# =========================================================================
def T3():
    print("\n=== T3  eta_crit sanity + (capacity - eta_crit) vs Johnson, prize rates ===", flush=True)
    print("  prize: p ~ n*2^128, n=2^mu.  eta_crit ~ mu/(2(128+mu)).", flush=True)
    print(f"{'mu':>4} {'rho':>7} {'cap=1-rho':>10} {'Johnson':>9} {'etacrit':>8} "
          f"{'floor':>8} {'floor>J?':>9} {'margin':>8}", flush=True)
    for mu in [25, 30, 35]:
        n = 2**mu
        for rho in [1/2, 1/4, 1/8, 1/16]:
            s_top = (rho + (math.sqrt(rho)-rho)) * n  # s at Johnson edge ~ sqrt(rho)*n
            # eta_crit uses s ~ (rho+eta)*n; near the floor eta~eta_crit so s~(rho+eta_crit)*n.
            # The KB uses s ~ n at the binding a=s (degree of x^a). Use the KB's formula directly:
            logp = math.log2(n) + 128
            eta_crit = mu/(2*(128+mu))   # KB's stated value (s~n, log2 s ~ mu)
            cap = 1 - rho
            johnson = 1 - math.sqrt(rho)
            floor = cap - eta_crit
            print(f"{mu:>4} {rho:>7.4f} {cap:>10.4f} {johnson:>9.4f} {eta_crit:>8.4f} "
                  f"{floor:>8.4f} {str(floor>johnson):>9} {floor-johnson:>8.4f}", flush=True)

if __name__ == "__main__":
    print("#"*90)
    print("# ATTACKER: break the #444 beyond-Johnson floor")
    print("#"*90)
    T3()

    # T1: exact worst-case at prize-like primes
    for n in [16, 32]:
        p = find_prize_like_prime(n, 4.0)
        T1(n, p, [1/2, 1/4])

    # T2: hunt for defects above eta_crit over many small primes
    # n=16: try (s,c) with various eta; small primes make eta_crit big BUT we want eta>eta_crit.
    # Strategy: pick LARGE eta (c near s) so eta is big; then even moderate p gives eta>eta_crit.
    print("\n" + "#"*90)
    print("# T2: the decisive counterexample hunt")
    print("#"*90)
    for (n, s, c) in [(16, 6, 4), (16, 8, 6), (16, 4, 2), (16, 8, 4),
                      (32, 6, 4), (32, 8, 6), (32, 8, 4), (32, 10, 6)]:
        if comb(n, s) > 3_000_000:
            continue
        primes = primes_1_mod_n(n, 80, idx_min=2, pmin=n)
        T2(n, s, c, primes)
