"""
#407 toric-exact-cohomology probe.

GOAL. The moment method gives B = max_{b!=0}|eta_b| <= (q*E_r)^{1/2r}, eta_b = sum_{x in mu_n} psi(bx).
The wall is at E_r (additive energy of mu_n to depth r). The standard 'deep-moment / Betti wall'
asserts E_r's char-p value departs from char-0 once the AMBIENT Adolphson-Sperber Betti number ~ n^{2r}
overtakes. The NOVEL question: compute the EXACT cohomology (exact middle Betti number) of the energy
variety V_r via the Newton-polytope NORMALIZED VOLUME (Adolphson-Sperber / Denef-Loeser exact Betti),
NOT the crude ambient bound. Is it genuinely SMALL (=> Weil cancellation to deep r => prize) or as big
as ambient (=> wall confirmed by exact computation, the crude bound was already tight)?

We work two incarnations and CHECK them against brute-force point counts mod small primes p = 1 mod n.

INCARNATION A (the exponential sum the moment is built from).
  S_r(b) := sum_{x_1..x_r, y_1..y_r in mu_n} psi(b*(sum x_i - sum y_j))   [b != 0]
          = | sum_{x in mu_n} psi(b x) |^{2r}  = |eta_b|^{2r}.
  As a function of the single variable x ranging over the TORUS via x = g^a (a in Z/n), eta_b is a
  1-variable exponential sum sum_{a in Z/n} psi(b g^a). Its "variety" is the affine line A^1_b and the
  trace-function sheaf FT_psi(delta_{mu_n}) of GENERIC RANK n (already known: EffKatzConductorBarrier).
  So |eta_b| is governed by an n-dim cohomology -> the per-b sum is a sum of n Weil numbers of size
  sqrt q. That gives |eta_b| <= n sqrt q TRIVIALLY (useless). The MOMENT is the average, NOT per-b.

INCARNATION B (the ENERGY variety itself -- this is what AS actually governs for E_r).
  E_r = (1/q) sum_b S_r(b) = #{ a_1..a_r, c_1..c_r in Z/n : sum g^{a_i} = sum g^{c_j} in F_q }.
  This is a point count of the affine variety
      V_r = { (a, c) in (Z/n)^{2r} : sum_{i} g^{a_i} - sum_{j} g^{c_j} = 0 }.
  Parametrize the torus T = (F_q^*) by the n-th roots. Better: the GENERATING exponential sum whose
  Newton polytope we want is
      N_r := sum_{t in F_q^*} [ sum_{x in mu_n} psi(t * x) ]^r * [ conj ]^r  -- already incarnation A.

  The RIGHT toric object (Adolphson-Sperber) for E_r is the Laurent polynomial in 2r torus variables
      f(u_1..u_r, v_1..v_r) = lambda * ( sum_i u_i^? ... )  -- diagonal/Fermat hypersurface.
  Concretely E_r is the number of F_q points of the toric hypersurface
      H_r : sum_{i=1}^r X_i = sum_{j=1}^r Y_j ,   X_i, Y_j in mu_n  (n-th roots of unity),
  i.e. each variable constrained to mu_n (a 0-dim subscheme of G_m). The exact cohomology of this
  is what we compute via the Newton polytope of the associated EXPONENTIAL SUM.

THE ACTUAL AS COMPUTATION.
  E_r - (n^{2r}/q)   [the main term n^{2r}/q removed]  equals an exponential-sum average:
      E_r = (1/q) [ n^{2r}  +  sum_{b != 0} |eta_b|^{2r} ].
  The deviation sum_{b!=0}|eta_b|^{2r} is the trace of Frobenius on the cohomology of the 1-param
  family b -> |eta_b|^{2r}. eta_b = sum_{x in mu_n} psi(bx); as a Laurent poly in x (over the torus,
  with x ranging over mu_n which we lift to the torus variable and impose x^n=1), this is the
  GAUSS-PERIOD function. Its Newton polytope in the "x" torus is the convex hull of the exponents,
  but mu_n is a FINITE set, not a polytope -- so the right framing is the TWISTED toric sum.

We therefore compute, EXACTLY:
  (1) The number of Weil eigenvalues (= dimension of the relevant cohomology = "effective Betti")
      of the sheaf G_r := (FT_psi delta_{mu_n})^{otimes r} (x) (its dual)^{otimes r} on A^1_b,
      by computing the EXACT generic rank of the r-th moment family. This is the EXACT analogue of
      the "middle Betti number" for the energy.
  (2) Compare to the AMBIENT bound n^{2r} that the wall uses.
  (3) Brute-force E_r mod actual primes p=1 mod n to see whether the EXACT count matches the
      char-0 value (2r-1)!! n^r (so Weil cancellation IS available) or blows up (wall genuine).
"""

import itertools, math
from functools import reduce
import cmath

def doublefact_odd(k):
    # (2r-1)!! for k = 2r-1
    r = 0
    res = 1
    m = k
    while m > 0:
        res *= m
        m -= 2
    return res

def double_factorial_2rm1(r):
    # (2r-1)!! = product of odd numbers up to 2r-1
    res = 1
    for i in range(1, 2*r, 2):
        res *= i
    return res

# ---------------------------------------------------------------------------
# Brute-force E_r over an actual finite field F_p with p = 1 mod n.
# mu_n = the order-n subgroup of F_p^*. E_r = #{ a,c in (mu_n)^{2r} : sum a = sum c }.
# We count via the additive-energy convolution: count multiset sums.
# ---------------------------------------------------------------------------
def find_prime_1_mod_n(n, lo):
    p = lo
    while True:
        p += 1
        if p % n != 1:
            continue
        # primality
        if p < 2: continue
        isp = True
        for d in range(2, int(p**0.5)+1):
            if p % d == 0:
                isp = False; break
        if isp:
            return p

def subgroup_mu_n(p, n):
    # find element of order n in F_p^*
    # g = h^{(p-1)/n} for a primitive root h
    def order(x):
        o = 1; y = x % p
        while y != 1:
            y = (y*x) % p; o += 1
        return o
    # find a generator of the order-n subgroup directly
    e = (p-1)//n
    for h in range(2, p):
        g = pow(h, e, p)
        if order(g) == n:
            mu = [pow(g, k, p) for k in range(n)]
            return sorted(set(mu))
    raise RuntimeError("no subgroup")

def E_r_bruteforce(p, n, r):
    mu = subgroup_mu_n(p, n)
    assert len(mu) == n
    # distribution of sum of r elements of mu (with repetition, ordered)
    # convolution of the r-fold sumset count
    from collections import defaultdict
    cur = {0:1}
    for _ in range(r):
        nxt = defaultdict(int)
        for s,c in cur.items():
            for x in mu:
                nxt[(s+x)%p] += c
        cur = nxt
    # E_r = sum_s cur[s]^2
    return sum(c*c for c in cur.values())

# ---------------------------------------------------------------------------
# EXACT effective Betti = number of nonzero Weil eigenvalues of the deviation family.
# We use the moment identity: sum_{b!=0} |eta_b|^{2r} = q*E_r - n^{2r}.
# The "effective Betti" is the SMALLEST number N(r) of Weil numbers w_i (|w_i| = q^{w/2})
# such that the deviation is sum_i w_i^{(deg)} ... -- but for the BOUND we want the size:
# AS-EXACT says |sum_{b!=0}|eta_b|^{2r}| <= (effective Betti) * q^{ (top weight)/2 }.
# Equivalently the per-b sum |eta_b|^{2r} is a fixed nonneg real; the moment is its average.
#
# The KEY exact toric quantity AS gives for the energy variety is the NORMALIZED VOLUME of the
# Newton polytope of the defining Laurent polynomial f = sum X_i - sum Y_j with X,Y in mu_n.
# Since each variable lies in mu_n (n-th roots), the natural toric model uses the variables
# t_i, s_j on G_m^{2r} and the Laurent polynomial  f = sum_i t_i - sum_j s_j  with the EXTRA
# multiplicative constraints t_i^n = s_j^n = 1.  This is a 0-DIMENSIONAL fibre structure:
# mu_n^{2r} is FINITE.  So E_r is literally a finite character-sum, NOT a positive-dim variety
# point count. The cohomology that controls E_r as p varies is the GALOIS / Frobenius action on
# the (2r-1)!! diagonal solution classes PLUS the off-diagonal mod-p coincidences.
# ---------------------------------------------------------------------------

def char0_value(n, r):
    # Lam-Leung char-0 value: E_r^C = (2r-1)!! * n^r  for mu_n essentially-Sidon (n a 2-power)
    return double_factorial_2rm1(r) * (n**r)

def ambient_bound(n, r):
    return n**(2*r)

# ---------------------------------------------------------------------------
# THE EXACT TORIC / NEWTON-POLYTOPE COMPUTATION (the novel step).
# Model E_r as: the number of solutions to sum_{i=1}^r zeta^{a_i} = sum_{j=1}^r zeta^{c_j}
# where zeta = primitive n-th root, a_i,c_j in Z/n, equality IN F_q (char p).
# In CHAR 0 (zeta a complex root), the solutions are exactly the (2r-1)!! perfect matchings
# of the 2r indices into negation-pairs (Lam-Leung): each X_i paired with a -X_j (= zeta^{c+n/2}).
# The "variety" V_r = vanishing locus of  P(a,c) = sum zeta^{a_i} - sum zeta^{c_j}  is a union
# of LINEAR (coset) subschemes -> its cohomology is determined by the lattice of relations.
#
# THE NEWTON-POLYTOPE VOLUME: P, as a polynomial in the 2r MONOMIAL variables u_k = zeta^{a_k},
# is the LINEAR form L = u_1+...+u_r - u_{r+1}-...-u_{2r}. Its Newton polytope is the SIMPLEX
# Delta = conv{0, e_1, ..., e_{2r}} (a unit cross-polytope edge set), with each u_k on the torus
# but ALSO subject to u_k^n = 1. The toric variety is (mu_n)^{2r}, a finite group scheme.
# The AS normalized volume of a LINEAR form on a torus of dim d is d! * vol(Delta).
# But the binding constraint is u_k^n=1: the cohomology of the FIBRE PRODUCT.
#
# We compute the EXACT count two ways and compare to (2r-1)!! n^r and to n^{2r}.
# ---------------------------------------------------------------------------

def char0_count_complex(n, r):
    # brute-force the char-0 count by complex arithmetic (small n,r): solutions to
    # sum zeta^{a_i} = sum zeta^{c_j}, a,c in Z/n.  Count by hashing the complex sum (rounded).
    zeta = [cmath.exp(2j*cmath.pi*k/n) for k in range(n)]
    from collections import defaultdict
    cur = {(0.0,0.0):1}
    # distribution of sum of r roots (ordered, with repetition)
    dist = defaultdict(int)
    def roundc(z, prec=6):
        return (round(z.real,prec), round(z.imag,prec))
    # build r-fold sum distribution
    d = {(0.0,0.0):1}
    for _ in range(r):
        nd = defaultdict(int)
        for (re,im),c in d.items():
            for z in zeta:
                nd[roundc(complex(re,im)+z)] += c
        d = nd
    return sum(c*c for c in d.values())

# ---------------------------------------------------------------------------
print("="*78)
print("PART 1: char-0 value vs ambient bound vs EXACT char-0 count")
print("="*78)
print(f"{'n':>4} {'r':>3} {'(2r-1)!!n^r':>14} {'exact char0':>14} {'ambient n^2r':>16} {'amb/char0':>10}")
for n in [4, 8]:
    for r in [1,2,3,4]:
        c0 = char0_value(n, r)
        ex = char0_count_complex(n, r)
        amb = ambient_bound(n, r)
        print(f"{n:>4} {r:>3} {c0:>14} {ex:>14} {amb:>16} {amb/c0:>10.2f}")

print()
print("="*78)
print("PART 2: char-p EXACT count vs char-0 count  (does Weil cancellation hold deep?)")
print("="*78)
print("E_r over F_p, p = 1 mod n, sweeping p upward. Compare to exact char-0 count.")
print("DEVIATION = E_r(F_p) - char0count.  Onset = first p where deviation != 0 going DOWN.")
for n in [4, 8]:
    print(f"\n--- n = {n} ---")
    c0 = {r: char0_count_complex(n, r) for r in [2,3]}
    print(f"  exact char-0 counts: r=2 -> {c0[2]},  r=3 -> {c0[3]}")
    print(f"  {'p':>8} {'log_n p':>8} | {'E_2':>10} {'dev2':>8} | {'E_3':>10} {'dev3':>8}")
    lo = n
    for _ in range(8):
        p = find_prime_1_mod_n(n, lo); lo = p
        e2 = E_r_bruteforce(p, n, 2)
        e3 = E_r_bruteforce(p, n, 3)
        lnp = math.log(p)/math.log(n)
        print(f"  {p:>8} {lnp:>8.2f} | {e2:>10} {e2-c0[2]:>8} | {e3:>10} {e3-c0[3]:>8}")

print()
print("="*78)
print("PART 3: EXACT EFFECTIVE BETTI of the deviation = (q*E_r - exactchar0count)/q")
print("   The deviation D_r(p) := E_r(F_p) - char0count = (1/p) sum_{b!=0}|eta_b|^{2r} - corr.")
print("   Actually q*E_r = n^{2r} + sum_{b!=0}|eta_b|^{2r}, and char0count is the p->inf limit.")
print("   So Delta(p) := E_r(F_p) - char0count is a sum of Frobenius traces. We extract its")
print("   GROWTH RATE in p: Delta(p) ~ Betti_eff * p^{theta}. Fit theta and Betti_eff.")
print("="*78)

def fit_growth(n, r, num=12):
    c0 = char0_count_complex(n, r)
    lo = n
    data = []
    for _ in range(num):
        p = find_prime_1_mod_n(n, lo); lo = p
        e = E_r_bruteforce(p, n, r)
        d = e - c0
        data.append((p, d))
    return c0, data

for n in [4, 8]:
    for r in [2, 3]:
        c0, data = fit_growth(n, r, num=14)
        # exponent theta of |Delta| ~ p^theta : use last several nonzero points
        nz = [(p,d) for (p,d) in data if d != 0]
        print(f"\n n={n} r={r}  char0count={c0}   (ambient n^2r = {n**(2*r)}, char0val (2r-1)!!n^r={char0_value(n,r)})")
        print(f"   {'p':>7} {'Delta':>10} {'Delta/p':>10} {'Delta/p^.5':>12} {'Delta/p^1.5':>12} {'Delta/n^r':>10}")
        for (p,d) in data:
            print(f"   {p:>7} {d:>10} {d/p:>10.3f} {d/p**0.5:>12.3f} {d/p**1.5:>12.4f} {d/(n**r):>10.3f}")

print()
print("="*78)
print("PART 4: THE RELATION-LATTICE SOURCE of each spike (the EXACT toric cohomology)")
print("  CLAIM: Delta_r(p) != 0  IFF  p divides the norm of some 'short relation' = a nonzero")
print("  cyclotomic integer  R = sum_{i<=r} zeta^{a_i} - sum_{j<=r} zeta^{c_j}  that is NONZERO")
print("  in char 0 but == 0 mod p. Each such relation is a lattice point of the kernel of the")
print("  evaluation map Z[mu_n]^{(deg<=r)} -> F_p. The number of relation CLASSES (up to the")
print("  S_r x S_r x Z/n symmetry) = the EXACT effective Betti / # of Frobenius eigenvalues.")
print("="*78)

# enumerate, in char 0, all multiset-pairs (A multiset of r roots, C multiset of r roots) with
# A != C as multisets but sum_A = sum_C  -- none in char 0 except the (2r-1)!! matchings which ARE
# already equal-as-the-energy-solution. The EXTRA char-p solutions are pairs with sum_A - sum_C a
# NONZERO cyclotomic integer whose norm is divisible by p.
# We compute the set of NONZERO values  v = sum_A - sum_C  (as cyclotomic integers, represented in
# the power basis 1,zeta,...,zeta^{n-1}) and their norms; p | Delta iff p | some norm.

def cyclotomic_reduce(coeffs, n):
    # reduce a Z-vector of length up to 2n in the basis zeta^k, using zeta^n = 1, into length n
    out = [0]*n
    for k,c in enumerate(coeffs):
        out[k % n] += c
    return tuple(out)

def sum_to_vec(indices, n, sign):
    v = [0]*n
    for a in indices:
        v[a % n] += sign
    return v

import numpy as np
from itertools import combinations_with_replacement as cwr

def short_relation_norms(n, r, maxprime=400):
    # collect distinct NONZERO cyclotomic integers v = sum_A - sum_C, A,C multisets of size r,
    # represented mod (X^n - 1). Then for each, the values that could vanish mod p are those whose
    # entries are NOT all-equal (all-equal => v = c*(1+zeta+..)=0 only if c=0). We test which primes
    # p (1 mod n, brute range) make E_r deviate, vs which divide a relation norm.
    # Build the set of reachable difference-vectors (in Z^n mod the all-ones vector, since
    #   1+zeta+...+zeta^{n-1} = 0 for n>1).
    vecs = set()
    roots = list(range(n))
    # multisets of size r
    multis = list(cwr(roots, r))
    sums = {}
    for A in multis:
        v = tuple(sum_to_vec(A, n, 1))
        sums.setdefault(v, []).append(A)
    distinct_sumvecs = list(sums.keys())
    # difference vectors
    diffs = set()
    for va in distinct_sumvecs:
        for vc in distinct_sumvecs:
            d = tuple(va[k]-vc[k] for k in range(n))
            diffs.add(d)
    return diffs, sums

def vanishes_mod_p(dvec, p, n):
    # the cyclotomic integer with these power-basis coeffs vanishes mod p at a primitive n-th root
    # iff, for the specific subgroup generator g in F_p, sum_k dvec[k] g^k == 0 mod p.
    mu = subgroup_mu_n(p, n)  # mu[k] = g^k for the chosen g
    s = sum(dvec[k]*mu[k] for k in range(n)) % p
    return s == 0

for n in [4, 8]:
    for r in [2,3]:
        diffs, sums = short_relation_norms(n, r)
        # the "all-ones-multiple" diffs (which vanish identically for n>1) and the zero diff are the
        # char-0 energy solutions; the REST are genuine nonzero cyclotomic integers.
        def is_trivial(d):
            # d is char-0 zero iff d is a constant vector (multiple of all-ones), since 1+..+z^{n-1}=0
            return len(set(d)) == 1
        nontrivial = [d for d in diffs if not is_trivial(d)]
        print(f"\n n={n} r={r}: #distinct sum-vectors={len(sums)}, #diff-vectors={len(diffs)}, "
              f"#nontrivial(char-0-nonzero)={len(nontrivial)}")
        # now: a prime p shows a spike iff some nontrivial d vanishes mod p.
        lo=n; spikes=[]; matches=[]
        for _ in range(14):
            p=find_prime_1_mod_n(n,lo); lo=p
            e=E_r_bruteforce(p,n,r); c0=char0_count_complex(n,r)
            spike = (e-c0)!=0
            anyvanish = any(vanishes_mod_p(d,p,n) for d in nontrivial)
            spikes.append((p,spike,anyvanish))
        ok = all(s==a for (_,s,a) in spikes)
        print(f"   spike <=> some nontrivial relation vanishes mod p :  {ok}")
        for (p,s,a) in spikes:
            flag = "" if s==a else "  <-- MISMATCH"
            print(f"     p={p:>5}  spike={s}  relation_vanishes={a}{flag}")

print()
print("="*78)
print("PART 5: CORRECTED relation source -- spike <=> p | NORM of a short relation,")
print("        but only counting GENUINELY-NEW solutions (the deviation is SIGNED).")
print("="*78)
print("  The cyclotomic-integer R = sum_A - sum_C lives in Z[zeta_n]. p (split, =1 mod n)")
print("  factors into primes of degree 1; R == 0 at OUR embedding zeta->g iff the prime ideal")
print("  (p, zeta-g) divides (R). Whether E_r SEES it depends on g. But E_r is g-INDEPENDENT")
print("  (Galois conjugation permutes the g's and fixes E_r). So the deviation counts, over ALL")
print("  conjugate embeddings, the relations vanishing -- = number of prime-ideal factors of (R)")
print("  above p, summed over relation classes. KEY MAGNITUDE: each contributes O(1), and the")
print("  number of relation CLASSES with norm divisible by a given p is the EXACT BETTI input.")
print()
print("  We TEST the magnitude law directly:  |Delta_r(p)| is bounded by  Betti_eff(r) * (small),")
print("  and Betti_eff is p-INDEPENDENT. Measure max_p |Delta_r(p)| / n^r over the swept range:")

for n in [4,8]:
    print(f"\n  n={n}:")
    for r in [2,3]:
        c0=char0_count_complex(n,r)
        lo=n; vals=[]
        for _ in range(40):
            p=find_prime_1_mod_n(n,lo); lo=p
            e=E_r_bruteforce(p,n,r)
            vals.append((p, e-c0))
        nz=[(p,d) for p,d in vals if d!=0]
        maxd = max(abs(d) for p,d in vals)
        # for p beyond the char-0 threshold tau_r ~ n^{(r+3)/2}, spikes should be RARE & bounded
        tau = n**((r+3)/2)
        beyond = [(p,d) for p,d in vals if p>tau]
        beyond_nz = [(p,d) for p,d in beyond if d!=0]
        print(f"   r={r}: char0={c0}, tau~n^((r+3)/2)={tau:.0f}, n^r={n**r}, ambient={n**(2*r)}")
        print(f"      max|Delta| over 40 primes = {maxd}  (= {maxd/n**r:.3f} * n^r, "
              f"{maxd/n**(2*r):.4f} * ambient)")
        print(f"      # nonzero-Delta primes BEYOND tau: {len(beyond_nz)} / {len(beyond)}; "
              f"their p and Delta/n^r: {[(p, round(d/n**r,3)) for p,d in beyond_nz][:8]}")

print()
print("="*78)
print("PART 6: LONG SWEEP -- does Delta vanish for ALL p > tau, or do sporadic spikes persist?")
print("  This is the decisive toric question: if Delta(p)=0 for all large p, the energy variety")
print("  cohomology gives EXACT char-0 value at large p (full Weil cancellation, deep moments OK).")
print("  If sporadic spikes persist at large p, those are the resonant primes = the wall carriers.")
print("="*78)
for n in [4, 8]:
    for r in [2,3]:
        c0=char0_count_complex(n,r)
        lo=n; nz=[]; total=0; maxp=0
        # sweep many primes
        for _ in range(120):
            p=find_prime_1_mod_n(n,lo); lo=p; maxp=p; total+=1
            e=E_r_bruteforce(p,n,r)
            d=e-c0
            if d!=0: nz.append((p,d))
        tau=n**((r+3)/2)
        beyond=[(p,d) for p,d in nz if p>tau]
        print(f"\n n={n} r={r}: swept {total} primes up to {maxp}, tau~{tau:.0f}")
        print(f"   nonzero-Delta primes (ALL): {[(p, d) for p,d in nz]}")
        print(f"   nonzero-Delta primes BEYOND tau: {beyond}")
        if beyond:
            print(f"   ** sporadic large-p spikes persist: ratios Delta/n^r = {[round(d/n**r,4) for p,d in beyond]}")
        else:
            print(f"   ** NO spikes beyond tau in {total} primes -> Delta(p)=0 for all p>tau in range")

print()
print("="*78)
print("PART 7: WHAT SETS tau_r? Newton-polytope VOLUME vs ARITHMETIC (norm of short relations)")
print("  The largest prime that can carry a spike = the largest prime dividing the NORM of any")
print("  minimal short relation R (a cyclotomic integer that is a +/-1 combination of <=2r roots).")
print("  AS/toric volume governs the NUMBER of relations; the ARITHMETIC (norm size) governs the")
print("  largest resonant prime = tau_r. If tau_r is the norm-size, the wall is ARITHMETIC, not")
print("  cohomological -- and NO toric refinement of the Betti number can move it.")
print("="*78)
from math import gcd
def max_resonant_prime(n, r):
    # largest prime p=1 mod n that divides the norm of a nontrivial short relation
    # R = sum_A - sum_C, A,C multisets size r. Norm = prod over Galois (zeta->zeta^k, gcd(k,n)=1).
    # Compute via resultant: norm of f(zeta) = Res(Phi_n(x), f(x))/lc... ; we use numeric product.
    import numpy as np
    zetas = [cmath.exp(2j*cmath.pi*k/n) for k in range(n) if gcd(k,n)==1]
    multis = list(cwr(range(n), r))
    sumvecs = set()
    for A in multis:
        v=[0]*n
        for a in A: v[a]+=1
        sumvecs.add(tuple(v))
    sumvecs=list(sumvecs)
    best=0; bestR=None
    seen=set()
    for va in sumvecs:
        for vc in sumvecs:
            d=tuple(va[k]-vc[k] for k in range(n))
            if len(set(d))==1: continue  # trivial (char-0 zero)
            if d in seen: continue
            seen.add(d)
            # norm = product over primitive embeddings of |sum d[k] zeta^k|... but that's complex;
            # the actual integer norm = prod_{k coprime} (sum_j d[j] zeta_k^j). Compute & round.
            nm=1.0
            for z in zetas:
                val=sum(d[j]*(z**j) for j in range(n))
                nm*= val
            nm=round(nm.real)
            if nm==0: continue
            anm=abs(nm)
            # factor anm, take largest prime that is 1 mod n
            m=anm
            f=2
            while f*f<=m:
                while m%f==0:
                    if f%n==1 and f>best: best=f; bestR=d
                    m//=f
                f+=1
            if m>1 and m%n==1 and m>best:
                best=m; bestR=d
    return best, bestR

for n in [4,8]:
    for r in [2,3]:
        tau=n**((r+3)/2)
        mp, R = max_resonant_prime(n,r)
        print(f" n={n} r={r}: tau~n^((r+3)/2)={tau:.0f}; largest resonant prime (1 mod n) dividing a"
              f" short-relation norm = {mp}")
        print(f"        => log_n(tau)={(r+3)/2:.2f},  log_n(max resonant p)={math.log(max(mp,1))/math.log(n):.2f}")
