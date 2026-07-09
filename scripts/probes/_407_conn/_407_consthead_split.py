"""
C084 probe: Two-Gauss-sum hybrid HEAD/TAIL split of the completion identity.

CLAIM (C084): in the in-tree completion identity
    t * eta_b = sum_{j<t} tau(chi^{dj}, psi_b),    t = (q-1)/d,
the worst-case proof bounds ALL t-1 nontrivial terms by sqrt(q) and triangle-sums.
HYBRID: split the index sum into a CONSTANT/POLYLOG HEAD {0<=j<J} (J=O(1) or polylog)
where chi^{dj}(b) phases are "pinned", plus a residual tail. The QR/index-2 lane is
the J=1 effective-phase collapse. The novel hope: a constant/polylog head J already
captures the BULK of the cancellation, i.e.
    S_J := ||sum_{j<J} tau(chi^{dj}, psi_b)||
    full := ||sum_{j<t} tau(chi^{dj}, psi_b)|| = t * B_b
and S_J / full -> 1 FAST as J grows (polylog J suffices), so the open tail is negligible.

We test the OPPOSITE possibility too: the partial head S_J GROWS like sqrt(J)*sqrt(q)
(random-walk of J flat unit-modulus-sqrt(q) phases) and only at J ~ t does it collapse
to the true t*B. If so the head captures NONE of the cancellation - all m phases needed.

PRIZE REGIME: proper dyadic mu_n, q prime = 1 mod n, q ~ n^beta (beta 3-4), n << sqrt(q).
d = n (so the subgroup IS mu_n, t = m = (q-1)/n is the cofactor = number of phases).
EXACT arithmetic: chi = full-order mult char via primitive root + discrete log table;
tau computed in high-precision complex.
"""
import cmath, math
from sympy import isprime, primitive_root

def find_prime(n, beta_target):
    target = int(round(n**beta_target))
    q = target - (target % n) + 1
    if q <= n: q += n
    for _ in range(2_000_000):
        if q % n == 1 and isprime(q):
            return q
        q += n
    return None

def dlog_table(g, q):
    """ind[x] = discrete log base g, for x in 1..q-1."""
    ind = [0]*q
    x = 1
    for e in range(q-1):
        ind[x] = e
        x = (x*g) % q
    return ind

def tau_powers(g, q, ind, d, t, b):
    """Return list of tau_j = gaussSum(chi^{dj}, psi_b) for j=0..t-1,
    where chi(y) = exp(2pi i ind[y]/(q-1)) is the full-order character,
    psi_b(y) = exp(2pi i b*y / q).
    tau_j = sum_{y=1}^{q-1} chi^{dj}(y) * psi(b*y)
          = sum_{y} exp(2pi i [ (dj)*ind[y]/(q-1) + b*y/q ]).
    """
    w1 = 2*math.pi/(q-1)
    w2 = 2*math.pi/q
    Q1 = q-1
    # Precompute per-y the additive-char phase and the index
    taus = []
    # exponential bases
    # For efficiency, accumulate per j. But t can be up to ~q/n; keep q modest.
    # Build arrays
    inds = [0]*(q)      # ind[y] for y=1..q-1
    addph = [0.0]*(q)   # b*y mod q
    for y in range(1, q):
        inds[y] = ind[y]
        addph[y] = w2 * ((b*y) % q)
    for j in range(t):
        dj = (d*j) % Q1
        s = 0j
        c = w1*dj
        # tau_j = sum_y exp(i*(c*ind[y] + addph[y]))
        for y in range(1, q):
            s += cmath.exp(1j*(c*inds[y] + addph[y]))
        taus.append(s)
    return taus

def eta(b, S, q):
    s = 0j
    w = 2*math.pi/q
    for y in S:
        s += cmath.exp(1j*w*((b*y) % q))
    return s

def subgroup(g, n, q):
    h = pow(g, (q-1)//n, q)
    S, x = [], 1
    for _ in range(n):
        S.append(x); x = (x*h) % q
    return S

def maxB_arg(S, q):
    """return (B, argmax b)."""
    best, bb = 0.0, 1
    for b in range(1, q):
        v = abs(eta(b, S, q))
        if v > best: best, bb = v, b
    return best, bb

print("="*100)
print("C084 PROBE: HEAD/TAIL split of completion sum t*eta_b = sum_{j<t} tau(chi^{dj},psi_b)")
print("="*100)
print("Question: does a CONSTANT/POLYLOG head J capture the bulk? (S_J/full -> 1 fast?)")
print("or does the head random-walk (S_J ~ sqrt(J)*sqrt(q)) and need ALL t=m phases?")
print()

# keep q small enough that t=(q-1)/n phases x (q-1) terms is tractable
cases = [
    (8,  3.3),
    (8,  3.7),
    (16, 3.0),
    (16, 3.4),
    (32, 2.8),
]

for n, beta in cases:
    q = find_prime(n, beta)
    if q is None:
        print(f"n={n}: no prime"); continue
    g = primitive_root(q)
    ind = dlog_table(g, q)
    S = subgroup(g, n, q)
    d = n
    t = (q-1)//d   # = m, number of phases
    B, bstar = maxB_arg(S, q)
    beta_eff = math.log(q)/math.log(n)
    full_norm = t*B   # = ||sum_j tau_j||
    rq = math.sqrt(q)
    print(f"--- n={n}  q={q}  beta_eff={beta_eff:.2f}  t=m={t}  B={B:.3f}  "
          f"full=t*B={full_norm:.2f}  sqrt(q)={rq:.2f}  B/sqrt(n*log2 m)={B/math.sqrt(n*math.log2(t)):.3f} ---")
    # compute the worst-case b's tau partial sums
    taus = tau_powers(g, q, ind, d, t, bstar)
    # sanity: the j=0 term (trivial char chi^0=1) should have |tau_0|=1 (= -1 actually)
    # full partial:
    partials = []
    acc = 0j
    for j in range(t):
        acc += taus[j]
        partials.append(abs(acc))
    # verify completion identity: |partials[-1]| == t*B  (up to fp)
    id_err = abs(partials[-1] - full_norm)
    print(f"    completion identity check: ||sum all tau_j|| = {partials[-1]:.3f}  vs t*B = {full_norm:.3f}   err={id_err:.2e}")
    # head fractions at J = 1, 2, log2 t, sqrt t, t/2, t
    import math as _m
    Jlist = sorted(set([1, 2, max(1,int(round(_m.log2(t)))), max(1,int(round(_m.sqrt(t)))),
                        max(1,t//4), max(1,t//2), t]))
    print(f"    {'J':>6} {'S_J=||head||':>14} {'S_J/full':>10} {'S_J/(J)':>10} {'S_J/sqrt(J*q)':>14}  interpretation")
    for J in Jlist:
        SJ = partials[J-1]
        frac = SJ/full_norm if full_norm>0 else float('nan')
        per = SJ/J
        rw = SJ/math.sqrt(J*q)   # if ~1, head is a random walk of flat sqrt(q) phases
        tag = ""
        if J==1: tag="(J=1 = QR collapse claim)"
        elif J==t: tag="(full)"
        print(f"    {J:>6} {SJ:>14.3f} {frac:>10.4f} {per:>10.3f} {rw:>14.3f}  {tag}")
    print()

print("="*100)
print("INTERPRETATION KEY:")
print("  - If S_J/full -> 1 already at constant/polylog J  => C084 HEAD captures the bulk (PROGRESS).")
print("  - If S_J/sqrt(J*q) ~ const (random-walk) until J~t, and S_J/full small for small J,")
print("    => the head carries NO cancellation; all m phases needed. C084 hope REFUTED, welds to W-BGK.")
print("  - The TRUE collapse to t*B (the small full value) happens only via cancellation among")
print("    ALL m phases (the discarded triangle ineq), exactly the open BGK sqrt-cancellation.")
