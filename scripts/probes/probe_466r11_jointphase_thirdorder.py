#!/usr/bin/env python3
"""
#466 Round 11 -- LANE S completeness-scout probe.

Question (stress-test of the ONE flagged live direction, JointPhaseFieldStructure):
  Round 10 found the joint two-frequency distribution (eta_b, eta_{zeta b}) is
  marginal-determined at r=2 (C/(mean)^2 ~ 0.9991). The flagged-open sub-thread is
  whether the JOINT phase field carries b-SENSITIVE content at deeper order that is
  invisible to marginal (multiset/moment) functionals.

  This probe asks the cleanest breadth version:
  Is there a THIRD-ORDER joint invariant of the adjacent-coset pair that is
    (a) b-SENSITIVE (varies over cosets b, not constant), AND
    (b) NOT predicted by the marginal magnitudes {|eta_b|} alone?

  Concretely we compute, per coset b:
    T3(b) = Re < eta_b^2 * conj(eta_{zeta b}) >   (a signed 3rd-order cross object)
    and compare against the marginal-only prediction (which, if the pair were
    magnitude-multiset-determined, would make any function of the pair depend on b
    ONLY through (|eta_b|,|eta_{zeta b}|)).

  b-sensitivity test: does T3(b) vary across b beyond what (|eta_b|,|eta_{zeta b}|)
  explains?  We regress T3 on the marginals and look at the RESIDUAL variance.
  If residual ~ 0  -> marginal-determined (gauge / b-blind third order too) -> collapse.
  If residual >> 0 and STABLE across primes -> genuinely b-sensitive non-moment content.

Regime discipline: proper mu_n < F_p^*, p == 1 mod n, p >= n^4, >=2 primes distinct
v2(p-1), exclude X^{n/2} = +-1.  Verdict needs >= 2 primes.
"""
import cmath, math

def find_primes(n, count, pmin):
    ps = []
    p = pmin
    # ensure p == 1 mod n, prime
    def isprime(x):
        if x < 2: return False
        if x % 2 == 0: return x == 2
        i = 3
        while i*i <= x:
            if x % i == 0: return False
            i += 2
        return True
    p = ((pmin // n) + 1) * n + 1
    while len(ps) < count:
        if p > n and isprime(p):
            ps.append(p)
        p += n
    return ps

def prim_root(p):
    # find a generator of F_p^*
    phi = p - 1
    # factor phi
    f = []
    x = phi
    d = 2
    while d*d <= x:
        if x % d == 0:
            f.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: f.append(x)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in f):
            return g
    raise RuntimeError

def v2(x):
    c = 0
    while x % 2 == 0:
        x //= 2; c += 1
    return c

def analyze(n, p):
    g = prim_root(p)
    m = (p - 1) // n
    # zeta = generator of mu_n: g^m has order n
    zeta = pow(g, m, p)
    # mu_n elements
    mu = [pow(zeta, k, p) for k in range(n)]
    # exclude X^{n/2} = +-1 trap: zeta^{n/2} should not be +-1 (it's -1 for a genuine
    # primitive n-th root; that's fine -- the trap is p with X^{n/2}=1 i.e. order < n).
    # Guard: order of zeta must be exactly n.
    assert pow(zeta, n, p) == 1 and all(pow(zeta, d, p) != 1 for d in range(1, n))
    tau = 2j * math.pi / p
    def eta(b):
        s = 0j
        for x in mu:
            s += cmath.exp(tau * ((b * x) % p))
        return s
    # cosets: b ranges over representatives; eta_b constant on b*mu_n dilation cosets.
    # We take b = 1..p-1 but reduce by dilation coset (pick one rep per coset).
    # coset of b under mu_n multiplication: {b*mu_n}. Number of cosets = m.
    seen = set()
    reps = []
    for b in range(1, p):
        if b in seen: continue
        reps.append(b)
        for x in mu:
            seen.add((b * x) % p)
    assert len(reps) == m
    etab = {b: eta(b) for b in reps}
    # map any residue to its coset rep's eta (up to the dilation; |eta| is constant on coset,
    # phase rotates). For the joint (eta_b, eta_{zeta b}): zeta*b is in the SAME coset as b!
    # (zeta in mu_n).  So "adjacent coset" via zeta is TRIVIAL -- zeta b ~ b.
    # The genuinely adjacent structure is the TOWER step: compare mu_n vs mu_{2n} is a
    # different subgroup.  Within a fixed p, the meaningful adjacent pairing is b vs b*t
    # where t is a fixed coset-shift (t not in mu_n).  Use t = smallest nonresidue-type shift:
    # pick t = g (generator) so g*mu_n is the NEXT dilation coset.
    t = g % p
    def eta_of(res):
        # res is any nonzero residue; find its coset rep
        # coset rep = res * zeta^{-k} landing in reps; brute: eta is well-defined by
        # |.| on coset but PHASE differs. We need eta(res) exactly for the joint object,
        # so just compute it directly.
        s = 0j
        for x in mu:
            s += cmath.exp(tau * ((res * x) % p))
        return s
    # Build per-coset third-order cross object with the fixed shift t:
    #   T3(b) = Re( eta(b)^2 * conj(eta(t*b)) )
    # and marginals u=|eta(b)|, w=|eta(t*b)|.
    data = []
    for b in reps:
        eb = etab[b]
        etb = eta_of((t * b) % p)
        T3 = (eb*eb*etb.conjugate()).real
        data.append((abs(eb), abs(etb), T3))
    # Regress T3 on features of (u,w): [1, u^2 w, u w^2, u^3, w^3] -- all marginal-magnitude
    # monomials of total degree 3 that could produce a degree-3 signed object.
    import statistics
    U = [d[0] for d in data]; W = [d[1] for d in data]; Y = [d[2] for d in data]
    # feature matrix
    feats = []
    for u,w in zip(U,W):
        feats.append([1.0, u*u*w, u*w*w, u**3, w**3])
    k = len(feats[0])
    # normal equations (small k)
    A = [[0.0]*k for _ in range(k)]
    bv = [0.0]*k
    for row,y in zip(feats,Y):
        for i in range(k):
            bv[i] += row[i]*y
            for j in range(k):
                A[i][j] += row[i]*row[j]
    # solve A c = bv (Gaussian elim)
    M = [A[i][:] + [bv[i]] for i in range(k)]
    for col in range(k):
        piv = max(range(col,k), key=lambda r: abs(M[r][col]))
        M[col],M[piv] = M[piv],M[col]
        if abs(M[col][col]) < 1e-15: continue
        for r in range(k):
            if r==col: continue
            f = M[r][col]/M[col][col]
            for c in range(col, k+1):
                M[r][c] -= f*M[col][c]
    c = [M[i][k]/M[i][i] if abs(M[i][i])>1e-15 else 0.0 for i in range(k)]
    pred = [sum(cc*row[i] for i,cc in enumerate(c)) for row in feats]
    resid = [y-pp for y,pp in zip(Y,pred)]
    var_y = statistics.pvariance(Y) if len(Y)>1 else 0.0
    var_r = statistics.pvariance(resid) if len(resid)>1 else 0.0
    r2 = 1 - var_r/var_y if var_y>0 else float('nan')
    # b-sensitivity of T3 itself:
    return {
        'p': p, 'm': m, 'v2': v2(p-1),
        'meanU2': statistics.fmean([u*u for u in U]),
        'std_T3': math.sqrt(var_y),
        'resid_frac': var_r/var_y if var_y>0 else float('nan'),  # unexplained by marginals
        'R2_marginal': r2,
    }

if __name__ == '__main__':
    for n in (16, 32):
        pmin = n**4
        primes = find_primes(n, 6, pmin)
        # keep >=2 distinct v2 classes
        print(f"\n=== n={n}, p>=n^4={pmin} ===")
        print(f"{'p':>10} {'m':>10} {'v2':>3} {'std_T3':>12} {'resid_frac':>12} {'R2_marg':>10}")
        vseen = {}
        for p in primes:
            r = analyze(n, p)
            print(f"{r['p']:>10} {r['m']:>10} {r['v2']:>3} {r['std_T3']:>12.4f} "
                  f"{r['resid_frac']:>12.6f} {r['R2_marginal']:>10.6f}")
        print("Interpretation: resid_frac ~ 0  => joint 3rd-order object is marginal-determined")
        print("                (b-blind at 3rd order too, collapses like r=2).")
        print("                resid_frac >> 0 and STABLE across primes => genuinely b-sensitive.")

# --- Adversarial follow-up: is T3 a SIGNED object (mean ~ 0), and does its coset-sum
# --- carry b-sensitive magnitude info, or does it cancel (the known signed-3rd-order trap)?
def followup(n, p):
    import statistics, cmath, math
    g = prim_root(p); m = (p-1)//n; zeta = pow(g, m, p)
    mu = [pow(zeta,k,p) for k in range(n)]; tau = 2j*math.pi/p
    seen=set(); reps=[]
    for b in range(1,p):
        if b in seen: continue
        reps.append(b)
        for x in mu: seen.add((b*x)%p)
    t = g % p
    def eta_of(res):
        s=0j
        for x in mu: s+=cmath.exp(tau*((res*x)%p))
        return s
    T3=[]; absmax=0.0
    for b in reps:
        eb=eta_of(b); etb=eta_of((t*b)%p)
        T3.append((eb*eb*etb.conjugate()).real)
        absmax=max(absmax, abs(eb))
    mean=statistics.fmean(T3); sd=statistics.pstdev(T3)
    # A magnitude bound needs |eta| ~ sqrt(n log m). Does |T3| max relate to M^3?
    return {'p':p,'meanT3':mean,'mean/sd':mean/sd if sd>0 else 0.0,
            'M':absmax,'M/sqrt_nlogm':absmax/math.sqrt(n*math.log(m)),
            'maxAbsT3/M^3':max(abs(x) for x in T3)/absmax**3}

print("\n=== FOLLOWUP: is T3 signed (mean~0) => needs even moment for magnitude ===")
for n in (16,32):
    for p in find_primes(n, 2, n**4):
        r=followup(n,p)
        print(f"n={n} p={r['p']:>10} meanT3={r['meanT3']:>10.3f} mean/sd={r['mean/sd']:>+7.4f} "
              f"M/sqrt(nlogm)={r['M/sqrt_nlogm']:>6.3f} maxAbsT3/M^3={r['maxAbsT3/M^3']:>7.4f}")
