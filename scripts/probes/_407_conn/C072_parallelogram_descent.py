"""
C072 probe: "Reality from -1=zeta^{n/2} makes the dyadic parallelogram a REAL 2D
rotation whose only fixed point is the coherent worst case; ||A-B|| (the chi-twisted
odd-half period) breaks coherence, tying the gap to Lam-Leung antipodal rigidity."

THE CLAIM TO TEST (from C072.json):
  eta_b(mu_{2k}) = A + B,  A = eta_b(mu_k),  B = eta_{b*zeta}(mu_k).
  Parallelogram: ||A+B||^2 + ||A-B||^2 = 2(||A||^2 + ||B||^2)   [trivially true].
  C072's bet: at the WORST coset b* (the one maximizing ||A+B|| = B(mu_{2k})), the
  twisted odd-half period ||A-B|| stays Omega(M(k)^2), which would FORCE
  ||A||^2 + ||B||^2 < 2 M(k)^2, giving a "soft descent" of the house.

  Equivalently: worst case (||A+B|| max) <=> ||A-B|| min <=> A,B aligned (coherence).
  The descent works ONLY if A,B CANNOT align at the worst b (||A-B|| bounded below).

We test EXACTLY (exact big-int field arithmetic + exact-as-possible complex eta) on
PROPER dyadic subgroups mu_n < F_q^*, q prime = 1 mod n, q ~ n^beta (beta>=4),
n << sqrt(q) -- the PRIZE regime (never full group, never small prime).

DECISIVE measurements at the worst frequency b* (argmax over b!=0 of |eta(mu_{2k},b)|):
  (T1) the parallelogram identity holds (sanity, should be ~0 residual).
  (T2) r_twist := ||A-B|| / M(k),  M(k) = sqrt(k) (the sqrt-cancellation target scale).
       Is r_twist bounded BELOW (descent) or near 0 (coherence -> no descent)?
  (T3) the alignment angle between A and B at b*: if A,B ALIGN (||A-B||~0) at the worst
       b, the descent is VACUOUS (the worst case IS the coherent fixed point).
  (T4) does ||A||^2+||B||^2 <= 2 M(k)^2 hold at b*? (the descent conclusion). If NOT,
       descent fails: the halving inflates rather than controls.
  (T5) cross-check vs the actual house ratio C0 = B(mu_n)/sqrt(n) and whether the
       parallelogram gives ANY upper bound on B(mu_{2k}) beyond the trivial
       B(mu_{2k}) <= 2 max(B(mu_k at the two freqs)).
"""

import cmath, math

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def find_prime(n, beta_min):
    """smallest prime q = 1 mod n with q >= n**beta_min and n << sqrt(q)."""
    target = int(n**beta_min)
    q = target - (target % n) + 1
    if q < target: q += n
    while q <= n*n:
        q += n
    while not is_prime(q):
        q += n
    return q

def primitive_root_mod(q):
    facs = []
    m = q-1
    d = 2
    while d*d <= m:
        if m % d == 0:
            facs.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: facs.append(m)
    g = 2
    while True:
        if all(pow(g, (q-1)//p, q) != 1 for p in facs):
            return g
        g += 1

def subgroup(q, g, n):
    """mu_n = the order-n subgroup of F_q^* (n | q-1)."""
    h = pow(g, (q-1)//n, q)  # element of order n
    S = []
    cur = 1
    for _ in range(n):
        S.append(cur)
        cur = (cur * h) % q
    return S, h

def eta(q, G, b):
    """eta_b(G) = sum_{x in G} exp(2*pi*i * b*x / q)."""
    s = 0+0j
    for x in G:
        ang = 2.0*math.pi*((b*x) % q)/q
        s += cmath.exp(1j*ang)
    return s

def coset_reps(q, g, n):
    """one representative per mu_n-coset of F_q^* (eta is constant on these cosets).
    cosets = <g^n> ... we take {g^j : j=0..(q-1)/n - 1} as a transversal of mu_n."""
    m = (q-1)//n
    gn = pow(g, n, q)   # generator of the index-n subgroup (size m) -- WRONG transversal.
    # Correct transversal of mu_n in F_q^*: mu_n = <g^m>. Cosets repr by g^0..g^{m-1}.
    reps = []
    cur = 1
    for _ in range(m):
        reps.append(cur)
        cur = (cur*g) % q
    return reps

def analyze(mu, beta):
    n2 = 2**mu          # = 2k, the upper level
    k  = n2//2          # the lower level size
    q  = find_prime(n2, beta)
    g  = primitive_root_mod(q)
    G2, h2 = subgroup(q, g, n2)   # mu_{2k}
    Gk, hk = subgroup(q, g, k)    # mu_k  (subgroup of G2)
    # a zeta with zeta^k = -1 : zeta = generator of mu_{2k} (order 2k), zeta^k has order 2 => -1
    zeta = h2
    assert pow(zeta, k, q) == q-1, "zeta^k must be -1 mod q"

    M = math.sqrt(k)            # the sqrt-cancellation scale at level k
    Mk_target = math.sqrt(n2)   # scale at level 2k (for house C0)

    # worst frequency b* over the upper level -- scan ONLY mu_{2k}-coset reps
    # (eta(G2,.) is constant on mu_{2k}-cosets; transversal has (q-1)/n2 elements)
    reps = coset_reps(q, g, n2)
    best_b, best_val = None, -1.0
    for b in reps:
        if b == 0: continue
        v = abs(eta(q, G2, b))
        if v > best_val:
            best_val, best_b = v, b
    B_2k = best_val             # = B(mu_{2k}) = max_b |eta(mu_{2k},b)|

    # at b*, decompose: A = eta_b(mu_k), B_half = eta_{b*zeta}(mu_k)
    b = best_b
    A = eta(q, Gk, b)
    Bh = eta(q, Gk, (b*zeta) % q)
    AplusB = A + Bh
    AminusB = A - Bh
    # T1 parallelogram residual
    par = abs(abs(AplusB)**2 + abs(AminusB)**2 - 2*(abs(A)**2+abs(Bh)**2))
    # consistency: A+B should equal eta_b(mu_{2k})
    recon = abs(AplusB - eta(q, G2, b))

    # T2 twist ratio
    r_twist = abs(AminusB)/M
    nrmAB = abs(A)**2 + abs(Bh)**2
    # T3 alignment angle between A and B_half (degrees); 0 = aligned (coherent), 90 = orthogonal
    if abs(A) > 1e-12 and abs(Bh) > 1e-12:
        cosang = (A.real*Bh.real + A.imag*Bh.imag)/(abs(A)*abs(Bh))
        cosang = max(-1.0, min(1.0, cosang))
        ang = math.degrees(math.acos(cosang))
    else:
        ang = float('nan')
    # T4 descent conclusion test: ||A||^2+||B||^2 <= 2 M^2 = 2k ?
    descent_ok = nrmAB <= 2*M*M + 1e-6

    # also: the worst b for the LOWER level (does the upper worst b coincide?)
    repsk = coset_reps(q, g, k)
    bestk_b, bestk_val = None, -1.0
    for bb in repsk:
        if bb == 0: continue
        vv = abs(eta(q, Gk, bb))
        if vv > bestk_val:
            bestk_val, bestk_b = vv, bb
    B_k = bestk_val

    C0_2k = B_2k/math.sqrt(n2)
    C0_k  = B_k/math.sqrt(k)

    return dict(mu=mu, n2=n2, k=k, q=q, beta=beta,
                B_2k=B_2k, C0_2k=C0_2k, B_k=B_k, C0_k=C0_k,
                par_resid=par, recon=recon,
                absA=abs(A), absBh=abs(Bh), absApB=abs(AplusB), absAmB=abs(AminusB),
                r_twist=r_twist, nrmAB=nrmAB, two_Msq=2*M*M, descent_ok=descent_ok,
                align_deg=ang)

print("="*100)
print("C072: dyadic parallelogram descent at the WORST coset b* (PRIZE regime: proper mu_n, q~n^beta)")
print("="*100)
print(f"{'mu':>3} {'n=2k':>5} {'k':>4} {'q':>9} {'b':>2} | {'B(2k)':>7} {'C0(2k)':>6} | "
      f"{'|A|':>6} {'|Bh|':>6} {'|A-B|':>6} {'r_twist':>7} {'align°':>6} | "
      f"{'||A||²+||B||²':>11} {'2M²=2k':>7} {'descent?':>8}")
rows = []
# (mu, beta) pairs kept in the PRIZE regime (n=2^mu proper subgroup, q~n^beta, n<<sqrt q)
# capped so coset transversals (q/n reps) stay tractable in exact python.
cases = [(3,4),(4,4),(5,4),(6,4), (3,5),(4,5),(5,5)]
for (mu, beta) in cases:
        r = analyze(mu, beta)
        rows.append(r)
        print(f"{r['mu']:>3} {r['n2']:>5} {r['k']:>4} {r['q']:>9} {0:>2} | "  # b printed below
              f"{r['B_2k']:>7.3f} {r['C0_2k']:>6.3f} | "
              f"{r['absA']:>6.3f} {r['absBh']:>6.3f} {r['absAmB']:>6.3f} {r['r_twist']:>7.3f} "
              f"{r['align_deg']:>6.1f} | "
              f"{r['nrmAB']:>11.3f} {r['two_Msq']:>7.1f} {str(r['descent_ok']):>8}")

print()
print("Diagnostics:")
print(f"  max parallelogram residual (should be ~0): {max(r['par_resid'] for r in rows):.2e}")
print(f"  max reconstruction residual A+B vs eta(2k,b) (should be ~0): {max(r['recon'] for r in rows):.2e}")
print()
print("KEY READOUTS at worst b*:")
print(f"  alignment angle range (deg): {min(r['align_deg'] for r in rows):.1f} .. {max(r['align_deg'] for r in rows):.1f}")
print(f"     (near 0  => A,B ALIGNED => ||A-B||~0 => the worst case IS the coherent fixed point => descent VACUOUS)")
print(f"  r_twist = ||A-B||/sqrt(k) range: {min(r['r_twist'] for r in rows):.3f} .. {max(r['r_twist'] for r in rows):.3f}")
print(f"     (bounded BELOW => descent has teeth; near 0 => no descent)")
desc_fail = [r for r in rows if not r['descent_ok']]
print(f"  descent conclusion ||A||²+||B||² <= 2k:  fails in {len(desc_fail)}/{len(rows)} cases")
print(f"  C0(2k) [dyadic house] range: {min(r['C0_2k'] for r in rows):.3f} .. {max(r['C0_2k'] for r in rows):.3f}")
print(f"  C0(k)  [one level down]    : {min(r['C0_k'] for r in rows):.3f} .. {max(r['C0_k'] for r in rows):.3f}")
