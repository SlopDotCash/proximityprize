"""
C077 attack: "Free-cumulant (planar) spectral-edge bound" for B = max_b |eta_b|.

CLAIM (C077): B is the spectral edge of the m-atom measure mu = empirical law of the
eigenvalues {eta_i} = Gauss periods. The edge of a measure is governed by its FREE
cumulants (R-transform), not classical cumulants. Proven low-order free cumulants
kappa_2^free = mu_2 = 1, kappa_4^free = mu_4 - 2 mu_2^2 = 1 - 3/n > 0 are O(1) bounded
=> edge ~ 2 sqrt(n) * (1 + correction) ~ sqrt(n) polylog.

WHAT WE TEST (prize regime ONLY: dyadic mu_n PROPER subgroup, p=1 mod n prime,
n << sqrt q, beta = log_n p in [4,5], m = (p-1)/n large):

 (1) VERIFY the moment numbers C077 quotes: mu_2 = 1, mu_4 = 3 - 3/n (normalized by
     n^r), classical kappa_4 = -3/n, free kappa_4 = 1 - 3/n.  [exact-ish, double prec]

 (2) THE DECISIVE TEST. Reconstruct the spectral edge from FINITELY MANY free cumulants
     vs the TRUE edge B = max|eta|. The free-cumulant -> edge map for a compactly
     supported measure is: edge = max of the support, and for a measure the edge is
     determined by the R-transform R(z) = sum_{k>=1} kappa_{k+1} z^k via the relation
     that the edge is where the inverse Cauchy transform K(z)=1/z + R(z) has a critical
     point (K'(z*)=0, edge = K(z*)).  Truncating R at order 2r uses only the first r
     free cumulants. We ask: does the edge predicted by the LOW free cumulants
     (kappa_2, kappa_4 only, all proven) track B, or does it need the HIGH free
     cumulants (kappa_{2r}, r ~ log m, exactly the open deep moments)?

 (3) Compare to the *semicircle* edge 2 sqrt(n) (only kappa_2 nonzero) and the true B.
     If true B ~ sqrt(n log m) >> 2 sqrt(n), the edge is NOT captured by low cumulants;
     the gap is carried by the high free cumulants = the open deep-moment wall.

 (4) Compute the HIGH free cumulants directly (Mobius on noncrossing partitions) and
     check whether they are O(1)-bounded (C077's hope) or GROW (which would mean the
     edge bound needs them all = no free-probability shortcut).
"""

import cmath, math

def _is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

# ---------- prize-regime proper-subgroup primes ----------
def find_primes(n, beta_lo, beta_hi, count):
    lo = int(n**beta_lo); hi = int(n**beta_hi)
    out = []
    start = max(lo, n+1)
    # we need p = 1 mod n; step by n from the first such value
    first = start + ((1 - start) % n)
    p = first
    while p < hi:
        if _is_prime(p):
            out.append(p)
            if len(out) >= count:
                break
        p += n
    return out

def subgroup(n, p):
    # find generator of F_p^*, take g^{(p-1)/n} as generator of the order-n subgroup
    # quick generator search
    def is_gen(g):
        seen = set(); x = 1
        for _ in range(p-1):
            x = x*g % p
        return True
    # multiplicative order n element: take any g, raise to (p-1)/n
    e = (p-1)//n
    for g in range(2, p):
        h = pow(g, e, p)
        # check order exactly n
        if pow(h, n, p) == 1:
            # verify order is exactly n (no proper divisor)
            ok = all(pow(h, n//d, p) != 1 for d in set([2]) if n % d == 0)
            if ok:
                # build subgroup
                H = []
                x = 1
                for _ in range(n):
                    H.append(x); x = x*h % p
                if len(set(H)) == n:
                    return H
    return None

def periods(n, p, H):
    # eta_b = sum_{y in H} exp(2 pi i b y / p), real (since -1 in H for dyadic n)
    w = 2*math.pi/p
    cosw = [math.cos(w*j) for j in range(p)]
    sinw = [math.sin(w*j) for j in range(p)]
    etas = []
    for b in range(1, p):  # b != 0
        re = 0.0; im = 0.0
        for y in H:
            idx = (b*y) % p
            re += cosw[idx]; im += sinw[idx]
        etas.append(complex(re, im))
    return etas

# ---------- moments of the period measure (over b != 0), normalized ----------
def normalized_moments(etas, n, maxr):
    # use real parts (eta is real up to tiny im for dyadic n); use |eta| magnitude squared moments
    # The measure mu = empirical law of {eta_b} (real). Moments mu_{2r} = E[(eta/sqrt n)^{2r}]
    vals = [e.real for e in etas]
    N = len(vals)
    mom = {}
    for r in range(1, maxr+1):
        s = sum((v/math.sqrt(n))**(2*r) for v in vals)/N
        mom[2*r] = s
    return mom

# ---------- free cumulants from moments (Mobius on noncrossing partitions) ----------
# moment-cumulant: m_k = sum over NC(k) of prod kappa_{block}. Even measure => odd vanish.
# We invert recursively for the (raw, unnormalized) moments of the real measure eta (not /sqrt n).
# Use the standard recursion via the generating identity M(z) = 1 + sum m_k z^k,
# and free cumulants via R-transform. Easiest: use the recursion
#   m_n = sum_{s=1}^{n} kappa_s * sum_{ i_1+...+i_s = n-s } prod m_{i_j}
# (free moment-cumulant relation). Solve for kappa_n.
def free_cumulants_from_moments(m, K):
    # m: dict {k: m_k}, m_0 = 1; compute kappa_1..kappa_K
    m = dict(m); m[0] = 1.0
    kappa = {}
    # build using: m_n = sum_{s=1}^n kappa_s * B_{n,s} where
    # B_{n,s} = sum over compositions of (n-s) into s nonneg parts of prod m_{parts}
    # We'll compute m-extended convolution. Use DP for sum over s ordered tuples.
    # Helper: coefficient sum over (i_1..i_s) >=0 summing to t of prod m_{i_j}.
    from functools import lru_cache
    def Bts(t, s):
        # number-weighted: convolution power s of sequence m_0,m_1,... at index t
        # m as polynomial coeffs
        # do iterative convolution
        seq = [m.get(i, 0.0) for i in range(t+1)]
        res = [1.0]  # s=0 -> delta at 0
        for _ in range(s):
            new = [0.0]*(t+1)
            for a in range(len(res)):
                if a > t: break
                for b in range(t+1-a):
                    new[a+b] += res[a]*seq[b]
            res = new
        return res[t] if t < len(res) else 0.0
    for nidx in range(1, K+1):
        # m_n = sum_{s=1}^{n} kappa_s * B_{n-s, s}
        # isolate kappa_n: B_{0,n} = m_0^n = 1
        rhs = m.get(nidx, 0.0)
        acc = 0.0
        for s in range(1, nidx):
            acc += kappa[s]*Bts(nidx-s, s)
        kappa[nidx] = rhs - acc  # since B_{0,n}=1
    return kappa

# ---------- spectral edge from free cumulants via R-transform critical point ----------
# K(z) = 1/z + R(z), R(z) = sum_{k>=1} kappa_{k+1} z^k. Edge = K(z*) at K'(z*)=0, z*>0 minimal.
def edge_from_R(kappa, K, ztol=1e-12):
    # R(z) = sum_{k=1}^{K-1} kappa_{k+1} z^k  (need kappa_2.. = free cumulants of measure)
    # build K(z) = 1/z + sum kappa_{j} z^{j-1}, j>=2
    def Kfun(z):
        s = 1.0/z
        for j in range(2, K+1):
            s += kappa.get(j, 0.0) * z**(j-1)
        return s
    def Kp(z):
        s = -1.0/z**2
        for j in range(2, K+1):
            s += kappa.get(j, 0.0)*(j-1)*z**(j-2)
        return s
    # find smallest positive critical point by scanning
    best = None
    z = 1e-4
    prev = Kp(z)
    zmax = 5.0
    steps = 200000
    for i in range(1, steps+1):
        zn = 1e-4 + (zmax-1e-4)*i/steps
        cur = Kp(zn)
        if prev == 0 or (prev < 0 and cur >= 0) or (prev > 0 and cur <= 0):
            # bisect
            a, b = z, zn
            for _ in range(60):
                mwz = (a+b)/2
                if Kp(a)*Kp(mwz) <= 0: b = mwz
                else: a = mwz
            zc = (a+b)/2
            val = Kfun(zc)
            if best is None or val < best:
                best = val
            break
        z = zn; prev = cur
    return best

print("="*80)
print("C077: free-cumulant spectral-edge bound for B = max_b |eta_b|")
print("prize regime: dyadic mu_n PROPER subgroup, p=1 mod n, n << sqrt q, beta in [4,5]")
print("="*80)

for n in [8, 16, 32]:
    ps = find_primes(n, 4.0, 4.6, 1)
    if not ps:
        ps = find_primes(n, 3.5, 5.0, 1)
    if not ps:
        print(f"n={n}: no prime found in band"); continue
    p = ps[0]
    H = subgroup(n, p)
    if H is None:
        print(f"n={n} p={p}: subgroup build failed"); continue
    m = (p-1)//n
    beta = math.log(p)/math.log(n)
    etas = periods(n, p, H)
    B = max(abs(e) for e in etas)            # the TRUE spectral edge (= max|eta|)
    # normalized moments mu_{2r} = E[(eta/sqrt n)^{2r}]
    mom = normalized_moments(etas, n, 8)
    mu2 = mom[2]; mu4 = mom[4]; mu6 = mom[6]
    kappa4_cl = mu4 - 3*mu2**2
    kappa4_free = mu4 - 2*mu2**2
    print(f"\n--- n={n}  p={p}  beta={beta:.2f}  m={m} ---")
    print(f"  C077's moment numbers (normalized by n^r):")
    print(f"    mu_2 = {mu2:.5f}   (claim 1)")
    print(f"    mu_4 = {mu4:.5f}   (claim 3 - 3/n = {3-3/n:.5f})")
    print(f"    mu_6 = {mu6:.5f}   (claim 15-45/n+40/n^2 = {15-45/n+40/n**2:.5f})")
    print(f"    classical kappa_4 = mu4 - 3 mu2^2 = {kappa4_cl:+.5f}  (claim -3/n = {-3/n:+.5f})")
    print(f"    FREE     kappa_4 = mu4 - 2 mu2^2 = {kappa4_free:+.5f}  (claim 1-3/n = {1-3/n:+.5f})")

    # --- the spectral edge tests (work with RAW measure eta, edge in units of sqrt(n)) ---
    # raw moments of eta (NOT normalized): m_{2r} = E[eta^{2r}] = n^r * mu_{2r}
    raw = {}
    vals = [e.real for e in etas]
    Nv = len(vals)
    Kmax = 16  # use up to 8 even moments -> free cumulants up to order 16
    for k in range(1, Kmax+1):
        raw[k] = sum(v**k for v in vals)/Nv   # odd ~ 0
    kap = free_cumulants_from_moments(raw, Kmax)

    # edge predicted using ONLY low cumulants (kappa_2 only = semicircle; +kappa_4; ... )
    sc_edge = 2*math.sqrt(kap[2]) if kap[2] > 0 else float('nan')   # semicircle 2 sqrt(var)
    # build truncated kappa dicts
    def edge_trunc(order):
        kk = {j: kap[j] for j in range(2, order+1)}
        return edge_from_R(kk, order)
    e_k2 = edge_trunc(2)    # semicircle
    e_k4 = edge_trunc(4)
    e_k6 = edge_trunc(6)
    e_k8 = edge_trunc(8)
    e_kall = edge_trunc(Kmax)

    print(f"  free cumulants kappa_2..kappa_{Kmax} (RAW, units involve n):")
    for j in range(2, Kmax+1, 2):
        # normalize free cumulant by n^{j/2} to see scale vs O(1) hope
        print(f"    kappa_{j} = {kap[j]:+.4e}   kappa_{j}/n^{j//2} = {kap[j]/n**(j//2):+.5f}")
    print(f"  EDGE from free cumulants (truncated), in units of sqrt(n):")
    print(f"    semicircle (k2 only)  edge/sqrt(n) = {e_k2/math.sqrt(n):.4f}   (=2.0 = pure semicircle)")
    if e_k4: print(f"    +k4                   edge/sqrt(n) = {e_k4/math.sqrt(n):.4f}")
    if e_k6: print(f"    +k6                   edge/sqrt(n) = {e_k6/math.sqrt(n):.4f}")
    if e_k8: print(f"    +k8                   edge/sqrt(n) = {e_k8/math.sqrt(n):.4f}")
    if e_kall: print(f"    all to k{Kmax}          edge/sqrt(n) = {e_kall/math.sqrt(n):.4f}")
    print(f"  TRUE edge  B = max|eta|       B/sqrt(n)     = {B/math.sqrt(n):.4f}")
    print(f"  TRUE edge  B                  B/sqrt(n log m) = {B/math.sqrt(n*math.log(m)):.4f}")
    print(f"  ratio  B / (semicircle edge 2 sqrt n)        = {B/(2*math.sqrt(n)):.4f}")
