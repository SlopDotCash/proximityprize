#!/usr/bin/env python3
"""
G94 probe: generic chaining under Jacobi-cocycle metrics on the Gauss-period field.

Field: eta_b = sum_{x in mu_n} e_p(b x), b over the m = (p-1)/n coset reps of F_p*/mu_n.
(eta is coset-invariant and REAL for 2-power n since -1 in mu_n.)

Jacobi apparatus: empirical spectral measure nu = uniform on {eta_c : c coset}, its
orthonormal-polynomial recurrence coefficients (a_k, b_k) (Jacobi matrix), the transfer-matrix
cocycle T_k(z) = [[(z-a_{k-1})/b_k, -b_{k-1}/b_k],[1,0]] and its products A_K(z).

Candidate metrics d(b,b') (all except d_orbit factor through the VALUES (eta_b, eta_b')
because the Jacobi apparatus depends on b only through the evaluation energy eta_b):
  d_val      = |eta_b - eta_b'|                       (G70/OC-CHAIN 1-D Euclidean baseline)
  d_cd(N)    = || phi_N(eta_b) - phi_N(eta_b') ||_2,  phi_N = (p_0,...,p_N) CD-kernel embedding
  d_tm(K)    = || A_K(eta_b) - A_K(eta_b') ||_F       (transfer-matrix product metric)
  d_proj(K)  = RP^1 angle between A_K(eta).(1,0)      (projective cocycle direction)
  d_hyp(K)   = hyperbolic dist between truncated m-functions m_K(eta + i h)
  d_lyap(K)  = |L_K(eta_b) - L_K(eta_b')|, L_K = (1/K) log ||A_K||   (finite Lyapunov)
  d_orbit    = (sum_j 2^{-j} (eta_{2^j b} - eta_{2^j b'})^2)^{1/2}   (mult-2 orbit path; NOT
               value-factored -- the one candidate that uses b beyond eta_b)

Tests per metric:
  * DOMINATION / det-sub-Gaussianity: for a DETERMINISTIC field the tail condition
    P(|eta_b - eta_b'| > t) <= 2 exp(-t^2/d^2) forces |eta_b - eta_b'| <= sqrt(ln 2) * d.
    We measure dom := max_pairs |Delta eta| / d  (dom = inf over rescalings; sub-G at scale
    s means dom/s <= sqrt(ln2)). Hard failure: d ~ 0 with Delta eta != 0.
  * gamma_2 via greedy admissible nets (sizes 1,2,4,16,256,65536 capped at m), value
    gamma2 = max_b sum_k 2^{k/2} dist(b, T_k). Normalized certificate scale:
    gamma2_norm = gamma2 * dom / sqrt(ln 2)  (the smallest gamma2 achievable while the
    deterministic sub-Gaussian tail condition holds). Compare vs M, sqrt(n ln p), spread.
  * moment-ratio: z = |Delta eta|/d over pairs; report quantiles/max (Gaussian-like tail
    needs bounded z; det reading needs z <= sqrt(ln 2) after rescale by dom... i.e. z/dom).
  * lone-spike countermodel: field with one atom at s = sqrt(2 n ln m), rest 0.
Also: spacing-law check max_j (b_j^2 - b_{j-1}^2)/n on the Hermite ramp.
"""
import numpy as np, math, sys

rng = np.random.default_rng(4660094)

def is_prime(q):
    if q < 2: return False
    for r in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if q % r == 0: return q == r
    d, s = q-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x = pow(a, d, q)
        if x in (1, q-1): continue
        for _ in range(s-1):
            x = x*x % q
            if x == q-1: break
        else: return False
    return True

def primitive_root(p):
    fac = []
    t = p-1; d = 2
    while d*d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0: t //= d
        d += 1
    if t > 1: fac.append(t)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g
    raise RuntimeError

def primes_1modn(n, lo, hi, count, include=()):
    out = list(include)
    q = lo - ((lo-1) % n)  # q = 1 mod n
    q += 0 if q % n == 1 else n  # crude; fix below
    q = (lo // n) * n + 1
    while q < lo: q += n
    while len(out) < count and q <= hi:
        if q not in out and is_prime(q): out.append(q)
        q += n
    return sorted(out)

def gauss_periods(p, n):
    """Return eta over the m coset reps, plus coset-index lookup and the rep list."""
    m = (p-1)//n
    g = primitive_root(p)
    # discrete log table: dl[g^a mod p] = a
    dl = np.zeros(p, dtype=np.int64)
    x = 1
    for a in range(p-1):
        dl[x] = a
        x = x*g % p
    mu = np.array([pow(g, m*j, p) for j in range(n)], dtype=np.int64)
    reps = np.array([pow(g, i, p) for i in range(m)], dtype=np.int64)
    # eta_i = sum_x cos(2 pi (rep_i * x)/p)  (real since -1 in mu_n for 2-power n)
    prod = (reps[:, None] * mu[None, :]) % p
    eta = np.cos(2*np.pi*prod/np.float64(p)).sum(axis=1)
    coset_of = dl % m  # coset index of any y in F_p^*: dl[y] mod m
    return eta, coset_of, reps

def stieltjes(eta, w, K):
    """Orthonormal polys of discrete measure sum w_i delta_{eta_i}. Returns a[0..K-1],
    b[1..K] (b[0]=1 conv), and V (m x (K+1)) with V[:,k] = p_k(eta_i). Full reorth."""
    mvals = len(eta)
    a, b = [], [1.0]
    V = np.zeros((mvals, K+2))
    V[:, 0] = 1.0
    for k in range(K+1):
        xv = eta * V[:, k]
        ak = float(np.sum(w * xv * V[:, k]))
        a.append(ak)
        t = xv - ak*V[:, k] - (b[k]*V[:, k-1] if k >= 1 else 0.0)
        # reorthogonalize twice
        for _ in range(2):
            for j in range(k+1):
                t -= np.sum(w*t*V[:, j]) * V[:, j]
        bk = math.sqrt(max(float(np.sum(w*t*t)), 0.0))
        if bk < 1e-10 or k == K:
            return np.array(a), np.array(b), V[:, :k+1]
        b.append(bk)
        V[:, k+1] = t/bk
    return np.array(a), np.array(b), V[:, :K+1]

def transfer_products(a, b, K, zvals):
    """A_K(z) = T_K ... T_1, T_k = [[(z-a[k-1])/b[k], -b[k-1]/b[k]],[1,0]]. Vectorized over z."""
    N = len(zvals)
    A = np.zeros((N, 2, 2), dtype=complex)
    A[:, 0, 0] = 1; A[:, 1, 1] = 1
    for k in range(1, K+1):
        T = np.zeros((N, 2, 2), dtype=complex)
        T[:, 0, 0] = (zvals - a[k-1])/b[k]
        T[:, 0, 1] = -(b[k-1] if k >= 2 else 1.0)/b[k]
        T[:, 1, 0] = 1
        A = np.einsum('nij,njk->nik', T, A)
    return A

def m_function_trunc(a, b, K, zvals):
    """Truncated continued fraction m_K(z) = 1/(a0 - z - b1^2/(a1 - z - ...))."""
    f = a[K] - zvals
    for k in range(K-1, -1, -1):
        f = a[k] - zvals - (b[k+1]**2)/f
    return 1.0/f

def pdist_from_features(F):
    """Pairwise Euclidean distance matrix from feature rows."""
    sq = np.sum(F*F, axis=1)
    D2 = sq[:, None] + sq[None, :] - 2*F@F.T
    np.maximum(D2, 0, out=D2)
    return np.sqrt(D2)

def greedy_gamma2(D):
    """Greedy admissible nets: sizes 1,2,4,16,256,65536 (capped). Returns gamma2 upper est."""
    mv = D.shape[0]
    sizes = [1]
    k = 1
    while sizes[-1] < mv:
        sizes.append(min(2**(2**k), mv)); k += 1
    # farthest-point traversal
    order = [int(np.argmin(D.sum(axis=1)))]  # start at medoid
    dist_to_net = D[order[0]].copy()
    for _ in range(1, sizes[-1]):
        nxt = int(np.argmax(dist_to_net))
        order.append(nxt)
        np.minimum(dist_to_net, D[nxt], out=dist_to_net)
    total = np.zeros(mv)
    for k, s in enumerate(sizes):
        net = order[:s]
        dmin = D[net].min(axis=0)
        total += (2**(k/2)) * dmin
    return float(total.max())

def analyze_metric(name, D, eta, results, hard_eps=1e-9):
    mv = len(eta)
    iu = np.triu_indices(mv, 1)
    dE = np.abs(eta[:, None] - eta[None, :])[iu]
    dm = D[iu]
    hard = int(np.sum((dm < 1e-12) & (dE > hard_eps)))
    mask = dm > 1e-12
    z = dE[mask]/dm[mask]
    dom = float(z.max()) if len(z) else 0.0
    q99 = float(np.quantile(z, 0.99)) if len(z) else 0.0
    med = float(np.median(z)) if len(z) else 0.0
    g2 = greedy_gamma2(D)
    diam = float(dm.max())
    results.append(dict(name=name, dom=dom, z99=q99, zmed=med, hard=hard,
                        g2=g2, diam=diam))
    return results

def run_instance(p, n, Kdepths=None, verbose=True):
    m = (p-1)//n
    eta, coset_of, reps = gauss_periods(p, n)
    M = float(np.abs(eta).max())
    spread = float(eta.max() - eta.min())
    tgt = math.sqrt(n*math.log(p))
    w = np.full(m, 1.0/m)
    K = min(m-1, 48)
    a, b, V = stieltjes(eta, w, K)
    Kav = len(b)-1  # available depth for transfer products
    kstar = int(np.argmax(b[1:]) + 1)
    # spacing law on the ramp (up to kstar)
    db2 = np.diff(b**2)  # b_1^2-b_0^2,...
    ramp = db2[1:kstar] / n if kstar >= 2 else np.array([])
    spacing_max = float(ramp.max()) if len(ramp) else float('nan')
    Klog = max(2, min(Kav, int(math.ceil(math.log(p)))))
    Kt = min(Kav, max(2, kstar))
    if verbose:
        print(f"\n=== n={n} p={p} m={m} beta={math.log(p)/math.log(n):.2f} "
              f"M={M:.3f} spread={spread:.3f} sqrt(n ln p)={tgt:.3f} M/tgt={M/tgt:.3f}")
        print(f"    Jacobi: depth avail={Kav}, turnover k*={kstar}, b_k^2/nk ramp head="
              f"{[round(b[k]**2/(n*k),3) for k in range(1,min(6,Kav+1))]}, "
              f"spacing law max (b_j^2-b_(j-1)^2)/n on ramp = {spacing_max:.4f}")

    results = []
    # d_val baseline
    Dval = np.abs(eta[:, None] - eta[None, :])
    analyze_metric("d_val", Dval, eta, results)
    # d_cd at several depths
    for N in sorted(set([2, min(Klog, V.shape[1]-1), min(Kt, V.shape[1]-1), V.shape[1]-1])):
        F = V[:, :N+1]
        analyze_metric(f"d_cd(N={N})", pdist_from_features(F), eta, results)
    # transfer-matrix metrics at K in {Klog, kstar}
    for KK in sorted(set([Klog, Kt])):
        A = transfer_products(a, b, KK, eta.astype(complex))
        Fr = np.real(A).reshape(m, 4)
        analyze_metric(f"d_tm(K={KK})", pdist_from_features(Fr), eta, results)
        # projective direction of A.(1,0)
        v = np.real(A[:, :, 0])  # (m,2)
        nv = np.linalg.norm(v, axis=1); nv[nv == 0] = 1
        u = v/nv[:, None]
        cosang = np.abs(u@u.T); np.clip(cosang, -1, 1, out=cosang)
        Dproj = np.arccos(cosang)  # RP^1 angle in [0, pi/2]
        analyze_metric(f"d_proj(K={KK})", Dproj, eta, results)
        # finite Lyapunov
        normA = np.linalg.norm(np.real(A), axis=(1, 2))
        L = np.log(np.maximum(normA, 1e-300))/KK
        analyze_metric(f"d_lyap(K={KK})", np.abs(L[:, None]-L[None, :]), eta, results)
    # hyperbolic m-function metric
    h = float(np.median(np.diff(np.sort(eta))))
    h = max(h, 1e-6)
    mf = m_function_trunc(a, b, min(Klog, Kav), eta + 1j*h)
    im = np.imag(mf)
    if np.all(im > 0):
        du = np.abs(mf[:, None]-mf[None, :])**2/(2*np.outer(im, im))
        Dhyp = np.arccosh(1+du)
        analyze_metric(f"d_hyp(K={min(Klog,Kav)},h={h:.2g})", Dhyp, eta, results)
    else:
        print(f"    [d_hyp skipped: Im m_K not all >0 at h={h:.3g} "
              f"(min Im = {im.min():.3g}) -- not Herglotz at this truncation]")
    # orbit metric (multiply coset by 2), J=8 levels, weights 2^-j
    idx = np.arange(m)
    orbF = []
    cur = reps.copy()
    for j in range(8):
        orbF.append((2.0**(-j/2)) * eta[coset_of[cur % p]])
        cur = (cur*2) % p
    orbF = np.array(orbF).T  # (m, 8)
    analyze_metric("d_orbit(J=8,w=2^-j)", pdist_from_features(orbF), eta, results)

    sln2 = math.sqrt(math.log(2))
    if verbose:
        print(f"    {'metric':24s} {'dom':>9s} {'z99/dom':>8s} {'hard0':>5s} "
              f"{'g2':>10s} {'diam':>10s} {'g2n':>9s} {'g2n/M':>7s} {'g2n/tgt':>8s} {'g2n/sprd':>8s}")
        for r in results:
            g2n = r['g2']*r['dom']/sln2  # gamma2 at the sub-Gaussian-legal rescale
            print(f"    {r['name']:24s} {r['dom']:9.3f} "
                  f"{(r['z99']/r['dom'] if r['dom']>0 else 0):8.3f} {r['hard']:5d} "
                  f"{r['g2']:10.3f} {r['diam']:10.3f} {g2n:9.2f} {g2n/M:7.3f} "
                  f"{g2n/tgt:8.3f} {g2n/spread:8.3f}")
    return dict(p=p, n=n, m=m, M=M, spread=spread, tgt=tgt, kstar=kstar,
                spacing_max=spacing_max, results=results)

def lone_spike_test(n=16, m=445):
    """Countermodel: one atom at s=sqrt(2 n ln m), rest exactly 0."""
    s = math.sqrt(2*n*math.log(m))
    eta = np.zeros(m); eta[0] = s
    w = np.full(m, 1.0/m)
    a, b, V = stieltjes(eta, w, 4)  # 2-atom support -> chain ends at depth 1
    Kav = len(b)-1
    print(f"\n=== LONE-SPIKE countermodel: m={m}, spike s={s:.3f}, "
          f"Jacobi chain length={Kav} (2-atom measure => depth 1)")
    print(f"    a={np.round(a,4)}, b={np.round(b,4)}")
    results = []
    analyze_metric("d_val", np.abs(eta[:, None]-eta[None, :]), eta, results)
    analyze_metric(f"d_cd(N={V.shape[1]-1})", pdist_from_features(V), eta, results)
    if Kav >= 1:
        A = transfer_products(a, b, 1, eta.astype(complex))
        analyze_metric("d_tm(K=1)", pdist_from_features(np.real(A).reshape(m, 4)), eta, results)
        normA = np.linalg.norm(np.real(A), axis=(1, 2))
        L = np.log(np.maximum(normA, 1e-300))
        analyze_metric("d_lyap(K=1)", np.abs(L[:, None]-L[None, :]), eta, results)
    sln2 = math.sqrt(math.log(2))
    print(f"    {'metric':16s} {'dom':>9s} {'hard0':>5s} {'g2':>10s} {'diam':>10s} "
          f"{'g2n':>9s} {'g2n/spike':>9s}")
    for r in results:
        g2n = r['g2']*r['dom']/sln2
        print(f"    {r['name']:16s} {r['dom']:9.3f} {r['hard']:5d} {r['g2']:10.3f} "
              f"{r['diam']:10.3f} {g2n:9.2f} {g2n/s:9.3f}")
    print("    VERDICT expected: every metric either has hard0>0 (fails sub-G outright: "
          "distinct values at zero distance) or g2n/spike >= ~0.6 (gauge >= sup).")

def main():
    print("G94 Jacobi-cocycle metric probe. det-sub-G legality threshold: after rescale to "
          "dom=sqrt(ln 2)=0.8326, gamma2_norm (g2n) is the smallest chaining gauge value "
          "consistent with the deterministic tail condition. Collapse theorem predicts "
          "g2n >= spread/(2 sqrt(ln2)) = 0.60*spread for EVERY metric.")
    inst = []
    for n, lo, hi, cnt, incl in [(8, 700, 4000, 3, ()),
                                 (16, 6500, 20000, 3, ()),
                                 (32, 64000, 90000, 2, (65537,))]:
        ps = primes_1modn(n, lo, hi, cnt, include=incl)
        for p in ps[:cnt]:
            inst.append((p, n))
    summ = []
    for p, n in inst:
        summ.append(run_instance(p, n))
    lone_spike_test()
    # summary of collapse-law empirical check
    print("\n=== COLLAPSE-LAW CHECK: min over metrics of g2n/spread per instance "
          "(theorem floor = 1/(2 sqrt(ln 2)) = 0.6005)")
    sln2 = math.sqrt(math.log(2))
    for s in summ:
        vals = [(r['g2']*r['dom']/sln2)/s['spread'] for r in s['results'] if r['hard'] == 0]
        nm = [r['name'] for r in s['results'] if r['hard'] == 0]
        if vals:
            i = int(np.argmin(vals))
            print(f"  n={s['n']} p={s['p']}: min g2n/spread = {min(vals):.3f} ({nm[i]}); "
                  f"hard-failures: {[r['name'] for r in s['results'] if r['hard']>0]}")
    print("\n  spacing-law audit: " + ", ".join(
        f"n={s['n']},p={s['p']}: {s['spacing_max']:.3f}" for s in summ))

if __name__ == "__main__":
    main()
