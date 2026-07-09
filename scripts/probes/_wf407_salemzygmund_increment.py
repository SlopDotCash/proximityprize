#!/usr/bin/env python3
"""
WF407 / route salemzygmund — increment metric + sub-Gaussian proxy probe.

THE OBJECT. p prime, p-1 = m*n, mu_n = order-n subgroup of F_p^x (index m).
Gauss period:   eta_b = sum_{x in mu_n} e_p(b*x),   b in F_p^x.
Coset reduction: eta_b depends only on the coset b*mu_n, so there are m distinct
values eta_c, c=0..m-1 (one per coset).  B = max_{c} |eta_c|  (over nonzero cosets).

DFT identity (Weil): eta_c = (1/m)[ -1 + sum_{j=1}^{m-1} tau_j * omega^{-jc} ],
where omega = e(1/m), tau_j = Gauss sum of the j-th index-m character, |tau_j|=sqrt(p).
So with a_j = tau_j/sqrt(p) unimodular:
   P(c) := sum_{j=1}^{m-1} a_j omega^{-jc},   |eta_c + 1/m| = (sqrt(p)/m)|P(c)|.
   B ~ (sqrt(p)/m) * ||P||_inf  = (sqrt(p)/m) max_c |P(c)|.

SALEM-ZYGMUND: for RANDOM unimodular a_j, ||P||_inf ~ sqrt(m log m), giving
   B ~ (sqrt(p)/m) sqrt(m log m) = sqrt(p/m) sqrt(log m) = sqrt(n log m).

We test, directly on the REAL Gauss-sum sequence:
 (1) the increment metric  d(c,c') = ||eta_c - eta_{c'}||_{psi2}  (and its L2 surrogate);
     CLAIM (KB self-refutation): the L2 increment is FLAT ~ sqrt(2n) for all c != c'.
 (2) the per-period sub-Gaussian PROXY sigma^2 from the empirical MGF
     M(lambda) = (1/m) sum_c exp(lambda Re(zeta-bar eta_c)); fit log M(lambda) <= sigma^2 lambda^2/2.
 (3) whether B / sqrt(n log m) is O(1) and whether ||P||_inf / sqrt(m log m) -> ~1
     (the Salem-Zygmund constant), comparing to a random-unimodular control.
"""
import cmath, math, random

def is_prime(n):
    if n < 2: return False
    for d in range(2, int(n**0.5)+1):
        if n % d == 0: return False
    return True

def primitive_root(p):
    # find a generator of F_p^x
    if p == 2: return 1
    fac = []
    phi = p-1
    d = 2; t = phi
    while d*d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0: t//=d
        d += 1
    if t > 1: fac.append(t)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fac):
            return g
    return None

def gauss_periods(p, n, g=None):
    """Return list of the m distinct eta values (one per coset), m=(p-1)//n.
    eta_b = sum_{x in mu_n} e_p(b x).  cosets indexed c=0..m-1: representative b = g^c."""
    assert (p-1) % n == 0
    m = (p-1)//n
    if g is None: g = primitive_root(p)
    # mu_n = <g^m>  (order n)
    gen = pow(g, m, p)
    mu = []
    x = 1
    for _ in range(n):
        mu.append(x); x = (x*gen) % p
    # representative for coset c is g^c
    e = [cmath.exp(2j*math.pi*k/p) for k in range(p)]
    etas = []
    bc = 1  # g^c
    for c in range(m):
        s = 0j
        for x in mu:
            s += e[(bc*x) % p]
        etas.append(s)
        bc = (bc*g) % p
    return etas, m, g

def l2_increment_stats(etas):
    """Empirical pairwise |eta_c - eta_c'| over all c<c'. Returns (mean, min, max) of the
    distances and of distances^2 (the squared L2 increment)."""
    m = len(etas)
    dists = []
    for i in range(m):
        for j in range(i+1, m):
            dists.append(abs(etas[i]-etas[j]))
    import statistics as st
    d2 = [d*d for d in dists]
    return (st.mean(dists), min(dists), max(dists),
            st.mean(d2), min(d2), max(d2))

def subgauss_proxy(etas):
    """Fit a sub-Gaussian proxy sigma^2 to the real part value distribution.
    For direction zeta, X_zeta(c) = Re(zeta-bar * eta_c). Centered. The smallest sigma^2
    s.t. (1/m) sum exp(lambda X) <= exp(sigma^2 lambda^2 /2) for all tested lambda.
    Report worst-case (over a few directions) proxy / n and compare to variance/n."""
    m = len(etas)
    import statistics as st
    worst_proxy = 0.0
    worst_var = 0.0
    dirs = [cmath.exp(2j*math.pi*t/16) for t in range(16)]
    lambdas = [0.25,0.5,0.75,1.0,1.5,2.0]
    for zeta in dirs:
        X = [(zeta.conjugate()*e).real for e in etas]
        mu = st.mean(X)
        Xc = [x-mu for x in X]
        var = st.pvariance(Xc) if len(Xc)>1 else 0.0
        worst_var = max(worst_var, var)
        for lam in lambdas:
            M = st.mean(math.exp(lam*x) for x in Xc)
            # sigma^2 needed: log M <= sigma^2 lam^2/2  => sigma^2 >= 2 log M / lam^2
            need = 2*math.log(M)/(lam*lam) if M>0 else 0.0
            worst_proxy = max(worst_proxy, need)
    return worst_proxy, worst_var

def P_supnorm(etas, m):
    """||P||_inf = (m/sqrt(p)) * max_c |eta_c + 1/m|  but we just compute directly
    B = max_{c=1..m-1} |eta_c| over nonzero cosets (c=0 is the trivial coset = principal)."""
    # c=0 corresponds to b in mu_n itself (the principal period); B excludes... actually
    # B = max over b!=0 of |eta_b|, which is max over ALL m cosets. The c=0 period is the
    # subgroup's own period (real, ~ -1/... ). Take max over all but report both.
    mags = [abs(e) for e in etas]
    return max(mags), max(mags[1:]) if m>1 else max(mags)

def main():
    random.seed(1)
    print(f"{'p':>7} {'n':>5} {'m':>6} | {'B':>8} {'sqrt(n log m)':>13} {'R=B/that':>9} "
          f"| {'d2_mean/n':>9} {'d2_min/n':>9} {'d2_max/n':>9} | {'proxy/n':>8} {'var/n':>7} "
          f"| {'||P||inf':>9} {'sqrt(m logm)':>11} {'SZconst':>8}")
    # sweep p = 1 mod n for n = 8,16,32 with growing m
    cases = []
    for n in [8, 16, 32, 64]:
        cnt = 0
        p = n+1
        while cnt < 6:
            p += n  # p = 1 mod n candidates step by n
            # need p prime and p-1 = m n with m as large as we can afford
            if is_prime(p) and (p-1) % n == 0:
                m = (p-1)//n
                if m < 8: continue
                # cost ~ m*n ~ p; cap p
                if p > 60000: break
                cases.append((p,n,m))
                cnt += 1
    for (p,n,m) in cases:
        etas, m, g = gauss_periods(p, n)
        B_all, B_nonprinc = P_supnorm(etas, m)
        B = B_all
        target = math.sqrt(n*math.log(m))
        R = B/target if target>0 else float('nan')
        dmean,dmin,dmax,d2mean,d2min,d2max = l2_increment_stats(etas)
        proxy, var = subgauss_proxy(etas)
        # ||P||_inf relation: B ~ (sqrt(p)/m)||P||inf  => ||P||inf = B*m/sqrt(p)
        Pinf = B*m/math.sqrt(p)
        szref = math.sqrt(m*math.log(m))
        szconst = Pinf/szref if szref>0 else float('nan')
        print(f"{p:>7} {n:>5} {m:>6} | {B:8.3f} {target:13.3f} {R:9.3f} "
              f"| {d2mean/n:9.3f} {d2min/n:9.3f} {d2max/n:9.3f} | {proxy/n:8.3f} {var/n:7.3f} "
              f"| {Pinf:9.3f} {szref:11.3f} {szconst:8.3f}")

    # RANDOM control: replace tau_j/sqrt(p) by random unimodular, rebuild eta, measure SZ const.
    print("\n--- RANDOM unimodular control (a_j iid uniform on unit circle) ---")
    print(f"{'m':>6} {'n(=p/m)':>8} | {'||P||inf':>9} {'sqrt(m logm)':>11} {'SZconst':>8} "
          f"| {'d2_mean/n':>9} {'d2_max/n':>9} | {'proxy/n':>8}")
    for (m, n) in [(64,8),(128,16),(256,16),(512,32),(1024,32)]:
        a = [cmath.exp(2j*math.pi*random.random()) for _ in range(m-1)]
        om = cmath.exp(-2j*math.pi/m)
        # P(c) = sum_{j=1}^{m-1} a_j om^{jc}; eta_c surrogate = (1/m)(-1 + sqrt(p) P(c)), p=n*m+1
        p = n*m+1
        Pvals = []
        etas = []
        for c in range(m):
            s = sum(a[j-1]*(om**(j*c)) for j in range(1,m))
            Pvals.append(s)
            etas.append((-1 + math.sqrt(p)*s)/m)
        Pinf = max(abs(v) for v in Pvals)
        szref = math.sqrt(m*math.log(m))
        import statistics as st
        d2 = []
        for i in range(0,m,max(1,m//64)):
            for j in range(i+1,m,max(1,m//64)):
                d2.append(abs(etas[i]-etas[j])**2)
        proxy, var = subgauss_proxy(etas)
        print(f"{m:>6} {n:>8} | {Pinf:9.3f} {szref:11.3f} {Pinf/szref:8.3f} "
              f"| {st.mean(d2)/n:9.3f} {max(d2)/n:9.3f} | {proxy/n:8.3f}")

if __name__ == "__main__":
    main()
