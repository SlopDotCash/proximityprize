#!/usr/bin/env python3
"""
G98 probe: Guth-Maynard large-values / Halasz-Montgomery Gram bootstrap for the
Gauss-period sup problem.

Object: eta_b = sum_{x in mu_n} e_p(b x), mu_n = order-n (dyadic) subgroup of F_p^*,
p ~ n^4 (beta = 4).  M = max_{b != 0} |eta_b|.  Target: C * sqrt(n log(p/n)).

Facts used: -1 in mu_n (n even) => eta_b is REAL; eta is constant on mu_n-cosets of b.

Probe questions:
 (i)   additive structure of the extremal frequency set B (top-r cosets):
       does B-B collide into few mu_n-cosets?  Are |eta| values on B-B atypical
       (above/below the sqrt(n) Parseval-typical level)?
 (ii)  Halasz-Montgomery Gram inequality  r V^2 <= n*(n + (r-1)*M')  with
       M' = max off-diagonal |eta_{b-b'}| over B: informative or vacuous at these scales?
       Also the spectral form  sum_B |eta_b|^2 <= n * lambda_max(Gram).
 (iii) bootstrap fixed point M <= f(M), f(V)^2 = n^2/r + n*M'(V): where does it sit
       vs sqrt(n log(p/n)) vs trivial n?
"""
import numpy as np
from math import log, sqrt, isqrt

def is_prime(x):
    if x < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % q == 0: return x == q
    d, s = x-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        v = pow(a, d, x)
        if v in (1, x-1): continue
        for _ in range(s-1):
            v = v*v % x
            if v == x-1: break
        else:
            return False
    return True

def factorize(x):
    fs = {}
    d = 2
    while d*d <= x:
        while x % d == 0:
            fs[d] = fs.get(d,0)+1; x //= d
        d += 1
    if x > 1: fs[x] = fs.get(x,0)+1
    return fs

def primitive_root(p):
    fs = factorize(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fs):
            return g
    raise RuntimeError

class Dlog:
    """BSGS discrete log base g mod p."""
    def __init__(self, g, p):
        self.p = p; self.g = g
        self.t = isqrt(p-1) + 1
        self.baby = {}
        cur = 1
        for j in range(self.t):
            self.baby.setdefault(cur, j)
            cur = cur * g % p
        self.giant = pow(pow(g, self.t, p), p-2, p)  # g^{-t}
    def __call__(self, y):
        p = self.p
        cur = y % p
        for i in range(self.t + 1):
            j = self.baby.get(cur)
            if j is not None:
                return (i * self.t + j) % (p-1)
            cur = cur * self.giant % p
        raise ValueError(f"dlog fail {y}")

def run(n, beta=4.0, rs=(4, 8, 16, 32)):
    # smallest prime p >= n^beta with n | p-1
    p = int(round(n**beta))
    p += (1 - p) % n
    while not is_prime(p): p += n
    m = (p-1)//n
    g = primitive_root(p)
    # mu_n = <g^m>
    gm = pow(g, m, p)
    mu = np.empty(n, dtype=np.int64)
    cur = 1
    for i in range(n):
        mu[i] = cur; cur = cur * gm % p
    assert cur == 1 and (p-1) in mu  # -1 in mu_n
    ind = np.zeros(p)
    ind[mu] = 1.0
    eta_c = np.fft.fft(ind)          # eta'_b = sum_x e^{-2pi i b x/p} = eta_{-b} = eta_b (real)
    assert np.abs(eta_c.imag).max() < 1e-6 * n
    eta = eta_c.real                 # eta[b] for all b in Z_p (eta[0] = n)
    abseta = np.abs(eta)
    M = abseta[1:].max()
    target = sqrt(n*log(p/n))
    dlog = Dlog(g, p)
    coset = lambda y: dlog(y) % m
    # Parseval typical level over nonzero b
    rms = sqrt((abseta[1:]**2).mean())
    print(f"\n===== n={n}  p={p}  m={m}  beta={log(p)/log(n):.3f} =====")
    print(f"M = {M:.4f}   sqrt(n log(p/n)) = {target:.4f}   C = M/target = {M/target:.4f}"
          f"   trivial n = {n}   RMS|eta| (b!=0) = {rms:.4f}  (sqrt(n)={sqrt(n):.3f})")
    # ---- level-set counts (in cosets) at various levels
    # one value per coset: sample reps g^i
    reps = np.empty(m, dtype=np.int64)
    cur = 1
    for i in range(m):
        reps[i] = cur; cur = cur * g % p
    ceta = abseta[reps]              # |eta| per coset
    order = np.argsort(-ceta)
    for frac in (1.0, 0.9, 0.7, 0.5):
        T = frac*M
        cnt = int((ceta >= T - 1e-9).sum())
        markov = (p*n - n*n)/p / (T*T) * m  # E|eta|^2 ~ n(p-n)/p per b; count over m cosets
        print(f"  level T={frac:.1f}M={T:9.3f}: #cosets>=T = {cnt:6d}   Parseval/Markov coset count ~ {markov:10.1f}")
    Ttar = target
    cnt_tar = int((ceta >= Ttar).sum())
    print(f"  level T=target={Ttar:9.3f}: #cosets>=T = {cnt_tar}")
    # ---- extremal sets
    for r in rs:
        if r > m: continue
        B = reps[order[:r]]          # one rep per top-r coset
        V = ceta[order[r-1]]         # min large value in B
        etaB = eta[B]
        # Gram matrix G[b,b'] = eta[b-b']  (real symmetric)
        D = (B[:,None] - B[None,:]) % p
        G = eta[D]
        offabs = np.abs(G[~np.eye(r,dtype=bool)])
        Mp_max, Mp_mean, Mp_med = offabs.max(), offabs.mean(), np.median(offabs)
        ev = np.linalg.eigvalsh(G)
        lam_max = ev[-1]
        rowsum = np.abs(G).sum(axis=1).max()
        sumsq = float((etaB**2).sum())
        # (i) additive structure: distinct cosets among differences
        diffs = D[~np.eye(r,dtype=bool)]
        dc = {coset(int(y)) for y in diffs}
        # self-referential: are the differences themselves large-value cosets?
        # rank of |eta| on differences vs global coset distribution
        quant = (ceta[None,:] <= np.abs(eta[diffs])[:,None]).mean(axis=1)  # percentile of each diff value
        # (ii) HM inequality:  r V^2 <= n(n + (r-1) M')
        lhs = r*V*V
        rhs_max = n*(n + (r-1)*Mp_max)
        rhs_spec = n*lam_max
        # informativeness ratio: V^2/(n*M') must exceed 1 for the count bound to bite
        info = V*V/(n*Mp_max)
        info_mean = V*V/(n*Mp_mean)
        # (iii) fixed point of V = sqrt(n^2/r + n*M') with M' = measured
        fp = sqrt(n*n/r + n*Mp_max)
        fp_mean = sqrt(n*n/r + n*Mp_mean)
        print(f"  r={r:3d}: V={V:9.3f}  |B-B| cosets={len(dc):5d}/{r*(r-1):5d}"
              f"  off|eta|: max={Mp_max:9.3f} mean={Mp_mean:8.3f} med={Mp_med:8.3f}"
              f"  (sqrt n={sqrt(n):.2f}, log(p/n)={log(p/n):.2f})")
        print(f"         diff-value percentile: mean={quant.mean():.3f} med={np.median(quant):.3f}"
              f"  (0.5 = typical; >0.5 = extremal diffs are LARGE-|eta|)")
        print(f"         Gram: lam_max={lam_max:10.3f} maxrowsum={rowsum:10.3f}  sum|eta_b|^2={sumsq:12.3f}"
              f"  spectral bound n*lam_max={rhs_spec:14.3f} (slack x{rhs_spec/sumsq:7.2f})")
        print(f"         HM: rV^2={lhs:12.1f} <= n(n+(r-1)M')={rhs_max:14.1f} (slack x{rhs_max/lhs:8.2f})"
              f"  INFO ratio V^2/(nM')={info:.4f} (mean-M': {info_mean:.4f})  {'INFORMATIVE' if info>1 else 'VACUOUS'}")
        print(f"         bootstrap fixed pt f(V)=sqrt(n^2/r+nM'): {fp:9.3f} (mean-M': {fp_mean:9.3f})"
              f"   vs target {target:8.3f}  vs trivial n={n}")
        # eigenvalue spectrum summary
        print(f"         Gram spectrum (top 5 / bottom 2): {np.round(ev[::-1][:5],2)} ... {np.round(ev[:2],2)}")
    # what M' would HM need at the target level to certify count < 1 at V slightly above target?
    # r(V^2 - nM') <= n^2 - nM'  => count<1 iff V^2 > n^2. Show the needed off-diag for info at target:
    print(f"  [analysis] HM informative at V=target needs M' < V^2/n = log(p/n) = {log(p/n):.3f}"
          f"   ; typical |eta| ~ sqrt(n) = {sqrt(n):.3f}  ; measured min over ALL nonzero cosets = {ceta.min():.4f}")
    print(f"  [analysis] HM certifies EMPTY level set only when V > n (trivial): V^2>n^2 from r<1 condition.")

if __name__ == "__main__":
    for n in (8, 16, 32, 64):
        run(n)
