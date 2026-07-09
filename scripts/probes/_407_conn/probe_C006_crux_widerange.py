#!/usr/bin/env python3
"""
C006 CRUX, corrected + wide log-m range.

The decisive question: is the open input REALLY "a single MGF with sigma^2=O(n)" (=> REDUCED,
genuinely off the all-moments BGK wall), or does controlling that MGF at the lambda the
maximal inequality needs amount to controlling all high moments (=> welds to BGK => OPEN)?

CORRECTION of the previous probe: the Chernoff optimum for a TRUE sigma^2 ~ n proxy is
   lambda* = sqrt(2 log m / sigma^2) ~ sqrt(2 log m / n),
which GROWS with log m (previous probe wrongly used lambda*=2logm/B which SHRINKS).
We probe the empirical MGF at this GROWING lambda* and extract
   sigma2_eff(m) = 2 log Mhat(lambda*) / lambda*^2.
If C006's insight is right, sigma2_eff/n stays O(1) as m -> infinity.
If it grows like log m (or worse), the single MGF is NOT a weaker input.

We push n THIN and m LARGE (up to ~ a few thousand) so log m spans a real range.
Compare ALWAYS against a RANDOM-unimodular Salem-Zygmund control (the idealized model where
the MGF IS genuinely sigma^2 = n/2 bounded): if the real Gauss sequence tracks the control,
the single-MGF reduction is honest; if it diverges upward, it welds to BGK.
"""
import cmath, math
import statistics as st

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; fac = []; t = phi; d = 2
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

def gauss_periods(p, n, g):
    m = (p-1)//n
    gen = pow(g, m, p)
    mu = []; x = 1
    for _ in range(n):
        mu.append(x); x = (x*gen) % p
    e = [cmath.exp(2j*math.pi*k/p) for k in range(p)]
    etas = []
    bc = 1
    for c in range(m):
        s = 0j
        for x in mu:
            s += e[(bc*x) % p]
        etas.append(s)
        bc = (bc*g) % p
    return etas, m

def mgf_sigma2_at_lambda(etas, lam, ndirs=24):
    """worst-direction sigma2_eff = 2 log Mhat(lam)/lam^2, Mhat=(1/m)sum exp(lam Re(zbar eta))."""
    worst = 0.0
    for t in range(ndirs):
        zeta = cmath.exp(2j*math.pi*t/ndirs)
        X = [(zeta.conjugate()*e).real for e in etas]
        mu = st.mean(X)
        Xc = [x-mu for x in X]
        Mhat = st.mean(math.exp(lam*x) for x in Xc)
        if Mhat > 1 and lam > 0:
            worst = max(worst, 2*math.log(Mhat)/(lam*lam))
    return worst

def main():
    print("# C006 CRUX wide-range:  lambda* = sqrt(2 log m / n)  (GROWS with log m)")
    print("# sigma2_eff(m) = worst-dir 2 log Mhat(lambda*)/lambda*^2  ;  bounded/n => REDUCED, grows => OPEN(BGK)")
    print()
    print("## REAL Gauss-period sequence (thin n, m as large as affordable)")
    print(f"{'p':>9} {'n':>4} {'m':>6} {'logm':>6} {'beta':>5} | {'B':>8} {'B/sqrt(2nlogm)':>14} "
          f"| {'lam*':>6} {'sig2eff/n':>10}")
    rows = {}
    for n in [8, 16, 32, 64]:
        # collect several primes, then keep the few with the LARGEST m (largest log m) under cost cap
        cands = []
        p = n
        while p < 250000:
            p += 1
            if p % n != 1 or not is_prime(p): continue
            m = (p-1)//n
            if m < 32: continue
            cands.append((p, m))
        # cost ~ p (building e[] and m periods of n terms = (p-1) work). cap total p.
        cands = [c for c in cands if c[0] < 200000]
        # pick a geometric spread in m
        cands.sort(key=lambda c: c[1])
        if not cands: continue
        pick = []
        if len(cands) <= 6:
            pick = cands
        else:
            idxs = [int(round(i*(len(cands)-1)/5)) for i in range(6)]
            pick = [cands[i] for i in sorted(set(idxs))]
        for (p, m) in pick:
            g = primitive_root(p)
            etas, m = gauss_periods(p, n, g)
            B = max(abs(e) for e in etas)
            logm = math.log(m)
            lam = math.sqrt(2*logm/n)
            s2 = mgf_sigma2_at_lambda(etas, lam)
            beta = math.log(p)/math.log(n)
            print(f"{p:>9} {n:>4} {m:>6} {logm:6.2f} {beta:5.2f} | {B:8.3f} {B/math.sqrt(2*n*logm):14.4f} "
                  f"| {lam:6.3f} {s2/n:10.4f}")
            rows.setdefault(n, []).append((logm, s2/n, B/math.sqrt(2*n*logm)))

    print()
    print("## RANDOM-unimodular SZ control (idealized: MGF truly sigma^2-bounded). Same lambda*.")
    print(f"{'m':>7} {'n':>4} {'logm':>6} | {'||P||inf/sqrt(2m logm)':>22} | {'lam*':>6} {'sig2eff/n':>10}")
    import random
    random.seed(7)
    ctrl = {}
    for n in [8, 16, 32, 64]:
        for m in [256, 1024, 4096, 16384]:
            a = [cmath.exp(2j*math.pi*random.random()) for _ in range(m-1)]
            om = cmath.exp(-2j*math.pi/m)
            p = n*m+1
            etas = []
            # P(c)=sum a_j om^{jc}; eta_c surrogate = (sqrt(p) P(c) - 1)/m, |eta|~ (sqrt(p)/m)|P|
            # but for MGF/scaling we only need the eta_c shape; use eta_c = (sqrt(p)/m) Re/Im of P
            Pabs = []
            for c in range(m):
                # fast: P(c) via direct sum (m up to 16384 * (m-1) terms is too slow); use FFT
                pass
            # use numpy FFT for speed
            import numpy as np
            aj = np.zeros(m, dtype=complex)
            for j in range(1, m):
                aj[j] = a[j-1]
            P = np.fft.fft(aj)  # P[c] = sum_j aj[j] exp(-2pi i jc/m) = sum a_j om^{jc}
            etas = (math.sqrt(p)*P - 1)/m
            B = float(np.max(np.abs(etas)))
            Pinf = float(np.max(np.abs(P)))
            logm = math.log(m)
            lam = math.sqrt(2*logm/n)
            # MGF over directions
            worst = 0.0
            for t in range(24):
                zeta = cmath.exp(2j*math.pi*t/24)
                X = (np.conj(zeta)*etas).real
                Xc = X - X.mean()
                Mhat = float(np.mean(np.exp(lam*Xc)))
                if Mhat > 1 and lam > 0:
                    worst = max(worst, 2*math.log(Mhat)/(lam*lam))
            print(f"{m:>7} {n:>4} {logm:6.2f} | {Pinf/math.sqrt(2*m*logm):22.4f} | {lam:6.3f} {worst/n:10.4f}")
            ctrl.setdefault(n, []).append((logm, worst/n))

    print()
    print("## slope of sigma2_eff/n vs log m  (REAL vs CONTROL); ~0 => bounded MGF => REDUCED")
    def slope(pts):
        pts = sorted(pts)
        xs=[x for x,_ in pts]; ys=[y for _,y in pts]
        if len(pts)<2: return float('nan')
        xb=sum(xs)/len(xs); yb=sum(ys)/len(ys)
        num=sum((x-xb)*(y-yb) for x,y in pts); den=sum((x-xb)**2 for x in xs)
        return num/den if den else float('nan')
    for n in sorted(set(list(rows)+list(ctrl))):
        rs = rows.get(n,[]); cs = ctrl.get(n,[])
        rsl = slope([(x,y) for x,y,_ in rs]) if rs else float('nan')
        csl = slope(cs) if cs else float('nan')
        rrange = (min(y for _,y,_ in rs), max(y for _,y,_ in rs)) if rs else (0,0)
        print(f" n={n:>3}: REAL slope={rsl:+.4f} range[{rrange[0]:.3f},{rrange[1]:.3f}] | CONTROL slope={csl:+.4f}")

if __name__ == "__main__":
    main()
