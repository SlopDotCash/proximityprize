#!/usr/bin/env python3
# G217 companion: m-scaling of phase coherence + argument histogram.
#
# The main probe (g217_phase_alignment_probe.py) shows R_coh -> 1/sqrt(#modes) at the
# best-populated cell (p=257,n=16: 15 modes, R_coh=0.2587 vs rand 0.2582). Small-m cells
# show artifactual R_coh=1 (too few shells to cancel). This companion isolates the
# m-scaling on a FIXED n=16 with GROWING m (more quotient characters = the true test of
# whether phase alignment survives), and histograms the phase argument
#    phi_r(chi) = arg( What(chi) * conj(Rhat(chi)) )   in [-pi, pi]
# to test half-plane concentration directly: H_align predicts phi clustered near 0
# (Re>0); H_random predicts phi ~ uniform on the circle (no half-plane bias), so the
# aligned-mass fraction w+ -> 1/2 and R_coh -> 1/sqrt(N).
#
# n=16 fixed; sweep primes p = 16*k+1 prime, ascending, so m=(p-1)/16 grows.

import itertools, math, cmath
from collections import Counter
from sympy import primitive_root as pr, isprime

def build_group(p, n):
    g = pr(p); m = (p - 1) // n
    G = sorted({pow(g, (m * k) % (p - 1), p) for k in range(n)})
    return set(G), g, m

def W_G_exact(p, G):
    Gs = set(G); W = [0]*p
    for t in range(p):
        W[t] = sum(1 for y in G if (2*y - t) % p in Gs)
    return W

def R_r_exact(p, G, r):
    Gl = sorted(G)
    sA = Counter(sum(A) % p for A in itertools.combinations(Gl, r))
    sB = Counter(sum(B) % p for B in itertools.combinations(Gl, r-1))
    R = [0]*p
    for sa, ca in sA.items():
        for sb, cb in sB.items():
            R[(sa - sb) % p] += ca*cb
    return R

def dlog_table(p, g):
    d = [0]*p; v = 1
    for e in range(p-1):
        d[v] = e; v = (v*g) % p
    return d

def analyze(p, n, r):
    G, g, m = build_group(p, n)
    W = W_G_exact(p, G); R = R_r_exact(p, G, r)
    p1 = p-1; dlog = dlog_table(p, g)
    Mr = math.comb(n, r)*math.comb(n, r-1)
    A_exact = p*sum(W[t]*R[t] for t in range(p)) - n*n*Mr
    phis = []; svals = []
    for j in range(m):
        a = (n*j) % p1
        if a == 0: continue
        What = 0j; Rhat = 0j
        for t in range(1, p):
            ph = cmath.exp(-2j*math.pi*a*dlog[t]/p1)
            What += W[t]*ph; Rhat += R[t]*ph
        prod = What*Rhat.conjugate()
        phis.append(math.atan2(prod.imag, prod.real))
        svals.append(prod.real)
    N = len(svals)
    L1 = sum(abs(s) for s in svals); sig = sum(svals)
    R_coh = abs(sig)/L1 if L1 else float('nan')
    w_plus = sum(s for s in svals if s > 0)/L1 if L1 else float('nan')
    # half-plane concentration: fraction of L1-mass with |phi|<pi/2 (Re>0)
    inhalf = sum(abs(s) for s in svals if s > 0)  # s>0 == Re>0
    frac_half = inhalf/L1 if L1 else float('nan')
    rand = 1.0/math.sqrt(N) if N else float('nan')
    return dict(p=p, n=n, r=r, m=m, N=N, A=A_exact, R_coh=R_coh,
                w_plus=w_plus, frac_half=frac_half, rand=rand)

def main():
    n = 16
    primes = [p for p in range(17, 1200) if isprime(p) and (p-1) % n == 0]
    print(f"n={n}, growing m. Half-plane concentration frac_half should ->1 for H_align, ->1/2 for H_random.")
    print(f"{'p':>5} {'m':>4} {'N':>4} {'R_coh':>8} {'rand':>8} {'R/rand':>7} {'w+':>7} {'frac_half':>9}")
    for p in primes:
        r = 5
        try:
            x = analyze(p, n, r)
        except Exception as e:
            print(f"skip {p}: {e}"); continue
        ratio = x['R_coh']/x['rand'] if x['rand'] else float('nan')
        print(f"{x['p']:>5} {x['m']:>4} {x['N']:>4} {x['R_coh']:>8.4f} {x['rand']:>8.4f} "
              f"{ratio:>7.3f} {x['w_plus']:>7.4f} {x['frac_half']:>9.4f}")

if __name__ == "__main__":
    main()
