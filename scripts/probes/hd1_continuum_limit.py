#!/usr/bin/env python3
"""
hd1_continuum_limit.py — the exact m -> infinity limit of the d = 1 hidden-derivative
interpolation threshold (list-decoding setting), obtained by passing the exact block-rank
formula of hd1_interpolation_threshold.ld_rank_formula and the dimension count to scaled
variables x = i/m, y = j/m, sigma = s/m, beta = B/m = A/(k-1):

    rank/m^3  -> IR(beta, sigma) = int_0^1 dx int_0^{min(beta, x+sigma)} dy
                                     min( min(1-x, y),  min(x, y) - max(0, y - sigma) )
    dim/(w m^3) -> IQ(beta, sigma) = int_0^beta min(y, sigma) (beta - y) dy

The threshold beta*(rho, sigma) solves rho * IQ = IR (rho = w/n); the optimal sigma minimises
A/sqrt(n w) = beta* sqrt(rho).  Output at the four prize rates (matches the discrete scans of
the note to the fourth digit):

    rho=1/2 : sigma*=0.310, A/sqrt(nw)=0.97566, delta=0.31010  (Johnson 0.29289)
    rho=1/4 : sigma*=0.455, 0.93759, delta=0.53121             (Johnson 0.50000)
    rho=1/8 : sigma*=0.553, 0.90244, delta=0.68094             (Johnson 0.64645)
    rho=1/16: sigma*=0.661, 0.87243, delta=0.78189             (Johnson 0.75000)
"""
# rank/m^3 -> IR(beta,sigma) = int_0^1 dx int_0^{min(beta, x+sigma)} dy  min( min(1-x, y), min(x,y) - max(0, y-sigma) )
# dim/(w m^3) -> IQ(beta,sigma) = int_0^beta min(y,sigma) (beta - y) dy
# threshold: rho * IQ = IR  (rho = w/n).  Solve for beta, minimize over sigma.  Report A/sqrt(n w) = beta*sqrt(rho).
import math
from scipy import integrate, optimize
def IR(beta, sigma):
    def inner(x):
        ymax = min(beta, x + sigma)
        if ymax <= 0: return 0.0
        f = lambda y: min(min(1 - x, y), min(x, y) - max(0.0, y - sigma))
        # piecewise-linear integrand: integrate with breakpoints
        pts = sorted(set([0.0, ymax] + [p for p in [x, 1 - x, sigma, x + sigma, 1 - x + 0] if 0 < p < ymax]))
        tot = 0.0
        for a, b in zip(pts[:-1], pts[1:]):
            tot += integrate.quad(f, a, b)[0]
        return tot
    pts = sorted(set([0.0, 1.0] + [p for p in [0.5, sigma, 1 - sigma, beta, beta - sigma, 1 - beta] if 0 < p < 1]))
    tot = 0.0
    for a, b in zip(pts[:-1], pts[1:]):
        tot += integrate.quad(inner, a, b, limit=200)[0]
    return tot
def IQ(beta, sigma):
    return integrate.quad(lambda y: min(y, sigma) * (beta - y), 0, beta)[0]
def beta_star(rho, sigma):
    g = lambda b: rho * IQ(b, sigma) - IR(b, sigma)
    return optimize.brentq(g, 1.0, 4.0)
for rho in [0.5, 0.25, 0.125, 0.0625]:
    best = None
    for sigma in [0.2, 0.25, 0.28, 0.3, 0.32, 0.35, 0.4, 0.5, 0.6, 0.8, 1.0]:
        b = beta_star(rho, sigma)
        r = b * math.sqrt(rho)
        if best is None or r < best[1]: best = (sigma, r, b)
    sig = optimize.minimize_scalar(lambda sg: beta_star(rho, sg) * math.sqrt(rho), bounds=(0.05, 2.0), method='bounded', options={'xatol':1e-4})
    r = sig.fun; sg = sig.x
    print(f"rho={rho}: grid best sigma={best[0]} ratio={best[1]:.6f}; optimized sigma={sg:.4f} ratio={r:.6f} -> delta={1 - r*math.sqrt(rho):.6f} (Johnson {1-math.sqrt(rho):.6f}, capacity {1-rho})", flush=True)
