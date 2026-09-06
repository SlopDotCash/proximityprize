#!/usr/bin/env python3
"""
hdinf_continuum_lp.py — the m -> infinity limit of the order-d hidden-derivative
interpolation threshold (counting rank bound), with the cap treated as a FREE REGION,
reduced exactly to a two-dimensional occupancy problem.

Reduction (exact in the scaling m -> infinity, m/w -> 0; derivation in the KB note
deltastar-hdinf-cap-variational-2026-09-06.md): scale bs = m*c, blocks
(g1, g2) = m*(gamma1, gamma2).  Every functional depends on a cap point c in
R_{>=0}^d only through (S, J) = (sum_j c_j, sum_j j*c_j):

  dim/(w m^{d+2})    -> IQ = integral o(S,J) (beta - S)^2 / 2        (beta = A/w)
  cols(g1,g2)/m^d    -> C(gamma1, gamma2) = integral o(S,J) [S <= gamma1] [J + gamma2 in [0,1)]
  rows(g1,g2)/m^d    -> R_d(gamma1, gamma2) = integral_{sigma + gamma2 in [0,1)} mu_d(gamma1, sigma)
                        with mu_d = pushforward of Lebesgue on R_{>=0}^{d+1} under
                        (sum eta + etaE, sum_j j eta_j + (d+1) etaE)
  rank/m^{d+2}       -> IR = integral min(R_d, C) dgamma1 dgamma2
  threshold          : least beta with  rho * IQ > IR  for some occupancy
                       0 <= o(S,J) <= nu_d(S,J),
where nu_d = pushforward of Lebesgue on R_{>=0}^d under (sum c, sum j c).  Both nu_d and
mu_d are computed by ray convolutions (direction (1, j), density dt), one per derivative
order — COST LINEAR IN d, so the d -> infinity limit is directly computable.

rho*IQ - IR is convex in o (IR is an inf of linear functionals), so optima are bang-bang;
solved by iterated marginal pricing: include cell (S,J) iff its dimension value
rho (beta-S)^2/2 exceeds its rank price integral over cols-binding blocks it feeds.

delta = 1 - rho*beta; Johnson beta = 1/sqrt(rho); capacity beta = 1 (any rate).
The discretization uses midpoint cell centers and windows of exact scaled length 1; the
remaining bias is removed by Richardson extrapolation over the h-ladder.

Validation: d=1 must reproduce hd1_continuum_limit.py (0.97566 at rate 1/2 etc.); the
counting bound equals the exact rank at d=1.
"""
import argparse
import math
import sys

import numpy as np


class Grid:
    """Cell centers at (i+1/2)h.  S axis also serves gamma1; J axis serves J and sigma."""

    def __init__(self, h, smax, jmax, g2min):
        self.h = h
        self.ns = int(round(smax / h))
        self.nj = int(round((jmax + 1.0) / h))  # sigma reaches 1 + |g2min|
        self.n2 = int(round((1.0 - g2min) / h))
        self.g2min = g2min
        self.S = (np.arange(self.ns) + 0.5) * h
        self.J = (np.arange(self.nj) + 0.5) * h
        self.G2 = g2min + (np.arange(self.n2) + 0.5) * h


def ray_convolve(dens, j):
    """Convolve with the ray {t*(1, j) : t >= 0}, density dt (unit speed in the count
    coordinate).  Recurrence: out[s, u] = h * dens[s, u] + out[s-1, u-j]  (h from dt)."""
    ns, nj = dens.shape
    out = np.empty_like(dens)
    out[0, :] = dens[0, :]
    for s in range(1, ns):
        out[s, :] = dens[s, :]
        if j < nj:
            out[s, j:] += out[s - 1, : nj - j]
        # j >= nj: shifted term falls off the grid
    return out


def pushforward(weights, grid):
    """Density of the image of Lebesgue on R_{>=0}^len(weights) under
    (sum t_i, sum weights_i t_i), on the (S, J) grid.  Each ray multiplies by h
    (the dt measure), the origin delta carries 1/h^2."""
    dens = np.zeros((grid.ns, grid.nj))
    dens[0, 0] = 1.0 / grid.h / grid.h
    for j in weights:
        dens = ray_convolve(dens, j) * grid.h
    return dens


def window_sum(csum, lo_idx, W):
    """csum: cumulative over axis 1 (inclusive).  Sum of W cells starting at lo_idx."""
    n = csum.shape[1]
    ilo = max(lo_idx, 0)
    ihi = min(lo_idx + W, n)
    if ihi <= ilo:
        return np.zeros(csum.shape[0])
    upper = csum[:, ihi - 1]
    lower = csum[:, ilo - 1] if ilo >= 1 else np.zeros(csum.shape[0])
    return upper - lower


def _win_start(lo, h):
    """First cell index whose center (i+1/2)h >= lo."""
    return int(math.ceil(lo / h - 0.5 - 1e-12))


def row_density(d, grid):
    mu = pushforward(list(range(1, d + 1)) + [d + 1], grid)
    h = grid.h
    csum = np.cumsum(mu, axis=1) * h
    W = int(round(1.0 / h))
    R = np.empty((grid.ns, grid.n2))
    for t2 in range(grid.n2):
        g2 = grid.G2[t2]
        R[:, t2] = window_sum(csum, _win_start(-g2, h), W)
    return R


def cols_from_occupancy(o, grid):
    h = grid.h
    ps = np.cumsum(o, axis=0) * h  # prefix over S (S <= gamma1, midpoint: index match)
    csum = np.cumsum(ps, axis=1) * h
    W = int(round(1.0 / h))
    C = np.empty((grid.ns, grid.n2))
    for t2 in range(grid.n2):
        g2 = grid.G2[t2]
        C[:, t2] = window_sum(csum, _win_start(-g2, h), W)
    return C


def price(binding, grid):
    """price(S, J) = integral over {gamma1 >= S} x {gamma2 in [-J, 1-J)} of binding."""
    h = grid.h
    sfx = np.cumsum(binding[::-1, :], axis=0)[::-1, :] * h
    csum = np.cumsum(sfx, axis=1) * h
    W = int(round(1.0 / h))
    P = np.empty((grid.ns, grid.nj))
    for tj in range(grid.nj):
        Jv = grid.J[tj]
        lo_idx = _win_start(-Jv - grid.g2min, h)
        P[:, tj] = window_sum(csum, lo_idx, W)
    return P


MARGIN_TOL = 1e-10  # a positive margin below this is a numerical artifact, not feasibility


def feasible(rho, beta, grid, nu, R, iters=40, o0=None):
    """max_o [rho IQ - IR] > 0?  Returns (best margin, best occupancy).
    Cap mass is restricted to J <= -g2min so every column window lies on-grid
    (mass beyond leaks rank cost off the gamma2 boundary and fakes feasibility)."""
    h = grid.h
    nu = nu * (grid.J[None, :] <= -grid.g2min - h / 2)
    val = rho * np.maximum(beta - grid.S, 0.0)[:, None] ** 2 / 2.0
    val = np.broadcast_to(val, nu.shape)
    # columns only exist in blocks with gamma1 <= beta (weighted-degree cap)
    live = (grid.S <= beta)[:, None]

    def eval_margin(occ):
        C = cols_from_occupancy(occ, grid) * live
        return (occ * val).sum() * h * h - np.minimum(R, C).sum() * h * h, C

    if o0 is not None and o0.shape != nu.shape:
        o0 = None
    if o0 is None:
        best0, occ = -np.inf, None
        for frac in (0.12, 0.18, 0.22, 0.27, 0.33, 0.45):
            for jcap in (0.75, 1.5, 3.0, 6.0, None):
                cand = nu * (grid.S[:, None] <= frac * beta)
                if jcap is not None:
                    cand = cand * (grid.J[None, :] <= jcap)
                mg, _ = eval_margin(cand)
                if mg > best0:
                    best0, occ = mg, cand
    else:
        occ = np.minimum(o0, nu)
    best, best_o = -np.inf, occ
    for _ in range(iters):
        mg, C = eval_margin(occ)
        if mg > best:
            best, best_o = mg, occ
        binding = ((C < R) & live).astype(np.float64)
        pr = price(binding, grid)
        target = nu * (val > pr)
        if np.array_equal(target, occ):
            break
        occ = target if best < mg + 1e-15 else 0.5 * occ + 0.5 * target
    mg, _ = eval_margin(occ)
    if mg > best:
        best, best_o = mg, occ
    return best, best_o


def beta_star_at_h(rho, d, h, jmax, blo, bhi, bits=20, o_seed=None):
    grid = Grid(h, bhi + 2 * h, jmax, -jmax)
    nu = pushforward(list(range(1, d + 1)), grid)
    R = row_density(d, grid)
    o_warm = [None]

    def ok(beta):
        m, o = feasible(rho, beta, grid, nu, R, o0=None)
        if o_seed is not None:
            m2, o2 = feasible(rho, beta, grid, nu, R, o0=o_seed)
            if m2 > m:
                m, o = m2, o2
        if m > MARGIN_TOL:
            o_warm[0] = o
        return m > MARGIN_TOL

    lo, hi = blo, bhi
    if not ok(hi):
        return None, None
    for _ in range(bits):
        mid = (lo + hi) / 2
        if ok(mid):
            hi = mid
        else:
            lo = mid
    return hi, o_warm[0]


def beta_star(rho, d, jmax=None, hs=(0.02, 0.01, 0.005), blo=1.0, bhi=None,
              verbose=False, o_seed=None):
    """h-ladder plus Richardson extrapolation (bias is O(h)).  Returns
    (extrapolated beta, ladder, final occupancy at the finest h)."""
    bhi = bhi or 1.0 / math.sqrt(rho) + 0.02
    jmax = jmax or max(4.0, min(1.5 * d, 12.0))
    vals = []
    o_dict = {}
    for h in hs:
        seed = o_seed.get(h) if o_seed is not None else None
        b, o = beta_star_at_h(rho, d, h, jmax, blo, bhi, o_seed=seed)
        if b is None:
            return None, None, None
        vals.append((h, b))
        if o is not None:
            o_dict[h] = o
        if verbose:
            print(f"    h={h}: beta={b:.6f}", flush=True)
    (h1, b1), (h2, b2) = vals[-2], vals[-1]
    b_extrap = (h1 * b2 - h2 * b1) / (h1 - h2)
    return b_extrap, vals, o_dict


def validate():
    print("== d=1 continuum: reproduce hd1_continuum_limit (ratio = beta*sqrt(rho))")
    tgt = {0.5: 0.97566, 0.25: 0.93759, 0.125: 0.90244}
    fails = 0
    for rho, ref in tgt.items():
        b, vals, _ = beta_star(rho, 1, jmax=4.0, verbose=True)
        ratio = b * math.sqrt(rho)
        ok = abs(ratio - ref) < 0.0015
        fails += 0 if ok else 1
        print(f"  rho={rho}: beta*={b:.5f} ratio={ratio:.5f} (ref {ref}) "
              f"delta={1 - rho * b:.5f} {'OK' if ok else 'MISMATCH'}", flush=True)
    print("VALIDATE", "PASS" if fails == 0 else "FAIL")
    return fails


def sweep(rho, ds_list, hs=(0.02, 0.01, 0.005), jmax=None):
    print(f"== continuum d-sweep at rho={rho} (counting bound, free 2D occupancy, "
          f"Richardson over h={hs})")
    print(f"   Johnson ratio=1.0000, beta={1 / math.sqrt(rho):.4f}; capacity beta=1 "
          f"(delta={1 - rho:.4f})")
    out = []
    seed = None
    for d in ds_list:
        b, vals, o_last = beta_star(rho, d, hs=hs, jmax=jmax, o_seed=seed)
        if b is None:
            print(f"  d={d}: infeasible", flush=True)
            continue
        ratio = b * math.sqrt(rho)
        ladder = " ".join(f"{bb:.5f}" for _, bb in vals)
        print(f"  d={d:>3}: beta*={b:.5f} ratio={ratio:.5f} delta={1 - rho * b:.5f} "
              f"[ladder {ladder}]", flush=True)
        out.append((d, b))
        if o_last:
            seed = o_last
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["validate", "solve", "sweep"])
    ap.add_argument("--rho", type=float, default=0.5)
    ap.add_argument("--d", type=int, default=4)
    ap.add_argument("--ds", type=str, default="1,2,3,4,6,8,12,16")
    ap.add_argument("--jmax", type=float, default=None)
    ap.add_argument("--hs", type=str, default="0.02,0.01,0.005")
    args = ap.parse_args()
    hs = tuple(float(x) for x in args.hs.split(","))
    if args.cmd == "validate":
        sys.exit(1 if validate() else 0)
    elif args.cmd == "solve":
        b, vals, _ = beta_star(args.rho, args.d, hs=hs, jmax=args.jmax, verbose=True)
        print(f"beta*={b} ratio={b * math.sqrt(args.rho):.6f} "
              f"delta={1 - args.rho * b:.6f}")
    else:
        sweep(args.rho, [int(x) for x in args.ds.split(",")], hs=hs, jmax=args.jmax)
