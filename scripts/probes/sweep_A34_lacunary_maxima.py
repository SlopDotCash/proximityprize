#!/usr/bin/env python3
"""
sweep_A34_lacunary_maxima.py  -- Actionable A34
===============================================

Lacunary cyclotomic resultant maxima for the KKH26 collision object, s in {8,...,256}.

CONTEXT (reconstructed from KKH26SumsOfRootsOfUnity.lean + SharpResultantBound.lean,
all IN-TREE PROVEN, axiom-clean):
  s = 2^m  (smooth subgroup order in the KKH26 counterexample),
  h = s/2 = 2^{m-1} = deg Phi_s = phi(s).
  Collision polynomial  R = P_d1 - P_d2,  P_d = sum over T of X^i minus sum over U-minus-T of X^i,  |U| = r.
  On the window [0,h):  deg R < h,  ||R||_1 <= 2r <= 2h = s,  ||R||_2^2 <= 4r <= 4h = 2s.
  Collision resultant N = Res_Z(R, Phi_s).  KKH26 needs  p doesn't divide N  <=  |N| < p.

THREE IN-TREE BOUNDS on |N|:
  (A) house / l1   (natAbs_resultant_cyclotomic_le):   |N| <= ||R||_1^h <= (2r)^h <= s^h
  (B) Parseval+AMGM, WORST r=h (cyclotomicLandauSqBound): |N|^2 <= (4h)^h * 2^{h-1}
  (B') Parseval+AMGM, FIXED r  (same proof, ||R||_2^2<=4r): |N|^2 <= (4r)^h  =>  |N| <= (4r)^{h/2}
       [the AM-GM step is  prod_j |R(zeta^odd)|^2 <= ( (sum_j ...)/h )^h = (h*||R||_2^2 / h)^h
        = (||R||_2^2)^h <= (4r)^h ; the in-tree file fixes r=h, this is the general-r form.]

PRIZE CAP: q < 2^256.  Row "s" OPEN UNCONDITIONALLY (no Thorner-Zaman) at degree-r iff the
threshold |N|-bound < 2^256: then some prime p in (bound, 2^256) works directly.
"""

import itertools, math, cmath, random
P = lambda *a: print(*a, flush=True)
CAP = 256.0

# ---------------------------------------------------------------------------
P("="*94)
P("Part 1: WORST-CASE (r=h) thresholds per route vs prize cap 2^256")
P("="*94)
P(f"{'m':>3} {'s':>5} {'h':>5} {'house log2':>12} {'Parseval log2':>14} "
  f"{'house<256':>10} {'Pars<256':>9}")
for m in range(3, 10):
    s = 2**m; h = s//2
    lh = h*m
    lp = (h/2.0)*(2.0+math.log2(h)) + (h-1)/2.0   # log2 of sqrt((4h)^h 2^{h-1})
    P(f"{m:>3} {s:>5} {h:>5} {lh:>12.1f} {lp:>14.1f} {str(lh<CAP):>10} {str(lp<CAP):>9}")
P("  's=64'=m6  's=128'=m7  's=256'=m8.  WORST r=h: even Parseval fails s>=128.")

# ---------------------------------------------------------------------------
P("")
P("="*94)
P("Part 2: FIXED-r Parseval threshold  |N| <= (4r)^{h/2}  (the genuine lever)")
P("  row(s,r) OPEN iff (h/2)*log2(4r) < 256.  Largest r that keeps s open:")
P("="*94)
P(f"{'m':>3} {'s':>5} {'h':>5} {'max r open':>12} {'r/h':>7} "
  f"{'log2 at r=2':>12} {'log2 at r=h/2':>14}")
for m in range(3, 11):
    s = 2**m; h = s//2
    # find largest r with (h/2)*log2(4r) < 256
    rmax = 0
    for r in range(1, h+1):
        if (h/2.0)*math.log2(4*r) < CAP:
            rmax = r
    log2_r2  = (h/2.0)*math.log2(4*2)   if h>0 else 0
    log2_rh2 = (h/2.0)*math.log2(4*(h//2)) if h>=2 else 0
    P(f"{m:>3} {s:>5} {h:>5} {rmax:>12} {(rmax/h if h else 0):>7.3f} "
      f"{log2_r2:>12.1f} {log2_rh2:>14.1f}")

# ---------------------------------------------------------------------------
P("")
P("="*94)
P("Part 3: which r does the PRIZE delta* window pin?  delta* = 1 - (r-2)/s (KKH26 Prop 1).")
P("  window interior: 1-sqrt(rho) < delta* < 1-rho.  For rate rho, r ranges as below.")
P("  (s here = subgroup order; KKH26 uses code length n = s*m', this is the s-axis.)")
P("="*94)
P("  BINDING r for a below-capacity counterexample = SMALLEST in-window r = r_lo = ceil(2+rho*s)")
P("  (ceiling delta*<=1-(r-2)/s is strongest for large r, but the WEAKEST r that is still")
P("   below capacity 1-rho is r_lo; that is the cheapest counterexample, smallest |N|.)")
P(f"{'rho':>8} {'s':>6} {'r_lo':>6} {'r_lo/h':>7} {'(h/2)log2(4 r_lo)':>18} {'< 256 ?':>9}")
for rho in (0.5, 0.25, 0.125, 0.0625):
    for s in (128, 256):
        h = s//2
        r_lo = math.ceil(2 + rho*s)
        log2_lo = (h/2.0)*math.log2(4*r_lo) if r_lo>0 else 0
        P(f"{rho:>8} {s:>6} {r_lo:>6} {(r_lo/h):>7.3f} {log2_lo:>18.1f} {str(log2_lo<CAP):>9}")
P("  KEY: fixed-r Parseval opens s=128 for the BINDING r_lo at rho<=1/4 (rho=1/2 fails by ~1 bit).")
P("  s=256 fails at ALL prize rates (r_lo too large).  This is the NOVEL A34 partial.")

# ---------------------------------------------------------------------------
def prim_roots(s): return [cmath.exp(2j*cmath.pi*(2*j+1)/s) for j in range(s//2)]
def res_abs(coeffs, roots):
    prod = 1.0
    for w in roots:
        val=0j; wp=1+0j
        for c in coeffs:
            if c: val += c*wp
            wp *= w
        prod *= abs(val)
    return prod

def worst(m, r, samples=120000, seed=1):
    s=2**m; h=s//2; roots=prim_roots(s)
    best=0.0; bv=None
    if h <= 10:  # exhaustive ternary, l1<=2r
        for vec in itertools.product((-1,0,1), repeat=h):
            if sum(abs(c) for c in vec) > 2*r or all(c==0 for c in vec): continue
            v=res_abs(vec, roots)
            if v>best: best=v; bv=vec
    else:
        rng=random.Random(seed); idx=list(range(h))
        for _ in range(samples):
            k=rng.randint(2, min(2*r,h)); pos=rng.sample(idx,k)
            vec=[0]*h
            for p in pos: vec[p]=rng.choice((-1,1))
            v=res_abs(vec, roots)
            if v>best: best=v; bv=list(vec)
    return best, bv

P("")
P("="*94)
P("Part 4: TRUE worst-case max|N| (ternary, l1<=2r, r=h) vs ceilings + AM-GM tightness")
P("  geo/arith ratio -> 1  ==>  AM-GM tight  ==>  NO tighter-than-Parseval bound at worst case")
P("="*94)
P(f"{'m':>3} {'s':>5} {'h':>4} {'log2 maxN':>11} {'log2 Pars':>10} "
  f"{'maxN/h':>8} {'Pars/h':>8} {'geo/arith':>10}")
for m in range(3, 6):  # s=8,16,32  (h<=16; 32 sampled)
    s=2**m; h=s//2
    lp=(h/2.0)*(2.0+math.log2(h))+(h-1)/2.0
    best,vec=worst(m,h)
    lb=math.log2(best) if best>0 else 0.0
    roots=prim_roots(s); vals=[]
    for w in roots:
        val=0j; wp=1+0j
        for c in vec:
            if c: val+=c*wp
            wp*=w
        vals.append(abs(val)**2)
    arith=sum(vals)/len(vals)
    logs=[math.log(v) for v in vals if v>1e-12]
    geo=math.exp(sum(logs)/len(vals)) if len(logs)==len(vals) else 0.0
    P(f"{m:>3} {s:>5} {h:>4} {lb:>11.2f} {lp:>10.1f} {lb/h:>8.3f} {lp/h:>8.3f} "
      f"{(geo/arith if arith>0 else 0):>10.4f}")

P("")
P("DONE.")
