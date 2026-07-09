#!/usr/bin/env python3
# wf407w2_L4-onq_image_quantization.py
#
# Thread L4-onq (#407 prize) — "O(n) per-q e2=0 defect image bound (T400-05 follow-up)".
#
# Wave 1 (T400-05) measured the genuine per-q image of the e2=0 defect to be in units of n:
# {n,2n,3n}={16,32,48} at n=16,w=6 once the q-1 small-prime saturation artifact is escaped.
#
# THIS PROBE proves the MECHANISM behind the O(n) bound so it can be Lean-formalized:
#
#  (M1) DILATION ORBIT: the multiplicative group mu_n acts on w-subsets S by S -> g*S
#       (g in mu_n).  This action PRESERVES e2(S)=0 (mod q) and e1(g*S)=g*e1(S).
#       So the nonzero carrier e1 values are a UNION OF FULL <g>-ORBITS, each of size
#       n/|stab|.  For e1!=0 in F_q with g a primitive n-th root, the orbit {g^j*e1}
#       has size = ord(g)=n EXACTLY (no nonzero element of F_q is fixed by g!=1).
#       => the per-q image is a disjoint union of size-n orbits => image size = (#orbits)*n
#       => image size is a MULTIPLE OF n.  This is the "units of n" quantization, exactly.
#
#  (M2) STAIRCASE CEILING: the # of distinct orbits is bounded by the s_max=mu-1 staircase
#       (issue400-smax-law).  Measured #orbits <= 3 = mu-1 at n=16 (mu=4).  So
#       image <= (mu-1)*n = O(n), uniform in q below saturation.
#
#  (M3) SATURATION ESCAPE: the q-1 artifact occurs exactly when q-1 < (mu-1)*n, i.e. the
#       field is too small to hold all the orbit values.  Once q > (mu-1)*n+1 the genuine
#       image is exposed and equals (#orbits)*n <= (mu-1)*n.
#
# EXACT enumeration, no sampling.  Run:  python <thisfile>

import itertools
from math import comb
from sympy import isprime, primitive_root

def e1_vec(A, n):
    h = n // 2
    v = [0]*h
    for a in A:
        a %= n
        if a < h: v[a] += 1
        else: v[a-h] -= 1
    return tuple(v)

def e2_vec(A, n):
    h = n // 2
    v = [0]*h
    L = list(A)
    for a in range(len(L)):
        for b in range(a+1, len(L)):
            e = (L[a]+L[b]) % n
            if e < h: v[e] += 1
            else: v[e-h] -= 1
    return v

def zeta_modq(q, n):
    g = primitive_root(q)
    return pow(g, (q-1)//n, q)

def eval_modq(v, z, q):
    acc = 0; zp = 1
    for vi in v:
        if vi: acc = (acc + vi*zp) % q
        zp = (zp*z) % q
    return acc % q

def primes_1_mod_n(n, lo, hi):
    out = []
    m = max(1, (lo-1)//n)
    while True:
        q = n*m+1
        if q > hi: break
        if q >= lo and isprime(q): out.append(q)
        m += 1
    return out

def per_q_analysis(n, w, q):
    """Return (image_set, #orbits, orbit sizes) for the genuine carrier e1 image at q."""
    z = zeta_modq(q, n)
    image = set()
    for A in itertools.combinations(range(n), w):
        v2 = e2_vec(A, n)
        if eval_modq(v2, z, q) == 0:
            e1 = eval_modq(list(e1_vec(A, n)), z, q)
            if e1 != 0:
                image.add(e1)
    # decompose image into <z>-orbits  (e1 -> z*e1 mod q)
    image_set = set(image)
    seen = set(); orbits = []
    for e in sorted(image_set):
        if e in seen: continue
        orb = []
        x = e
        for _ in range(n):
            orb.append(x); seen.add(x); x = (x*z) % q
        orbits.append(orb)
    orbit_sizes = sorted(len(set(o)) for o in orbits)
    # verify closure: image is closed under mult by z
    closed = all(((e*z) % q) in image_set for e in image_set)
    return image_set, len(orbits), orbit_sizes, closed

if __name__ == "__main__":
    print("wf407-w2 / L4-onq : per-q e2=0 image QUANTIZATION (units of n) + staircase ceiling")
    print("="*78)

    for (n, w) in [(8,4),(8,6),(16,6),(16,8)]:
        mu = n.bit_length()-1
        smax = mu-1
        ceiling = smax * n
        print(f"\nn={n} (mu={mu}, s_max=mu-1={smax}, ceiling=(mu-1)*n={ceiling})  w={w}")
        print(f"  {'q':>7} {'image':>6} {'img/n':>6} {'#orb':>5} {'orbit-sizes':>14} {'closed':>7} {'<=ceil':>7}")
        violations = []
        for q in primes_1_mod_n(n, 17, 700 if n<=16 else 400):
            img, norb, osz, closed = per_q_analysis(n, w, q)
            sz = len(img)
            is_mult = (sz % n == 0)
            le_ceil = (sz <= ceiling)
            sat = (q-1) < ceiling
            tag = " SAT" if sat else ""
            if not closed or (not is_mult and sz>0) or (not le_ceil and not sat):
                violations.append((q, sz, closed))
            print(f"  {q:>7} {sz:>6} {sz/n:>6.2f} {norb:>5} {str(osz):>14} "
                  f"{str(closed):>7} {str(le_ceil):>7}{tag}")
        print(f"  --- all images multiples of n & <= (mu-1)*n (post-saturation)?  "
              f"{'YES' if not violations else 'NO: '+str(violations)}")
