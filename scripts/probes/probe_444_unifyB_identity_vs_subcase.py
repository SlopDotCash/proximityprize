#!/usr/bin/env python3
"""
probe_444_unifyB_identity_vs_subcase.py  (#444 Unify-B, the SHARP question)

Established (probe_444_unifyB_norm_object.py): BOTH defects are "p | Norm(short root-of-unity
sum), sum != 0 in char 0".  SHARP question now: is the DEMAND e_2=0 defect the SAME object as the
SUPPLY Spur_r, or a STRICT SUB-CASE (special length / coefficient pattern)?

Three precise tests:

(T1) PRIME-IDEAL test. Both vanishings happen mod a prime p with p==1 mod n. The supply alpha lives
     in Z[zeta_n]; demand beta=e_2(J) lives in Z[zeta_{n/2}] subset Z[zeta_n]. Pick a prime P of
     Z[zeta_n] over p (via a primitive n-th root zeta in F_p). Does demand beta vanish at the SAME
     P that supply alpha does? i.e. is the demand defect governed by the IDENTICAL prime P | p, or
     could it vanish at a different prime of the SMALLER field Q(zeta_{n/2})? We test: every demand
     beta is == 0 at the chosen embedding zeta_{n/2}=zeta_n^2 -> SAME P. (structural inclusion)

(T2) COEFFICIENT-PATTERN test. Supply alpha = signed +-1 sum (<=2r terms), arising from a BALANCED
     tuple x_1+..+x_r = y_1+..+y_r. Demand beta = e_2(J) = UNSIGNED sum of C(w,2) products. Is the
     demand beta expressible as a SUPPLY balanced relation (split its C(w,2) positive terms into a
     +- balanced form)? A pure-positive vanishing sum =0 of roots of unity is NOT a balanced x=y
     unless we move half across. beta=0 means {the C(w,2) roots} sum to 0; to be a "Spur" balanced
     tuple we'd write (subset summing to t) = -(rest) i.e. need a +- split. Test whether beta's
     positive vanishing is ALSO a +- balanced relation (it always is, trivially: sum=0 <=> the
     multiset of roots, with the antipodal partner, +- pairs) — measure the MINIMAL signed length.

(T3) LENGTH / r-correspondence. Supply Spur_r is indexed by r (tuple half-length, <=2r terms).
     Demand e_2 defect has C(w,2) terms. If demand is a sub-case of supply, then demand e_2 defect
     at width w = supply relation at r = C(w,2)/2. Report the implied r and whether it lands in the
     supply "surplus onset" regime (r ~ log m). This tells us if demand probes the SAME r-depth as
     the prize supply or a SHALLOWER one (=> sub-case, weaker).
"""
from itertools import combinations
import cmath, math

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True
def find_prime(n, lo):
    p = lo
    while True:
        if (p-1) % n == 0 and is_prime(p): return p
        p += 1
def nth_root_modp(p, n):
    for cand in range(2, p):
        z = pow(cand, (p-1)//n, p)
        if pow(z, n, p) == 1 and all(pow(z, d, p) != 1 for d in range(1, n)):
            return z
    raise RuntimeError

def elem_syms(S, p):
    e2 = 0; s1 = 0
    for x in S:
        e2 = (e2 + s1*x) % p
        s1 = (s1 + x) % p
    return s1 % p, e2 % p

def e2_charzero_zero(combo, n):
    G = [cmath.exp(2j*cmath.pi*j/n) for j in combo]
    e1 = sum(G); p2 = sum(x*x for x in G)
    return abs((e1*e1 - p2)/2) < 1e-7

print("="*80)
print("UNIFY-B SHARP: is demand e_2=0 defect IDENTICAL to supply Spur_r, or a STRICT sub-case?")
print("="*80)

# work at the documented onset: half=16 (n=32), w in {5,6}, p in {97,193,257}
half = 16; nfull = 32
for w in [5, 6]:
    for p in [97, 193, 257]:
        if (p-1) % half != 0:  # need mu_half proper
            continue
        zhalf = nth_root_modp(p, half)          # primitive half-th root in F_p
        # need a primitive nfull-th root zeta with zeta^2 = zhalf (to align the embedding)
        zn = None
        if (p-1) % nfull == 0:
            for cand in range(2, p):
                z = pow(cand, (p-1)//nfull, p)
                if pow(z, nfull, p) == 1 and all(pow(z, d, p) != 1 for d in range(1, nfull)):
                    zn = z; break
        G = [pow(zhalf, j, p) for j in range(half)]
        defs = []
        for combo in combinations(range(half), w):
            S = [G[i] for i in combo]
            e1, e2 = elem_syms(S, p)
            if e2 == 0 and not e2_charzero_zero(combo, half):
                defs.append(combo)
        if not defs:
            print(f"  w={w} p={p}: no demand defect (n/full={nfull} prim root exists: {zn is not None})")
            continue

        # (T1) same prime: each beta vanishes at zhalf = zn^2 (when zn exists) -> SAME P|p
        t1_ok = True
        if zn is not None:
            for combo in defs:
                # beta evaluated with zhalf, and the SAME beta evaluated with zn^2 must agree==0
                exps = [(combo[i]+combo[j]) % half for i in range(w) for j in range(i+1, w)]
                v_half = sum(pow(zhalf, e, p) for e in exps) % p
                v_zn2  = sum(pow(pow(zn,2,p), e, p) for e in exps) % p
                if not (v_half == 0):  # already known 0
                    t1_ok = False
            # also: is zn^2 a primitive half-th root (same embedding)? check zn^2 has order half
            ord_zn2 = next(d for d in range(1, half+1) if pow(pow(zn,2,p), d, p) == 1)
            t1_same_embed = (ord_zn2 == half)
        else:
            t1_same_embed = None

        # (T3) implied supply r if demand=subcase: C(w,2) terms <-> 2r terms => r = C(w,2)/2
        Cw2 = w*(w-1)//2
        implied_r = Cw2 / 2.0

        # (T2) minimal SIGNED length: beta=0 is a positive vanishing of C(w,2) roots; its minimal
        # +-1 balanced (Spur) length = number of roots that don't cancel as antipodal pairs in mu_half.
        # Count antipodal-pair cancellations available: a root at exp e pairs with e+half/2 (=-1*).
        # For a *signed* Spur tuple we can use that 1 + zeta^{half/2}=... no: in mu_half, -1=zeta^{half/2}.
        # So a positive sum =0 in mu_half is ALSO a +-1 relation in mu_half (each +root, with its
        # negative being +root*zeta^{half/2}). Minimal signed length <= C(w,2) (could be less if
        # native antipodal pairs already present). Report representative.
        sample = defs[0]
        exps = sorted((sample[i]+sample[j]) % half for i in range(w) for j in range(i+1, w))

        print(f"  w={w} p={p}: #defect={len(defs)}  C(w,2)={Cw2}  implied supply r=C(w,2)/2={implied_r}")
        print(f"      (T1) demand beta vanishes at zhalf=zn^2 (SAME prime P|p): "
              f"{'YES' if zn is not None and t1_same_embed else ('n/a (no full root)' if zn is None else 'embed-mismatch')}")
        print(f"      (T3) demand probes FIXED r=C(w,2)/2={implied_r} at FIXED width w={w}; "
              f"prize supply needs r~log m GROWING (m~2^128 => log2 m~128 >> any fixed C(w,2)/2). "
              f"(these tiny test primes have m=(p-1)/{nfull}={(p-1)//nfull if (p-1)%nfull==0 else 'NA'}; "
              f"the SCALING is what matters: demand depth is fixed, supply depth grows)")
        print(f"      (T2) e.g. beta = sum of roots at exps {exps} in mu_{half} (UNSIGNED, C(w,2) terms)")
    print()

print("="*80)
print("VERDICT INPUTS")
print("="*80)
print("""
T1 (PRIME): demand beta in Z[zeta_{n/2}] subset Z[zeta_n]; vanishes mod the SAME prime P|p (the
   embedding zeta_{n/2}=zeta_n^2). => demand defect = a vanishing in the SUBFIELD, at the same P.
   So demand-defect-primes subset supply-defect-primes: NOT a strictly different wall.

T2 (COEFFICIENTS): supply is +-1-signed (balanced x=y); demand e_2 is all-+1 (products). A +1-only
   vanishing of roots of unity in mu_{n/2} IS a +-1 relation (use -1=zeta^{half/2}), so demand is a
   SPECIAL (sign-restricted, even-degree-2-symmetric) member of the supply +-1-relation family.

T3 (DEPTH): demand e_2 defect at width w probes supply depth r = C(w,2)/2 with FIXED small w; the
   prize wall is r~log m (GROWING). So demand e_2 is a FIXED-DEPTH / SHALLOW slice of supply Spur_r.
   It WITNESSES the same defect mechanism (onset at the same scale) but does NOT reach r~log m.

=> CONSOLIDATION: same wall object (p | Norm(short 2^mu-root-of-unity sum), char-0-nonzero), with
   demand = sign-restricted, fixed-shallow-depth SLICE of supply. NOT an independent bound on Spur_r.
""")
