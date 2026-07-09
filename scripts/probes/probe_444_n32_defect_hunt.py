#!/usr/bin/env python3
"""
probe_444_n32_defect_hunt.py  (#444 SEAM A, CRACK-HUNT stage 1)

Find the SMALLEST char-p DEFECT for the EXACT config n=32, m0=8, j=4.
DEFECT = T subset mu_32, |T|=8, e_1(T)=...=e_4(T)=0 mod p, T NOT a coset of mu_8.

Char-0 rigidity (DyadicFourierUncertainty): only mu_8-cosets are lacunary in char 0.
A defect can appear mod p when p divides the norm of a "short relation" (#407 lacunary-floor /
additive-energy literature). The depth-j onset prime grows ~ (2j)^{n/2}; for n=32 the norm wall
is enormous, so a defect at a SMALL prime requires p | N(short relation).

This probe was NOT covered exhaustively by prior probes: probe_444_defect_onset_verify2.py SKIPS
n=32,s=8 because comb(32,8)=10.5M > 3e6 cap, and only tries ONE prime per n.

Search design (pruned exhaustive per prime):
  - index space {0..31}, val[i]=zeta^i.
  - e_1=e_2=e_3=e_4=0 mod p  (j=4 lacunary; char p>4 so equiv to power sums p_1..p_4=0).
  - ROTATION INVARIANCE: idx-shift (mult by zeta) preserves lacunary AND coset properties.
    Every 8-subset has a rotation containing index 0; fixing 0 in T and requiring min(full)==0
    enumerates each rotation class via its 0-containing rep. (We keep all such reps; a set may have
    several rotations through 0 only if it is itself rotation-symmetric, handled by the seen-set.)
  - e_1=0 COMPLETION TRICK: pick 6 other indices (+ idx0 = 7 chosen), the 8th val is forced to
    -(sum of 7) mod p to make e_1=0; O(1) membership test. Then check e_2=e_3=e_4=0.
    This turns an 8-deep enumeration into a 6-deep one: C(31,6)=736281 completions per prime.
"""
import itertools, sys, math
from sympy import isprime, primitive_root

def subgroup_idx(n, p):
    g = primitive_root(p); zeta = pow(g, (p-1)//n, p)
    val = []; x = 1
    for i in range(n):
        val.append(x); x = (x*zeta) % p
    return val, zeta

def is_coset(Tset, n, m0):
    """Tset (frozenset of indices) is a coset of mu_{m0}: arithmetic progression step=n/m0."""
    step = n//m0
    if len(Tset) != m0: return False
    for i0 in range(step):  # only need base residues 0..step-1
        if set((i0 + step*j) % n for j in range(m0)) == Tset:
            return True
    return False

def search(n, p, m0=8, j=4, report_cap=8):
    val, zeta = subgroup_idx(n, p)
    valset = {v: i for i, v in enumerate(val)}
    defects = []; total_lac = 0; seen = set()
    others = list(range(1, n))
    for combo in itertools.combinations(others, m0-2):   # 6 others + idx0 = 7 chosen
        Tidx7 = (0,) + combo
        s = 0
        for i in Tidx7: s += val[i]
        s %= p
        v8 = (-s) % p                     # forces e_1 = 0
        i8 = valset.get(v8)
        if i8 is None or i8 in Tidx7: continue
        full = frozenset(Tidx7 + (i8,))
        if len(full) != m0: continue
        if min(full) != 0: continue       # rotation-rep: keep only sets whose min index is 0
        if full in seen: continue
        seen.add(full)
        Tv = [val[i] for i in full]
        e = [1, 0, 0, 0, 0]               # elem sym up to e_4
        for r in Tv:
            for t in range(4, 0, -1):
                e[t] = (e[t] + e[t-1]*r) % p
        if e[1] == 0 and e[2] == 0 and e[3] == 0 and e[4] == 0:
            total_lac += 1
            if not is_coset(full, n, m0):
                defects.append(tuple(sorted(full)))
                if len(defects) >= report_cap:
                    return total_lac, defects, True
    return total_lac, defects, False

def gen_primes_smallidx(n, count):
    out = []; pp = n+1
    while len(out) < count:
        if isprime(pp) and (pp-1) % n == 0:
            out.append(pp)
        pp += n
    return out

def gen_primes_prize(n, count, beta=4.0):
    """primes near n^beta (prize-shaped index m=(p-1)/n)."""
    out = []
    target = int(n**beta); pp = target - (target % n) + 1
    while len(out) < count:
        if pp > n and isprime(pp) and (pp-1) % n == 0 and (pp-1)//n >= 2:
            out.append(pp)
        pp += n
    return out

if __name__ == "__main__":
    n, m0, j = 32, 8, 4
    mode = sys.argv[1] if len(sys.argv) > 1 else "small"
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    if mode == "small":
        primes = gen_primes_smallidx(n, count)
        label = "SMALL-INDEX p=1 mod 32"
    elif mode == "prize":
        primes = gen_primes_prize(n, count, 4.0)
        label = "PRIZE-SHAPED p~n^4"
    else:
        primes = [int(mode)]
        label = f"single p={mode}"
    print(f"#444 n={n} m0={m0} j={j} DEFECT hunt. {label} ({len(primes)} primes)", flush=True)
    first_defect = None
    sanity_coset_found = True
    for p in primes:
        idx = (p-1)//n
        tot, defs, capped = search(n, p, m0, j)
        # sanity: a mu_8 coset is ALWAYS lacunary; there are n/m0=4 of them; total_lac>=... but we only
        # count rotation reps with min index 0. The 4 cosets are {0,4,..},{1,5,..},{2,6,..},{3,7,..};
        # only {0,4,8,12,16,20,24,28} has min 0 -> exactly 1 coset rep expected. So tot includes >=1.
        flag = f"  <== DEFECT x{len(defs)}{'+' if capped else ''}" if defs else ""
        coset_ok = tot >= 1  # at least the canonical mu_8 coset (min-0 rep)
        if not coset_ok: sanity_coset_found = False
        print(f"  p={p:9d} idx={idx:6d} log2p={math.log2(p):5.1f}: lac_reps(min0)={tot:3d} "
              f"DEFECTS={len(defs):3d}{flag}", flush=True)
        if defs and first_defect is None:
            first_defect = (p, defs[0])
            print(f"     first defect T(idx)={defs[0]}", flush=True)
    print(f"\nsanity (canonical mu_8 coset detected every prime): {sanity_coset_found}", flush=True)
    if first_defect:
        print(f"FIRST DEFECT: p={first_defect[0]} T={first_defect[1]}", flush=True)
    else:
        print(f"NO DEFECT over {len(primes)} primes (every size-8 j=4 lacunary subset is a mu_8 coset).",
              flush=True)
