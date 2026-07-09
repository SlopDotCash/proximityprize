#!/usr/bin/env python3
"""
probe_444_trace_identity_audit.py  (#444 ATTACKER — audit Step 2's trace identity / norm ceiling)

Step 2 of the floor uses:  Tr_{Q(zeta_n)/Q}(beta_C * conj(beta_C)) = phi(n)*|C|  for antipodal-free C,
then AM-GM gives |N(beta_C)| <= |C|^{phi(n)/2}, hence p^{c/2} <= |C|^{n/4}, p <= |C|^{1/(2eta)}.

A free run of probe_444_trace_identity.py showed MISMATCH at p=193, p=257. Audit:
  (1) Is the trace identity Tr(beta.beta_bar) = phi(n)*|C| actually TRUE for antipodal-free C?
      Tr(beta beta_bar) = sum_{x,y in C} Tr(zeta^{idx(x)-idx(y)}). Diagonal gives phi(n)*|C|.
      Off-diagonal Tr(zeta^d) (d != 0 mod n) = the integer Ramanujan-type value, NOT zero in
      general for n=2^mu. So the identity is FALSE unless all cross Tr(zeta^d)=0.
  (2) For n=2^mu: Tr_{Q(zeta_n)/Q}(zeta_n^d) = 0 unless n | 2d (i.e. d = n/2), in which case
      Tr(zeta^{n/2}) = Tr(-1) = -phi(n). Antipodal-free means no d = n/2 difference => all
      cross terms vanish => identity SHOULD hold. So mismatch must mean the witness is NOT
      antipodal-free, OR the sum-over-odd-j != Tr (it IS Tr, since (Z/2^mu)* = odds).
  (3) Re-examine the p=193/257 witnesses: are they antipodal-free? Print the exact Tr value,
      phi(n)*|C|, and the antipodal pairs present.
  (4) DECISIVE: even if the trace identity is exactly right, the norm CEILING is
      p^{c/2} <= |C|^{n/4}. Audit whether the *actual defects found* obey p <= |C|^{1/(2eta)}.
      If a real defect VIOLATES p <= |C|^{1/(2eta)}, the norm bound (hence Step 2) is refuted.
"""
import itertools, cmath, math
from sympy import isprime, primitive_root

def subgroup(n, p):
    g = primitive_root(p); z = pow(g, (p-1)//n, p)
    e = []; x = 1
    for _ in range(n):
        e.append(x); x = (x*z) % p
    return e

def find_defect_full(n, p, sz, c):
    """First non-antipodal-balanced size-sz subset with p_1..p_c == 0 mod p. Return idx tuple."""
    elts = subgroup(n, p)
    negmap = {x: (p-x) % p for x in elts}
    idxof = {v: i for i, v in enumerate(elts)}
    for T in itertools.combinations(range(n), sz):
        Tel = [elts[i] for i in T]
        if all(sum(pow(x, j, p) for x in Tel) % p == 0 for j in range(1, c+1)):
            Tset = set(Tel)
            bal = all(negmap[x] in Tset for x in Tel)
            if not bal:
                return T
    return None

def tr_zeta(n, d):
    """Tr_{Q(zeta_n)/Q}(zeta_n^d), n=2^mu: = sum over odd j of zeta_n^{j*d}. Compute exactly (real)."""
    s = sum(cmath.exp(2j*math.pi*(j*d % n)/n) for j in range(1, n, 2))
    return s  # should be (near) real integer

def trace_beta_betabar(n, idxs):
    """Tr(beta beta_bar) = sum_{x,y} Tr(zeta^{idx_x - idx_y})."""
    total = 0+0j
    for a in idxs:
        for b in idxs:
            total += tr_zeta(n, (a-b) % n)
    return total

def sum_odd_sigma_sq(n, idxs):
    tot = 0.0
    for j in range(1, n, 2):
        sv = sum(cmath.exp(2j*math.pi*(j*i % n)/n) for i in idxs)
        tot += abs(sv)**2
    return tot

def antipodal_pairs(n, idxs):
    half = n//2; s = set(idxs)
    pairs = [(i, (i+half) % n) for i in idxs if i < (i+half) % n and ((i+half) % n) in s]
    return pairs

def norm_abs(n, idxs):
    prod = 1.0
    for j in range(1, n, 2):
        sv = sum(cmath.exp(2j*math.pi*(j*i % n)/n) for i in idxs)
        prod *= abs(sv)
    return prod

if __name__ == "__main__":
    print("### (2) Tr_{Q(zeta_n)/Q}(zeta_n^d) for n=32, all d (should be 0 except d=0 -> phi(n), d=16 -> -phi(n)) ###")
    n = 32
    nz = [(d, complex(round(tr_zeta(n, d).real, 6), round(tr_zeta(n, d).imag, 6))) for d in range(n)]
    for d, v in nz:
        if abs(v) > 1e-6:
            print(f"   d={d}: Tr(zeta^d)={v}")
    print(f"   (phi(32)={n//2})")

    print("\n### (1)(3) Trace identity audit at the mismatch primes ###")
    for p, sz, c in [(97, 6, 2), (193, 6, 2), (257, 8, 2), (449, 6, 2), (577, 8, 2)]:
        if (p-1) % n:
            continue
        T = find_defect_full(n, p, sz, c)
        if T is None:
            print(f"   p={p} sz={sz} c={c}: no non-balanced defect")
            continue
        tr = trace_beta_betabar(n, T)
        so = sum_odd_sigma_sq(n, T)
        phiC = (n//2) * sz
        ap = antipodal_pairs(n, T)
        print(f"   p={p} sz={sz} c={c} T={T}")
        print(f"        Tr(beta.beta_bar)={complex(round(tr.real,4),round(tr.imag,4))}  "
              f"sum_odd|sigma|^2={so:.4f}  phi(n)*|C|={phiC}  "
              f"antipodal_pairs={ap}  antipodal_free={len(ap)==0}")
        match = abs(so - phiC) < 1e-6
        print(f"        => identity holds? {match}  (mismatch => witness has antipodal pairs, "
              f"so it's NOT a free-core C — the identity is about the antipodal-FREE core only)")

    print("\n### (4) DECISIVE: do ACTUAL defects obey the norm ceiling p <= |C|^(1/(2 eta))? ###")
    print("    For a NON-antipodal-balanced defect, the 'free core' C = part not in antipodal pairs.")
    print("    eta = c/n. Ceiling uses |C| (free-core size), not |S|. Test p <= |C|^{1/(2 eta)}.")
    for p in [97, 193, 257, 353, 449, 577, 641, 769]:
        if (p-1) % n:
            continue
        for sz, c in [(6, 2), (8, 2), (8, 3), (10, 2), (6, 3)]:
            T = find_defect_full(n, p, sz, c)
            if T is None:
                continue
            # free core = indices whose antipode is NOT in T
            half = n//2; s = set(T)
            core = [i for i in T if ((i+half) % n) not in s]
            Cn = len(core)
            eta = c / n
            ceil_S = sz ** (1.0/(2*eta))   # ceiling using |S|
            ceil_C = (Cn ** (1.0/(2*eta))) if Cn > 0 else float('inf')  # ceiling using |C|
            viol_S = p > ceil_S
            viol_C = p > ceil_C
            print(f"   p={p} sz={sz} c={c} |C|={Cn} eta={eta:.4f}: ceil(|S|)={ceil_S:.4g} "
                  f"p>ceil_S?{viol_S}  ceil(|C|)={ceil_C:.4g} p>ceil_C?{viol_C}"
                  + ("  <<< NORM-CEILING VIOLATED" if (viol_C or (Cn==0 and viol_S)) else ""))
            break
