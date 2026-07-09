#!/usr/bin/env python3
"""
Attacker R-b: scrutinize the antipodal decomposition + recursion (steps 2-3 of the floor).

We test, EXACTLY (no sampling), over real defect sets S found by brute force:
  (i)   When the free core C is nonempty, is p^{ceil(c/2)} | N(beta_C)?  Or do dependencies
        reduce the exponent (the p^c vs p^{ceil(c/2)} class of error)?  AND is the trace
        identity Tr(beta_C beta_C-bar) = phi(n)|C| really valid for the EXTRACTED core C
        (not the whole S)?
  (ii)  When C is empty, does S recurse cleanly to the squared half on mu_{n/2}, and is
        eta_crit really only decreasing?
  (iii) Can a defect have a SMALL nonzero free core that evades the norm bound?  We directly
        check the threshold |C| >= p^{2 eta} against actual |C| of found defects.
  (iv)  Does the even-condition coupling between pairs and C break the clean split?  We test
        whether the odd conditions REALLY fall entirely on C (independent of pairs), and
        whether p_j(C)=0 for the odd j actually holds for the extracted core.

KEY DEFINITIONS (matching the doc):
  - S = size-s subset of mu_n with p_1(S)=...=p_c(S)=0 mod p   (c = s-k = eta*n conditions)
  - antipodal pair {x,-x}: both x and -x=p-x in S
  - C = free core = elements of S whose antipode is NOT in S
  - beta_C = sum_{x in C} zeta^{idx(x)}  in Z[zeta_n]; conjugates sigma_j for odd j.
"""
import itertools, cmath, math
from sympy import isprime, primitive_root, factorint, symbols, Poly, resultant, cyclotomic_poly, ZZ
from fractions import Fraction

_X = symbols('x')

def exact_norm_int(idxs, n):
    """Exact algebraic norm N_{Q(zeta_n)/Q}(beta) as a Python int, where
       beta = sum_{i in idxs} zeta_n^i.  Computed as Res_x(Phi_n(x), B(x)) where
       B(x) = sum x^i  (mod the convention; norm = prod over all roots of Phi_n of B(root))."""
    # B(x) = sum_{i} x^{i mod n}
    from collections import Counter
    cnt = Counter(i % n for i in idxs)
    Bpoly = Poly(sum(c*_X**e for e, c in cnt.items()), _X, domain=ZZ)
    Phi = Poly(cyclotomic_poly(n, _X), _X, domain=ZZ)
    r = resultant(Phi, Bpoly)
    return int(r)

def subgroup(n, p):
    g = primitive_root(p); z = pow(g, (p-1)//n, p)
    e, x = [], 1
    for _ in range(n):
        e.append(x); x = (x*z) % p
    return e

def idx_map(elts, p):
    return {x: i for i, x in enumerate(elts)}

def power_sums_vanish(Tel, p, c):
    return all(sum(pow(x, j, p) for x in Tel) % p == 0 for j in range(1, c+1))

def extract_core(Tel, p):
    """Return (pairs_list, core_list): pairs = elements x with (p-x) also in T; core = rest."""
    Tset = set(Tel)
    core = [x for x in Tel if (p-x) % p not in Tset]
    pairs = [x for x in Tel if (p-x) % p in Tset]
    return pairs, core

def exact_norm(idxs, n):
    """N(beta) = prod over ALL phi(n) conjugates (odd j) of sigma_j(beta).  beta in Z[zeta_n].
       beta = sum zeta^{idx}.  Computed as a rational integer via the complex product (rounded).
       Returns a real integer (the algebraic norm)."""
    prod = 1.0+0j
    for j in range(1, n, 2):
        s = sum(cmath.exp(2j*cmath.pi*j*idx/n) for idx in idxs)
        prod *= s
    # N(beta) is a rational integer: imaginary part must round to 0
    return prod.real

def trace_bbbar(idxs, n):
    """Tr(beta beta-bar) = sum_{j odd} |sigma_j(beta)|^2 (the M conjugates of beta beta-bar)."""
    M = n//2
    total = 0.0
    for j in range(1, n, 2):
        s = sum(cmath.exp(2j*cmath.pi*j*idx/n) for idx in idxs)
        total += abs(s)**2
    return total

def odd_power_sums_of_core(core, p, c):
    """Check p_j(core)=0 mod p for odd j<=c."""
    res = {}
    for j in range(1, c+1, 2):
        res[j] = sum(pow(x, j, p) for x in core) % p
    return res

def vp(N, p):
    """p-adic valuation of integer N."""
    Ni = int(N)
    if Ni == 0:
        return ("ZERO", Ni)
    v = 0
    a = abs(Ni)
    while a % p == 0:
        a //= p; v += 1
    return (v, Ni)

def search_all_defects(n, p, sz, c, limit=None):
    """Return list of (T_tuple, pairs, core) for every size-sz S with vanishing power sums
       that is NOT a full mu_{?}-coset (i.e. has a nonempty free core OR is otherwise a defect)."""
    elts = subgroup(n, p); im = idx_map(elts, p)
    out = []
    for T in itertools.combinations(elts, sz):
        Tel = list(T)
        if power_sums_vanish(Tel, p, c):
            pairs, core = extract_core(Tel, p)
            out.append((Tel, pairs, core))
            if limit and len(out) >= limit:
                break
    return out, im

print("="*90)
print("R-b ATTACK: antipodal decomposition + recursion (steps 2-3)")
print("="*90)

# Use small n=32 where brute force is feasible; c=2 (so ceil(c/2)=1 odd condition: j=1)
# and c=4 (ceil(c/2)=2 odd conditions: j=1,3).
for (n, sz, c) in [(32,6,2),(32,8,4),(16,5,2),(16,6,4)]:
    print(f"\n{'#'*70}\n# n={n} size s={sz} c={c} conditions (k={sz-c}); odd-j conditions: {list(range(1,c+1,2))}")
    print(f"{'#'*70}")
    primes = [p for p in range(n+1, 2000) if isprime(p) and (p-1)%n==0][:6]
    for p in primes:
        defs, im = search_all_defects(n, p, sz, c)
        # classify each found S
        n_total = len(defs)
        with_core = [(T,pr,co) for (T,pr,co) in defs if len(co)>0]
        without_core = [(T,pr,co) for (T,pr,co) in defs if len(co)==0]
        print(f"\n  p={p}: total vanishing-S = {n_total}; with-free-core = {len(with_core)}; "
              f"fully-antipodal = {len(without_core)}")
        # (i)+(iv) for each S with a nonzero free core: check norm valuation & trace & odd-sums-on-core
        for (T, pairs, core) in with_core[:5]:
            idxs = [im[x] for x in core]
            N = exact_norm_int(idxs, n)
            v, Ni = vp(N, p)
            tr = trace_bbbar(idxs, n)
            trace_pred = (n//2)*len(core)
            odd = odd_power_sums_of_core(core, p, c)
            odd_all_zero = all(val==0 for val in odd.values())
            ceil_c2 = (c+1)//2
            tag = "p^{ceil(c/2)}|N OK" if (isinstance(v,int) and v>=ceil_c2) else "*** EXPONENT SHORT ***"
            if v=="ZERO": tag = "*** N(beta_C)=0 ! ***"
            print(f"      |C|={len(core):2d} core_idx={sorted(idxs)} "
                  f"v_p(N)={v} (need>={ceil_c2}) [{tag}]")
            print(f"        trace Tr(bb-bar)={tr:.1f} vs phi(n)|C|={trace_pred} "
                  f"match={abs(tr-trace_pred)<1e-6}; odd p_j(C) mod p ={odd} allzero={odd_all_zero}")
