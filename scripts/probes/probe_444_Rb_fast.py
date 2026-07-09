#!/usr/bin/env python3
"""
R-b FAST: targeted checks, no resultants in the inner loop.  Uses exact integer norm only
on the handful of cores that actually appear.

Core questions:
 (i)  exponent: is v_p(N(beta_C)) >= ceil(c/2) for cores of real defects?  (dependency check)
 (iii) small-core evasion: collect ALL distinct (|C|) values of free cores over many primes,
       and check directly whether |C| >= p^{2 eta} is ever satisfiable for found defects
       (i.e. does any defect have |C| reaching the norm threshold).
 (iv) split: verify odd p_j(C)=0 holds on the extracted core for the odd j<=c.

We ALSO test the *converse direction* of the floor logic at SMALL n where defects DO exist
(p below the ceiling): there the bound is NOT vacuous, so we can see whether the antipodal
recursion + norm bound correctly predicts the (non)existence of free-core defects.
"""
import itertools, cmath
from sympy import isprime, primitive_root, symbols, Poly, resultant, cyclotomic_poly, ZZ
from collections import Counter

_X = symbols('x')

def subgroup(n, p):
    g = primitive_root(p); z = pow(g, (p-1)//n, p)
    e, x = [], 1
    for _ in range(n):
        e.append(x); x = (x*z) % p
    return e

def exact_norm_int(idxs, n):
    cnt = Counter(i % n for i in idxs)
    Bpoly = Poly(sum(c*_X**e for e, c in cnt.items()), _X, domain=ZZ)
    Phi = Poly(cyclotomic_poly(n, _X), _X, domain=ZZ)
    return int(resultant(Phi, Bpoly))

def vp(N, p):
    if N == 0: return "ZERO"
    v, a = 0, abs(int(N))
    while a % p == 0:
        a //= p; v += 1
    return v

def analyze(n, sz, c, pmax=600):
    print(f"\n{'='*80}\n n={n} s={sz} c={c} (k={sz-c}); odd j<=c: {list(range(1,c+1,2))}; ceil(c/2)={(c+1)//2}")
    print(f"{'='*80}")
    primes = [p for p in range(n+1, pmax) if isprime(p) and (p-1)%n==0]
    for p in primes:
        elts = subgroup(n, p); im = {x:i for i,x in enumerate(elts)}
        defects_with_core = []
        for T in itertools.combinations(elts, sz):
            Tel = list(T); Tset = set(Tel)
            if all(sum(pow(x,j,p) for x in Tel)%p==0 for j in range(1,c+1)):
                core = [x for x in Tel if (p-x)%p not in Tset]
                if core:
                    defects_with_core.append((Tel, core))
        if not defects_with_core:
            # is p below the naive ceiling s^{1/(2eta)} = s^{n/(2c)} ?
            eta = c/n; ceil = sz**(n/(2*c))
            print(f"  p={p}: NO free-core defect. (norm ceiling s^(1/2eta)={ceil:.3g}, p{'<=' if p<=ceil else '> '}ceil)")
            continue
        eta = c/n
        thresh = p**(2*eta)
        print(f"  p={p}: {len(defects_with_core)} free-core defects.  threshold |C|>=p^(2eta)={thresh:.3g}")
        seen_cores = set()
        for (Tel, core) in defects_with_core:
            key = tuple(sorted(im[x] for x in core))
            if key in seen_cores: continue
            seen_cores.add(key)
            idxs = list(key)
            N = exact_norm_int(idxs, n)
            v = vp(N, p)
            odd = {j: sum(pow(x,j,p) for x in core)%p for j in range(1,c+1,2)}
            allz = all(val==0 for val in odd.values())
            need = (c+1)//2
            short = "" if (v=="ZERO" or (isinstance(v,int) and v>=need)) else "  <<< EXPONENT SHORT"
            evade = "  <<< EVADES BOUND (|C|<thresh but defect exists!)" if len(core) < thresh else ""
            print(f"      |C|={len(core)} idx={idxs} N={N} v_p(N)={v}(need>={need}){short} "
                  f"odd_pj_on_core={odd} allzero={allz}{evade}")

# Pick parameters where defects EXIST below ceiling so the bound is testable, and where it doesn't.
analyze(8, 4, 2, pmax=400)    # n=8: ceil = 4^(8/4)=16 small -> defects may appear above
analyze(8, 5, 3, pmax=400)
analyze(16, 6, 2, pmax=300)
analyze(16, 8, 4, pmax=300)
