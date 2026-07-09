#!/usr/bin/env python3
"""
R-b POINT (i): the EXPONENT.  Find ANY free-core defect with ceil(c/2) >= 2 and verify
whether v_p(N(beta_C)) >= ceil(c/2).  If a defect appears with v_p(N) < ceil(c/2), the
floor's divisibility step is BROKEN (dependencies reduce the exponent -> p^c vs p^{ceil(c/2)}
class of error).  We scan many (n, s, c, p) to harvest free-core defects with c=3,4,5.

We DON'T restrict to defects being non-cosets; ANY S with vanishing power sums and a nonempty
free core is the test object (that's exactly beta_C with the odd conditions on it).

Also (point iii): we record, for EACH free-core defect, whether the norm-threshold inequality
  p^{ceil(c/2)} <= |N(beta_C)| <= |C|^{n/4}
actually holds as an integer chain (the real, un-idealized inequality the floor rests on).
"""
import itertools
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
    Bpoly = Poly(sum(co*_X**e for e, co in cnt.items()), _X, domain=ZZ)
    Phi = Poly(cyclotomic_poly(n, _X), _X, domain=ZZ)
    return int(resultant(Phi, Bpoly))
def vp(N, p):
    if N == 0: return "ZERO"
    v, a = 0, abs(int(N))
    while a % p == 0:
        a //= p; v += 1
    return v

def harvest(n, s_list, c_list, pmax):
    print(f"\n{'='*88}\n n={n}  searching for free-core defects with ceil(c/2)>=2 (c>=3)")
    print(f"{'='*88}")
    primes = [p for p in range(n+1, pmax) if isprime(p) and (p-1)%n==0]
    any_short = False
    any_found = False
    for s in s_list:
        for c in c_list:
            if c >= s: continue
            need = (c+1)//2
            if need < 2: continue   # only test the multi-prime exponent regime
            for p in primes:
                elts = subgroup(n, p); im = {x:i for i,x in enumerate(elts)}
                seen = set()
                for T in itertools.combinations(elts, s):
                    Tel = list(T); Tset = set(Tel)
                    if all(sum(pow(x,j,p) for x in Tel)%p==0 for j in range(1,c+1)):
                        core = [x for x in Tel if (p-x)%p not in Tset]
                        if not core: continue
                        key = tuple(sorted(im[x] for x in core))
                        if key in seen: continue
                        seen.add(key)
                        idxs = list(key)
                        N = exact_norm_int(idxs, n)
                        v = vp(N, p)
                        ub = len(core)**(n//4)   # |C|^{n/4} upper bound (n divisible by 4)
                        lhs = p**need
                        chain_ok = (N != 0) and (lhs <= abs(N) <= ub)
                        short = isinstance(v,int) and v < need
                        if short: any_short = True
                        any_found = True
                        flag = "  <<<<< EXPONENT SHORT!" if short else ""
                        chainflag = "" if chain_ok or N==0 else "  <<<<< CHAIN FAILS!"
                        print(f"  s={s} c={c} need={need} p={p}: |C|={len(core)} idx={idxs} "
                              f"N={N} v_p={v}{flag}  [p^need={lhs} <= |N|={abs(N)} <= |C|^(n/4)={ub}? "
                              f"{chain_ok}]{chainflag}")
    if not any_found:
        print("  (no free-core defects with ceil(c/2)>=2 found in this range)")
    return any_short

# n must be div by 4 for |C|^{n/4} integer; scan n=8,16 with c=3,4,5
s_short = harvest(8, s_list=[5,6,7], c_list=[3,4,5], pmax=2000)
s_short |= harvest(16, s_list=[7,8,9,10], c_list=[3,4,5], pmax=600)
print(f"\n>>> ANY EXPONENT-SHORT DEFECT FOUND: {s_short}")
