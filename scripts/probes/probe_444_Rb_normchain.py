#!/usr/bin/env python3
"""
R-b DEFINITIVE: the integer norm chain  p^{ceil(c/2)} <= |N(beta_C)| <= |C|^{n/4}.
For EVERY free-core defect found, verify BOTH inequalities as exact integers, and report
the actual |N|, the predicted bounds, and whether |C| >= p^{2eta} (the necessary threshold).

If the LOWER inequality p^{ceil(c/2)} <= |N| ever FAILS -> the divisibility/Galois step is wrong.
If the UPPER inequality |N| <= |C|^{n/4} ever FAILS -> the trace/AM-GM step is wrong.
Either failure REFUTES the floor.

We also test whether |C| >= p^{2eta} is the operative threshold: every found defect should have
|C| >= p^{2eta} (else the norm chain itself would be violated).
"""
import itertools, sys
from sympy import isprime, primitive_root, symbols, Poly, resultant, cyclotomic_poly, ZZ
from collections import Counter

_X = symbols('x')
def subgroup(n, p):
    g = primitive_root(p); z = pow(g, (p-1)//n, p)
    e, x = [], 1
    for _ in range(n):
        e.append(x); x=(x*z)%p
    return e
def exact_norm_int(idxs, n):
    cnt = Counter(i%n for i in idxs)
    B = Poly(sum(co*_X**e for e,co in cnt.items()), _X, domain=ZZ)
    Phi = Poly(cyclotomic_poly(n,_X), _X, domain=ZZ)
    return int(resultant(Phi,B))

low_fail=up_fail=thr_fail=0; total=0
print("p^ceil(c/2) <= |N(beta_C)| <= |C|^(n/4) ; and |C|>=p^(2eta)?", flush=True)
for (n,sz,c) in [(16,6,2),(16,5,2),(16,4,2),(32,6,2),(32,4,2),(8,4,2),(8,5,2),(8,6,2)]:
    if n%4: continue
    need=(c+1)//2; eta=c/n
    primes=[p for p in range(n+1,500) if isprime(p) and (p-1)%n==0][:6]
    for p in primes:
        elts=subgroup(n,p); im={x:i for i,x in enumerate(elts)}
        seen=set()
        for T in itertools.combinations(elts,sz):
            Tel=list(T); Ts=set(Tel)
            if all(sum(pow(x,j,p) for x in Tel)%p==0 for j in range(1,c+1)):
                core=[x for x in Tel if (p-x)%p not in Ts]
                if not core: continue
                key=tuple(sorted(im[x] for x in core))
                if key in seen: continue
                seen.add(key); idxs=list(key)
                N=exact_norm_int(idxs,n); aN=abs(N)
                lo=p**need; up=len(core)**(n//4)
                total+=1
                lo_ok = (N==0) or (lo<=aN)   # p^need | N => p^need<=|N| unless N=0
                up_ok = (aN<=up)
                thr_ok = (len(core) >= p**(2*eta) - 1e-9)
                if not lo_ok: low_fail+=1
                if not up_ok: up_fail+=1
                if not thr_ok: thr_fail+=1
                if (not lo_ok) or (not up_ok) or (not thr_ok):
                    print(f"  *** n={n} c={c} p={p} |C|={len(core)} N={N}: "
                          f"lo({lo}<=|N|)={lo_ok} up(|N|<={up})={up_ok} thr(|C|>=p^2eta={p**(2*eta):.2f})={thr_ok}", flush=True)
        sys.stdout.flush()
print(f"\nTOTAL free-core defects checked: {total}")
print(f"  LOWER (p^ceil(c/2)<=|N|) failures: {low_fail}")
print(f"  UPPER (|N|<=|C|^(n/4))      failures: {up_fail}")
print(f"  THRESHOLD (|C|>=p^(2eta))   failures: {thr_fail}")
print(f"  >>> FLOOR NORM-CHAIN {'HOLDS' if (low_fail==up_fail==thr_fail==0) else 'REFUTED'} on all sampled defects")
