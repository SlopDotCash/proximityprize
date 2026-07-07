#!/usr/bin/env python3
"""
#466 LANE F1 -- floor-successor-as-norm: EXACT char-0 obstruction norm.

For n = 2^k the cyclotomic field is Q(zeta_n) with Phi_n(x) = x^{n/2} + 1, so
Z[zeta_n] arithmetic is elementary: zeta^{n/2} = -1.

Predicate (floor_scan_poly.c semantics): points x_j = zeta^j (char-0 lift of g0^j).
  A subset A of Z/n is a floor-bad witness at p iff, with
    V_A(t) = prod_{j in A} (t - zeta^j)   (monic, deg |A| = 5n/8),
    r(t)   = t^{3n/4} mod V_A(t)          (deg < |A|),
  all obstruction coeffs r_k, k in [n/2+1, |A|-1], vanish mod P=(p, zeta - g0).

CHAR-0 MECHANISM: r_k(A) is an algebraic integer in Z[zeta_n]. Realizable at p
=> p | Norm_{Q(zeta_n)/Q}(r_k(A)) = Res(Phi_n, r_k) in Z. This is p-INDEPENDENT.

This probe:
  (a) recomputes the n=16 witnesses (mod-17 enum), prints Norm(r_9) factorization
      for all realizable patterns AND a sample of non-realizable ones;
  (b) does the same at n=32 (orbit rep from round-7);
  (c) computes the obstruction norms for a CANONICAL adjacent-7th-type pattern at
      n=64 in char-0 (no 2.2e15 scan) and reads off the ==1-mod-64 prime factor.
  (d) tests the uniform conjecture: the unique ==1-mod-n prime factor of the
      obstruction norm(s) == least prime ==1 mod n = p_min(n).
"""
import sys
from itertools import combinations
from sympy import factorint, resultant, symbols, Poly, ZZ

# ----------------------------------------------------------------------------
# mod-p realizability enumeration (to FIND the n=16 witnesses), from structure probe
# ----------------------------------------------------------------------------
def isprime(n):
    if n < 2: return False
    d = 2
    while d*d <= n:
        if n % d == 0: return False
        d += 1
    return True

def generator(p):
    m = p-1; fac = []; mm = m; d = 2
    while d*d <= mm:
        if mm % d == 0:
            fac.append(d)
            while mm % d == 0: mm //= d
        d += 1
    if mm > 1: fac.append(mm)
    for h in range(2, p):
        if all(pow(h, (p-1)//q, p) != 1 for q in fac):
            return h
    raise RuntimeError("no generator")

def setup_modp(p, n):
    g = generator(p); g0 = pow(g, (p-1)//n, p)
    return [pow(g0, j, p) for j in range(n)]

def realizable_modp(A, Xpow, p, half, deg34):
    # V = prod (x - root); r = x^deg34 mod V; check r_k==0 for k in [half+1, |A|-1]
    V = [1]
    for j in A:
        root = Xpow[j]; newV = [0]*(len(V)+1)
        for i, c in enumerate(V):
            newV[i] = (newV[i] - root*c) % p
            newV[i+1] = (newV[i+1] + c) % p
        V = newV
    D = len(V)-1
    r = [(-V[k]) % p for k in range(D)]
    for _ in range(deg34 - D):
        top = r[D-1]; nr = [0]*D
        for k in range(D-1, 0, -1):
            nr[k] = (r[k-1] - top*V[k]) % p
        nr[0] = (-top*V[0]) % p
        r = nr
    return all(r[k] == 0 for k in range(half+1, D))

def enumerate_realizable(p, n):
    m = n//4; half = n//2; deg34 = 3*n//4
    agr_min = m - m//4; agr_maj = m - m//2
    Xpow = setup_modp(p, n)
    cls = [[j for j in range(n) if j % 4 == c] for c in range(4)]
    cmin = list(combinations(range(m), agr_min))
    cmaj = list(combinations(range(m), agr_maj))
    found = []
    for c0 in range(4):
        mn0, mn1, mj0, mj1 = c0, (c0+1)%4, (c0+2)%4, (c0+3)%4
        for a in cmin:
            for b in cmin:
                for d in cmaj:
                    for e in cmaj:
                        A = [cls[mn0][i] for i in a] + [cls[mn1][i] for i in b] + \
                            [cls[mj0][i] for i in d] + [cls[mj1][i] for i in e]
                        if realizable_modp(sorted(A), Xpow, p, half, deg34):
                            found.append(tuple(sorted(A)))
    return found

# ----------------------------------------------------------------------------
# Z[zeta_n] char-0 arithmetic for n = 2^k  (Phi_n = x^{n/2}+1, zeta^{n/2} = -1)
# element = list of n//2 python ints (exact, arbitrary precision)
# ----------------------------------------------------------------------------
def zmono(j, half):
    """zeta^j as an element (list length half). half = n//2."""
    n = 2*half
    j %= n
    e = [0]*half
    if j < half:
        e[j] = 1
    else:
        e[j-half] = -1   # zeta^{half+r} = -zeta^r
    return e

def zadd(a, b):
    return [x+y for x, y in zip(a, b)]

def zsub(a, b):
    return [x-y for x, y in zip(a, b)]

def zmul(a, b, half):
    """multiply two Z[zeta] elements, reduce mod x^half + 1."""
    raw = [0]*(2*half-1)
    for i, ai in enumerate(a):
        if ai == 0: continue
        for j, bj in enumerate(b):
            if bj == 0: continue
            raw[i+j] += ai*bj
    res = raw[:half] + [0]*(half - min(half, 2*half-1-half)) if False else raw[:half]
    res = raw[:half][:]  # coeffs 0..half-1
    for i in range(half, 2*half-1):
        res[i-half] -= raw[i]   # x^half = -1
    return res

def obstruction_coeffs(A, n):
    """Return list of (k, r_k) for k in obstruction range; r_k in Z[zeta_n]."""
    half = n//2
    Asz = len(A)
    deg34 = 3*n//4
    # V_A(t) = prod (t - zeta^j): list of Z[zeta] coeffs, index = power of t
    V = [[0]*half for _ in range(Asz+1)]
    V[0] = [1] + [0]*(half-1)
    curlen = 1  # current degree+1
    for j in A:
        zj = zmono(j, half)
        # new = t*V - zeta^j * V  => new[i] = V[i-1] - zj*V[i]
        new = [[0]*half for _ in range(curlen+1)]
        for i in range(curlen+1):
            hi = V[i-1] if i-1 >= 0 and i-1 < curlen else [0]*half
            lo = V[i] if i < curlen else [0]*half
            new[i] = zsub(hi, zmul(zj, lo, half))
        for i in range(curlen+1):
            V[i] = new[i]
        curlen += 1
    # now V[0..Asz] monic (V[Asz] == 1)
    # divide t^deg34 by V (monic) -> remainder r, deg < Asz
    # represent dividend as coeff list length deg34+1
    D = Asz
    # r = t^D mod V = -(V[0..D-1])
    r = [ [ -V[k][t] for t in range(half) ] for k in range(D) ]
    for _ in range(deg34 - D):
        # multiply r by t, reduce: top = r[D-1]; r' [k] = r[k-1] - top*V[k]
        top = r[D-1]
        nr = [None]*D
        for k in range(D-1, 0, -1):
            nr[k] = zsub(r[k-1], zmul(top, V[k], half))
        nr[0] = [ -x for x in zmul(top, V[0], half) ]
        r = nr
    half_idx = n//2
    out = []
    for k in range(half_idx+1, D):
        out.append((k, r[k]))
    return out

# ----------------------------------------------------------------------------
# Norm = Res(Phi_n, a) where a(x) = sum a_i x^i, Phi_n = x^{n/2}+1
# ----------------------------------------------------------------------------
_x = symbols('x')
def znorm(a, n):
    half = n//2
    Phi = Poly([1] + [0]*(half-1) + [1], _x, domain=ZZ)  # x^half + 1
    ap = Poly(list(reversed(a)), _x, domain=ZZ) if any(a) else Poly(0, _x, domain=ZZ)
    return int(resultant(Phi, ap))

def onemod(N, n):
    """prime factors of |N| that are == 1 mod n."""
    if N == 0: return None
    f = factorint(abs(N))
    return {p: e for p, e in f.items() if p % n == 1}

def least_prime_1modn(n):
    p = n+1
    while True:
        if isprime(p): return p
        p += n

# ----------------------------------------------------------------------------
def analyze_pattern(A, n, label=""):
    obs = obstruction_coeffs(A, n)
    norms = []
    for k, rk in obs:
        N = znorm(rk, n)
        norms.append((k, N, factorint(abs(N)) if N else {}, onemod(N, n)))
    return norms

def report(A, n, tag):
    norms = analyze_pattern(A, n)
    onemods = set()
    print(f"  [{tag}] A={tuple(A)}")
    for k, N, fac, om in norms:
        facs = "*".join(f"{p}^{e}" if e > 1 else f"{p}" for p, e in sorted(fac.items()))
        print(f"     r_{k}: Norm = {N}  = {facs}   (==1 mod {n} factors: {om})")
        if om: onemods |= set(om.keys())
    return onemods

if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"

    if what in ("all", "16"):
        n = 16
        print(f"\n########## n={n}  (p_min = {least_prime_1modn(n)}) ##########")
        found = enumerate_realizable(17, n)
        print(f"n=16 p=17: {len(found)} realizable patterns (expect 160)")
        allom = set()
        distinct_norms = {}
        for A in found:
            norms = analyze_pattern(list(A), n)
            key = tuple(N for _, N, _, _ in norms)
            distinct_norms.setdefault(key, []).append(A)
            for k, N, fac, om in norms:
                if om: allom |= set(om.keys())
        print(f"  distinct obstruction-norm tuples across 160 realizable: {len(distinct_norms)}")
        for key, pats in distinct_norms.items():
            fac = factorint(abs(key[0]))
            facs = "*".join(f"{p}^{e}" if e>1 else f"{p}" for p,e in sorted(fac.items()))
            print(f"    Norm(r_9) = {key[0]} = {facs}  [{len(pats)} patterns]")
        print(f"  UNION of ==1-mod-{n} prime factors over all realizable: {sorted(allom)}")
        print(f"  p_min({n}) = {least_prime_1modn(n)}")

        # non-realizable sample: same structured family, different picks
        print("  --- non-realizable structured patterns (norm comparison) ---")
        m=n//4; agr_min=m-m//4; agr_maj=m-m//2
        cls=[[j for j in range(n) if j%4==c] for c in range(4)]
        cmin=list(combinations(range(m),agr_min)); cmaj=list(combinations(range(m),agr_maj))
        Xp=setup_modp(17,n); half=n//2; deg34=3*n//4
        shown=0
        for a in cmin:
          for b in cmin:
            for d in cmaj:
              for e in cmaj:
                A=sorted([cls[0][i] for i in a]+[cls[1][i] for i in b]+[cls[2][i] for i in d]+[cls[3][i] for i in e])
                if not realizable_modp(A,Xp,17,half,deg34):
                    report(A,n,"NONreal")
                    shown+=1
                if shown>=4: break
              if shown>=4: break
            if shown>=4: break
          if shown>=4: break

    if what in ("all", "32"):
        n = 32
        print(f"\n########## n={n}  (p_min = {least_prime_1modn(n)}) ##########")
        reps = [
            (0,1,3,4,8,9,10,11,12,13,14,15,16,17,21,22,24,25,27,30),
            (0,4,5,6,7,8,9,10,11,12,13,17,18,20,21,23,26,28,29,31),
            (0,1,2,3,4,5,6,7,8,9,13,14,16,17,19,22,24,25,27,28),
        ]
        allom=set()
        for A in reps:
            om = report(sorted(A), n, "n32rep")
            allom |= om
        print(f"  UNION of ==1-mod-{n} prime factors: {sorted(allom)}")
        print(f"  p_min({n}) = {least_prime_1modn(n)}")

    if what in ("all", "64"):
        n = 64
        print(f"\n########## n={n}  (p_min = {least_prime_1modn(n)}) -- CHAR-0, NO SCAN ##########")
        # canonical adjacent-7th-type pattern: c0=0; minority classes 0,1 take first
        # agr_min positions, majority classes 2,3 take first agr_maj positions.
        m=n//4; agr_min=m-m//4; agr_maj=m-m//2
        cls=[[j for j in range(n) if j%4==c] for c in range(4)]
        def canon(pmin_sel, pmaj_sel):
            return sorted([cls[0][i] for i in pmin_sel[0]]+[cls[1][i] for i in pmin_sel[1]]
                          +[cls[2][i] for i in pmaj_sel[0]]+[cls[3][i] for i in pmaj_sel[1]])
        A = canon((range(agr_min),range(agr_min)),(range(agr_maj),range(agr_maj)))
        print(f"  canonical A ({len(A)} pts) = {tuple(A)}")
        om = report(A, n, "n64canon")
        print(f"  ==1-mod-{n} prime factors: {sorted(om)}")
        print(f"  p_min({n}) = {least_prime_1modn(n)}")

    if what == "anneal64":
        # targeted anneal to find a REALIZABLE pattern at n=64, p given (default 193)
        import random
        n = 64; p = int(sys.argv[2]) if len(sys.argv) > 2 else 193
        if not (isprime(p) and (p-1) % n == 0):
            print(f"p={p} not prime==1 mod {n}"); sys.exit(1)
        m=n//4; half=n//2; deg34=3*n//4
        agr_min=m-m//4; agr_maj=m-m//2
        Xp=setup_modp(p,n)
        cls=[[j for j in range(n) if j%4==c] for c in range(4)]
        def energy(A):
            V=[1]
            for j in A:
                root=Xp[j]; nV=[0]*(len(V)+1)
                for i,c in enumerate(V):
                    nV[i]=(nV[i]-root*c)%p; nV[i+1]=(nV[i+1]+c)%p
                V=nV
            D=len(V)-1; r=[(-V[k])%p for k in range(D)]
            for _ in range(deg34-D):
                top=r[D-1]; nr=[0]*D
                for k in range(D-1,0,-1): nr[k]=(r[k-1]-top*V[k])%p
                nr[0]=(-top*V[0])%p; r=nr
            return sum(1 for k in range(half+1,D) if r[k]!=0)
        rng=random.Random(int(sys.argv[3]) if len(sys.argv)>3 else 12345)
        restarts=int(sys.argv[4]) if len(sys.argv)>4 else 200
        best=999; found=None
        for R in range(restarts):
            c0=rng.randrange(4)
            classes=[c0,(c0+1)%4,(c0+2)%4,(c0+3)%4]
            agr=[agr_min,agr_min,agr_maj,agr_maj]
            sel=[rng.sample(range(m),agr[i]) for i in range(4)]
            def build(sel):
                A=[]
                for ci,c in enumerate(classes):
                    for i in sel[ci]: A.append(cls[c][i])
                return sorted(A)
            E=energy(build(sel)); stagn=0
            while stagn<3000:
                if E==0: found=build(sel); break
                ci=rng.randrange(4); cur=sel[ci]
                miss=[x for x in range(m) if x not in cur]
                pos=rng.randrange(len(cur)); c2=cur[:]; c2[pos]=rng.choice(miss)
                s2=sel[:]; s2[ci]=c2; E2=energy(build(s2))
                if E2<=E:
                    if E2<E: stagn=0
                    else: stagn+=1
                    sel=s2; E=E2
                else: stagn+=1
            if E<best:
                best=E; print(f"  restart {R}: best E={best}")
            if found: break
        if found:
            print(f"  REALIZABLE at p={p}: A={tuple(found)}")
            om=report(found,n,"n64REAL")
            print(f"  ==1-mod-64 primes: {sorted(om)}")
        else:
            print(f"  NO realizable found at p={p} in {restarts} restarts (bestE={best})")
