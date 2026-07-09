"""
probe_444_angleC_orbit.py  --  Angle C: bound O_P (= #distinct nonzero dilation-orbits of the
Schur-ratio scalar gamma) DIRECTLY via the dilation-orbit / parity-split structure.

SETUP (the proven clean reduction):
  mu_n = order-n=2^mu subgroup of F_p*, p = 1 mod n large (char-0 worst case).
  Deep band depth r: agreement a0=r+1, codeword deg k=r-1, deficit 2.
  Witness LINE (x^e, x^f).  S (r+1)-subset of mu_n is BAD <=>
      h_{e-r}(S) h_{f-r+1}(S) = h_{f-r}(S) h_{e-r+1}(S)          (variety V)
  and then gamma = -h_{e-r}(S)/h_{f-r}(S).  gamma is dilation-equivariant:
      gamma(gS) = g^{e-f} gamma(S),  orbit size n/d, d=gcd(e-f,n).
  #bad = [gamma=0?] + (n/d)*O_P.

CALIBRATION ANCHOR (r=3): O_P = C(n/4,2).  Maximizer line per CONTEXT for r=3
  bilinear model is (x^{n/2}, x^{n/2-1}).

This probe:
  (1) reproduces O_P = C(n/4,2) at r=3 via the h_m Schur-ratio definition (anti-fabrication);
  (2) for each (r, n) and the TRUE maximizer line, computes the FULL set of nonzero gammas, their
      dilation-orbit decomposition, and O_P; cross-checks O_P against the CONTEXT measured values;
  (3) studies the structure of the gamma-VALUE set: is each orbit a coset of a fixed subgroup?
      what is the algebraic degree?  This is the data Angle C needs.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

PRIMES = [2013265921, 3221225473]

def mu_n(n, p):
    e = (p - 1) // n
    for c in range(2, 600):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and pow(h, n // 2, p) != 1:
            return h, [pow(h, i, p) for i in range(n)]
    raise RuntimeError("no generator")

def h_powers(elts, M, p):
    """complete-homogeneous h_0..h_M of the multiset `elts` via power sums Newton recurrence.
       h_m = (1/m) sum_{i=1}^m P_i h_{m-i},  P_i = sum z^i."""
    P = [0]*(M+1)
    for i in range(1, M+1):
        P[i] = sum(pow(z, i, p) for z in elts) % p
    H = [0]*(M+1)
    H[0] = 1
    for m in range(1, M+1):
        s = 0
        for i in range(1, m+1):
            s = (s + P[i]*H[m-i]) % p
        H[m] = (s * pow(m, p-2, p)) % p
    return H

def gamma_of_S(Spts, e, f, r, p):
    """Return gamma = -h_{e-r}/h_{f-r} if S is bad (det=0), else None.
       Returns ('zero',) for gamma=0, ('inf',) for hf=0 pin, else ('val', gamma)."""
    M = max(e-r, e-r+1, f-r, f-r+1)
    if min(e-r, f-r) < 0:
        return None
    H = h_powers(Spts, M, p)
    her, her1 = H[e-r], H[e-r+1]
    hfr, hfr1 = H[f-r], H[f-r+1]
    det = (her*hfr1 - hfr*her1) % p
    if det != 0:
        return None
    # bad. gamma = -her/hfr
    if hfr == 0:
        if her == 0:
            return ('deg',)   # fully degenerate, both zero
        return ('inf',)
    g = (-her * pow(hfr, p-2, p)) % p
    if g == 0:
        return ('zero',)
    return ('val', g)

def analyze(n, r, e, f, p, w):
    a0 = r+1
    d = gcd((e-f) % n, n)
    mult = pow(w, (e-f) % n, p)   # dilation by g acting on gamma: gamma -> g^{e-f} gamma
    nz = set(); zero=False; inf=0; deg=0
    for Sidx in combinations(range(n), a0):
        Spts = [pow(w, i, p) for i in Sidx]
        res = gamma_of_S(Spts, e, f, r, p)
        if res is None: continue
        if res[0]=='zero': zero=True
        elif res[0]=='inf': inf+=1
        elif res[0]=='deg': deg+=1
        else: nz.add(res[1])
    # orbit decomposition of nonzero gammas under gamma -> mult*gamma
    rem=set(nz); orbs=[]
    while rem:
        x=next(iter(rem)); o=[]; cur=x
        for _ in range(n//d + 1):
            if cur in rem: o.append(cur);
            cur=cur*mult%p
        # build true orbit
        o=set(); cur=x
        for _ in range(n):
            o.add(cur); cur=cur*mult%p
        orbs.append(len(o & nz)); rem-=o
    OP=len(orbs)
    K=(1<<r)*comb(n//2,r)
    bad = len(nz) + (1 if zero else 0)
    return dict(n=n,r=r,e=e,f=f,d=d,nz=len(nz),OP=OP,orbs=Counter(orbs),
                zero=zero,K=K,bad=bad,Kdn=K*d/n)

# ---- TRUE maximizer lines from CONTEXT ----
LINES = {
  3: lambda n:(n//2, n//2-1),
  4: lambda n:(n//2+2, n//4+1),
  5: lambda n:(n//2+1, n-1),
  6: lambda n:(n//2+4, n//2+2),   # (x^{n/2+4},x^{n/2+2}) -> at n=16 (12,10), n=32 (20,18): #bad-max
}
OP_EXPECT = {  # CONTEXT measured O_P
  (3,16):6,(3,32):28,
  (4,16):9,(4,32):97,(4,64):897,
  (5,16):11,(5,32):90,
  (6,16):14,(6,32):203,   # CONTEXT note: global max is 203 not 185
}

if __name__=="__main__":
    p = PRIMES[0]
    w,_ = mu_n(16,p) if False else (None,None)
    print(f"# prime p={p}")
    todo = []
    import sys
    if len(sys.argv)>1:
        # args: r,n pairs like 3:16 4:32
        for a in sys.argv[1:]:
            r,n = map(int,a.split(':')); todo.append((r,n))
    else:
        todo = [(3,16),(3,32),(4,16),(4,32),(5,16),(5,32),(6,16)]
    for (r,n) in todo:
        w,_=mu_n(n,p)
        e,f = LINES[r](n)
        res = analyze(n,r,e,f,p,w)
        exp = OP_EXPECT.get((r,n),'?')
        ok = (res['OP']==exp) if exp!='?' else None
        print(f"r={r} n={n} line(x^{e},x^{f}) d={res['d']}: O_P={res['OP']} (expect {exp} ok={ok}) "
              f"#bad={res['bad']} K={res['K']} K*d/n={res['Kdn']:.1f} "
              f"O_P<=K*d/n? {res['OP']<=res['Kdn']}  orbit-size-dist={dict(res['orbs'])}")
