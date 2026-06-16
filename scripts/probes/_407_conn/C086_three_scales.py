#!/usr/bin/env python3
"""
C086 attack: "E(G)=3n^2-3n (SidonModNeg, r=2) and its hypothesis are the SAME char-p
coincidence wall that gates the all-witness count AND the Gauss-period (deep-moment) house."

The connection asserts ONE Prop `NoShortVanishingRelation mu_n p` gates FOUR faces:
  (1) SidonModNeg  (E(G)=3n^2-3n exactly)        <- r=2  / support<=4 +-1 relation
  (2) all-witness fit/unfit dichotomy            <- divided-difference fit, ~degree-2
  (3) e_2=0 algebraic rigidity (claims NO BGK)    <- resultant-height threshold c ~ n^3
  (4) deep-moment anomaly W-anomaly (BGK house)   <- 2r ~ 2 log q  (DEEP)

KEY honest question (after C033 already split count<->energy by factor beta*H(rho)):
SidonModNeg is the r=2 / additive-energy face -- the SHALLOWEST possible. Is its char-p
onset at the SAME prime scale as the deep-moment (BGK) anomaly onset?  If SidonModNeg
fails (E > 3n^2-3n) at a much SMALLER prime / much lower beta than the deep-moment
anomaly needs, the "same wall" claim is FALSE: r=2 and r~log q are different scales.

We measure, exactly, for dyadic mu_n at PROPER-subgroup primes:
  (A) SIDON face (r=2): the energy excess E^{Fp}(mu_n) - (3n^2-3n).  excess>0  <=>
      SidonModNeg fails <=> a genuine support-<=4 +-1 relation vanishes mod p.
      Report the minimal support of any GENUINE (nonzero in C) such relation.
  (B) DEEP face (r): minimal r with E_r^{Fp}(mu_n) > E_r^{char0}(mu_n)  (first non-Wick
      mod-p collision = the W-anomaly onset).  Relation length 2r.
We then ask: is support_A == 2r_B?  And how do BOTH compare to the prize-regime
deep depth 2 log q?
"""
import itertools
from math import comb, log2, log
from collections import Counter

def isprime(m):
    if m < 2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if m % p == 0: return m == p
    d = m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x = pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x = x*x%m
            if x==m-1: break
        else: return False
    return True

def factorize(m):
    fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    return fs

def primitive_root(q):
    facs=factorize(q-1)
    for g in range(2,q):
        if all(pow(g,(q-1)//p,q)!=1 for p in facs): return g
    raise RuntimeError

def mu_subgroup(q,n):
    assert (q-1)%n==0
    g=primitive_root(q); h=pow(g,(q-1)//n,q)
    P=[]; x=1
    for _ in range(n): P.append(x); x=x*h%q
    assert len(set(P))==n
    return P

# ---- char-0 reduction of {-1,0,1}-combo of zeta_n powers, n=2^mu, minpoly X^{n/2}+1 ----
def char0_reduce(coeffs,n):
    half=n//2; red=[0]*half
    for j,c in enumerate(coeffs):
        if c==0: continue
        jj=j%n; sign=1
        while jj>=half: jj-=half; sign=-sign
        red[jj]+=sign*c
    return red
def char0_is_zero(coeffs,n):
    return all(v==0 for v in char0_reduce(coeffs,n))

# ---- (A) SIDON face: exact additive energy E^{Fp}(mu_n) and the excess vs 3n^2-3n ----
def energy_fp(P,q):
    rc=Counter()
    for a in P:
        for b in P:
            rc[(a+b)%q]+=1
    return sum(v*v for v in rc.values())

def min_genuine_support4_relation(P,q,n):
    """smallest support s in {2,3,4} of a GENUINE (vanish mod q, nonzero in C) +-1 relation.
    SidonModNeg failure <=> such a relation at support exactly 3 or 4 (a+b=c+d nontrivial,
    a+b!=0) i.e. support-4 signed; or a 3-term a+b=c => support 3."""
    for s in range(2, 5):
        for positions in itertools.combinations(range(n), s):
            for signs_rest in itertools.product((1,-1), repeat=s-1):
                signs=(1,)+signs_rest
                val=0
                for pos,sg in zip(positions,signs):
                    val=(val+sg*P[pos])%q
                if val%q==0:
                    coeffs=[0]*n
                    for pos,sg in zip(positions,signs): coeffs[pos]=sg
                    if not char0_is_zero(coeffs,n):
                        return s,list(zip(positions,signs))
    return None,None

# ---- (B) DEEP face: E_r^{Fp} vs E_r^{char0}, first non-Wick mod-p collision ----
def E_r_modq(P,q,r):
    base=Counter(P); dist=Counter({0:1})
    for _ in range(2*r):
        nd=Counter()
        for s,c in dist.items():
            for v,cv in base.items():
                nd[(s+v)%q]+=c*cv
        dist=nd
    return dist[0]
def E_r_char0(n,r):
    half=n//2; m=2*r
    w=[0]*(m+1)
    for k in range(0,m+1):
        if k%2==0: w[k]=comb(k,k//2)
    dp=[0]*(m+1); dp[0]=1
    for _c in range(half):
        nd=[0]*(m+1)
        for used in range(m+1):
            if dp[used]==0: continue
            for k in range(0,m-used+1):
                if w[k]==0 and k!=0: continue
                nd[used+k]+=dp[used]*comb(m-used,k)*w[k]
        dp=nd
    return dp[m]
def deep_onset(P,q,n,max_r=5):
    for r in range(1,max_r+1):
        Efp=E_r_modq(P,q,r); E0=E_r_char0(n,r)
        if Efp>E0: return r,Efp,E0
    return None,None,None

def H(rho):
    return -rho*log2(rho)-(1-rho)*log2(1-rho) if 0<rho<1 else 0.0

def run():
    print("="*100)
    print("C086: SIDON (r=2) face vs DEEP-MOMENT (BGK) face -- SAME char-p wall?")
    print("="*100)
    # For each n, scan proper-subgroup primes upward; find where SidonModNeg FIRST fails
    # (E^{Fp} > 3n^2-3n) and where the deep-moment anomaly first appears.
    for n in [8, 16, 32]:
        mu=int(round(log2(n)))
        sid_floor=3*n*n-3*n
        print(f"\n=== n={n} (mu={mu}), Sidon floor 3n^2-3n = {sid_floor} ===")
        # collect proper-subgroup primes q = 1 mod n with n^2 < q (proper, n<<sqrt q desired)
        primes=[]
        q=n+1
        while len(primes)<60 and q < (n**4 if n<=16 else n**3):
            if isprime(q): primes.append(q)
            q+=n
        first_sidon_fail=None; first_deep=None
        rows=[]
        for q in primes:
            if q<=n*n: continue  # require proper-ish; skip tiny
            P=mu_subgroup(q,n)
            beta=log(q)/log(n)
            Efp=energy_fp(P,q)
            excess=Efp-sid_floor
            sid_fail = excess>0
            sup,rel = (None,None)
            if sid_fail:
                sup,rel=min_genuine_support4_relation(P,q,n)
            er,Efpr,E0=deep_onset(P,q,n,max_r=5)
            rows.append((q,beta,excess,sup,er))
            if sid_fail and first_sidon_fail is None:
                first_sidon_fail=(q,beta,excess,sup,rel)
            if er is not None and first_deep is None:
                first_deep=(q,beta,er,Efpr,E0)
        # print a compact scan: first few + the onset rows
        print(f"  scanned {len(rows)} proper primes in [{rows[0][0] if rows else '-'}, {rows[-1][0] if rows else '-'}]")
        if first_sidon_fail:
            q,beta,exc,sup,rel=first_sidon_fail
            print(f"  [SIDON r=2] FIRST excess>0 at q={q} (beta={beta:.2f}): excess={exc}, "
                  f"genuine relation support={sup}, rel={rel}")
        else:
            print(f"  [SIDON r=2] NO excess>0 found over scanned proper primes (SidonModNeg holds throughout)")
        if first_deep:
            q,beta,er,Efpr,E0=first_deep
            print(f"  [DEEP r] FIRST non-Wick collision at q={q} (beta={beta:.2f}): r={er} "
                  f"(2r={2*er}), E_r^Fp={Efpr} > E_r^char0={E0}")
        else:
            print(f"  [DEEP r] NO deep anomaly up to r=5 over scanned proper primes")
        # cross-tab: at primes where BOTH measured, do they coincide?
        both=[(q,b,exc,sup,er) for (q,b,exc,sup,er) in rows if exc>0 and er is not None]
        if both:
            print(f"  [CROSS] primes with BOTH sidon-fail AND deep-anomaly: {len(both)}")
            for (q,b,exc,sup,er) in both[:5]:
                print(f"     q={q} beta={b:.2f}: sidon support={sup} (length<=4)  vs  deep 2r={2*er}  "
                      f"=> same? {sup==2*er}")
        # primes where sidon fails but NO deep anomaly (decisive: r=2 shallower than deep)
        only_sidon=[(q,b,exc,sup) for (q,b,exc,sup,er) in rows if exc>0 and er is None]
        only_deep=[(q,b,er) for (q,b,exc,sup,er) in rows if exc==0 and er is not None]
        print(f"  [SPLIT] sidon-fail-but-no-deep-anomaly: {len(only_sidon)} primes | "
              f"deep-anomaly-but-sidon-OK: {len(only_deep)} primes")
        if only_sidon[:3]:
            print(f"     e.g. sidon-fail-only: {[(q,round(b,2)) for (q,b,exc,sup) in only_sidon[:5]]}")
        if only_deep[:3]:
            print(f"     e.g. deep-only:       {[(q,round(b,2)) for (q,b,er) in only_deep[:5]]}")

    print("\n"+"="*100)
    print("SCALE COMPARISON in TRUE prize regime (q ~ n^4.5, eps*=2^-128, q eps* ~ n):")
    print("  SIDON r=2 face: support<=4 relation = FIXED length 4 (independent of n)")
    print("  COUNT/floor face (C033): s* ~ 2.5 log2 n")
    print("  DEEP/BGK face:  2r ~ 2 log2 q = 2*beta*log2 n  (grows with beta and n)")
    for n in [8,16,32,2**30,2**32]:
        ln=log2(n)
        print(f"   n={n}: sidon len=4 (fixed) | count s*={2.465*ln:.1f} | deep 2r={2*4.5*ln:.0f}")
    print("="*100)

if __name__=="__main__":
    run()
