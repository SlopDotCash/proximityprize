#!/usr/bin/env python3
"""SYZ39 -- bad-prime law + cyclotomic factor structure of SylvesterInjective.

The rate-1/2 proximity-strip residual (SYZ38) is the injectivity of the
generalized Sylvester map for a pairwise-coprime band triple (W_AB,W_AC,W_BC)
over a mu_n domain.  Equivalent evaluation form:

  SylvesterInjective FAILS  <=>  the d_AB x (b_AC+b_BC+2) evaluation matrix
      M[row=root rho of W_AB][col] with
         cols 0..b_AC   :  W_AC(rho) * rho^j
         cols b_AC+1..  : -W_BC(rho) * rho^j
      does NOT have full column rank.

All entries are cyclotomic integers in Z[omega_n].  Over a field GF(p)
containing mu_n, "bad prime" = rank drops mod p.  In char 0 the obstruction is
the gcd-of-maximal-minors ideal; bad rational primes divide Norm(any nonzero
maximal minor).  We:

  (1) GF(p) rank scan over p = 1 mod n to enumerate ACTUAL bad primes per config
      (reproduces the known n=13,k=7 p=31 flip);
  (2) exact cyclotomic-integer computation of a maximal minor, its norm
      Res(Phi_n, minor) in Z, and its factorization  ->  the SIZE BOUND and the
      factor structure (does it factor through cyclotomic norms of root
      differences?);
  (3) structural read: are the bad primes exactly the primes dividing small
      cyclotomic quantities (differences of roots of unity)?

Pure stdlib.
"""
import itertools, math
from fractions import Fraction

# ----------------------------------------------------------------------------
# cyclotomic polynomial Phi_n over Z  (integer coeff list, low->high)
# ----------------------------------------------------------------------------
def poly_divmod_int(a, b):
    a = a[:]; db = len(b)-1
    q = [0]*(max(len(a)-db,0))
    while len(a)-1 >= db and any(a):
        d = len(a)-1
        if a[d] == 0:
            a.pop(); continue
        assert a[d] % b[db] == 0, "non-exact"
        c = a[d]//b[db]; q[d-db] = c
        for i in range(db+1):
            a[d-db+i] -= c*b[i]
        a.pop()
    while len(a)>1 and a[-1]==0: a.pop()
    return q, a

def cyclotomic(n):
    # Phi_n(x) = prod_{d|n} (x^d - 1)^mu(n/d); compute by successive division.
    # start with x^n - 1, divide by Phi_d for proper divisors d|n.
    from functools import lru_cache
    @lru_cache(None)
    def phi(m):
        num = [-1]+[0]*(m-1)+[1]  # x^m - 1
        for d in range(1, m):
            if m % d == 0:
                q,_ = poly_divmod_int(num, phi(d))
                num = q
        return tuple(num)
    return list(phi(n))

# ----------------------------------------------------------------------------
# Z[omega]:  element = integer list mod Phi_n (deg < phi(n)); omega = x
# ----------------------------------------------------------------------------
class Cyc:
    def __init__(self, n, phin, coeffs):
        self.n=n; self.phin=phin
        self.c=self._red(coeffs)
    def _red(self, a):
        a=[int(x) for x in a]
        db=len(self.phin)-1
        while len(a)-1>=db and any(a[db:]):
            d=len(a)-1
            if a[d]==0: a.pop(); continue
            c=a[d]  # phin monic
            for i in range(db+1):
                a[d-db+i]-=c*self.phin[i]
            a.pop()
        while len(a)>1 and a[-1]==0: a.pop()
        return a
    def __add__(s,o):
        m=max(len(s.c),len(o.c)); a=[0]*m
        for i,x in enumerate(s.c):a[i]+=x
        for i,x in enumerate(o.c):a[i]+=x
        return Cyc(s.n,s.phin,a)
    def __sub__(s,o):
        m=max(len(s.c),len(o.c)); a=[0]*m
        for i,x in enumerate(s.c):a[i]+=x
        for i,x in enumerate(o.c):a[i]-=x
        return Cyc(s.n,s.phin,a)
    def __mul__(s,o):
        a=[0]*(len(s.c)+len(o.c)-1)
        for i,x in enumerate(s.c):
            if x:
                for j,y in enumerate(o.c): a[i+j]+=x*y
        return Cyc(s.n,s.phin,a)
    def is_zero(s): return not any(s.c)

def omega_pow(n, phin, e):
    e%=n
    return Cyc(n,phin,[0]*e+[1])

# ----------------------------------------------------------------------------
# integer resultant Res(A,B) via subresultant-free pseudo-euclid (exact, Z)
# Norm_{Q(w)/Q}(f(w)) = Res(Phi_n, f)  (Phi_n monic)  -> integer.
# ----------------------------------------------------------------------------
def deg(a):
    d=len(a)-1
    while d>0 and a[d]==0: d-=1
    return d if any(a) else -1

def resultant_int(A,B):
    # A,B integer coeff lists low->high.  Use rational Euclid then clear:
    # simpler: use fraction-based Euclid, Res via product of leading coeffs.
    A=[Fraction(x) for x in A]; B=[Fraction(x) for x in B]
    def d(p):
        k=len(p)-1
        while k>0 and p[k]==0:k-=1
        return k if any(p) else -1
    res=Fraction(1); s=1
    a,b=A,B
    while d(b)>0 or (d(b)==0 and b[0]!=0):
        da,db=d(a),d(b)
        if db<0: return 0
        # a mod b
        lead_b=b[db]
        r=a[:]
        while d(r)>=db and d(r)>=0:
            dr=d(r); coef=r[dr]/lead_b
            for i in range(db+1):
                r[dr-db+i]-=coef*b[i]
            while len(r)>1 and r[-1]==0: r.pop()
            if not any(r): r=[Fraction(0)]; break
        dr=d(r)
        # res *= lead_b^(da-dr) * (-1)^(da*db)
        res*= lead_b**(da-dr) * Fraction((-1)**(da*db))
        a,b=b,r
        if not any(b):
            # gcd nontrivial -> resultant 0
            return 0
    db=d(b)
    res*= b[0]**d(a)
    assert res.denominator==1
    return int(res)

def resultant_mod(A,B,q):
    """Res(A,B) mod q for integer polys A,B (low->high), via Euclid in GF(q)."""
    a=[x%q for x in A]; b=[x%q for x in B]
    def d(p):
        k=len(p)-1
        while k>0 and p[k]%q==0: k-=1
        return k if any(x%q for x in p) else -1
    res=1
    while True:
        db=d(b)
        if db<0: return 0            # gcd nontrivial -> resultant 0
        da=d(a)
        if db==0:
            res=res*pow(b[0]%q, da, q)%q
            return res%q
        # a mod b  in GF(q)
        r=[x%q for x in a]; lb=b[db]; ilb=pow(lb,q-2,q)
        while d(r)>=db:
            dr=d(r); coef=r[dr]*ilb%q
            for i in range(db+1):
                r[dr-db+i]=(r[dr-db+i]-coef*b[i])%q
            if d(r)==dr:  # safety
                r[dr]=0
        dr=d(r)
        # res *= lb^(da-dr) * (-1)^(da*db)
        res=res*pow(lb,da-dr,q)%q
        if (da*db)%2: res=(-res)%q
        a,b=b,r

def factorize(m):
    m=abs(m); f={}
    d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d+=1 if d==2 else 2
    if m>1: f[m]=f.get(m,0)+1
    return f

# ----------------------------------------------------------------------------
# GF(p) linear algebra
# ----------------------------------------------------------------------------
def rank_mod(rows, ncols, p):
    M=[[x%p for x in r] for r in rows]; r=0; nr=len(M)
    for c in range(ncols):
        piv=next((i for i in range(r,nr) if M[i][c]%p),None)
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]
        ic=pow(M[r][c],p-2,p); M[r]=[(x*ic)%p for x in M[r]]
        for i in range(nr):
            if i!=r and M[i][c]%p:
                f=M[i][c]; M[i]=[(M[i][j]-f*M[r][j])%p for j in range(ncols)]
        r+=1
        if r==nr: break
    return r

def roots_of_unity(n,p):
    if (p-1)%n: return None
    for cand in range(2,p):
        w=pow(cand,(p-1)//n,p)
        if all(pow(w,d,p)!=1 for d in range(1,n)):
            return [pow(w,i,p) for i in range(n)]
    return None

def primes_1modn(n, cnt, start=3):
    out=[]; p=start
    while len(out)<cnt:
        p+=1
        if p%n==1 and all(p%q for q in range(2,int(p**.5)+1)): out.append(p)
    return out

# ----------------------------------------------------------------------------
# build the evaluation Sylvester matrix (over GF(p) or over Z[omega])
# roots of W_AB : indices in (CA&CB)\T ; ring generator omega^i
# W_AC(rho)*rho^j  and  -W_BC(rho)*rho^j
# ----------------------------------------------------------------------------
def band_config(n, s, iAB, iAC, iBC):
    """Return index sets for one 'generic-position' band triple with the given
    pairwise-overlap sizes and empty triple intersection (T=empty), realised as
    disjoint blocks inside {0..n-1}."""
    # layout: [AB-block][AC-block][BC-block][A-only][B-only][C-only]
    need = iAB+iAC+iBC
    if need>n: return None
    AB=list(range(0,iAB)); AC=list(range(iAB,iAB+iAC)); BC=list(range(iAB+iAC,need))
    rest=list(range(need,n))
    # sizes: |CA|=|CB|=|CC|=s ; CA=AB+AC+Aonly ; CB=AB+BC+Bonly ; CC=AC+BC+Conly
    aA=s-iAB-iAC; aB=s-iAB-iBC; aC=s-iAC-iBC
    if min(aA,aB,aC)<0: return None
    if aA+aB+aC>len(rest): return None
    Aonly=rest[:aA]; Bonly=rest[aA:aA+aB]; Conly=rest[aA+aB:aA+aB+aC]
    CA=set(AB+AC+Aonly); CB=set(AB+BC+Bonly); CC=set(AC+BC+Conly)
    return CA,CB,CC

def eval_matrix_modp(WABroots, WAC_idx, WBC_idx, bAC, bBC, w, p):
    rows=[]
    for i in WABroots:
        rho=pow(w,i,p)
        wac=1
        for a in WAC_idx: wac=wac*((rho-pow(w,a,p))%p)%p
        wbc=1
        for a in WBC_idx: wbc=wbc*((rho-pow(w,a,p))%p)%p
        row=[]
        rj=1
        for j in range(bAC+1): row.append(wac*rj%p); rj=rj*rho%p
        rj=1
        for j in range(bBC+1): row.append((-wbc*rj)%p); rj=rj*rho%p
        rows.append(row)
    return rows

def eval_matrix_cyc(WABroots, WAC_idx, WBC_idx, bAC, bBC, n, phin):
    rows=[]
    for i in WABroots:
        rho=omega_pow(n,phin,i)
        wac=Cyc(n,phin,[1])
        for a in WAC_idx: wac=wac*(rho-omega_pow(n,phin,a))
        wbc=Cyc(n,phin,[1])
        for a in WBC_idx: wbc=wbc*(rho-omega_pow(n,phin,a))
        row=[]
        rj=Cyc(n,phin,[1])
        for j in range(bAC+1): row.append(wac*rj); rj=rj*rho
        rj=Cyc(n,phin,[1])
        for j in range(bBC+1): row.append(Cyc(n,phin,[0])-wbc*rj); rj=rj*rho
        rows.append(row)
    return rows

def det_cyc_ring(M, n, phin):
    """Exact determinant over the RING Z[omega] by cofactor expansion (no
    inversion). M is a square list of Cyc.  Returns a Cyc."""
    size=len(M)
    if size==1: return M[0][0]
    if size==2:
        return M[0][0]*M[1][1]-M[0][1]*M[1][0]
    acc=Cyc(n,phin,[0])
    for j in range(size):
        minor=[[M[i][c] for c in range(size) if c!=j] for i in range(1,size)]
        term=M[0][j]*det_cyc_ring(minor,n,phin)
        if j%2==0: acc=acc+term
        else: acc=acc-term
    return acc

def det_cyc(M, n, phin):
    """Determinant of a square matrix over Q(omega) (fraction of Cyc), returned
    as an integer coeff list mod Phi_n (should be integral for our matrices)."""
    # Fraction-free Bareiss over Z[omega] would need division; instead do
    # Gaussian elimination over the field Q(omega) using rational-cyclotomic.
    # Represent entries as (Fraction-coeff poly mod Phi_n). We implement inverse
    # via extended euclid mod Phi_n over Q.
    size=len(M)
    # convert to fraction-poly
    A=[[ [Fraction(x) for x in e.c] for e in row] for row in M]
    phi=[Fraction(x) for x in phin]
    def norm(p):
        p=p[:]
        while len(p)>1 and p[-1]==0: p.pop()
        return p
    def pmul(a,b):
        r=[Fraction(0)]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            if x:
                for j,y in enumerate(b): r[i+j]+=x*y
        return preduce(r)
    def psub(a,b):
        m=max(len(a),len(b)); r=[Fraction(0)]*m
        for i,x in enumerate(a): r[i]+=x
        for i,x in enumerate(b): r[i]-=x
        return norm(r)
    def preduce(a):
        a=a[:]; db=len(phi)-1
        while len(a)-1>=db and any(a[db:]):
            d=len(a)-1
            if a[d]==0: a.pop(); continue
            c=a[d]
            for i in range(db+1): a[d-db+i]-=c*phi[i]
            a.pop()
        return norm(a)
    def pdegf(a):
        d=len(a)-1
        while d>0 and a[d]==0: d-=1
        return d if any(a) else -1
    def pinv(a):
        # extended euclid: find u with a*u = 1 mod phi
        r0,r1=phi[:],preduce(a[:])
        s0,s1=[Fraction(0)],[Fraction(1)]
        while pdegf(r1)>=0 and any(r1):
            # r0 = q r1 + r2
            q=[Fraction(0)]; rem=r0[:]
            while pdegf(rem)>=pdegf(r1) and any(rem):
                dr=pdegf(rem); d1=pdegf(r1)
                coef=rem[dr]/r1[d1]
                term=[Fraction(0)]*(dr-d1)+[coef]
                q=psub([Fraction(0)]*len(q) if False else q, [ -t for t in term]) if False else q
                # q += term
                if len(q)<len(term): q=q+[Fraction(0)]*(len(term)-len(q))
                for i,t in enumerate(term): q[i]+=t
                sub=pmul(term,r1)
                rem=psub(rem,sub)
            r2=rem
            s2=psub(s0,pmul(q,s1))
            r0,r1=r1,r2; s0,s1=s1,s2
        # r0 = gcd (constant); u = s0 / r0
        c=r0[0]
        return norm([x/c for x in s0])
    # gaussian elimination
    det=[Fraction(1)]
    for col in range(size):
        piv=None
        for i in range(col,size):
            if any(A[i][col]): piv=i;break
        if piv is None: return [0]
        if piv!=col: A[col],A[piv]=A[piv],A[col]; det=[-x for x in det]
        det=pmul(det,A[col][col])
        inv=pinv(A[col][col])
        A[col]=[pmul(inv,e) for e in A[col]]
        for i in range(col+1,size):
            f=A[i][col]
            if any(f):
                A[i]=[psub(A[i][j],pmul(f,A[col][j])) for j in range(size)]
    # det should be integral cyclotomic
    return det

def cyc_norm(detpoly):
    # detpoly fraction list; must be integer -> clear & Res with Phi
    ints=[]
    for x in detpoly:
        ints.append(x)
    # if not integral, scale: but expect integral
    denom=1
    for x in ints: denom=math.lcm(denom, x.denominator)
    scaled=[int(x*denom) for x in ints]
    return scaled, denom

# ----------------------------------------------------------------------------
def analyze_config(n,k,CA,CB,CC,label,verbose=True):
    T=CA&CB&CC
    AB=(CA&CB)-T; AC=(CA&CC)-T; BC=(CB&CC)-T
    mAB,mAC,mBC,t=len(CA&CB),len(CA&CC),len(CB&CC),len(T)
    dAB=len(AB)  # deg W_AB
    bAC=k-1-mAC; bBC=k-1-mBC
    if bAC<0 or bBC<0:
        return None
    ncols=(bAC+1)+(bBC+1)
    WABroots=sorted(AB)
    WAC_idx=sorted(AC); WBC_idx=sorted(BC)
    info=dict(n=n,k=k,label=label,mAB=mAB,mAC=mAC,mBC=mBC,t=t,dAB=dAB,
              bAC=bAC,bBC=bBC,ncols=ncols,dim_ok=(ncols<=dAB))
    # --- GF(p) rank scan ---
    ps=primes_1modn(n,12)
    badps=[]
    for p in ps:
        ru=roots_of_unity(n,p)
        if ru is None: continue
        w=ru[1]
        rows=eval_matrix_modp(WABroots,WAC_idx,WBC_idx,bAC,bBC,w,p)
        rk=rank_mod(rows,ncols,p)
        if rk<ncols: badps.append(p)
    info['scanned_primes']=ps
    info['bad_primes_in_scan']=badps
    # --- char-0 minor norm (take first ncols rows if dim_ok) ---
    if info['dim_ok'] and dAB>=ncols:
        phin=cyclotomic(n)
        Mc=eval_matrix_cyc(WABroots,WAC_idx,WBC_idx,bAC,bBC,n,phin)
        phi=cyclotomic(n)
        minorpolys=[]
        rowcombos=list(itertools.combinations(range(dAB),ncols))
        for rc in rowcombos[:40]:
            sub=[Mc[i][:] for i in rc]
            detc=det_cyc_ring(sub,n,phin)
            if any(detc.c):
                minorpolys.append(detc.c)
        info['n_nonzero_minors']=len(minorpolys)
        # char-0 bad primes: q | gcd-of-minor-norms  <=>  Res(Phi_n, minor)=0 mod q
        # for EVERY minor. Scan small primes q.
        char0_bad=[]
        if minorpolys:
            for q in SMALLPRIMES:
                if all(resultant_mod(phi,mp,q)==0 for mp in minorpolys):
                    char0_bad.append(q)
        info['char0_bad_primes']=char0_bad
        # exact norm of a single minor (size bound) via CRT of Res mod primes
        if minorpolys:
            mp=minorpolys[0]
            info['single_minor_norm']=crt_resultant(phi,mp)
        else:
            info['single_minor_norm']=0
    return info

SMALLPRIMES=[p for p in range(2,20000) if all(p%d for d in range(2,int(p**.5)+1))]

def crt_resultant(A,B):
    """Exact |Res(A,B)| via CRT of resultant mod primes (Hadamard-bounded)."""
    import math as _m
    # Hadamard-ish bound on |Res| = prod |B(root_i)| <= (1+maxcoef)^deg ... just
    # accumulate primes until product stabilizes twice.
    prod=1; rem=0; primes=[]
    for q in SMALLPRIMES:
        if q<3: continue
        r=resultant_mod(A,B,q)
        # incremental CRT
        if not primes:
            rem=r; prod=q
        else:
            # solve x = rem (mod prod), x = r (mod q)
            g,inv=prod%q, None
            inv=pow(prod%q,q-2,q)
            t=((r-rem)*inv)%q
            rem=rem+prod*t; prod*=q
        primes.append(q)
        if prod>10**40: break
    # symmetric representative
    if rem>prod//2: rem-=prod
    return abs(rem)

def band_triples(n, k, cap=200):
    """Enumerate band triples as actual index subsets of {0..n-1} (T may be
    nonempty), matching the SYZ37 probe geometry."""
    pts=list(range(n))
    slo=2*n//3+1; shi=(3*n-1)//4
    for s in range(slo,shi+1):
        if s<=k: continue
        omin=max(2*s-n,0); omax=k-1
        if omin>omax: continue
        CA=frozenset(pts[:s]); cnt=0
        for CB in itertools.combinations(pts,s):
            CBs=frozenset(CB)
            if CBs==CA: continue
            if not (omin<=len(CA&CBs)<=omax): continue
            for CC in itertools.combinations(pts,s):
                CCs=frozenset(CC)
                if CCs in (CA,CBs): continue
                if not (omin<=len(CA&CCs)<=omax and omin<=len(CBs&CCs)<=omax): continue
                if len(CA|CBs|CCs)>n: continue
                yield set(CA),set(CBs),set(CCs); cnt+=1
                if cnt>=cap: return

def main():
    print("="*80)
    print("SYZ39  bad-prime law + cyclotomic structure of SylvesterInjective  (mu_n domain)")
    print("="*80)

    import sys, random
    ns = [int(x) for x in sys.argv[1:]] or [13,14,15,16]
    for n in ns:
        k=n//2 if n%2==0 else (n+1)//2  # rate ~1/2
        print(f"\n### n={n} k={k} (mu_n, primes = 1 mod {n}) ###",flush=True)
        cfgs=list(band_triples(n,k,cap=1200))
        random.Random(7).shuffle(cfgs)
        cfgs=cfgs[:120]
        dimok=0; consist_ok=True
        # aggregate per ncols: max extra-bad-prime (excluding n), max bitlen(|Res|)
        agg={}
        extra_primes=set()
        for CA,CB,CC in cfgs:
            info=analyze_config(n,k,CA,CB,CC,"")
            if info is None or not info['dim_ok'] or 'char0_bad_primes' not in info: continue
            dimok+=1
            c0=set(info['char0_bad_primes'])
            extra=sorted(c0-{n})
            extra_primes|=set(extra)
            nc=info['ncols']; bl=info['single_minor_norm'].bit_length()
            a=agg.setdefault(nc,{'cnt':0,'n_in_all':True,'maxextra':0,'maxbl':0,'exset':set()})
            a['cnt']+=1
            if n not in c0: a['n_in_all']=False
            a['maxextra']=max(a['maxextra'], max(extra) if extra else 0)
            a['maxbl']=max(a['maxbl'],bl)
            a['exset']|=set(extra)
            if not (set(info['bad_primes_in_scan'])<=c0): consist_ok=False
        print(f"  analyzed dim_ok configs: {dimok}; scan⊆char0 consistency: {consist_ok}")
        print(f"  ALL genuine extra bad primes (excl n={n}) seen: {sorted(extra_primes)}")
        print(f"  per-ncols  [ncols: cnt, n|Res always?, max_extra_prime, max_bitlen(|Res|), extra_primes]")
        for nc in sorted(agg):
            a=agg[nc]
            print(f"    ncols={nc:2d}: cnt={a['cnt']:3d} n_divides_all={a['n_in_all']} "
                  f"max_extra_prime={a['maxextra']} max_bitlen|Res|={a['maxbl']} "
                  f"extra_primes={sorted(a['exset'])[:12]}")

if __name__=="__main__":
    main()
