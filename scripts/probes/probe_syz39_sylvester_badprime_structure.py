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
containing mu_n, "bad prime" = rank drops mod p at the chosen embedding
omega -> w.  In char 0 the obstruction is the gcd-of-maximal-minors ideal: rank
loss modulo a prime IDEAL P of Z[omega] means ALL maximal minors lie in the SAME
P.  A rational prime q dividing Norm(minor) for every minor is only a NECESSARY
candidate filter: each norm can be divisible by q through a DIFFERENT prime
ideal above q (different embedding).  Example (audit finding L126): the 2x1
matrix (i-2, i+2)^T over Z[i] has both norms 5, but rank 1 modulo both primes
above 5 (i=2 and i=-2), since the entries never vanish together.  Moreover only
the first 40 nonzero maximal minors are used, which over-approximates further.

We report three distinct layers:

  (1) ACTUAL rank failures: GF(p) rank scan over p = 1 mod n at ONE chosen
      embedding w (reproduces the known n=13,k=7 p=31 flip);
  (2) NORM CANDIDATES (over-inclusive): small primes q < 20000 dividing the
      norm Res(Phi_n, minor) of each of the first 40 nonzero maximal minors;
  (3) COMMON-PRIME-IDEAL obstructions: for a candidate q = 1 mod n (q split, so
      the primes above q are (q, omega - zeta) for the primitive n-th roots zeta
      in GF(q)), the FULL matrix is reduced at every embedding zeta and its
      rank is computed exactly; q is certified iff some embedding loses rank.
      Candidates with q != 1 mod n (inert/ramified primes, residue field larger
      than GF(q)) are left UNCERTIFIED, neither confirmed nor excluded.
  plus an exact integer norm of one minor (Hadamard-bounded CRT, see
  crt_resultant) and its factorization (trial division, so the factor list is
  a complete certified factorization).

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
    if d(a)<0 or d(b)<0: return 0
    # Loop only while deg b > 0; a nonzero constant b ends with b0^deg(a) below.
    # (The earlier condition also looped on a nonzero constant b, reduced a mod b to
    # 0 and wrongly returned 0 for every coprime pair.)
    while d(b)>0:
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
        # Norm CANDIDATES: q divides Res(Phi_n, minor) for every one of the (at
        # most 40) computed minors.  Necessary for a common prime-ideal
        # obstruction, NOT sufficient (different minors may vanish at different
        # primes above q); see the module docstring.
        cands=norm_candidate_primes(phi,minorpolys,SMALLPRIMES)
        info['norm_candidate_primes']=cands
        # Common-prime-ideal certification for split candidates (q = 1 mod n),
        # using the FULL matrix at every embedding omega -> zeta.
        certified=[]; uncertified=[]
        for q in cands:
            bad_emb=common_ideal_rank_deficient_embeddings(Mc,ncols,n,q)
            if bad_emb is None: uncertified.append(q)
            elif bad_emb: certified.append(q)
        info['common_ideal_bad_primes']=certified
        info['uncertified_candidate_primes']=uncertified
        # exact norm of a single minor (size bound) via CRT of Res mod primes
        if minorpolys:
            mp=minorpolys[0]
            info['single_minor_norm']=crt_resultant(phi,mp)
        else:
            info['single_minor_norm']=0
    return info

SMALLPRIMES=[p for p in range(2,20000) if all(p%d for d in range(2,int(p**.5)+1))]

def norm_candidate_primes(phi, minorpolys, primes):
    """Primes q (from `primes`) with Res(phi, mp) = 0 mod q for EVERY minor mp.

    phi = Phi_n is monic, so resultant_mod(phi, mp, q) is the reduction of the
    integer norm Res(phi, mp) for every q.  This is an over-inclusive CANDIDATE
    list for common prime-ideal obstructions (see the module docstring).  With no
    nonzero minors there is no information and the list is empty."""
    if not minorpolys: return []
    return [q for q in primes
            if all(resultant_mod(phi,mp,q)==0 for mp in minorpolys)]

def common_ideal_rank_deficient_embeddings(Mc, ncols, n, q):
    """For a prime q = 1 mod n, return the primitive n-th roots zeta in GF(q) at
    which the matrix Mc (rows of Cyc entries in Z[omega_n]) has rank < ncols
    modulo the prime ideal (q, omega - zeta).  Rank < ncols there is equivalent
    to ALL maximal minors lying in that common prime ideal.  Returns None when
    q != 1 mod n (prime ideals above q have a residue field larger than GF(q);
    not decided by this probe)."""
    if (q-1)%n or q%n==0: return None
    ru=roots_of_unity(n,q)
    if ru is None: return None
    zetas=[z for z in ru if all(pow(z,d,q)!=1 for d in range(1,n))]
    bad=[]
    for z in zetas:
        rows=[[sum(c*pow(z,i,q) for i,c in enumerate(e.c))%q for e in row] for row in Mc]
        if rank_mod(rows,ncols,q)<ncols: bad.append(z)
    return bad

def resultant_hadamard_bound(A,B):
    """A proved bound H >= |Res(A,B)| for integer polys A,B (low->high).

    Res(A,B) is the determinant of the Sylvester matrix, which has deg(B) rows
    carrying the coefficients of A and deg(A) rows carrying those of B, so by
    Hadamard's inequality |Res| <= ||A||_2^deg(B) * ||B||_2^deg(A).  Returned as
    an integer ceiling (via an integer square root of the squared bound)."""
    da,db=deg(A),deg(B)
    if da<0 or db<0: return 0
    sq=sum(x*x for x in A[:da+1])**db * sum(x*x for x in B[:db+1])**da
    r=math.isqrt(sq)
    return r if r*r==sq else r+1

def crt_resultant(A,B):
    """Exact |Res(A,B)| via CRT of resultant mod primes, stopped only once the
    modulus exceeds 2*H for the PROVED Hadamard bound H >= |Res(A,B)|
    (resultant_hadamard_bound), so the symmetric residue is the integer itself.

    Primes dividing lc(A)*lc(B) are skipped, so the degrees used by resultant_mod
    are the true degrees and its value is the reduction of the integer
    resultant.  (A fixed 10**40 modulus cap, used before the L126 audit fix,
    was not a bound: A = X-1, B = 11992411764462614086353260819346129198106
    returned 1, because the product of the primes 3..103 is B-1.)"""
    da,db=deg(A),deg(B)
    if da<0 or db<0: return 0
    H=resultant_hadamard_bound(A,B)
    lead=A[da]*B[db]
    prod=1; rem=0
    q=2
    while prod<=2*H:
        q+=1
        if any(q%d==0 for d in range(2,math.isqrt(q)+1)): continue
        if lead%q==0: continue
        r=resultant_mod(A,B,q)
        # incremental CRT: x = rem (mod prod), x = r (mod q)
        t=((r-rem)*pow(prod%q,q-2,q))%q
        rem=rem+prod*t; prod*=q
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
        dimok=0; consist_ok=True; cert_consist_ok=True
        # aggregate per ncols: max extra norm-candidate prime (excluding n),
        # max bitlen(|Res|)
        agg={}
        extra_primes=set(); certified_primes=set(); uncertified_primes=set()
        for CA,CB,CC in cfgs:
            info=analyze_config(n,k,CA,CB,CC,"")
            if info is None or not info['dim_ok'] or 'norm_candidate_primes' not in info:
                continue
            dimok+=1
            c0=set(info['norm_candidate_primes'])
            extra=sorted(c0-{n})
            extra_primes|=set(extra)
            certified_primes|=set(info['common_ideal_bad_primes'])
            uncertified_primes|=set(info['uncertified_candidate_primes'])
            if not (set(info['bad_primes_in_scan'])<=set(info['common_ideal_bad_primes'])):
                cert_consist_ok=False
            nc=info['ncols']; bl=info['single_minor_norm'].bit_length()
            a=agg.setdefault(nc,{'cnt':0,'n_in_all':True,'maxextra':0,'maxbl':0,'exset':set()})
            a['cnt']+=1
            if n not in c0: a['n_in_all']=False
            a['maxextra']=max(a['maxextra'], max(extra) if extra else 0)
            a['maxbl']=max(a['maxbl'],bl)
            a['exset']|=set(extra)
            if not (set(info['bad_primes_in_scan'])<=c0): consist_ok=False
        print(f"  analyzed dim_ok configs: {dimok}; scan⊆norm-candidates: {consist_ok}; "
              f"scan⊆common-ideal-certified: {cert_consist_ok}")
        print(f"  norm-divisor CANDIDATE primes (excl n={n}; necessary filter only, first 40 "
              f"minors, q<20000): {sorted(extra_primes)}")
        print(f"  COMMON-PRIME-IDEAL certified bad primes (q=1 mod n, some embedding loses "
              f"rank): {sorted(certified_primes)}")
        print(f"  UNCERTIFIED candidates (q!=1 mod n, not decided): {sorted(uncertified_primes)}")
        print(f"  per-ncols  [ncols: cnt, n|Res always?, max_extra_candidate, max_bitlen(|Res|), "
              f"extra_candidates]")
        for nc in sorted(agg):
            a=agg[nc]
            print(f"    ncols={nc:2d}: cnt={a['cnt']:3d} n_divides_all={a['n_in_all']} "
                  f"max_extra_candidate={a['maxextra']} max_bitlen|Res|={a['maxbl']} "
                  f"extra_candidates={sorted(a['exset'])[:12]}")

if __name__=="__main__":
    main()
