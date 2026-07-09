"""
C062 control: does the EXPLICIT order-2 auxiliary Q=(c-X)^{n+1}+X^{n+1}-c ever beat
the generic degree M*|A| on the genuine OFF-DIAGONAL set A=mu_n cap (c+mu_n), c^n!=1?

Two checks:
 (1) Find c with c^n != 1 (c not in mu_n) AND |A|>=2 (so order-2 is non-trivial),
     including SMALLER fields where off-diagonal A is bigger, and compute d_min(M)
     vs M*|A|. The order-2 explicit Q proves d_min(2) <= n+1. So if |A|>=2 and the
     GENERIC degree 2|A| EXCEEDS n+1, the explicit Q is STRICTLY sub-generic ->
     the degeneracy is real -> we then test whether order 3 keeps degree ~n.
 (2) Directly VERIFY the explicit Q vanishes to order exactly 2 (not 3) on A: build Q,
     check Hasse derivatives 0,1 are 0 and Hasse derivative 2 is NOT identically 0 on A.
     If Q vanishes only to order 2, the order-3 analogue must be a DIFFERENT polynomial.
"""
import math

def is_prime(x):
    if x<2: return False
    if x%2==0: return x==2
    i=3
    while i*i<=x:
        if x%i==0: return False
        i+=2
    return True

def primitive_root_manual(p):
    m=p-1; fac=set(); d=2; mm=m
    while d*d<=mm:
        while mm%d==0: fac.add(d); mm//=d
        d+=1
    if mm>1: fac.add(mm)
    for g in range(2,p):
        if all(pow(g,m//q,p)!=1 for q in fac): return g
    return None

def mu_n(p,n):
    g=primitive_root_manual(p); w=pow(g,(p-1)//n,p)
    S=set(); x=1
    for _ in range(n): S.add(x); x=(x*w)%p
    return S

def binom_mod(i,j,p):
    if j<0 or j>i: return 0
    num=1;den=1
    for t in range(j):
        num=(num*((i-t)%p))%p; den=(den*((t+1)%p))%p
    return (num*pow(den,p-2,p))%p

def rank_mod_p(rows,ncols,p):
    mat=[r[:] for r in rows]; nrows=len(mat); pr=0; rank=0
    for col in range(ncols):
        piv=None
        for r in range(pr,nrows):
            if mat[r][col]%p!=0: piv=r;break
        if piv is None: continue
        mat[pr],mat[piv]=mat[piv],mat[pr]
        inv=pow(mat[pr][col],p-2,p)
        mat[pr]=[(v*inv)%p for v in mat[pr]]
        for r in range(nrows):
            if r!=pr and mat[r][col]%p!=0:
                f=mat[r][col]; mat[r]=[(mat[r][k]-f*mat[pr][k])%p for k in range(ncols)]
        pr+=1; rank+=1
        if pr==nrows: break
    return rank

def build_H(A,M,D,p):
    rows=[]; ncols=D+1
    for y in A:
        powy=[1]*(D+1)
        for i in range(1,D+1): powy[i]=(powy[i-1]*y)%p
        for j in range(M):
            row=[0]*ncols
            for i in range(j,D+1):
                b=binom_mod(i,j,p)
                if b: row[i]=(b*powy[i-j])%p
            rows.append(row)
    return rows,ncols

def d_min(A,M,p,Dmax):
    for D in range(0,Dmax+1):
        rows,ncols=build_H(A,M,D,p)
        if rank_mod_p(rows,ncols,p)<ncols: return D
    return None

def hasse_eval(coeffs,j,y,p):
    # Hasse derivative order j of poly with coeff list 'coeffs', evaluated at y.
    s=0
    for i in range(j,len(coeffs)):
        b=binom_mod(i,j,p)
        if b and coeffs[i]%p:
            s=(s+coeffs[i]*b*pow(y,i-j,p))%p
    return s%p

def explicit_Q_coeffs(c,n,p):
    # Q=(c-X)^{n+1}+X^{n+1}-c, coeff list deg n+1
    import math as _m
    Q=[0]*(n+2)
    # (c-X)^{n+1} = sum_k C(n+1,k) c^{n+1-k} (-1)^k X^k
    for k in range(n+2):
        term=(binom_mod(n+1,k,p)*pow(c,n+1-k,p)*pow(p-1,k,p))%p
        Q[k]=(Q[k]+term)%p
    Q[n+1]=(Q[n+1]+1)%p   # + X^{n+1}
    Q[0]=(Q[0]-c)%p       # - c
    return Q

def find_offdiag(p,S,need=2):
    res=[]
    for c in range(1,p):
        if c in S: continue   # need c^n != 1
        A=[y for y in S if ((c-y)%p) in S]
        if len(A)>=need:
            res.append((c,A))
        if len(res)>=6: break
    return res

def run(n, p):
    S=mu_n(p,n)
    print(f"\n=== n={n}, p={p} ~ n^{round(math.log(p,n),2)}  n/sqrt(p)={n/p**0.5:.4f}  (PROPER: n!=p-1={p-1}) ===")
    offs=find_offdiag(p,S,need=2)
    if not offs:
        print(f"  no off-diagonal c (c^n!=1) with |A|>=2 -> off-diag sets all Sidon (|A|<=1).")
        return
    for c,A in offs[:4]:
        r=len(A)
        # (2) verify explicit Q vanishes to order exactly 2 on A
        Q=explicit_Q_coeffs(c,n,p)
        ord_ok = all(hasse_eval(Q,0,y,p)==0 and hasse_eval(Q,1,y,p)==0 for y in A)
        ord3 = all(hasse_eval(Q,2,y,p)==0 for y in A)
        print(f"  c={c} (c^n={pow(c,n,p)}!=1) off-diag |A|=r(c)={r};  deg Q={n+1}")
        print(f"     explicit Q: vanishes order>=2 on A: {ord_ok};  also order>=3 (Hasse_2==0) on A: {ord3}")
        # (1) generic d_min(M) vs M*|A|, and compare order-2 to explicit n+1
        Dmax=min(5*r+4, 3*n+8)
        print(f"     M : d_min(M)  generic=M*|A|  beats_generic?  rbound=floor/M    (explicit order2 deg={n+1})")
        for M in range(1,6):
            dm=d_min(A,M,p,Dmax)
            gen=M*r
            if dm is None:
                print(f"     {M} : >Dmax       {gen}")
            else:
                print(f"     {M} :  {dm:4d}        {gen:4d}        {'YES' if dm<gen else 'no':>3}            {dm//M}")

if __name__=="__main__":
    # Prize-regime thin (n^4) but search harder for off-diag |A|>=2:
    run(8, 4129)
    run(16, 65537)
    run(32, 1048609)
    # Also: a SHALLOWER field (n^2-ish) where off-diagonal A is bigger -> the regime where
    # the explicit Q's order-2 advantage (deg n+1 < 2|A|) can actually manifest.
    # n=16, p ~ n^2 = 256-ish, p=1 mod 16, proper.
    for n in (16,32):
        target=3*n*n
        k=(target-1)//n+1
        while True:
            p=k*n+1
            if is_prime(p) and p-1!=n: break
            k+=1
        run(n,p)
