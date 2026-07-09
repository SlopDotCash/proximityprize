"""
C062 v2: confluent Stepanov degree test, with proper handling of thin mu_n.

For thin prize-regime mu_n (n << sqrt p) the off-diagonal common set
A = mu_n cap (c + mu_n) is GENERICALLY tiny (|A| in {0,1,2}); r(c)=|A|.
This itself is the BGK/additive-energy regime: additive energy E(mu_n) = sum_c r(c)^2
is dominated by the few c with large r(c). The Stepanov claim is about bounding
the LARGEST r(c). So we must (a) report the actual r(c) spectrum over ALL c, and
(b) test the confluent auxiliary degree on the c that MAXIMIZE r(c).
"""
import math, random

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def find_prize_prime(n, beta_min):
    target = max(n**beta_min, 3*n)
    k = (target - 1)//n + 1
    while True:
        p = k*n + 1
        if is_prime(p): return p
        k += 1

def primitive_root_manual(p):
    m = p-1; fac=set(); d=2; mm=m
    while d*d <= mm:
        while mm%d==0: fac.add(d); mm//=d
        d+=1
    if mm>1: fac.add(mm)
    for g in range(2,p):
        if all(pow(g, m//q, p)!=1 for q in fac): return g
    return None

def mu_n(p, n):
    g = primitive_root_manual(p)
    w = pow(g,(p-1)//n,p)
    S=set(); x=1
    for _ in range(n): S.add(x); x=(x*w)%p
    assert len(S)==n
    return S

def binom_mod(i,j,p):
    if j<0 or j>i: return 0
    num=1;den=1
    for t in range(j):
        num=(num*((i-t)%p))%p
        den=(den*((t+1)%p))%p
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
                f=mat[r][col]
                mat[r]=[(mat[r][k]-f*mat[pr][k])%p for k in range(ncols)]
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

def rc_spectrum(S,p):
    # for every c in F_p, r(c)=|{y in S: c-y in S}|. = additive convolution count.
    Slist=sorted(S)
    cnt={}
    for a in Slist:
        for b in Slist:
            c=(a+b)%p
            cnt[c]=cnt.get(c,0)+1
    return cnt  # c -> #{(a,b) in S^2: a+b=c} = r(c)

def run(n,beta_min):
    p=find_prize_prime(n,beta_min); S=mu_n(p,n)
    print(f"\n=== n={n}, p={p} ~ n^{round(math.log(p,n),2)}  proper(n!=p-1) n/sqrt(p)={n/p**0.5:.4f} ===")
    cnt=rc_spectrum(S,p)
    # exclude diagonal c=2y? Actually r(c)=#reps with ordered (a,b). For c with c in S? we want the max r(c).
    # Off-diagonal cosets: c not in S (c^n != 1). c=0 has r(0)=#{y:-y in S}.
    vals=sorted(cnt.values(),reverse=True)
    maxr=vals[0]
    # which c achieve large r, off the trivial diagonal
    bigc=[(c,r) for c,r in cnt.items() if r>=3]
    bigc.sort(key=lambda t:-t[1])
    E=sum(r*r for r in cnt.values())
    print(f"  additive energy E(mu_n)=sum r(c)^2 = {E}   (=2n^2-n={2*n*n-n} if Sidon-like odd)")
    print(f"  max r(c) over all c = {maxr};   #c with r(c)>=3 = {len(bigc)}")
    print(f"  top r(c) values: {vals[:8]}")
    if not bigc:
        print("  no c with r(c)>=3 -> order-2/order-3 distinction VACUOUS at this thin n (Sidon-like).")
        return
    # take up to 3 distinct c with the largest r(c) (prefer off-diagonal c not in S)
    tested=0
    for c,r in bigc:
        offdiag = (c not in S)
        A=[y for y in S if ((c-y)%p) in S]
        assert len(A)==r
        Dmax=min(5*len(A)+4, 4*n+8)
        print(f"  -- c={c} ({'OFF-diag c^n!=1' if offdiag else 'on-diag/other'})  r(c)=|A|={r}")
        print(f"      M : d_min(M)  rbound=floor(d_min/M)  d_min/|A|  d_min/(M*|A|)   (|A|={r})")
        for M in range(1,6):
            dm=d_min(A,M,p,Dmax)
            if dm is None:
                print(f"      {M} : >Dmax({Dmax})")
                continue
            print(f"      {M} :  {dm:5d}     {dm//M:5d}                {dm/r:6.3f}    {dm/(M*r):6.3f}")
        tested+=1
        if tested>=3: break

if __name__=="__main__":
    for n in (8,16,32,64):
        run(n,beta_min=4)
