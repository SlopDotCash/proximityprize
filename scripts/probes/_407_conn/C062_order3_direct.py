"""
C062 final: the attack_plan asks for an order-3 auxiliary Psi with deg ~ n on
A = mu_n cap (c+mu_n), giving r(c) <= (n+1)/3, and an order-M family deg=O(n+M^2)
giving r(c) <= O(n^{2/3}).

We test the BEST POSSIBLE case for the connection: the LARGEST degenerate set,
A = mu_n itself (c=0). If even there no order-3 auxiliary of degree < 3|A|=3n exists,
then deg/3 >= n = trivial bound and the whole order-M ladder is dead.

We compute d_min(M) for A=mu_n directly, M=1..8, and report d_min/M (the r-bound).
For the order-M family to give r<=O(n^{2/3}) we'd need d_min(M)/M to DROP below n;
generic gives d_min(M)=M*n so d_min(M)/M = n flat. We confirm exactly which holds.
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

def find_prize_prime(n,beta_min):
    target=max(n**beta_min,3*n); k=(target-1)//n+1
    while True:
        p=k*n+1
        if is_prime(p): return p
        k+=1

def primitive_root_manual(p):
    m=p-1; fac=set(); d=2; mm=m
    while d*d<=mm:
        while mm%d==0: fac.add(d); mm//=d
        d+=1
    if mm>1: fac.add(mm)
    for g in range(2,p):
        if all(pow(g,m//q,p)!=1 for q in fac): return g

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

def run(n):
    p=find_prize_prime(n,4); S=sorted(mu_n(p,n))
    print(f"\n=== A = mu_n itself, n={n}, p={p}  (LARGEST degenerate set, best case for the route) ===")
    print(f"   want: order-M aux deg < M*n  =>  r-bound = floor(deg/M) < n.  generic = M*n flat.")
    print(f"   M : d_min(M)   M*n     r-bound=floor/M   discount(M*n - d_min)")
    for M in range(1,9):
        dm=d_min(S,M,p,M*n+4)
        if dm is None:
            print(f"   {M} :  >Dmax")
        else:
            print(f"   {M} :  {dm:5d}   {M*n:5d}      {dm//M:5d}             {M*n-dm}")

if __name__=="__main__":
    for n in (8,16,32):
        run(n)
