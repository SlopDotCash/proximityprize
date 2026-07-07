import numpy as np, math
def factor(x):
    fs,d=set(),2
    while d*d<=x:
        while x%d==0: fs.add(d); x//=d
        d+=1
    if x>1: fs.add(x)
    return fs
def prim_root(p):
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in factor(p-1)): return g

for (p,n,dchi) in [(193,8,2),(257,16,4),(577,8,3),(4129,16,2)]:
    g=prim_root(p); m=(p-1)//n
    # index function: ind[g^k]=k
    ind={}; x=1
    for k in range(p-1): ind[x]=k; x=x*g%p
    om=np.exp(2j*np.pi/(p-1))
    # chi: character of order dchi: chi(g^k)=e(k/dchi)
    if (p-1)%dchi: continue
    chi=lambda a: 0 if a%p==0 else np.exp(2j*np.pi*(ind[a%p]%dchi)/dchi)
    # wait chi(g^k) should = e(2pi i k/dchi): exponent k*(p-1)/dchi /(p-1)
    chi=lambda a: 0 if a%p==0 else np.exp(2j*np.pi*ind[a%p]/dchi) if False else 0
    def chif(a):
        a%=p
        if a==0: return 0
        return np.exp(2j*np.pi*(ind[a]% dchi)/dchi) if False else np.exp(2j*np.pi*ind[a]/ (p-1)*((p-1)//dchi))
    # lam_j(g^k)=e(2pi i j n k/(p-1)) trivial on mu_n=<g^m>: lam_j(g^m)=e(2pi i j n m/(p-1))=e(2pi i j) =1 OK
    def lam(j,a):
        a%=p
        if a==0: return 0
        return np.exp(2j*np.pi*j*n*ind[a]/(p-1))
    mun=[pow(g,m*i,p) for i in range(n)]
    # Jacobi coeff
    J={j: sum(lam(j,t)*chif(1-t) for t in range(p)) for j in range(m)}
    errs=[]
    for s in [1,2,5,g,123%p]:
        if s%p==0: continue
        W=sum(chif(s-y) for y in mun)
        rhs=chif(s)*(sum(J[j]*lam(j,s) for j in range(1,m))-1)/m
        errs.append(abs(W-rhs))
    Jmod=[abs(J[j])/math.sqrt(p) for j in range(1,m)]
    print(f"p={p} n={n} m={m} ord(chi)={dchi}  max|W-rhs|={max(errs):.2e}  |J|/sqrt(p) in [{min(Jmod):.3f},{max(Jmod):.3f}]")
