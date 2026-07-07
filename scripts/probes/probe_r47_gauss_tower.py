import numpy as np, math
from sympy import isprime
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
def run(p,n):
    g=prim_root(p); m=(p-1)//n; N=p-1
    pw=[1]*N
    for k in range(1,N): pw[k]=pw[k-1]*g%p
    ind={pw[k]:k for k in range(N)}
    ar=np.arange(N)
    psi=np.exp(2j*np.pi*np.array(pw)/p)   # ψ(g^k)
    # 𝔤_j = Σ_x λ_j(x)ψ(x) = Σ_k e(jnk/N)ψ(g^k)
    lamM=np.exp(2j*np.pi*np.outer(np.arange(m),n*ar)/N)
    Gs=lamM@psi
    Gm=Gs.copy(); Gm[0]=0
    # A-side sequence per r44: 𝔤⁻(j) = 𝔤_{−j}
    Gneg=np.zeros(m,dtype=complex)
    for j in range(m): Gneg[j]=Gm[(-j)%m]
    # B-side J for comparison
    chi_full=np.zeros(p); chi_full[1:]=np.where(np.array([ind[a] for a in range(1,p)])%2==0,1.0,-1.0)
    ts=np.arange(p); om=(1-ts)%p
    ks=np.array([ind[a] for a in range(1,p)])
    J=np.zeros(m,dtype=complex)
    for j in range(m):
        lv=np.zeros(p,dtype=complex); lv[1:]=np.exp(2j*np.pi*j*n*ks/N)
        J[j]=np.sum(lv[ts]*chi_full[om])
    Jm=J.copy(); Jm[0]=0
    def E3(v): return float(np.sum(np.abs(np.fft.ifft(np.fft.fft(v)**3))**2))
    eA=E3(Gneg); eB=E3(Jm)
    # modulus check + Parseval sanity
    modA=np.abs(Gm[1:])/math.sqrt(p)
    print(f"p={p:>6} n={n:>3} m={m:>4}: |𝔤|/√q∈[{modA.min():.3f},{modA.max():.3f}]  "
          f"E3^A/(6m³q³)={eA/(6*m**3*p**3):.3f}  E3^B/(6m³q³)={eB/(6*m**3*p**3):.3f}  A/B={eA/eB:.3f}")
for (p,n) in [(577,8),(3457,8),(4129,16),(5953,32)]:
    run(p,n)
