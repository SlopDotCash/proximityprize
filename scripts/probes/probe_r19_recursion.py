import numpy as np
from sympy import isprime, primitive_root

def cell(p, n, m):
    q = p
    g = primitive_root(p)
    # mu_n
    e = (p-1)//n
    G = np.zeros(p); 
    x = 1
    gpow_e = pow(g, e, p)
    v = 1
    for k in range(n):
        G[v] = 1.0
        v = (v*gpow_e) % p
    # H index m subgroup of F_p^*
    H = np.zeros(p)
    gm = pow(g, m, p)
    v = 1
    for k in range((p-1)//m):
        H[v] = 1.0
        v = (v*gm) % p
    eta = np.fft.ifft(G)*p            # eta_b
    w = np.conj(eta)*H
    I = np.fft.ifft(w)*p              # I_H(s0)
    Sig = np.sum(np.abs(eta)**2 * H)
    # D = {0} union mu_n
    Dmask = (G>0.5); Dmask = Dmask.copy(); Dmask[0]=True
    away = ~Dmask
    A2 = np.abs(I)**2
    S = {}
    for r in [1,2,3,4]:
        S[r] = np.sum(A2[away]**r)
    Map2 = A2[away].max()             # sup away |I|^2
    # Wick-normalized rung values
    dfac = {1:1,2:3,3:15,4:105}
    W = {r: S[r]/(dfac[r]*q*Sig**r) for r in [1,2,3,4]}
    # per-rung multiplier in units of Sigma, Wick-normalized
    L = {r: (S[r]/S[r-1])/((2*r-1)*Sig) for r in [2,3,4]}
    rho = {r: Map2*S[r-1]/S[r] for r in [2,3,4]}   # sup-split loss factor
    Lam = Map2/Sig
    # spike values
    spikes = np.abs(I[Dmask])**2
    return dict(p=p,n=n,m=m,Sig=Sig,W=W,L=L,rho=rho,Lam=Lam,
                sqq=np.sqrt(q), I0=abs(I[0]), spikemax=spikes.max(), spikemean=spikes.mean())

cells = []
for n in [8,16]:
    for m in [2,4]:
        for p in {8:[41,257,1009,4073],16:[97,257,12289,65537]}[n]:
            if (p-1)%n==0 and (p-1)%m==0:
                cells.append(cell(p,n,m))

print(f"{'p':>6} {'n':>3} {'m':>2} | {'W2':>7} {'W3':>7} {'W4':>7} | {'L3':>6} {'L4':>6} | {'rho3':>7} {'rho4':>7} | {'Lam':>8} {'Lam/sqq':>7}")
for c in cells:
    print(f"{c['p']:>6} {c['n']:>3} {c['m']:>2} | {c['W'][2]:7.3f} {c['W'][3]:7.3f} {c['W'][4]:7.3f} | "
          f"{c['L'][3]:6.3f} {c['L'][4]:6.3f} | {c['rho'][3]:7.2f} {c['rho'][4]:7.2f} | "
          f"{c['Lam']:8.2f} {c['Lam']/c['sqq']:7.3f}")

# Loss decomposition: total loss of provable chain S3 <= (S2)^{3/2} vs truth,
# split into split-loss rho3 and Chebyshev-loss chi3 = sqrt(S2)/Map2
print()
print(f"{'p':>6} {'n':>3} {'m':>2} | {'chain3=S2^1.5/S3':>16} {'rho3':>6} {'cheb3':>7} {'q^.5':>6} | {'Wick-need':>9}")
for c in cells:
    pass
