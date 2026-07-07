"""#466 round 21, lane HEADRUNG.
L_r := S_{r+1}^D / ((2r+1) * Sigma * S_r^D)  (sub-Wick per-rung multiplier, r19/r20).
Questions:
 (A) exact free-measure maximum of L_r given (Sigma, M, N, S_1): claim = Lambda/(2r+1),
     Lambda = M^2/Sigma (spike config saturates; upper bound x<=M^2 pointwise trivial).
 (B) true cells: L_r vs Lambda/(2r+1); which rungs are magnitude-provable (2r+1>=Lambda)?
 (C) direction of L_1<=1 vs constant-3 r=2 rung: with depletion S_1^D = qSig - |I0|^2 - Sig^2/n,
     L_1<=1  <=>  S_2^D <= 3 Sig S_1^D = 3qSig^2 - 3Sig*depl  which is STRONGER than
     S_2^D <= 3qSig^2 (constant-3 rung). Verify numerically + measure the two deficits.
 (D) adversarial PHASES (keep |eta| multiset on H, free phases): hill-climb to maximize L_1.
     If L_1 can be pushed >1, sub-Wick at r=1 is phase-deep even in the fixed-magnitude class.
"""
import numpy as np
from sympy import primitive_root
rng = np.random.default_rng(21)

def cell_data(p, n, m):
    g = primitive_root(p)
    e = (p-1)//n
    G = np.zeros(p); v = 1
    gpow = pow(g, e, p)
    for _ in range(n): G[v] = 1.0; v = (v*gpow) % p
    H = np.zeros(p); v = 1
    gm = pow(g, m, p)
    for _ in range((p-1)//m): H[v] = 1.0; v = (v*gm) % p
    eta = np.fft.ifft(G)*p
    Dmask = (G > .5); Dmask[0] = True
    return G, H, eta, Dmask

def moments(I, Dmask, Sig, rmax=10):
    A = (np.abs(I)**2)[~Dmask]
    S = {r: float(np.sum(A**r)) for r in range(1, rmax+1)}
    M2 = float(A.max())
    L = {r: (S[r+1]/S[r])/((2*r+1)*Sig) for r in range(1, rmax)}
    return S, M2, L

print("== (B)(C) true cells ==")
print(f"{'p':>6} {'n':>3} {'m':>2} | {'Lam':>6} | L1 L2 L3 | freeMax1=Lam/3 | L1<=1? | S2^D<=3SigS1^D? S2^D<=3qSig^2? | depl/qSig")
for n in [8, 16]:
    for m in [2, 4]:
        for p in {8:[41,257,1009,4073,12289],16:[97,257,12289,65537]}[n]:
            if (p-1)%n or (p-1)%m or ((p-1)//n)%m: continue
            G,H,eta,Dmask = cell_data(p,n,m)
            w = np.conj(eta)*H
            I = np.fft.ifft(w)*p
            Sig = float(np.sum(np.abs(eta)**2 * H))
            S,M2,L = moments(I,Dmask,Sig)
            Lam = M2/Sig
            I0 = abs(I[0])**2
            depl = I0 + Sig**2/n
            s1_id = p*Sig - depl
            assert abs(S[1]-s1_id)/s1_id < 1e-8, (S[1], s1_id)  # depletion identity check
            strong = S[2] <= 3*Sig*S[1]*(1+1e-12)      # L_1<=1
            c3 = S[2] <= 3*p*Sig**2*(1+1e-12)          # constant-3 rung
            print(f"{p:>6} {n:>3} {m:>2} | {Lam:6.2f} | {L[1]:.3f} {L[2]:.3f} {L[3]:.3f} |"
                  f" {Lam/3:6.2f} | {str(strong):>5} | {str(strong):>5} {str(c3):>5} | {depl/(p*Sig):.4f}")

print("\n== (A) free-measure optimization: max L_r given (Sigma,M,N,S_1) ==")
# free measure: x_1..x_N in [0,M2], sum x = S1 fixed. maximize (sum x^{r+1})/(sum x^r).
# claim: sup = M2 (k atoms at M2 + rest 0, k=S1/M2), so L_r max = Lam/(2r+1).
# random search + the explicit spike config vs claim.
for (Lam, N, r) in [(6.0, 500, 1), (12.4, 500, 1), (12.4, 500, 3), (3.0, 200, 1)]:
    Sig = 1.0; M2 = Lam*Sig; S1 = 0.9*N*Sig*0.05  # arbitrary budget << N*M2
    k = int(S1//M2)
    x = np.zeros(N); x[:k] = M2; x[k] = S1 - k*M2  # spike config, exact S1
    ratio = np.sum(x**(r+1))/np.sum(x**r)
    Lspike = ratio/((2*r+1)*Sig)
    best = Lspike
    for _ in range(2000):  # random-restart local search cannot beat spike
        y = rng.random(N)**4 * M2
        y *= S1/ y.sum()
        y = np.minimum(y, M2)
        if abs(y.sum()-S1)/S1 > .02: continue
        Lr = (np.sum(y**(r+1))/np.sum(y**r))/((2*r+1)*Sig)
        best = max(best, Lr)
    print(f"Lam={Lam:5.1f} r={r} | claim Lam/(2r+1)={Lam/(2*r+1):6.3f} | spike={Lspike:6.3f} | rand-best={best:6.3f}")

print("\n== (D) adversarial phases: maximize L_1 with TRUE |eta| multiset ==")
for (p,n,m) in [(1009,8,2),(4073,8,2),(12289,16,2),(257,16,4)]:
    if (p-1)%n or (p-1)%m or ((p-1)//n)%m: continue
    G,H,eta,Dmask = cell_data(p,n,m)
    mag = np.abs(eta)*H
    Sig = float(np.sum(mag**2))
    Hidx = np.where(H>.5)[0]
    def L1_of(phases):
        w = np.zeros(p, complex); w[Hidx] = mag[Hidx]*np.exp(1j*phases)
        I = np.fft.ifft(w)*p
        A = (np.abs(I)**2)[~Dmask]
        S1 = np.sum(A); S2 = np.sum(A**2)
        return S2/(3*Sig*S1), np.max(A)/Sig
    ph = np.angle(eta[Hidx])
    best, bestLam = L1_of(ph)
    # random restarts + hill-climb
    for restart in range(4):
        cur = rng.uniform(0, 2*np.pi, len(Hidx)) if restart else ph.copy()
        curL, curLam = L1_of(cur)
        step = 1.0
        for it in range(4000):
            j = rng.integers(len(Hidx))
            trial = cur.copy(); trial[j] += rng.normal(0, step)
            tL, tLam = L1_of(trial)
            if tL > curL: cur, curL, curLam = trial, tL, tLam
            if it % 800 == 799: step *= .6
        if curL > best: best, bestLam = curL, curLam
    trueL, trueLam = L1_of(np.angle(eta[Hidx]))
    print(f"p={p:>6} n={n:>2} m={m} | true L1={trueL:.4f} (Lam={trueLam:.2f}) | adversarial-phase best L1={best:.4f} (Lam@best={bestLam:.2f}) | broken={best>1}")
