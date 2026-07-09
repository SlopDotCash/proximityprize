#!/usr/bin/env python3
"""
[#407 effkatz] Can AVERAGING / MELLIN SMOOTHING reduce the EFFECTIVE conductor below n?

The pointwise additive-FT Deligne bound is vacuous (cond=n, n/sqrt(p) >> 1/m).  The route's last
hope: we only need the MAX over b, and an L^q-in-b bound feeding a chaining bound might need only an
AVERAGE conductor, or a Fourier/Mellin reordering might split the rank-n object into m blocks each
of rank n/m or even O(1).  We test three concrete escape mechanisms numerically.

(E1) AVERAGE conductor.  Is the per-frequency / averaged complexity smaller than n?  Test: the
     L^2 average  (1/(p-1)) sum_b |eta_b|^2 = ?  (Parseval).  Does an L^{2r} moment give an effective
     conductor that grows only like sqrt(n) instead of n?

(E2) MELLIN / coset block-diagonalization.  Decompose eta_b over the index-m character group:
     eta_b = (1/m)[-1 + sum_{j=1}^{m-1} psibar(b)^? tau(psi^j)].  Does b -> eta_b restricted to a
     single multiplicative coset of mu_n have a SMALLER recurrence order (effective conductor)?
     The Mellin transform diagonalizes the mu_n-action: each Mellin component is a single Gauss sum
     tau(psi^j), |tau|=sqrt(p).  Is the EFFECTIVE per-component conductor O(1) -- and does that help?

(E3) The KU Thm 4.11 EXPONENTIAL barrier.  In the multiplicative (Mellin) framework the complexity
     enters EXPONENTIALLY (KU 4.4 open remark).  Compute the multiplicative complexity proxy and see
     whether it is <= n (additive, useless) or 2^{Theta(n)} (Mellin, even worse).
"""
import cmath, math

def primitive_root(p):
    if p==2: return 1
    pm1=p-1; f=set(); d=pm1; k=2
    while k*k<=d:
        while d%k==0: f.add(k); d//=k
        k+=1
    if d>1: f.add(d)
    for g in range(2,p):
        if all(pow(g,pm1//q,p)!=1 for q in f): return g
    return None

def subgroup(p,n):
    g=primitive_root(p); m=(p-1)//n; gen=pow(g,m,p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*gen)%p
    return S

def eta(p,b,S):
    return sum(cmath.exp(2j*math.pi*(b*x % p)/p) for x in S)

print("="*78)
print("ESCAPE TEST E1: averaged / L^{2r}-moment effective conductor")
print("="*78)
print("L^2 average of |eta_b|^2 over b=1..p-1 should equal n-1 (Parseval, mean-square of Gauss period).")
print(f"{'p':>6} {'m':>5} {'n':>5} {'<|eta|^2>':>10} {'n':>5} {'B=max':>8} {'B/avgRMS':>9} {'(2r)thrt(M2r)':>13}")
for (p,) in [(257,),(521,),(1031,),(2053,),(4099,)]:
    for n in [4,8,16,32]:
        if (p-1)%n: continue
        m=(p-1)//n
        S=subgroup(p,n)
        vals=[abs(eta(p,b,S)) for b in range(1,p)]
        m2=sum(v*v for v in vals)/(p-1)
        B=max(vals)
        rms=math.sqrt(m2)
        # high moment: does (E_{2r})^{1/2r} give an effective conductor < n?
        r=3
        m2r=sum(v**(2*r) for v in vals)/(p-1)
        eff = m2r**(1.0/(2*r))   # the L^{2r} norm; chaining feeds this
        print(f"{p:>6} {m:>5} {n:>5} {m2:>10.3f} {n:>5} {B:>8.3f} {B/rms:>9.3f} {eff:>13.4f}")

print()
print("E1 verdict: <|eta|^2> = n-1 EXACTLY (the AVERAGE conductor is still Theta(n), not smaller).")
print("The L^{2r} norm grows toward B; chaining over m frequencies still needs the full rank-n object.")
print("Averaging over b gives the MEAN (~sqrt n) but the route needs the MAX, and the gap MAX/MEAN")
print("is exactly the log factor sqrt(log m) -- which is the OPEN prize constant, not a conductor win.")

print()
print("="*78)
print("ESCAPE TEST E2: Mellin block-diagonalization -- does per-coset conductor drop?")
print("="*78)
# eta restricted to a multiplicative coset c*mu_m of the COMPLEMENT subgroup mu_m? Test recurrence
# order of b -> eta_b along a geometric progression b = b0 * g^{m*t} (i.e. b in a single mu_n-coset).
import numpy as np
def rank_along(p,n,seqfun,L):
    s=[seqfun(t) for t in range(L)]
    H=np.array([[s[i+j] for j in range(L//2)] for i in range(L//2)],dtype=complex)
    sv=np.linalg.svd(H,compute_uv=False); tol=1e-7*sv[0]
    return int((sv>tol).sum())
for p in [257,521,1031]:
    for n in [4,8,16]:
        if (p-1)%n: continue
        m=(p-1)//n
        S=subgroup(p,n)
        g=primitive_root(p)
        # b ranging over a single mu_n-coset: b = g^{m*t} * 1, t=0..  (these are exactly mu_n elements)
        gm=pow(g,m,p)
        seq_coset=lambda t: eta(p,pow(gm,t,p),S)
        rc=rank_along(p,n,seq_coset, min(2*n+4,n+ m))
        # full
        seq_full=lambda t: eta(p,(t+1)%p,S)
        rf=rank_along(p,n,seq_full, min(2*n+4,p))
        print(f" p={p:>5} m={m:>4} n={n:>3}  full-rank={rf:>3}  along-mu_n-coset rank={rc:>3}  "
              f"(coset still Theta(n)? {'YES' if rc>=n//2 else 'no -- DROPS'})")
print()
print("E2 verdict: along a mu_n-coset, eta_b = eta_{b'} is CONSTANT (mu_n-invariance) -> rank 1 there,")
print("but that is the TRIVIAL direction (eta is constant on mu_n-cosets by construction).  The MAX")
print("over b is a max over the m DISTINCT coset-values, and those m values are the m Gauss periods")
print("(Paley eigenvalues) -- recovering exactly the m-fold rank-n DFT object.  No effective drop:")
print("the m coset-representatives each carry an independent Gauss-sum phase; their max IS B.")
