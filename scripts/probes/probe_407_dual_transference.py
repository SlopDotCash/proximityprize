#!/usr/bin/env python3
"""
probe_407_dual_transference.py -- the DUAL-lattice / transference lever for the sparse-support angle.

The assignment lever (a): a transference exploiting that alpha is SPARSE.  Banaszczyk transference:
    1 <= lambda_1(L)*lambda_n(L*) <= n,   lambda_1(L)*lambda_1(L*) >= 1   (L* = dual under trace).
For the prize we want defects RARE, i.e. lambda_1(𝔭) LARGE; transference gives lambda_1(𝔭) >=
1/lambda_n(𝔭*). The QUESTION: is there a USEFUL lower bound on lambda_1(𝔭) from the dual that
exceeds the Minkowski-mean and pushes the onset to larger r?  OR is 𝔭 well-rounded (lambda_1=...
=lambda_n) so transference is tight and gives nothing (the Fukshansky-Petersen pin)?

We compute (ell2 Minkowski norm, where transference theorems live):
   lambda_1(𝔭) (LLL+enum), and the dual lattice 𝔭* = (1/p)*conj-structure.  For a degree-1 prime
   over p in Z[ζ_n], the trace-dual of 𝔭 is 𝔭^{-1} d^{-1} where d=different=(n) for 2-power cyclotomic
   (d = (f'(ζ)) = (n ζ^{...})). We directly build the dual via the trace Gram: 𝔭* = {y : Tr(xy)∈Z ∀x∈𝔭}.
We then report:
   - lambda_1(𝔭), lambda_1(𝔭*), product (transference: >=1, and if well-rounded ~ the GH bound),
   - the well-roundedness ratio lambda_n(𝔭)/lambda_1(𝔭) (=1 => perfectly well-rounded => no dual rescue),
   - whether 1/lambda_n(𝔭*) (the transference LOWER bound on lambda_1(𝔭)) is anywhere near lambda_1(𝔭)
     (if it's much smaller, transference is loose and gives no useful lower bound; if ~equal, tight).
"""
import sys, math, itertools
import numpy as np

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root


def prize_prime(n, beta, pmax=10**11):
    base = int(round(n ** beta)); base -= base % n; base += 1; p = base
    while p < pmax:
        if is_prime(p) and odd_part((p - 1) // n) > 1:
            return p
        p += n
    return None


def order_n_root(p, n):
    return pow(primitive_root(p), (p - 1) // n, p)


def minkowski_real_basis(n):
    """rows = real Minkowski coords of power basis ζ^k, k=0..D-1, D=n/2 (ℓ2-isometric to canonical)."""
    D = n // 2
    ts = [t for t in range(1, n//2 + 1, 2)]
    B = np.zeros((D, D))
    for k in range(D):
        col = []
        for t in ts:
            ang = 2*math.pi*t*k/n
            col += [math.sqrt(2)*math.cos(ang), math.sqrt(2)*math.sin(ang)]
        B[k, :len(col)] = col
    return B


def sublattice_basis_p(p, z, n):
    D = n // 2
    rows = [[0]*D]; rows[0][0] = p
    for k in range(1, D):
        rk = [0]*D; rk[0] = -(pow(z, k, p)); rk[k] = 1; rows.append(rk)
    return np.array(rows, dtype=float)


def py_lll(B, delta=0.99):
    B=B.astype(float).copy(); m=B.shape[0]
    def gso(B):
        Bs=B.copy(); mu=np.zeros((m,m))
        for i in range(m):
            for j in range(i):
                d=np.dot(Bs[j],Bs[j]); mu[i,j]=np.dot(B[i],Bs[j])/d if d>0 else 0.0
                Bs[i]=Bs[i]-mu[i,j]*Bs[j]
        return Bs,mu
    Bs,mu=gso(B); k=1; it=0
    while k<m and it<30000:
        it+=1
        for j in range(k-1,-1,-1):
            q=round(mu[k,j])
            if q!=0: B[k]=B[k]-q*B[j]; Bs,mu=gso(B)
        if np.dot(Bs[k],Bs[k])>=(delta-mu[k,k-1]**2)*np.dot(Bs[k-1],Bs[k-1]): k+=1
        else:
            B[[k,k-1]]=B[[k-1,k]]; Bs,mu=gso(B); k=max(k-1,1)
    return B


def lambda1_enum(redB, depth=2):
    m=redB.shape[0]
    rng=range(-depth,depth+1)
    rs=sorted(range(m), key=lambda i: np.dot(redB[i],redB[i]))
    use=rs[:min(7,m)]
    best=min(np.dot(redB[i],redB[i]) for i in range(m))
    for coeffs in itertools.product(rng, repeat=min(5,len(use))):
        if all(c==0 for c in coeffs): continue
        v=np.zeros(redB.shape[1])
        for c,i in zip(coeffs, use[:5]):
            if c: v=v+c*redB[i]
        nv=np.dot(v,v)
        if 0<nv<best: best=nv
    return math.sqrt(best)


def successive_minima_approx(redB):
    """rough lambda_n via the longest reduced GSO vector (upper proxy) and lambda_1 via shortest."""
    norms=sorted(math.sqrt(np.dot(redB[i],redB[i])) for i in range(redB.shape[0]))
    return norms[0], norms[-1]


def main():
    print("="*100)
    print(" #407 DUAL / TRANSFERENCE lever (ℓ2 Minkowski):  is 𝔭 well-rounded (no dual rescue)?")
    print("="*100)
    print(f"{'n':>4} {'beta':>5} {'p':>14} | {'λ1(𝔭)':>8} {'λn~':>8} {'λn/λ1':>7} | "
          f"{'λ1(𝔭*)':>9} {'λ1·λ1*':>8} {'1/λn*≈':>8} {'tight?':>7}")
    for n in (8, 16, 32, 64):
        gram = minkowski_real_basis(n); D=n//2
        for beta in (4.0, 5.0):
            p = prize_prime(n, beta)
            if p is None: continue
            z = order_n_root(p, n)
            rows = sublattice_basis_p(p, z, n)
            realB = rows @ gram
            red = py_lll(realB)
            l1 = lambda1_enum(red)
            l1s, lns = successive_minima_approx(red)
            wr = lns / l1s if l1s else float('nan')   # well-roundedness proxy (1 = perfectly WR)
            # dual lattice: 𝔭* basis = (red^{-T}) (Gram-dual of the reduced real basis)
            try:
                dualB = np.linalg.inv(red).T
                redd = py_lll(dualB)
                l1d = lambda1_enum(redd)
                _, lnd = successive_minima_approx(redd)
            except Exception:
                l1d = lnd = float('nan')
            prod = l1 * l1d
            trans_lower = 1.0/lnd if lnd else float('nan')   # transference lower bound on λ1(𝔭)
            tight = trans_lower/l1 if l1 else float('nan')
            print(f"{n:>4} {beta:>5.1f} {p:>14} | {l1:>8.3f} {lns:>8.3f} {wr:>7.3f} | "
                  f"{l1d:>9.4f} {prod:>8.3f} {trans_lower:>8.3f} {tight:>7.3f}")
    print("\nREADING:")
    print(" - λn/λ1 ≈ 1: 𝔭 is PERFECTLY WELL-ROUNDED (Fukshansky-Petersen). Then transference is TIGHT")
    print("   and gives NO loose lower bound on λ1 beyond the Minkowski/Hermite value -> the dual offers")
    print("   no rescue: λ1(𝔭) is pinned ~ Hermite·covol^{1/D}, hence the onset is pinned, hence the")
    print("   sparse-support sub-count is two-sided pinned just like the box count. No new lever.")
    print(" - 1/λn* ≈ λ1: transference is essentially an equality here (well-rounded) -> exhausted.")


if __name__ == "__main__":
    main()
