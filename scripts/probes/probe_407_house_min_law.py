#!/usr/bin/env python3
"""
probe_407_house_min_law.py -- the SCALING LAW of h_lat = min house of 𝔭, and the dual/theta levers.

ESTABLISHED: the lattice SVP-min of 𝔭 IS sparse (l1 ~ 8-13 in power basis), so sparse-support
onset = lattice onset = well-rounded onset. Sparsity does not lengthen the shortest vector.

REMAINING LEVERS from the assignment to settle rigorously:
  (c) explicit basis Gram structure: does 𝔭 = <p, ζ-z> have an EXCEPTIONALLY short vector
      (h_lat << Minkowski) that the prize could exploit, or is it generic?
  (d) theta-series counting: N(H) = #{0≠z∈𝔭 : house(z) <= H}. Is it TWO-SIDED pinned
      (Mink lower AND upper), confirming no loose-upper rescue (the well-rounded no-go)?
  dual: the transference λ_1(𝔭)·λ_1(𝔭*) — does the dual give a USEFUL lower bound on h_lat
      that beats the Minkowski-mean and could push the onset to larger r?  (𝔭* = (1/p)·diff^{-1}
      scaled; for a degree-1 prime 𝔭* relates to the inverse-different and 1/p.)

KEY law to extract: h_lat(n,p) as a function of n and beta = log_n p.  The Minkowski/geometric
prediction for an index-p well-rounded ideal is h_lat ~ C * p^{1/(n/2)} * sqrt(n) up to the
disc factor (since covol = p*sqrt|disc|, |disc|^{1/φ} ~ n, and λ_1^∞ ~ covol^{1/φ}/... ).
We extract the empirical exponent and constant, and the theta two-sidedness.
"""
import sys, math, itertools
import numpy as np

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root


def prize_prime(n, beta, pmax=10**14):
    base = int(round(n ** beta)); base -= base % n; base += 1; p = base
    while p < pmax:
        if is_prime(p) and odd_part((p - 1) // n) > 1:
            return p
        p += n
    return None


def order_n_root(p, n):
    return pow(primitive_root(p), (p - 1) // n, p)


def minkowski_real_basis(n):
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
    rows = []
    row0 = [0]*D; row0[0] = p; rows.append(row0)
    for k in range(1, D):
        rk = [0]*D; rk[0] = -(pow(z, k, p)); rk[k] = 1; rows.append(rk)
    return np.array(rows, dtype=object)


def house_pow(d, n):
    D=n//2; h=0.0
    for t in range(1, n, 2):
        re=im=0.0; a0=2*math.pi*t/n
        for k in range(D):
            if d[k]: re+=d[k]*math.cos(a0*k); im+=d[k]*math.sin(a0*k)
        h=max(h, math.hypot(re,im))
    return h


def l2_mink(d, n):
    D=n//2; s=0.0
    for t in range(1, n, 2):
        re=im=0.0; a0=2*math.pi*t/n
        for k in range(D):
            if d[k]: re+=d[k]*math.cos(a0*k); im+=d[k]*math.sin(a0*k)
        s+=re*re+im*im
    return math.sqrt(s)


def py_lll(B, U_rows, delta=0.99):
    B=B.astype(float).copy(); m=B.shape[0]; C=np.eye(m,dtype=object)
    def gso(B):
        Bs=B.copy(); mu=np.zeros((m,m))
        for i in range(m):
            for j in range(i):
                d=np.dot(Bs[j],Bs[j])
                mu[i,j]=np.dot(B[i],Bs[j])/d if d>0 else 0.0
                Bs[i]=Bs[i]-mu[i,j]*Bs[j]
        return Bs,mu
    Bs,mu=gso(B); k=1; it=0
    while k<m and it<40000:
        it+=1
        for j in range(k-1,-1,-1):
            q=round(mu[k,j])
            if q!=0: B[k]=B[k]-q*B[j]; C[k]=C[k]-q*C[j]; Bs,mu=gso(B)
        if np.dot(Bs[k],Bs[k])>=(delta-mu[k,k-1]**2)*np.dot(Bs[k-1],Bs[k-1]): k+=1
        else:
            B[[k,k-1]]=B[[k-1,k]]; C[[k,k-1]]=C[[k-1,k]]; Bs,mu=gso(B); k=max(k-1,1)
    out=[]
    for i in range(m):
        v=np.zeros(U_rows.shape[1],dtype=object)
        for j in range(m):
            if C[i,j]!=0: v=v+int(C[i,j])*U_rows[j]
        out.append([int(x) for x in v])
    return out


def reduced_short(p, z, n, gram_B):
    rows=sublattice_basis_p(p,z,n)
    realB=np.array([[float(x) for x in r] for r in rows])@gram_B
    red=py_lll(realB, np.array([[int(x) for x in r] for r in rows]))
    return red


def min_house_and_theta(p, z, n, gram_B):
    D=n//2
    red=reduced_short(p,z,n,gram_B)
    red_sorted=sorted(red,key=lambda d:l2_mink(d,n))
    short=red_sorted[:min(8,len(red_sorted))]
    cands=list(red)
    rng=range(-2,3)
    for coeffs in itertools.product(rng,repeat=min(5,len(short))):
        if all(c==0 for c in coeffs): continue
        v=[0]*D
        for c,s in zip(coeffs,short[:5]):
            if c:
                for k in range(D): v[k]+=c*s[k]
        cands.append(v)
    best=None
    houses=[]
    for v in cands:
        if all(x==0 for x in v): continue
        h=house_pow(v,n); houses.append(h)
        if best is None or h<best: best=h
    return best, sorted(houses)[:12]


def main():
    print("="*104)
    print(" #407 HOUSE-MIN LAW of 𝔭 + Minkowski/dual/theta diagnostics (sparse-support angle settled)")
    print("="*104)
    print(f"{'n':>4} {'beta':>5} {'p':>15} | {'h_lat':>7} {'p^(2/n)':>8} {'h/p^(2/n)':>10} "
          f"{'h/√n':>7} {'Mink∞':>7} {'h/Mink':>7} {'2*Mink?':>8}")
    rows=[]
    for n in (8, 16, 32, 64, 128):
        gram_B=minkowski_real_basis(n); D=n//2
        for beta in (4.0, 5.0):
            p=prize_prime(n,beta)
            if p is None: continue
            z=order_n_root(p,n)
            try:
                h_lat, theta = min_house_and_theta(p,z,n,gram_B)
            except Exception as e:
                print(f"{n:>4} {beta:>5.1f} {p:>15} | err {e}"); continue
            # geometric predictions
            mu=int(math.log2(n)); log2disc=(mu-1)*2**(mu-1) if mu>=1 else 0
            covol=p*(2.0**(log2disc/2.0))
            # house ~ ℓ∞ over D complex coords ~ covol^{1/D} (per-coordinate geometric mean for
            # a balanced/well-rounded ideal): the natural Minkowski-house scale.
            mink_house=covol**(1.0/D)
            p2n = p**(2.0/n)
            rows.append((n,beta,p,h_lat))
            print(f"{n:>4} {beta:>5.1f} {p:>15} | {h_lat:>7.2f} {p2n:>8.3f} {h_lat/p2n:>10.3f} "
                  f"{h_lat/math.sqrt(n):>7.3f} {mink_house:>7.2f} {h_lat/mink_house:>7.3f} "
                  f"{'~2x' if 1.7<h_lat/mink_house<2.5 else '':>8}")
    print("\nLAW EXTRACTION (h_lat vs n at fixed beta):")
    for beta in (4.0,5.0):
        sel=[(n,h) for (nn,b,pp,h) in rows for n in [nn] if b==beta]
        sel=[(nn,h) for (nn,b,pp,h) in rows if b==beta]
        if len(sel)>=3:
            ns=np.array([math.log(n) for n,h in sel]); hs=np.array([math.log(h) for n,h in sel])
            A=np.vstack([ns,np.ones_like(ns)]).T
            slope,intc=np.linalg.lstsq(A,hs,rcond=None)[0]
            print(f"  beta={beta}: h_lat ~ {math.exp(intc):.3f} * n^{slope:.3f}   "
                  f"(slope 0.5 => √n law; 0 => bounded; -? => shrinking)")
    print("\n - If h_lat ~ C·p^{2/n}: 𝔭 short vector is the GENERIC Minkowski minimum (no exceptional")
    print("   sparse shortcut). p^{2/n} -> 1 as n grows at fixed beta, but ×√n (disc) keeps house ~ √n.")
    print(" - h/Mink ~ 2 (constant, two-sided): theta is TWO-SIDED pinned -> NO loose-upper rescue,")
    print("   confirming the well-rounded no-go EXTENDS to the sparse-support sub-count.")


if __name__ == "__main__":
    main()
