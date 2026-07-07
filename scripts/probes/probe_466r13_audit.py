#!/usr/bin/env python3
"""
ADVERSARIAL AUDIT of #466 R13 World-I-vs-II verdict.
Independent re-derivation (no reuse of worker code paths) of:
  (1) the 2nd-moment-over-offsets identity  sum_{s0}|I_H(s0)|^2 = q * sum_{b in H}|eta_b|^2
  (2) worst_s0 |I_H(s0)|  vs  sqrt|H|*M  vs  |H|*M
  (3) the phase counterexample (same moduli, random phase) -- is the collapse real?
  (4) THE CRUX the worker may have glossed: WHY does worst reach |H|*M?
      Test: is I_H(s0=0) = sum_{b in H} conj(eta_b) already ~ |H|*M?  Because eta_b
      for b in a coset are NOT random-phase -- they may be near-real-positive, so the
      DC offset s0=0 (or a structured s0) sums them coherently.  If worst is just the
      trivial coherent sum, that is a REAL effect but let's see if it's an artifact of
      H=quadratic-residues (a very special set) rather than a generic 'hyperplane'.
"""
import math, sys
import numpy as np

def is_prime(n):
    if n<2: return False
    if n%2==0: return n==2
    i=3
    while i*i<=n:
        if n%i==0: return False
        i+=2
    return True

def primitive_root(p):
    phi=p-1; f=[]; m=phi; d=2
    while d*d<=m:
        if m%d==0:
            f.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: f.append(m)
    for g in range(2,p):
        if all(pow(g,phi//x,p)!=1 for x in f): return g

def find_primes(n, count=2):
    pmin=n**4; out=[]; seen=set()
    p=pmin-(pmin%n)+1
    if p<pmin: p+=n
    while len(out)<count and p<pmin*80:
        if is_prime(p) and (p-1)%n==0:
            t=p-1; v2=0
            while t%2==0: t//=2; v2+=1
            if v2 not in seen: out.append(p); seen.add(v2)
        p+=n
    return out

def subgroup(p,n,g):
    h=pow(g,(p-1)//n,p); S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return S

def etas(p, mu):
    ind=np.zeros(p)
    for y in mu: ind[y%p]=1.0
    return np.conjugate(np.fft.fft(ind))  # eta[b] = sum_y exp(+2pi i b y/p)

out=[]
def P(s): out.append(s); print(s); sys.stdout.flush()

for n in [8,16]:
    for p in find_primes(n):
        g=primitive_root(p); mu=subgroup(p,n,g); eta=etas(p,mu)
        M=float(np.max(np.abs(eta[1:])))
        P(f"\n{'='*60}\nn={n} p={p} g={g}  M={M:.3f}")
        # brute-force check the 2nd moment identity for the FULL nonzero spectrum,
        # independently (direct double loop is too big; use the DFT but VERIFY on a
        # small explicit s0 sample against direct summation).
        deg=2
        gh=pow(g,deg,p); H=set(); x=1
        while x not in H: H.add(x); x=(x*gh)%p
        H.discard(0)
        Harr=np.array(sorted(H)); absH=len(Harr)
        cH=np.conjugate(eta[Harr])   # coefficients c_b = conj(eta_b), b in H
        # I(s0) = sum_{b in H} c_b * exp(2pi i b s0 / p)
        def I_direct(s0):
            ph=np.exp(2j*math.pi*(Harr.astype(np.float64)*s0 % p)/p)
            return complex(np.sum(cH*ph))
        # DFT of the full length-p coeff vector:
        cfull=np.zeros(p,dtype=complex); cfull[Harr]=cH
        X=np.fft.fft(cfull)     # X[k] = sum_b c_b exp(-2pi i b k/p) = I(-k)
        absI=np.abs(X)
        # VERIFY DFT vs direct on 5 random offsets
        maxerr=0.0
        for s0 in [0,1,7,p//3, p-2]:
            d=abs(I_direct(s0)); f=absI[(-s0)%p]
            maxerr=max(maxerr, abs(d-f))
        # 2nd moment identity
        lhs=float(np.sum(absI**2))
        rhs=float(p*np.sum(np.abs(eta[Harr])**2))
        P(f"  |H\\0|={absH}  DFT-vs-direct maxerr={maxerr:.2e}")
        P(f"  2nd-moment: sum_s0|I|^2 = {lhs:.4e}   q*sum_H|eta|^2 = {rhs:.4e}   "
          f"rel.diff={abs(lhs-rhs)/rhs:.2e}")
        worst=float(np.max(absI)); argw=int(np.argmax(absI))
        s0w=(-argw)%p
        MH=float(np.max(np.abs(eta[Harr])))
        P(f"  worst_s0|I| = {worst:.2f}  at s0={s0w}   (|H|*M_H={absH*MH:.1f}, sqrt|H|*M_H={math.sqrt(absH)*MH:.1f})")
        P(f"    worst/|H| = {worst/absH:.4f}   worst/(sqrt|H|*M_H) = {worst/(math.sqrt(absH)*MH):.3f}")
        # CRUX A: is the max at s0=0 (trivial coherent sum of conj(eta_b))?
        I0=abs(complex(np.sum(cH)))
        P(f"    |I(0)| = |sum_H conj(eta_b)| = {I0:.2f}   (worst at s0={s0w}, so max is {'AT' if s0w==0 else 'NOT AT'} 0)")
        # CRUX B: are the eta_b for b in H nearly real/aligned?  Check phase spread.
        angs=np.angle(eta[Harr])
        P(f"    phase spread of eta_b over H: circ.resultant |mean(e^{{i ang}})| = "
          f"{abs(np.mean(np.exp(1j*angs))):.4f}  (1=all aligned, 0=uniform)")
        # phase counterexample independently
        rng=np.random.default_rng(7)
        wr=[]
        for _ in range(10):
            ph=np.exp(2j*math.pi*rng.random(absH))
            c2=np.zeros(p,dtype=complex); c2[Harr]=np.abs(eta[Harr])*ph
            wr.append(float(np.max(np.abs(np.fft.fft(c2)))))
        wr=np.array(wr)
        P(f"    random-phase worst: mean={wr.mean():.1f}  true/random={worst/wr.mean():.2f}")

with open("scripts/probes/_out_466r13_audit.txt","w") as f:
    f.write("\n".join(out))
