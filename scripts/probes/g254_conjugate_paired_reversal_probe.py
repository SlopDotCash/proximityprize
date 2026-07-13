#!/usr/bin/env python3
"""G254: audit G252/G253 under mandatory quotient-character conjugation symmetry.

For actual dyadic-subgroup profiles
  W(t)=#{(y,z) in G^2: 2y-z=t}
  R_r(t)=#{(A,B): |A|=r, |B|=r-1, sum A-sum B=t},
compute their quotient DFTs. Because W,R are real, character rows a and -a are
conjugate and c_a=Re(What_a*conj(Rhat_a)) satisfies c_a=c_-a.

Restrict histogram-preserving sign moves to the honest paired class s_a=s_-a.
For odd quotient order m == 1 mod 4, there are an even number of nonprincipal
conjugate pairs, so an exactly balanced paired sign assignment exists. The exact
minimum flips half the PAIRS with largest real contribution. This tests whether
conjugation symmetry repairs the G252/G253 global-discrepancy no-go.
"""
from __future__ import annotations
import importlib.util, math
import numpy as np

spec=importlib.util.spec_from_file_location('g216','scripts/probes/g216_mellin_alignment_probe.py')
g216=importlib.util.module_from_spec(spec); spec.loader.exec_module(g216)


def analyze(n:int,p:int,r:int):
    assert (p-1)%n==0
    root=g216.primitive_root(p); m=(p-1)//n
    assert m%4==1
    G=g216.subgroup(p,n,root)
    dp=g216.subset_hists(G,p,r)
    R=g216.circ_corr(dp[r],dp[r-1]).astype(np.int64)
    W=np.zeros(p,dtype=np.int64)
    for y in G:
        for z in G:
            W[(2*y-z)%p]+=1
    reps=np.array([pow(root,j,p) for j in range(m)],dtype=np.int64)
    wc=W[reps].astype(np.float64); rc=R[reps].astype(np.float64)
    FW=np.fft.fft(wc); FR=np.fft.fft(rc)
    # nonprincipal rows split into pairs {a,m-a}, a=1..(m-1)/2
    h=(m-1)//2
    pair=[]; conj_err=0.0; contrib_err=0.0
    for a in range(1,h+1):
        b=m-a
        scale=max(1.0,abs(FW[a]),abs(FR[a]))
        conj_err=max(conj_err,abs(FW[b]-np.conj(FW[a]))/scale,
                     abs(FR[b]-np.conj(FR[a]))/scale)
        ca=float(np.real(FW[a]*np.conj(FR[a])))
        cb=float(np.real(FW[b]*np.conj(FR[b])))
        contrib_err=max(contrib_err,abs(ca-cb)/max(1.0,abs(ca),abs(cb)))
        pair.append(ca+cb)
    assert h%2==0
    pair=np.array(pair)
    aligned=float(pair.sum())
    tri=float(np.abs(pair).sum())
    top=np.sort(pair)[::-1][:h//2]
    paired_min=aligned-2*float(top.sum())
    # direct physical centered covariance and quotient Parseval consistency
    phys=int(p*np.dot(W,R)-int(W.sum())*int(R.sum()))
    # Sum nonprincipal DFT products equals m*sum_classes centered product.
    fourier=float(np.real(np.sum(FW[1:]*np.conj(FR[1:]))))
    class_center=float(m*np.dot(wc,rc)-wc.sum()*rc.sum())
    parseval_err=abs(fourier-class_center)/max(1.0,abs(class_center))
    print(f"n={n} p={p} r={r} m={m} pairs={h} aligned={aligned:.6g} "
          f"pairedMin={paired_min:.6g} pairedFrac={paired_min/(tri+1e-30):.6f} "
          f"reverses={paired_min < -1e-7*max(1.0,tri)} conjErr={conj_err:.2e} "
          f"pairErr={contrib_err:.2e} parsevalErr={parseval_err:.2e} phys={phys}")
    return paired_min,tri


def main():
    # All are proper dyadic subgroups, with odd m == 1 mod 4 and even pair count.
    cells=[(8,1801),(16,1297),(32,3617)]
    for n,p in cells:
        for r in (5,6):
            mn,tr=analyze(n,p,r)
            assert mn < -1e-7*max(1.0,tr)
    print("VERDICT: conjugate-pair-preserving, exactly balanced moves reverse every actual r=5/6 cell.")

if __name__=='__main__': main()
