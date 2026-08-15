#!/usr/bin/env python3
"""Exact probe for dyadic kernel-domain character normals in the #466 CORE covariance.

For G=<h> of order n and the canonical row W_G(t)=#{(y,z):2y-z=t}, write u=z/y.
Then exactly
  W_G(t)=sum_{j=0}^{n-1} 1_{(2-h^j)G}(t).
For the adjacent-rank row R_r, put
  H_j=sum_{t in (2-h^j)G} R_r(t).
Thus CORE A_r=p*sum_j H_j-n^2*sum_t R_r(t).  The unique real order-2 input-character
normal and the real order-4 normal are
  K2=p*sum_j (-1)^j H_j,
  K4=p*sum_j cos(pi*j/2) H_j,
with exact integer weights.  They are predeclared, row-labelled, and distinct from quotient-side
character truncations: Fourier analysis is on the kernel input u, before u -> (2-u)G.
"""
from __future__ import annotations
import importlib.util
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
P=ROOT/'scripts/probes/g276_termwise_weil_l1_probe.py'
spec=importlib.util.spec_from_file_location('g276',P)
g=importlib.util.module_from_spec(spec); spec.loader.exec_module(g)

def sgn(x): return (x>0)-(x<0)

def cell(n,p,r):
    W,hist,root=g.profiles(p,n)
    R=g.additive_corr_exact_fft(hist[r],hist[r-1])
    G,zroot=g.subgroup(p,n)
    # g.subgroup returns powers of zeta in exponent order, which is the canonical kernel order.
    assert zroot==root
    H=[]
    for u in G:
        a=(2-u)%p
        # a=0 iff 2 in G; then (2-u)G is the zero singleton with multiplicity n in the
        # original y-parametrization. Handle it with the exact class sum convention.
        if a==0:
            H.append(n*R[0])
        else:
            H.append(sum(R[(a*x)%p] for x in G))
    T=sum(R)
    A=p*sum(W[x]*R[x] for x in range(p))-n*n*T
    A2=p*sum(H)-n*n*T
    assert A==A2,(n,p,r,A,A2)
    k2=p*sum((1 if j%2==0 else -1)*v for j,v in enumerate(H))
    w4=(1,0,-1,0)
    k4=p*sum(w4[j%4]*v for j,v in enumerate(H))
    # generator inversion leaves K2 and Re K4 unchanged.
    Hr=[H[(-j)%n] for j in range(n)]
    assert k2==p*sum((1 if j%2==0 else -1)*v for j,v in enumerate(Hr))
    assert k4==p*sum(w4[j%4]*v for j,v in enumerate(Hr))
    return dict(n=n,p=p,r=r,A=A,K2=k2,K4=k4,H=H)

def main():
    cells=[]
    # Complete established n=16 window, both live ranks.
    for p in range(17,2601):
        if (p-1)%16==0 and g.is_prime(p):
            cells += [(16,p,5),(16,p,6)]
    # Cross-scale cells already used by G268/G278/G280.
    cells += [(8,113,3),(8,113,4),(8,2969,3),(8,2969,4),
              (32,641,5),(32,641,6),(32,1217,5),(32,1217,6),
              (32,3617,5),(32,3617,6),(32,70753,5),(32,70753,6)]
    rows=[]
    for c in cells:
        z=cell(*c); rows.append(z)
        print(f'n={z["n"]:2d} p={z["p"]:6d} r={z["r"]} A={z["A"]:+16d} '
              f'K2={z["K2"]:+18d} K4={z["K4"]:+18d}')
    print('\nSUMMARY')
    for key in ('K2','K4'):
        nz=[z for z in rows if z[key]]
        pairs=sorted(set((sgn(z['A']),sgn(z[key])) for z in nz))
        agree=sum(sgn(z['A'])==sgn(z[key]) for z in nz)
        print(f'{key}: agree={agree}/{len(nz)} pairs={pairs} zeros={len(rows)-len(nz)}')
        # A sign-carrying normal must at minimum avoid mismatches in either polarity.  Require
        # exact witnesses to both failures: normal positive with CORE negative, and normal negative
        # with CORE positive.  K2 in fact realizes all four quadrants; K4 need not.
        assert (-1,1) in pairs and (1,-1) in pairs,(key,pairs)
    # Same-cell adjacent-rank obstruction: a fixed normal can agree at one rank and fail at the next.
    by={(z['n'],z['p'],z['r']):z for z in rows}
    split=[]
    for n,p,r in cells:
        if r!=5 or (n,p,6) not in by: continue
        a,b=by[(n,p,5)],by[(n,p,6)]
        if sgn(a['K2'])==sgn(a['A']) and sgn(b['K2'])!=sgn(b['A']): split.append((n,p,'K2'))
        if sgn(a['K4'])==sgn(a['A']) and sgn(b['K4'])!=sgn(b['A']): split.append((n,p,'K4'))
    assert split
    print('adjacent-rank agree->fail witnesses:',split[:20])
    print(f'G285 EXACT PASS: {len(rows)} cells; both canonical low-order kernel-domain real character normals have exact sign mismatches in both directions.')

if __name__=='__main__': main()
