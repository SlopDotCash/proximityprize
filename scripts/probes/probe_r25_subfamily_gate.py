#!/usr/bin/env python3
"""Probe #466 R25 SUBY: subfamily-Y ChiDecompositionOff.

Question: for Y = chiFamily(chi^t) (t | m, m' = m/t), does the consumer's needed identity
  m * I_H(s0) = -|G| + sum_{chi' in Y} g(chi') T_{chi'}(s0)   (H = ker chi, coefficient m)
hold off D?  Equivalently residual(s0) := sum_{chi' in chiFamily(chi)\\Y} g T = 0 off D?

Exact algebra:  residual(s0) = m*I_H(s0) - m'*I_{H'}(s0)  where H' = ker(chi^t).
So Y-decomposition (with ORIGINAL H,m) <=> m*I_H = m'*I_{H'} off D.
"""
import cmath, math, itertools, random

def probe(p, m, t, Gset=None, seed=0):
    # multiplicative group of F_p
    # find generator
    def is_gen(g):
        seen=set(); x=1
        for _ in range(p-1):
            x=x*g%p; seen.add(x)
        return len(seen)==p-1
    g0 = next(g for g in range(2,p) if is_gen(g))
    assert (p-1)%m==0
    # chi(g0^k) = e^{2 pi i k / m}
    dlog = {}
    x=1
    for k in range(p-1):
        x = x*g0%p if k>0 else 1
    x=1; dlog[1]=0
    for k in range(1,p-1):
        x=x*g0%p; dlog[x]=k
    def chi_j(j, a):  # chi^j (a), chi of order m; chi(a)=e(dlog/ (p-1) * ((p-1)/m) )
        if a%p==0: return 0
        return cmath.exp(2j*math.pi * j * dlog[a%p] * ((p-1)//m) / (p-1))
    rng = random.Random(seed)
    if Gset is None:
        Gset = sorted(rng.sample(range(1,p), 4))
    psi = lambda a: cmath.exp(2j*math.pi*(a%p)/p)
    eta = lambda b: sum(psi(b*x) for x in Gset)
    gauss = lambda j: sum(chi_j(j,a)*psi(a) for a in range(1,p))
    T = lambda j,s0: sum(chi_j(j, s0-x).conjugate() for x in Gset)
    H  = [b for b in range(1,p) if abs(chi_j(1,b)-1)<1e-9]
    mp = m//t
    Hp = [b for b in range(1,p) if abs(chi_j(t,b)-1)<1e-9]
    I = lambda HH,s0: sum(eta(b).conjugate()*psi(b*s0) for b in HH)
    D = set(Gset)|{0}
    worst_id = 0.0; max_res = 0.0; nzero=0; ntot=0
    for s0 in range(p):
        if s0 in D: continue
        ntot+=1
        full = [j for j in range(1,m)]
        Yj   = [t*j for j in range(1,mp)]
        omitted = [j for j in full if j not in Yj]
        res = sum(gauss(j)*T(j,s0) for j in omitted)
        lhs = m*I(H,s0) - mp*I(Hp,s0)
        worst_id = max(worst_id, abs(res-lhs))
        max_res = max(max_res, abs(res))
        if abs(res)<1e-8: nzero+=1
    print(f"p={p} m={m} t={t} m'={mp} |H|={len(H)} |H'|={len(Hp)} G={Gset}: "
          f"identity err={worst_id:.2e}  max|res|={max_res:.3f}  res==0 at {nzero}/{ntot} offsets")

probe(41, 8, 2)
probe(41, 8, 4)
probe(41, 8, 2, seed=1)
probe(73, 8, 2)
probe(73, 8, 2, seed=2)
probe(41, 10, 5)
