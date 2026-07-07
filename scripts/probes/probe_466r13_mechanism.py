#!/usr/bin/env python3
"""
#466 R13 mechanism: WHY worst-case I(s0) over a proper hyperplane H reaches
|H|-scale (World II), and whether M can possibly control it.

Two clean facts to nail:
 (A) The second-moment (average over s0) is EXACTLY sqrt-scale and follows from M:
        (1/q) sum_{s0} |I(s0)|^2 = sum_{b in H} |eta_b|^2  <= |H|*M^2.
     So the L2-average |I| = sqrt(sum_{b in H}|eta_b|^2) <= sqrt(|H|)*M -- WORLD I holds ON AVERAGE.
 (B) The WORST s0 blows past it: it aligns the H-spectrum phases. We locate worst_s0
     and show |I(worst_s0)| ~ c*|H|*M with c bounded below (NOT -> 0), so no bound of
     the form f(M) alone controls it: two spectra with the SAME sup-norm M can have
     wildly different worst-case I (one aligned, one random). We demonstrate the
     COUNTEREXAMPLE-TO-DERIVABILITY: replace {eta_b} by a RANDOM-PHASE spectrum with
     the SAME |eta_b| (hence same M and same L2), and show worst|I| drops to sqrt-scale
     -- proving worst|I| depends on the SIGNS/PHASES, an input M does not carry.
"""
import math, sys
import numpy as np

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def primitive_root(p):
    phi = p-1; factors=[]; m=phi; d=2
    while d*d<=m:
        if m%d==0:
            factors.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: factors.append(m)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in factors): return g

def find_prime(n, pmin=None):
    if pmin is None: pmin=n**4
    p=pmin-(pmin%n)+1
    if p<pmin: p+=n
    while True:
        if is_prime(p) and (p-1)%n==0: return p
        p+=n

def subgroup(p,n,g):
    h=pow(g,(p-1)//n,p); S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return S

def all_etas(p, mu):
    ind=np.zeros(p);
    for y in mu: ind[y%p]=1.0
    return np.conjugate(np.fft.fft(ind))

def main():
    rng = np.random.default_rng(12345)
    lines=[]
    def P(s): lines.append(s); print(s); sys.stdout.flush()
    for n in [8,16]:
        p=find_prime(n); g=primitive_root(p); mu=subgroup(p,n,g)
        eta=all_etas(p,mu)
        M=float(np.max(np.abs(eta[1:])))
        deg=2
        gh=pow(g,deg,p); H=set(); x=1
        while x not in H: H.add(x); x=(x*gh)%p
        H.discard(0)
        Harr=np.array(sorted(H))
        absH=len(Harr)
        l2H=float(math.sqrt(np.sum(np.abs(eta[Harr])**2)))
        MH=float(np.max(np.abs(eta[Harr])))

        # (A) second moment over s0 EXACTLY:
        c=np.zeros(p,dtype=complex); c[Harr]=np.conjugate(eta[Harr])
        X=np.fft.fft(c)                       # X[k]=I(-k); |X| = set of |I(s0)|
        absI=np.abs(X)
        avg_sq = float(np.mean(absI**2))
        worst=float(np.max(absI))
        P(f"\nn={n} p={p} deg={deg} |H\\0|={absH} M={M:.3f} M_H={MH:.3f}")
        P(f"  (A) 2nd moment: mean_s0|I|^2 = {avg_sq:.2f}   sum_b|eta_b|^2 (over H) = {l2H**2:.2f}"
          f"   [equal => WORLD I holds on AVERAGE; sqrt = {math.sqrt(avg_sq):.2f} ~ sqrt|H|*? ]")
        P(f"      sqrt(mean|I|^2) = {math.sqrt(avg_sq):.2f}  <= sqrt|H|*M = {math.sqrt(absH)*M:.2f}  (World-I avg bound)")
        # (B) worst case
        ws0 = int(np.argmax(absI))
        P(f"  (B) WORST: worst|I| = {worst:.2f}  ~ {worst/absH:.4f}*|H|   (>> sqrt|H|*M={math.sqrt(absH)*M:.2f})")
        P(f"      worst / sqrt(mean|I|^2) = {worst/math.sqrt(avg_sq):.2f}  ~ sqrt|H|={math.sqrt(absH):.1f}"
          f"   => worst is sqrt|H| ABOVE the rms: a rare aligned peak, NOT the average")

        # (B-counterexample) SAME |eta_b|, random phases -> same M, same L2, different worst
        worst_rand=[]
        for _ in range(8):
            phase=np.exp(2j*math.pi*rng.random(absH))
            c2=np.zeros(p,dtype=complex)
            c2[Harr]=np.abs(eta[Harr])*phase     # identical moduli => identical M and L2
            w2=float(np.max(np.abs(np.fft.fft(c2))))
            worst_rand.append(w2)
        wr=np.array(worst_rand)
        P(f"  (B-CTX) SAME moduli |eta_b| (=> SAME M, SAME L2), RANDOMIZED phases:")
        P(f"      worst|I| over 8 draws: mean={wr.mean():.1f} max={wr.max():.1f} min={wr.min():.1f}")
        P(f"      TRUE(arith-phase) worst = {worst:.1f}   random-phase worst ~ {wr.mean():.1f}")
        P(f"      ratio true/random = {worst/wr.mean():.2f}  "
          f"=> worst|I| DEPENDS ON PHASES that M does NOT carry" if worst/wr.mean()>1.3
          else f"      ratio true/random = {worst/wr.mean():.2f}")
        # sqrt|H|*M reference for random
        P(f"      (random worst ~ sqrt(2 ln|H|)*L2rms-ish; sqrt|H|*M={math.sqrt(absH)*M:.1f}, L2={l2H:.1f})")

    with open("scripts/probes/_out_466r13_mechanism.txt","w") as f:
        f.write("\n".join(lines))

if __name__=="__main__":
    main()
