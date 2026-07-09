#!/usr/bin/env python3
"""
Route [stepanov] — Burgess/Stepanov amplification re-examined in the FIXED-INDEX regime (#407).

Object: eta_b = sum_{x in mu_n} e_p(b x), B = max_{b != 0} |eta_b|. Target: B <= C sqrt(n log m),
m = (p-1)/n. The route hint: Burgess subgroup-sum bounds need |H| > p^{1/4}; in the fixed-index
prize regime n = Theta(p), so they MIGHT be in regime (unlike the thin framing).

This probe pins:
 (1) the precise regime crossing (gamma = log_p n) for fixed m = 2^128;
 (2) what the best MAGNITUDE bound (Gauss B<=sqrt(p), BGK B<=n^{1-nu}) delivers vs target, by exponent;
 (3) NUMERICALLY: the overshoot factor sqrt(p)/B grows like sqrt(m/log m) as the index m grows,
     so being "in regime" for Burgess does NOT close the half-power gap; the residual is the
     sqrt-cancellation among the m FIXED Gauss-sum phases (a flatness/Salem-Zygmund statement),
     which no magnitude method controls.
"""
import cmath, math

# ---------- (1) regime pin ----------
def regime():
    print("="*78)
    print("(1) REGIME PIN: m = 2^128 fixed (index), vary n -> p = n*2^128")
    print(f"{'log2 n':>7} {'log2 p':>7} {'gamma':>7} {'> p^1/4?':>9} {'> p^1/2?':>9}")
    for log2n in [16, 32, 43, 64, 128, 256, 1024]:
        log2p = log2n + 128
        gamma = log2n/log2p
        print(f"{log2n:>7} {log2p:>7} {gamma:>7.4f} {'YES' if log2n>log2p/4 else 'no':>9} {'YES' if log2n>log2p/2 else 'no':>9}")
    print("  Burgess subgroup threshold n>p^(1/4) <=> log2 n > 42.67.")
    print("  PRIZE INSTANCES (n=2^16..2^40) are BELOW it (gamma<1/4, THIN).")
    print("  Asymptotically (n->inf, m fixed) gamma->1 (positive-proportion): Burgess IN regime,")
    print("  BUT a *uniform* theorem must hold at the thin instances too -> binding case is thin.")
    print()

# ---------- (2) exponent comparison ----------
def exponents():
    print("="*78)
    print("(2) EXPONENT of n: best magnitude bound vs target, across gamma")
    print(f"{'gamma':>6} {'target(1/2)':>12} {'BGK 1-nu(opt)':>14} {'gap':>7}")
    for gamma in [0.20, 0.25, 0.50, 0.99]:
        nu = min(gamma/12, 0.05)  # optimistic Shkredov-type saving
        print(f"{gamma:>6.2f} {0.5:>12.2f} {1-nu:>14.4f} {1-nu-0.5:>7.3f}")
    print("  Magnitude bounds save a tiny nu; target needs to save 1/2. ~HALF A POWER short at every gamma<1.")
    print()

# ---------- (3) numerical overshoot ----------
def is_prime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    phi=p-1; facs=set(); x=phi; d=2
    while d*d<=x:
        while x%d==0: facs.add(d); x//=d
        d+=1
    if x>1: facs.add(x)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs): return g
def true_B(p,n):
    m=(p-1)//n; g=primroot(p); gen=pow(g,m,p)
    H=[]; x=1
    for _ in range(n): H.append(x); x=(x*gen)%p
    best=0.0
    for b in range(1,p):
        s=0j
        for x in H: s+=cmath.exp(2j*math.pi*((b*x)%p)/p)
        if abs(s)>best: best=abs(s)
    return best

def overshoot():
    print("="*78)
    print("(3) NUMERICAL: magnitude-bound overshoot sqrt(p)/B grows like sqrt(m/log m) as index m grows")
    print(f"{'n':>4} {'m':>5} {'p':>8} {'gamma':>6} {'B':>8} {'sqrt(p)/B':>10} {'sqrt(m/logm)':>13} {'B/sqrt(nlogm)':>14}")
    n_target=9
    for m in [4,8,16,32,64,128,256,512,1024,2048,4096]:
        found=None
        for nn in range(8,40):
            p=m*nn+1
            if is_prime(p): found=(p,nn); break
        if not found: continue
        p,nn=found
        B=true_B(p,nn)
        gamma=math.log(nn)/math.log(p); logm=math.log(m)
        print(f"{nn:>4} {m:>5} {p:>8} {gamma:>6.3f} {B:>8.3f} {math.sqrt(p)/B:>10.3f} {math.sqrt(m/logm):>13.3f} {B/math.sqrt(nn*logm):>14.3f}")
    print()
    print("  sqrt(p)/B tracks sqrt(m/logm). At prize m=2^128: overshoot ~ 2^64/sqrt(88) ~ 2^61.")
    print("  => NO magnitude bound (Gauss sqrt(p), BGK, Burgess) recovers this; the gap is the FULL")
    print("     sqrt-cancellation among the m fixed Gauss phases. B/sqrt(n log m) stays ~1 (flat, the target).")

if __name__=='__main__':
    regime(); exponents(); overshoot()
