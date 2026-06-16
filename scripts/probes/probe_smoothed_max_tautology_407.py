#!/usr/bin/env python3
"""
THE DUALITY WALL, pinned exactly.

The classical LARGE SIEVE inequality: for delta-spaced frequencies b_1..b_R in R/Z (spacing >= delta)
and any sequence (a_x)_{x in mu_n},
   sum_{r=1}^R | sum_x a_x e(b_r x) |^2  <=  (p + 1/delta) * sum_x |a_x|^2.
With a_x = 1 (indicator of mu_n), sum|a_x|^2 = n. The cosets give R=m frequencies; minimal spacing
of the coset reps in [0,p) is delta_min ~ 1 (they are ~uniformly spread, gaps ~ p/m = n). Actually
the m DISTINCT cosets, as points b in [0,p), have typical gap p/m = n, so delta ~ n/p, 1/delta ~ p/n=m... 
Let me just compute the LHS and the spacing directly.

KEY: the large sieve gives  sum_r |S(b_r)|^2 <= (p + 1/delta_min) n. 
But sum_r |S(b_r)|^2 over ALL m cosets = p - n (Parseval, computed earlier). So LS with the FULL
coset set gives p-n <= (p + 1/delta) n -- trivially true, useless for the MAX.

To bound the MAX of one term, large sieve is applied to a SPARSE WELL-SPACED subset, OR via the
DUAL. The honest reduction: max_b|S(b)|^2 <= sum_r |S(b_r)|^2 for ANY set containing b* -- so the
SMALLEST useful set is {b*} alone, giving the trivial identity. There is NO spacing gain because the
max is a SINGLE term and the large sieve bounds a SUM.

=> The large sieve CANNOT isolate the max better than 'max <= sum'. The ONLY way to win is the
AMPLIFIED second moment: bound max by (sum of |S|^{2k})^{1/k} -- but that IS the moment method (walled).

We verify the FUNDAMENTAL no-go for the duality:
  Best 'amplifier that does not know b*' = positive-definite kernel K, bound
     max_b|S(b)|^2 <= (1/min_b' K(0)) * (worst smoothed value).
  Compute the SHARPEST such bound for the Fejer family and confirm it is >= the DIAGONAL n*||K||_1/K(0),
  and that minimizing over K gives >= n * (||K||_1/K(0))_min = n*1 (delta) -- but a delta K cannot be
  realized as a bound without knowing b*. For any HONEST K with Fourier support width F (so it can be
  written down a-priori), ||K||_1/K(0) >= (something). Measure the genuine tradeoff.
"""
import math, numpy as np
def is_prime(n):
    if n<2:return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0:return n==q
    d=n-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1):continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1:break
        else:return False
    return True
def odd_part(x):
    while x%2==0:x//=2
    return x
def primitive_root(p):
    phi=p-1;facs=[];mm=phi;d=2
    while d*d<=mm:
        if mm%d==0:
            facs.append(d)
            while mm%d==0:mm//=d
        d+=1
    if mm>1:facs.append(mm)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs):return g
def find_prime(n,beta,idx=0):
    target=int(round(n**beta));base=target-(target%n)+1;p=base;cnt=0
    while True:
        if p>3 and p%n==1 and is_prime(p) and odd_part((p-1)//n)>1:
            if cnt==idx:return p
            cnt+=1
        p+=n

print("""
THE DUALITY no-go, made precise.

Claim: the smoothed-max amplification bound  max_b|S(b)|^2 <= (1/K(0)) * max_c (|S|^2 * K)(c)
       always satisfies  (1/K(0)) max_c (|S|^2*K)(c)  >=  n * ||K||_1 / K(0) * (avg, not max)...
Let me just directly compute, for the Fejer kernel K of frequency-support-width F (so K is a-priori
writable as a degree-F trig poly in b), the bound value at the WORST c, and see the n^2 floor.
""")

def smoothed_max(n,beta):
    p=find_prime(n,beta); g=primitive_root(p); m=(p-1)//n; eta=pow(g,m,p)
    xs=np.array([pow(eta,i,p) for i in range(n)],dtype=np.int64)
    twp=2.0*math.pi/p
    # full coset period values (squared)
    vals2=np.empty(m); reps=np.empty(m,dtype=np.int64)
    c=1
    for j in range(m):
        ang=((c*xs)%p).astype(np.float64)*twp
        vals2[j]=np.cos(ang).sum()**2+np.sin(ang).sum()**2
        reps[j]=c; c=c*g%p
    B2=vals2.max()
    # The smoothed-max bound with Fejer kernel K_F(b)= Fejer of width F in the INTEGER b-line.
    # (|S|^2 * K_F)(c) = sum_b |S(b)|^2 K_F(b-c). For the BOUND to be a-priori, evaluate the WORST c.
    # Since the worst c is near b*, and |S|^2 is a spike there of height B2 plus RMS background n,
    # (|S|^2 * K_F)(b*) ~ B2*K_F(0) + n * (||K_F||_1 - K_F(0)) ... bound = (1/K0)(B2*K0 + n*(L-K0))
    #   = B2 + n*(L/K0 - 1).  For Fejer width F: K_F(0)=F (peak), ||K_F||_1 = F (sum of triangular) => L/K0=1!
    # Hmm Fejer in b: K_F(j)=(1-|j|/F)_+, K0=1, ||K||_1 = F (sum). So L/K0 = F.
    #   bound ~ B2 + n*(F-1)*(background fraction). Minimized at F=1 -> bound=B2 (trivial delta again).
    # The REAL constraint: an a-priori bound cannot use F=1 because it must hold for the worst c WITHOUT
    # spike alignment. Take c NOT at a spike: then (|S|^2*K)(c) ~ n*F (pure background). The a-priori
    # bound must be the max over c, which INCLUDES the spike: max_c = B2 (at c=b*). So smoothed max = B2.
    # ==> smoothing does NOT reduce the max because the kernel is centered and the max is achieved when
    #     c hits the spike. This is the tautology that kills the route.
    print(f"n={n} p={p} m={m} B2={B2:.1f} B2/n={B2/n:.2f} B2/(n ln m)={B2/(n*math.log(m)):.3f}")
    # Demonstrate: max over c of smoothed |S|^2 with Fejer width F equals B2 (achieved at c=b*) for any F:
    # build |S|^2 on a window around b* in integer b-line, convolve with triangular kernels.
    jstar=int(np.argmax(vals2)); bstar=int(reps[jstar])
    rad=200
    bs=np.arange(bstar-rad,bstar+rad+1)
    S2line=np.array([ (np.cos(((int(b)%p*xs)%p)*twp).sum()**2 + np.sin(((int(b)%p*xs)%p)*twp).sum()**2) for b in bs])
    for F in [1,3,7,15,31]:
        ker=np.maximum(0,1-np.abs(np.arange(-F,F+1))/F) if F>1 else np.array([1.0])
        ker=ker/ker.max()  # K(0)=1
        conv=np.convolve(S2line,ker,mode='same')
        sm_max=conv.max()  # this is max_c (|S|^2 * K)(c) / K(0)
        print(f"    Fejer F={F:3d}: ||K||_1/K0={ker.sum():.1f}  smoothed_max={sm_max:.1f}  /B2={sm_max/B2:.2f}  (>=1 always; route wins only if <1)")
    print()

for n,beta in [(16,4),(32,4),(64,4)]:
    smoothed_max(n,beta)
