#!/usr/bin/env python3
"""
#407 cumulant-from-flatness: DOES the L1-autocorrelation bound on the DFT moment P_{2r}
stay within a CONSTANT of the Gaussian target as m grows? (The crux of the escape.)

Key normalized object: R(h) = (1/m) sum_j a_j conj(a_{j+h}),  a_j = tau_j/sqrt(p) unimodular.
By I3 (exact): R(h) = conj(tau_h) T_h / p, so |R(h)| = |T_h|/sqrt(p).  R(0) ~ 1.

DFT moment:  P_{2r} = m^r * W_r,  W_r := sum over closed r-walks (h_1+..+h_r=0) of prod_i R(h_i).
   r=1: W_1 = R(0) ~ 1, P_2 = m R(0) ~ m. target (2*1-1)!! m = m. ratio 1.
   r=2: W_2 = sum_h R(h)R(-h) = sum_h |R(h)|^2 (R(-h)=conj R(h)). target 3.
   r=3: W_3 = sum_{h1,h2} R(h1)R(h2)R(-h1-h2). target 15.
L1 bound:  W_r^{L1} := sum over closed r-walks of prod|R(h_i)|.  P_{2r} <= m^r W_r^{L1}.
TARGET:    (2r-1)!! (the diagonal/Gaussian W_r).  ESCAPE iff W_r^{L1} <= C*(2r-1)!! for ALL r<=ln m.

We measure W_r^{L1}/(2r-1)!! for r=2,3 (r=4 is O(m^3) loop, only small m) on GOOD primes
(N=2n-3, kappa~Gaussian) as m grows, to see if the L1 autocorrelation bound is m-STABLE.

ALSO: the autocorrelation sequence |R(h)| = |T_h|/sqrt(p). Its OWN sup and L1/L2 profile:
  S1 := sum_{h!=0}|R(h)|,  S2 := sum_{h!=0}|R(h)|^2,  Rmax := max_{h!=0}|R(h)|.
If |R(h)| ~ |T_h|/sqrt(p) ~ sqrt(n)/sqrt(p) ~ 1/sqrt(m) (generic), then S2 ~ m*(1/m)=O(1) (good),
S1 ~ m/sqrt(m)=sqrt(m) (BAD for triangle), Rmax ~ sqrt(log m)/sqrt(m) (good). So the L2/sup
profile of R is GOOD (sub-Gaussian) while L1 is bad -- the moment route uses L2-type (W_r), not L1.
"""
import cmath, math
import sympy

def primitive_root(p): return int(sympy.primitive_root(p))

def setup(p,n):
    m=(p-1)//n
    g=primitive_root(p)
    dlog=[0]*p;cur=1
    for k in range(p-1): dlog[cur]=k; cur=cur*g%p
    def chi_pow(j,x):
        x%=p
        if x==0: return 0.0
        return cmath.exp(2j*math.pi*(j*dlog[x])/m)
    def psi(x): return cmath.exp(2j*math.pi*(x%p)/p)
    mu=[pow(g,(m*t)%(p-1),p) for t in range(n)]
    tau=[sum(chi_pow(j,x)*psi(x) for x in range(1,p)) for j in range(m)]
    a=[t/math.sqrt(p) for t in tau]
    mu_set=set(mu)
    return m,a,mu,mu_set

def Ncount(p,n,mu,mu_set):
    inv=[0]*p
    for x in range(1,p): inv[x]=pow(x,p-2,p)
    N=0
    for w in mu:
        if w==1: continue
        A=(1-w)%p
        for wp in mu:
            if wp==1: continue
            B=(1-wp)%p
            if (A*inv[B])%p in mu_set: N+=1
    return N

def dfac2(r):
    x=1
    for i in range(1,r+1): x*=(2*i-1)
    return x

def run(p,n,want_r4=False):
    m,a,mu,mu_set=setup(p,n)
    R=[sum(a[j]*a[(j+h)%m].conjugate() for j in range(m))/m for h in range(m)]
    absR=[abs(x) for x in R]
    # W_r L1 (closed walk, abs)
    W2L1=sum(absR[h]*absR[(-h)%m] for h in range(m))
    W3L1=0.0
    for h1 in range(m):
        for h2 in range(m):
            W3L1+=absR[h1]*absR[h2]*absR[(-h1-h2)%m]
    out=dict(m=m,W2L1=W2L1,W2r=W2L1/dfac2(2),
             W3L1=W3L1,W3r=W3L1/dfac2(3))
    if want_r4 and m<=30:
        W4L1=0.0
        for h1 in range(m):
            for h2 in range(m):
                for h3 in range(m):
                    W4L1+=absR[h1]*absR[h2]*absR[h3]*absR[(-h1-h2-h3)%m]
        out['W4L1']=W4L1; out['W4r']=W4L1/dfac2(4)
    # autocorr profile
    S1=sum(absR[h] for h in range(1,m)); S2=sum(absR[h]**2 for h in range(1,m))
    Rmax=max(absR[1:],default=0.0)
    out.update(S1=S1,S2=S2,Rmax=Rmax,S1_over_sqrtm=S1/math.sqrt(m),
               Rmax_times_sqrtm=Rmax*math.sqrt(m),
               Rmax_norm=Rmax*math.sqrt(m)/math.sqrt(math.log(max(m,2))))
    out['N']=Ncount(p,n,mu,mu_set); out['floor']=2*n-3
    return out

def find_primes(n,count,start=2,cap=30000):
    out=[];k=start
    while len(out)<count:
        p=k*n+1
        if p>cap: break
        if sympy.isprime(p): out.append(p)
        k+=1
    return out

if __name__=="__main__":
    print("#407: L1-autocorrelation moment-bound m-scaling (GOOD primes N=2n-3 highlighted)\n")
    print(f"{'p':>6}{'n':>4}{'m':>5} | {'N-fl':>5} | {'W2/3':>7}{'W3/15':>7} | "
          f"{'S2':>6}{'S1/vm':>6}{'Rmax*vm':>8}{'Rmaxnrm':>8}")
    for n in [8,16,32]:
        # get a range of m by scanning primes
        ps=find_primes(n,30)
        for p in ps:
            r=run(p,n)
            if r['m']<3 or r['m']>60: continue
            # only print every few, and always good primes
            good = (r['N']==r['floor'])
            tag=" G" if good else "  "
            if r['m'] in (3,5,7,9,11,15,21,30,40,50) or good:
                print(f"{p:>6}{n:>4}{r['m']:>5} | {r['N']-r['floor']:>5} | "
                      f"{r['W2r']:>7.3f}{r['W3r']:>7.3f} | "
                      f"{r['S2']:>6.2f}{r['S1_over_sqrtm']:>6.2f}{r['Rmax_times_sqrtm']:>8.2f}{r['Rmax_norm']:>8.3f}{tag}")
    print("\nW2/3, W3/15 = L1 walk-bound / Gaussian target. If m-STABLE (~const) the L1 autocorr")
    print("certifies the cumulant. S2 (L2 of R) ~ O(1) good; S1/vm ~ const (L1 grows as sqrt m, bad);")
    print("Rmax*vm/sqrt(log m) ~ const = the autocorrelation sup obeys the sub-Gaussian law.")
