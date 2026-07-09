#!/usr/bin/env python3
"""
#407 cumulant-from-flatness: PIN the two laws precisely.
(A) L1 walk-bound growth: W_r^{L1}/(2r-1)!!  ~ ?  in m  (is it (log m)^{r/2}? a power of m?).
(B) autocorrelation sub-Gaussian law: |R(h)| = |T_h|/sqrt(p); does max_{h!=0}|R(h)| <= C sqrt(log m / m)?
    i.e. max_h |T_h| <= C sqrt(p log m / m) = C sqrt(n log m)   <-- EXACTLY the STFL tangent flatness!
    So the autocorrelation sup-law IS the tangent flatness conjecture. Confirm equivalence numerically
    and FIT the constant + the growth exponent of W_r^{L1}.

We fit on GOOD primes (N=2n-3) across the widest m range we can compute, n=8,16.
For (A): regress log(W_r^{L1}/(2r-1)!!) on log(log m) and on log m.
For (B): regress log(Rmax) on log m to confirm slope -1/2 with a log correction.
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
    mu_set=set(mu)
    tau=[sum(chi_pow(j,x)*psi(x) for x in range(1,p)) for j in range(m)]
    a=[t/math.sqrt(p) for t in tau]
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

def run(p,n):
    m,a,mu,mu_set=setup(p,n)
    R=[sum(a[j]*a[(j+h)%m].conjugate() for j in range(m))/m for h in range(m)]
    absR=[abs(x) for x in R]
    W2L1=sum(absR[h]*absR[(-h)%m] for h in range(m))
    W3L1=float('nan')
    if m<=45:
        W3L1=0.0
        for h1 in range(m):
            for h2 in range(m):
                W3L1+=absR[h1]*absR[h2]*absR[(-h1-h2)%m]
    Rmax=max(absR[1:],default=0.0)
    N=Ncount(p,n,mu,mu_set)
    return dict(m=m,N=N,floor=2*n-3,
                W2r=W2L1/dfac2(2),W3r=W3L1/dfac2(3),Rmax=Rmax,
                # tangent flatness: max|T_h| = Rmax*sqrt(p); normalize by sqrt(n log m)
                Tflat=Rmax*math.sqrt(p)/math.sqrt(n*math.log(max(m,2))),
                Rmax_law=Rmax/math.sqrt(math.log(max(m,2))/m))

def find_primes(n,count,start=2,cap=3500):
    out=[];k=start
    while len(out)<count:
        p=k*n+1
        if p>cap: break
        if sympy.isprime(p): out.append(p)
        k+=1
    return out

def fit(xs,ys):
    n=len(xs)
    if n<2: return (float('nan'),float('nan'))
    sx=sum(xs); sy=sum(ys); sxx=sum(x*x for x in xs); sxy=sum(x*y for x,y in zip(xs,ys))
    den=n*sxx-sx*sx
    if abs(den)<1e-12: return (float('nan'),float('nan'))
    slope=(n*sxy-sx*sy)/den
    intercept=(sy-slope*sx)/n
    return (slope,intercept)

def mean(v): return sum(v)/len(v) if v else float('nan')

if __name__=="__main__":
    print("#407: pin (A) L1-walk growth law, (B) autocorr sub-Gaussian = tangent flatness\n")
    rows=[]
    for n in [8,16]:
        for p in find_primes(n,70):
            r=run(p,n)
            if r['N']!=r['floor']: continue   # GOOD primes only
            if r['m']<5: continue
            rows.append((n,p,r))
        print(f"  (n={n}: collected {sum(1 for x in rows if x[0]==n)} good primes)",flush=True)
    # print a sample
    print(f"{'n':>3}{'p':>7}{'m':>5} | {'W2/3':>6}{'W3/15':>6} | {'Rmax':>7} {'Tflat':>6} {'Rmaxlaw':>7}")
    for (n,p,r) in rows:
        if r['m'] in (5,9,17,29,42,57,72,99,128) or p==rows[-1][1]:
            print(f"{n:>3}{p:>7}{r['m']:>5} | {r['W2r']:>6.3f}{r['W3r']:>6.3f} | "
                  f"{r['Rmax']:>7.4f} {r['Tflat']:>6.3f} {r['Rmaxlaw']:>7.3f}")
    # fits over all good rows with m large enough
    big=[r for (n,p,r) in rows if r['m']>=12]
    lm=[math.log(r['m']) for r in big]
    llm=[math.log(math.log(r['m'])) for r in big]
    print("\n--- FITS (good primes, m>=12) ---")
    for key,lab in [('W2r','W2/3'),('W3r','W3/15')]:
        ly=[math.log(r[key]) for r in big]
        s_lm=fit(lm,ly); s_llm=fit(llm,ly)
        print(f"log({lab}) = {s_lm[0]:+.3f}*log m + {s_lm[1]:+.2f}   |   "
              f"{s_llm[0]:+.3f}*log(log m) + {s_llm[1]:+.2f}")
    # Rmax law: log Rmax vs log m ; expect slope -1/2 (times sqrt log correction)
    lRmax=[math.log(r['Rmax']) for r in big]
    s=fit(lm,lRmax)
    print(f"log(Rmax) = {s[0]:+.3f}*log m + {s[1]:+.2f}   (slope -0.5 = 1/sqrt m scaling)")
    # Tflat (the tangent-flatness constant) trend
    Tf=[r['Tflat'] for r in big]
    print(f"Tflat = max|T_h|/sqrt(n log m): mean {mean(Tf):.3f} range [{min(Tf):.3f},{max(Tf):.3f}]  (FLAT => STFL law holds w/ that C)")
    print("\nINTERPRETATION:")
    print(" (A) W_r/(2r-1)!! slope vs log m: if ~+0.x*log m it GROWS polynomially (L1 route walls);")
    print("     if ~ via log(log m) with small power, drifts only logarithmically.")
    print(" (B) Rmax slope ~ -0.5 confirms |R(h)|<=C sqrt(log m/m) <=> max|T_h|<=C sqrt(n log m) = TANGENT FLATNESS.")
