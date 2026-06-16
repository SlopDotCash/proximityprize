#!/usr/bin/env python3
"""
WF407 / salemzygmund — DERANDOMIZATION test.

Salem-Zygmund genericity claim: the DETERMINISTIC Gauss-sum coefficient sequence
a_j = tau(psi^j)/sqrt(p)  behaves (for ||P||_inf) like a RANDOM unimodular sequence.
We test the ratio
    rho := ||P||_inf(real Gauss a_j)  /  ||P||_inf(random unimodular, same m)
sweeping toward the prize regime (large m = index, so log(p/n)=log m large).

If rho ~ 1 (or <= 1), the genericity/derandomization direction holds: the Gauss phases
are at most as aligned as random => the upper bound transfers. A rho >> 1 (alignment)
would REFUTE the route. We also directly report
    R_real = B/sqrt(n log m)   and   R_rand = B_rand/sqrt(n log m)
for matched (n,m).

KEY: we use the EXACT DFT identity P(c) = sum_{j=1}^{m-1} a_j omega^{-jc} with the TRUE
Gauss sums a_j computed from the multiplicative character of F_p (no eta recomputation),
so this isolates the coefficient sequence's flatness.
"""
import cmath, math, random, statistics as st

def is_prime(n):
    if n<2: return False
    for d in range(2,int(n**0.5)+1):
        if n%d==0: return False
    return True

def primitive_root(p):
    if p==2: return 1
    phi=p-1; fac=[]; t=phi; d=2
    while d*d<=t:
        if t%d==0:
            fac.append(d)
            while t%d==0: t//=d
        d+=1
    if t>1: fac.append(t)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g

def gauss_coeffs(p,n,g=None):
    """Return a_j = tau(psi^j)/sqrt(p) for j=1..m-1, where psi runs over the m characters
    trivial on mu_n (order dividing m), via the index-m character psi(g^k)=e(k/m).
    tau(chi) = sum_{t in F_p^x} chi(t) e_p(t).  chi = psi^j means chi(g^k)=e(jk/m).
    Using discrete log: every t = g^{dlog(t)}, chi(t)=e(j*dlog(t)/m)."""
    m=(p-1)//n
    if g is None: g=primitive_root(p)
    # discrete log table
    dlog=[0]*p
    x=1
    for k in range(p-1):
        dlog[x]=k
        x=(x*g)%p
    ep=[cmath.exp(2j*math.pi*t/p) for t in range(p)]
    # tau(psi^j) = sum_{t=1}^{p-1} e(j*dlog(t)/m) * e_p(t)
    a=[]
    for j in range(1,m):
        s=0j
        wj=cmath.exp(2j*math.pi*j/m)  # base for e(j*k/m) = wj^k
        for t in range(1,p):
            s+= (wj**dlog[t]) * ep[t]
        a.append(s/math.sqrt(p))
    return a,m,g

def Psupnorm_from_coeffs(a,m):
    """||P||_inf = max_{c=0..m-1} |sum_{j=1}^{m-1} a_j omega^{-jc}|, omega=e(1/m)."""
    om=cmath.exp(-2j*math.pi/m)
    best=0.0
    for c in range(m):
        s=0j
        wc=om**c  # omega^{-... } careful: we want omega^{-jc} = (om?) ; define base = e(-2pi i c/m)
        base=cmath.exp(-2j*math.pi*c/m)
        bj=1
        s=0j
        for j in range(1,m):
            bj*=base
            s+=a[j-1]*bj
        best=max(best,abs(s))
    return best

def main():
    random.seed(3)
    print("Derandomization ratio rho = ||P||_inf(Gauss) / ||P||_inf(random), matched m.")
    print(f"{'p':>7} {'n':>4} {'m':>5} {'beta=log_n p':>12} | {'Pinf_real':>10} {'Pinf_rand(med)':>14} "
          f"{'rho(med)':>9} | {'R_real':>7} {'unimod|a|err':>12}")
    cases=[]
    # push m up: small n, p as large as feasible (cost ~ p per character * m chars ~ p*m/n = p^2/n... heavy)
    for n in [4,6,8,10]:
        cnt=0; p=n+1
        while cnt<4:
            p+=1
            if p>4000: break
            if is_prime(p) and (p-1)%n==0:
                m=(p-1)//n
                if m<10: continue
                cases.append((p,n,m)); cnt+=1
    for (p,n,m) in cases:
        a,m,g=gauss_coeffs(p,n)
        # verify |a_j| ~ 1 (unimodular)
        amag_err=max(abs(abs(x)-1.0) for x in a)
        Pinf_real=Psupnorm_from_coeffs(a,m)
        # B_real = (sqrt(p)/m)*Pinf_real  (DFT identity, ignoring the -1/m principal shift)
        B_real=math.sqrt(p)/m*Pinf_real
        target=math.sqrt(n*math.log(m))
        R_real=B_real/target
        # random control: 30 trials
        rr=[]
        for _ in range(30):
            ar=[cmath.exp(2j*math.pi*random.random()) for _ in range(m-1)]
            rr.append(Psupnorm_from_coeffs(ar,m))
        Pinf_rand=st.median(rr)
        rho=Pinf_real/Pinf_rand if Pinf_rand>0 else float('nan')
        beta=math.log(p)/math.log(n)
        print(f"{p:>7} {n:>4} {m:>5} {beta:>12.3f} | {Pinf_real:>10.3f} {Pinf_rand:>14.3f} "
              f"{rho:>9.3f} | {R_real:>7.3f} {amag_err:>12.2e}")

if __name__=="__main__":
    main()
