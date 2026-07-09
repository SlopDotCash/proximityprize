#!/usr/bin/env python3
"""
#407 cumulant-from-flatness path (assigned angle).

GOAL: connect framings (1) DFT-flatness and (2) cumulant kappa_r RIGOROUSLY, identify
which direction is content, then attack the moment side via the EXACT autocorrelation.

SETUP (prize objects). F_p, n=2^a | p-1, m=(p-1)/n, chi mult char of order m,
mu_n = ker chi, psi=e_p.  tau_j = Gauss sum (|tau_j|=sqrt(p), j!=0; tau_0=-1).
a_j := tau_j / sqrt(p)  (UNIMODULAR for j!=0).
eta_b = sum_{x in mu_n} psi(bx) = (sqrt(p)/m) * D(b),   D(b) := sum_{j=0}^{m-1} a_j w_b^{-j},
   w_b = chi(b) on the unit circle (since eta_b = (1/m) sum_j chi^{-j}(b) tau_j, I1).
So |eta_b| = (sqrt(p)/m) |D(b)|, and the m-DFT D(b) of (a_j) is the central object.

DEFINE the DFT moment:  P_{2r} := (1/m) sum_b |D(b)|^{2r}   (average over the m cosets b).
Then sum_b |eta_b|^{2r} = (p^r / m^{2r}) sum_b |D(b)|^{2r} = (p^r / m^{2r-1}) P_{2r}.

CUMULANT (framing 2):  kappa_r = ( sum_b |eta_b|^{2r} / m ) / ((2r-1)!! n^r).
=> kappa_r = (p^r / m^{2r}) P_{2r} / ((2r-1)!! n^r) = P_{2r} / ((2r-1)!! m^r)  [using p ~ nm].
   (exact: p = nm+? -- p = n*m+1 region? No: p-1 = n*m, so p = nm+1; p^r/(n^r m^r) = (1+1/(nm))^r ~ 1.)

So the EXACT bridge is:   kappa_r  =  (p/(nm))^r * P_{2r} / ((2r-1)!! m^r).
The "flatness target" P_{2r} <= (2r-1)!! m^r  is EXACTLY  kappa_r <= (p/nm)^r ~ 1.

FRAMING (1) flatness: max_b |D(b)| <= C sqrt(m log m).  Note Parseval: P_2 = (1/m)sum|D|^2
 = sum_j |a_j|^2 = (m-1) + 1/p ~ m  (a_0=-1/sqrt(p) tiny).  So |D| has RMS sqrt(m); a
 Gaussian DFT would have P_{2r} ~ (2r-1)!! m^r EXACTLY (complex Gaussian moment). So:
   kappa_r <= 1  <=>  P_{2r} ~ (2r-1)!! m^r  <=>  the DFT (a_j -> D) is COMPLEX-GAUSSIAN to depth r.
   max_b|D(b)| <= C sqrt(m log m)  is the SUP-norm (flatness); P_{2r}<= (2r-1)!! m^r is the MOMENT.
 sup <= C sqrt(m log m)  ==(easy, Markov)==>  P_{2r} <= m^? ... ; moment ==> sup by Markov/union.

THE AUTOCORRELATION (I3, EXACT, machine-verified): with R(h) := (1/m) sum_j a_j conj(a_{j+h})
 the NORMALIZED autocorrelation of (a_j):  R(h) = A_h/(m p) = conj(tau_h) T_h / p = conj(a_h) T_h/sqrt(p).
 R(0) = (1/m) sum|a_j|^2 ~ 1.  P_{2r} expands (DFT moment) into sums of products of R over
 closed h-walks. THE QUESTION: does sum_h |R(h)|^2 (and higher) give P_4, ... <= (2r-1)!! m^r?
"""
import cmath, math
import sympy

def primitive_root(p): return int(sympy.primitive_root(p))

def setup(p, n):
    assert (p-1) % n == 0
    m = (p-1)//n
    g = primitive_root(p)
    dlog = [0]*p; cur=1
    for k in range(p-1): dlog[cur]=k; cur=cur*g%p
    def chi_pow(j,x):
        x%=p
        if x==0: return 0.0
        return cmath.exp(2j*math.pi*(j*dlog[x])/m)
    def psi(x): return cmath.exp(2j*math.pi*(x%p)/p)
    mu = [pow(g,(m*t)%(p-1),p) for t in range(n)]
    tau = []
    for j in range(m):
        s=0j
        for x in range(1,p): s += chi_pow(j,x)*psi(x)
        tau.append(s)
    a = [t/math.sqrt(p) for t in tau]            # a_j unimodular (j!=0)
    return dict(p=p,n=n,m=m,g=g,dlog=dlog,chi_pow=chi_pow,psi=psi,mu=mu,tau=tau,a=a)

def dfac2(r):
    x=1
    for i in range(1,r+1): x*=(2*i-1)
    return x

def analyze(p,n,rmax=4):
    S=setup(p,n); m=S['m']; a=S['a']; mu=S['mu']
    # D(b) = sum_j a_j w_b^{-j}, w_b = chi(b). Enumerate coset reps b.
    # easier: D over the m roots of unity. eta_b = (1/m) sum_j chi^{-j}(b) tau_j.
    # chi(b)=exp(2pi i c/m) for b=g^c. So index cosets by c=0..m-1.
    def D(c):
        return sum(a[j]*cmath.exp(-2j*math.pi*(j*c)/m) for j in range(m))
    Ds = [D(c) for c in range(m)]
    # Parseval check
    P2 = sum(abs(d)**2 for d in Ds)/m
    sum_a2 = sum(abs(x)**2 for x in a)
    # DFT moments P_{2r}
    P = {}
    for r in range(1,rmax+1):
        P[r] = sum(abs(d)**(2*r) for d in Ds)/m
    # cumulant via bridge: kappa_r = (p/(nm))^r * P_{2r} / ((2r-1)!! m^r)
    kap = {}
    for r in range(1,rmax+1):
        kap[r] = (p/(n*m))**r * P[r] / (dfac2(r)*m**r)
    # DIRECT cumulant from eta for cross-check: eta_b = (sqrt p / m) D(b)
    etas = [abs((math.sqrt(p)/m)*Ds[c]) for c in range(m)]
    kap_direct = {}
    for r in range(1,rmax+1):
        kap_direct[r] = (sum(e**(2*r) for e in etas)/m)/(dfac2(r)*n**r)
    # AUTOCORRELATION R(h) = (1/m) sum_j a_j conj(a_{(j+h)%m})
    def R(h): return sum(a[j]*a[(j+h)%m].conjugate() for j in range(m))/m
    Rh = [R(h) for h in range(m)]
    # Wiener-Khinchin: |D(c)|^2 = sum_h R(h) exp(-2pi i h c/m) * m? check: P4 in terms of R.
    # P_2 = (1/m) sum_c |D|^2 = m * R(0)  (since (1/m)sum_c|D(c)|^2 = m*|a-energy|/m... ) verify numerically.
    # E[|D|^2] over c picks h=0:  (1/m)sum_c |D(c)|^2 = sum_j |a_j|^2 = m R(0). good.
    # P_4 = (1/m) sum_c |D(c)|^4. |D|^2 = m sum_h R(h) e^{-2pi i h c/m}. So |D|^4=(m^2) sum_{h,h'} R(h)conjR(h') e^{-2pi i (h-h')c/m}
    #   (1/m) sum_c picks h=h': P_4 = m^2 sum_h |R(h)|^2.
    P4_from_R = m**2 * sum(abs(Rh[h])**2 for h in range(m))
    # so kappa_2 = (p/nm)^2 P_4/(3 m^2) = (p/nm)^2 sum_h|R(h)|^2 /3.
    # The flatness target kappa_2<=1 <=> sum_h |R(h)|^2 <= 3 (p/nm)^{-2} ~ 3.
    sumR2 = sum(abs(Rh[h])**2 for h in range(m))
    # R(0)=1 contributes 1; the OFF-diagonal sum_{h!=0}|R(h)|^2 must be <= ~2 for kappa_2<=1.
    offR2 = sum(abs(Rh[h])**2 for h in range(1,m))
    # max autocorrelation off-zero (the "flatness of a_j as a sequence"):
    maxRoff = max((abs(Rh[h]) for h in range(1,m)), default=0.0)
    house = max(etas[1:]) if m>1 else etas[0]
    law = math.sqrt(n*math.log(max(m,2)))
    return dict(p=p,n=n,m=m,P2=P2,sum_a2=sum_a2,
                P=P,kap=kap,kap_direct=kap_direct,
                P4_from_R=P4_from_R,sumR2=sumR2,offR2=offR2,maxRoff=maxRoff,
                house=house,C=house/law)

def find_primes(n,count,start=2,cap=4000):
    out=[];k=start
    while len(out)<count:
        p=k*n+1
        if p>cap: break
        if sympy.isprime(p): out.append(p)
        k+=1
    return out

if __name__=="__main__":
    print("#407 CUMULANT-FROM-FLATNESS bridge + autocorrelation moment test\n")
    print("Bridge check: kappa_r(bridge from P_2r) vs kappa_r(direct from eta) must match.\n")
    print(f"{'p':>5}{'n':>4}{'m':>4} | {'P2~m':>7} {'P4/Rcheck':>10} | "
          f"{'k1':>6}{'k2':>6}{'k3':>6} | {'kd2':>6} | {'sumR2':>6}{'offR2':>6}{'maxRoff':>8} | {'C':>5}")
    for n in [4,8,16,32]:
        ps = find_primes(n,4)+find_primes(n,1,start=30)
        for p in sorted(set(ps)):
            if p>2500: continue
            r=analyze(p,n,rmax=3)
            P4ok = abs(r['P'][2]-r['P4_from_R'])
            print(f"{p:>5}{n:>4}{r['m']:>4} | {r['P2']:>7.2f} {P4ok:>10.1e} | "
                  f"{r['kap'][1]:>6.3f}{r['kap'][2]:>6.3f}{r['kap'][3]:>6.3f} | "
                  f"{r['kap_direct'][2]:>6.3f} | {r['sumR2']:>6.2f}{r['offR2']:>6.2f}{r['maxRoff']:>8.3f} | {r['C']:>5.2f}")
    print("\nKEY: kap2(bridge)==kapd2(direct) confirms the EXACT bridge kappa_r = (p/nm)^r P_2r/((2r-1)!! m^r).")
    print("P4/Rcheck==0 confirms Wiener-Khinchin P_4 = m^2 sum_h|R(h)|^2 (kappa_2 <=> sum_h|R(h)|^2 <= 3).")
    print("offR2 = sum_{h!=0}|R(h)|^2 = the OFF-DIAGONAL autocorrelation energy = the content of kappa_2.")
