#!/usr/bin/env python3
"""
#407 route [rojasleon] — WHY Hasse-Davenport does not spoil flatness, made precise.

The HD product formula (d|q-1, chi a character):
    prod_{eps^d = 1} tau(chi*eps) = chi(d)^{-d} * tau(chi^d) * tau-of-eps-product-const.
For the period-relevant characters psi^j (trivial on mu_n, exponent e=n*j), and d=2:
   tau(psi^j) * tau(psi^j * lambda) = const * tau(psi^{2j})    where lambda = quad char.
The quad char lambda has exponent (p-1)/2.  In a_index units (e/n=j), lambda has index
(p-1)/(2n)=m/2, so psi^j*lambda has index j+m/2 (mod m).  Hence HD says
   a_j * a_{j+m/2} = (HD const) * a_{2j}     <-- a *relation*, exact.

QUESTION 1 (verify): does this exact relation hold numerically? -> confirm |LHS/RHS|=1, const.
QUESTION 2 (the crux): a RELATION among phases is not an ALIGNMENT.  Write theta_j=arg(a_j).
HD says theta_{2j} = theta_j + theta_{j+m/2} + c (mod 2pi).  This is a linear recurrence on
the phase sequence (a 'self-similar'/multiplicative structure), NOT a statement that the phases
point the same way.  We test: is theta a SOLUTION of an additive character (theta_j = alpha*j+b,
which WOULD align the DFT into a single spike), or is it 'multiplicatively chaotic'?
We measure (a) max DFT spike of e^{i theta} (=||P||, already ~random); (b) the linear-phase
residual: best-fit theta_j ~ alpha j and the fraction of energy it captures (a true alignment
would capture ~1); (c) the doubling-map orbit structure: HD ties j-frequencies along 2-adic
orbits j,2j,4j,... — does that create a low-dim subspace the sup-norm concentrates on?
"""
import math
import numpy as np
np.random.seed(7)

def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
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

def primitive_root(p):
    n=p-1;fac=set();d=2
    while d*d<=n:
        while n%d==0:fac.add(d);n//=d
        d+=1
    if n>1:fac.add(n)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g

def find_prime(n,beta,maxp=2_000_000):
    t0=max(2,int(round(n**beta))//n)
    for dt in range(0,400000):
        for t in (t0+dt,t0-dt):
            if t<2:continue
            p=1+n*t
            if p<=n or p>maxp:continue
            if is_prime(p):
                m=(p-1)//n;mm=m
                while mm%2==0:mm//=2
                if mm>1:return p
    return None

def gauss(p,g):
    pe=p-1;gk=np.empty(pe,np.int64);x=1
    for k in range(pe):gk[k]=x;x=(x*g)%p
    w=np.exp(2j*np.pi*gk/p)
    return np.fft.ifft(w)*pe   # tau[e]

print("="*88)
print("HD structure: relation vs alignment  (why Hasse-Davenport does not spoil flatness)")
print("="*88)
for (n,beta) in [(8,4),(16,4),(16,5),(32,4)]:
    p=find_prime(n,beta)
    if p is None: print(f"n={n}: no prime"); continue
    g=primitive_root(p); pe=p-1; m=(p-1)//n; sqp=math.sqrt(p)
    tau=gauss(p,g)
    idx=(n*np.arange(m))%pe
    A=tau[idx]/sqp                      # A[0]=triv, A[j]=a_j unimodular for j>=1
    # ---- Q1: verify HD relation a_j * a_{j+m/2} = const * a_{2j} (d=2) ----
    if m%2==0:
        j=np.arange(1,m//2)             # keep 2j<m, j+m/2<m, all !=0
        sel=(2*j<m)&((j+m//2)<m)&((2*j)%m!=0)
        j=j[sel]
        lhs=A[j]*A[(j+m//2)%m]
        rhs=A[(2*j)%m]
        ratio=lhs/rhs                   # should be a CONSTANT (the HD const) if relation exact
        magdev=float(np.max(np.abs(np.abs(ratio)-1.0)))
        # constancy of the phase:
        ph=ratio/np.abs(ratio)
        const_align=abs(np.mean(ph))    # ~1 => ratio is a constant phase (HD relation exact & rigid)
        print(f"\n--- n={n} beta={beta}  p={p}  m={m} ---")
        print(f"  [Q1 HD-relation exact?] |a_j a_(j+m/2) / a_2j|: |mag-1| max={magdev:.1e}  "
              f"phase-constancy |mean|={const_align:.4f}  (1=exact rigid HD const)  #={len(j)}")
        # Reconcile with earlier 'random' reading: earlier I divided a_2j by product (inverse) AND
        # iterated over ALL j including 2j wrapping; here restricting to the clean branch shows the
        # relation's true rigidity.  If const_align~1 the relation IS exact/rigid.
    # ---- Q2: is the phase sequence an ADDITIVE character (=> single DFT spike = full alignment)? ----
    a=A[1:]
    theta=np.angle(a)
    # best linear phase alpha: maximize |sum a_j e^{-i alpha j}| over alpha = the DFT we already do
    pad=np.zeros(m,dtype=complex);pad[1:]=a
    P=np.fft.fft(pad);spike=float(np.max(np.abs(P)))
    energy=np.sum(np.abs(a)**2)
    # Parseval: sum_c |P(c)|^2 = m * energy.  Top-mode SHARE = spike^2 / (m*energy).
    # pure additive char: P concentrates => share=1.  flat: share ~ (2 log m)/m -> 0.
    share=spike**2/(m*energy)
    over_flat=spike**2/(energy*math.log(m))   # ~2 for the random-flat law (||P||^2~2 energy log m)
    print(f"  [Q2 alignment] top-mode SHARE = {share:.5f}  (1=pure char=full alignment; "
          f"flat ~ 2lnm/m = {2*math.log(m)/m:.5f})   ||P||^2/(energy lnm)={over_flat:.2f} (~2=flat)")
    # ---- Q3: 2-adic doubling orbits — does HD concentrate energy on a low-dim orbit subspace? ----
    # HD ties a_{2j} to a_j; iterate j->2j builds orbits.  If the sup-norm were carried by a single
    # orbit, restricting P to one orbit's frequencies would reproduce most of ||P||.  Measure the
    # largest single-doubling-orbit L2 mass.
    seen=np.zeros(m,bool);orbmass=[]
    for s in range(1,m):
        if seen[s]:continue
        orb=[];x=s
        while not seen[x]:
            seen[x]=True;orb.append(x);x=(2*x)%m
            if x==0:break
        orbmass.append(np.sum(np.abs(P[orb])**2))
    orbmass=np.array(sorted(orbmass,reverse=True))
    totmass=np.sum(np.abs(P[1:])**2)
    print(f"  [Q3 orbit] #doubling-orbits={len(orbmass)}  largest orbit carries "
          f"{orbmass[0]/totmass*100:.2f}% of ||P||^2 energy; top-5 orbits {np.sum(orbmass[:5])/totmass*100:.1f}% "
          f"(low => sup-norm NOT carried by a 2-adic orbit => HD coupling is diffuse)")
print("\nVerdict logic: HD is an EXACT RIGID relation (Q1 const_align~1), but it is a")
print("multiplicative/doubling recurrence theta_2j=theta_j+theta_(j+m/2)+c, NOT an additive")
print("character (Q2 spike_frac~1/m), and its orbits don't concentrate energy (Q3). A relation")
print("that ties a phase to a PRODUCT of two others propagates flatness; it does not align it.")
