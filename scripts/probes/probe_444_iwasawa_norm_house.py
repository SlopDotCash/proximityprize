import numpy as np
import cmath, math

def factorize(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1
    if n>1: f[n]=f.get(n,0)+1
    return f

def primitive_root(p):
    fact=list(factorize(p-1).keys())
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fact): return g
    return None

def mu_n(p, n):
    # order-n multiplicative subgroup of F_p^*
    g=primitive_root(p)
    m=(p-1)//n
    h=pow(g,m,p)  # generator of order n
    return [pow(h,j,p) for j in range(n)], m

def gauss_period(p, sub, b):
    # eta_b = sum_{x in mu_n} e_p(b x)
    s=0+0j
    for x in sub:
        s+=cmath.exp(2j*math.pi*(b*x % p)/p)
    return s

def house(p, n):
    sub,m=mu_n(p,n)
    best=0.0
    for b in range(1,p):
        v=abs(gauss_period(p,sub,b))
        if v>best: best=v
    return best, m

def all_norms_geommean(p, n):
    # the m Galois conjugates of eta = eta_1 are eta_b for b ranging over coset reps of mu_n in F_p^*
    # Actually eta's conjugates under Gal(K_m/Q) are the m distinct period values.
    # Compute |N|^{1/m} = geometric mean of |sigma(eta)| over the m conjugates.
    sub,m=mu_n(p,n)
    # cosets: representatives = powers of generator g^0..g^{m-1}; eta_{g^i} are the conjugates
    g=primitive_root(p)
    conj=[]
    for i in range(m):
        b=pow(g,i,p)
        conj.append(abs(gauss_period(p,sub,b)))
    logmean=sum(math.log(c) for c in conj)/m
    gm=math.exp(logmean)
    return gm, m  # |N|^{1/m}

# Probe 1: the tower recursion ratio M(2n)^2 / M(n)^2  vs the conjectured <= 3 (=2+R_norm/M(n)^2, R_norm<=M(n)^2)
print("=== PROBE 1: tower recursion ratio M(2n)^2 / M(n)^2 (conjecture predicts <= 3) ===")
print(f"{'p':>10} {'n':>5} {'M(n)':>9} {'M(2n)':>9} {'ratio':>8} {'<=3?':>6} {'<=2?':>6}")
# need p with 2n | p-1, take clean towers
for p in [257, 769, 3329, 7681, 12289, 40961, 65537]:
    for mu in range(3,7):
        n=2**mu; n2=2*n
        if (p-1)%n2!=0: continue
        Mn,_=house(p,n)
        M2n,_=house(p,n2)
        ratio=(M2n**2)/(Mn**2)
        print(f"{p:>10} {n:>5} {Mn:>9.4f} {M2n:>9.4f} {ratio:>8.4f} {str(ratio<=3.0+1e-9):>6} {str(ratio<=2.0+1e-9):>6}")

print()
print("=== PROBE 2: geometric-mean conjugate modulus |N|^{1/m} vs sqrt(n)/2 (conjecture: |N|^{2/m}~n/4) ===")
print(f"{'p':>10} {'n':>5} {'m':>6} {'|N|^(1/m)':>11} {'sqrt(n)/2':>10} {'|N|^(2/m)/n':>12} {'house':>9} {'house/gm':>9}")
for p in [257, 769, 3329, 7681, 12289, 40961, 65537]:
    for mu in range(3,7):
        n=2**mu
        if (p-1)%n!=0: continue
        m=(p-1)//n
        if m>4000: continue  # keep conjugate enumeration feasible
        gm,_=all_norms_geommean(p,n)
        Mn,_=house(p,n)
        print(f"{p:>10} {n:>5} {m:>6} {gm:>11.4f} {math.sqrt(n)/2:>10.4f} {(gm**2)/n:>12.4f} {Mn:>9.4f} {Mn/gm:>9.4f}")
