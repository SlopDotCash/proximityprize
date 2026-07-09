import cmath, math
import sympy

def primitive_root(p):
    return int(sympy.primitive_root(p))

def subgroup(p,n):
    g=primitive_root(p); d=(p-1)//n; h=pow(g,d,p)
    S=[]; x=1
    for _ in range(n):
        S.append(x); x=(x*h)%p
    assert len(set(S))==n
    return S,g

def period_values(p,n):
    S,g=subgroup(p,n)
    m=(p-1)//n
    w=2*math.pi/p
    # precompute e_p table
    period=[]
    rep=1
    for i in range(m):
        s=0j
        for x in S:
            s+=cmath.exp(1j*w*((rep*x)%p))
        period.append(s)
        rep=(rep*g)%p
    return period,m

def stats(p,n):
    period,m=period_values(p,n)
    absv=[abs(z) for z in period]
    V={r:sum(a**r for a in absv) for r in (1,2,4,6)}
    B=max(absv)
    return B,V,m,absv

def primes_1modN(n, count, start=None):
    out=[]; 
    cand=(start or (n+1))
    if cand%2==0: cand+=1
    while len(out)<count:
        if (cand-1)%n==0 and sympy.isprime(cand):
            out.append(cand)
        cand+=1
    return out

print("=== (1) Garcia Thm1 (FIXED k=n, our index m=d): V4 over cosets ===")
print(f"{'p':>8} {'n':>4} {'m':>6} {'V4_emp':>16} {'Thm1':>16} {'ok':>4} {'B':>9} {'B^4':>14}")
for n in (4,8,16,32):
    for p in primes_1modN(n,3, start=2*n*50):
        B,V,m,absv=stats(p,n)
        # Thm1: 2|k -> 3p(k-1)-k^3 ; here k=n
        if n%2==0:
            thm1=3*p*(n-1)-n**3
        else:
            thm1=p*(2*n-1)-n**3
        ok=abs(V[4]-thm1)<1e-3
        print(f"{p:>8} {n:>4} {m:>6} {V[4]:>16.3f} {thm1:>16d} {str(ok):>4} {B:>9.4f} {B**4:>14.3f}")

print()
print("=== (2) What floor does fixed-k V4 imply? B^4<=V4 vs flat prediction ===")
print("Flat/random-like: if m periods each ~ CN(0, p/m... ) then E|eta|^2 = (V2/m), E|eta|^4=2(E|eta|^2)^2")
print("V2(coset) = ((n-1)p+1)/n approx p (since |period|^2 averages p/m * m? ) -- check")
print(f"{'p':>8} {'n':>4} {'m':>6} {'V2':>12} {'V2/m':>10} {'V4/m':>12} {'2*(V2/m)^2':>12} {'B':>9} {'sqrt(n ln m)':>12} {'B/sqrt(nlnm)':>12}")
for n in (8,16,32,64):
    for p in primes_1modN(n,2, start=2*n*200):
        B,V,m,absv=stats(p,n)
        v2=V[2]; v4=V[4]
        flat4=2*(v2/m)**2
        nlnm=n*math.log(m)
        print(f"{p:>8} {n:>4} {m:>6} {v2:>12.1f} {v2/m:>10.2f} {v4/m:>12.2f} {flat4:>12.2f} {B:>9.4f} {math.sqrt(nlnm):>12.4f} {B/math.sqrt(nlnm):>12.4f}")
