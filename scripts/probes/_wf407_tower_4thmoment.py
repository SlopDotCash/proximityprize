import cmath, math, sympy
def primitive_root(p): return int(sympy.primitive_root(p))
def gen_order_n(p,n):
    g=primitive_root(p); d=(p-1)//n; return pow(g,d,p), g
def subgroup_set(p,n):
    h,_=gen_order_n(p,n); S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return S
def periods(p,n):
    S=subgroup_set(p,n); g=primitive_root(p); m=(p-1)//n; w=2*math.pi/p
    out=[]; rep=1
    for i in range(m):
        s=sum(cmath.exp(1j*w*((rep*x)%p)) for x in S); out.append(s); rep=(rep*g)%p
    return out
def primes_1modN(n, start):
    cand=start|1
    while True:
        if (cand-1)%n==0 and sympy.isprime(cand): return cand
        cand+=2

# Does Garcia V4 obey a clean tower recursion?  V4(2n) vs V4(n)?
# Thm1 (2|k): V4 = 3p(k-1)-k^3, here k = subgroup order.  So as a function of subgroup order:
#   V4(n)=3p(n-1)-n^3   summed over the m=(p-1)/n cosets.
#   V4(2n)=3p(2n-1)-(2n)^3   over m/2 cosets.
# Ratio per-coset E2 := V4/m :  E2(n)=V4(n)/m = [3p(n-1)-n^3]*n/(p-1) -> 3n^2 - ... ;  doubling n doubles m halves
print("=== Garcia V4 as fn of subgroup order n; per-coset E2=V4/m; ratio E2(2n)/E2(n) ===")
print(f"{'n':>5} {'V4(n)=3p(n-1)-n^3':>20} {'m':>8} {'E2=V4/m':>14} {'E2/n^2':>10}")
p=primes_1modN(64, 2*64*5000)  # very large m, deep fixed-index
for a in range(1,8):
    n=2**a
    if (p-1)%n: continue
    m=(p-1)//n
    V4=3*p*(n-1)-n**3
    E2=V4/m
    print(f"{n:>5} {V4:>20d} {m:>8} {E2:>14.2f} {E2/n**2:>10.4f}")
print(f"(p={p})")
print()
print("=== KEY: B(2n) vs sqrt(2)*B(n) [folding => independence gives sqrt2 growth per level] ===")
print(f"{'n':>5} {'B(n)':>9} {'B(2n)':>9} {'B(2n)/B(n)':>11} {'sqrt2':>7} {'B(2n)/(B(n)*sqrt(1+ln2/ln(mn... )':>10}")
for a in range(2,7):
    n=2**a
    if (p-1)%(2*n): continue
    Bn=max(abs(z) for z in periods(p,n))
    B2n=max(abs(z) for z in periods(p,2*n))
    print(f"{n:>5} {Bn:>9.4f} {B2n:>9.4f} {B2n/Bn:>11.4f} {math.sqrt(2):>7.4f}")
