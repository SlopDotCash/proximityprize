import cmath, math, itertools
def primitive_root(p):
    if p==2: return 1
    n=p-1; fac=[]; d=2
    while d*d<=n:
        if n%d==0:
            fac.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: fac.append(n)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
def psi(p):
    w=cmath.exp(2j*math.pi/p); return lambda x: w**(x%p)
def subgroup(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p); S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return S
def eta(p,S,b,ps): return sum(ps((b*y)%p) for y in S)

# In the char-0 regime (p huge, no signed zero-sum relations among r roots), 
#   sum_{b!=0} eta_b^{r}  =  -n^{r}    for ALL r>=1 (since sum_all = q*N0 = 0, and eta_0^r = n^r)
# This is the EXACT statement: sum_{all b} eta_b^r = q * #{v in mu_n^r: sum v=0 mod p}.
# When that count is 0, sum_{b!=0} = -n^r.  Holds for both odd and even r in char 0 EXCEPT even r has diagonal sols.
print("=== char-0: sum_{b!=0} eta_b^r = -n^r  when no signed zero-sum (need p large) ===")
# pick p ~ large prime, p ≡ 1 mod n
def find_p(n, lo):
    p=lo
    while True:
        p+=1
        if p%2==1 and (p-1)%n==0:
            from sympy import isprime
            if isprime(p): return p
try:
    from sympy import isprime
    have_sympy=True
except Exception:
    have_sympy=False
    def isprime(x):
        if x<2: return False
        d=2
        while d*d<=x:
            if x%d==0: return False
            d+=1
        return True
    def find_p(n,lo):
        p=lo
        while True:
            p+=1
            if p%2==1 and (p-1)%n==0 and isprime(p): return p

for n in [4,8]:
    p=find_p(n, 4001)   # large prime so few/no short relations
    ps=psi(p); S=subgroup(p,n)
    for r in [1,3,5,7]:
        allm=sum(eta(p,S,b,ps)**r for b in range(p))
        nz=(allm - n**r)
        print(f"n={n} p={p} r={r}: sum_{{b!=0}} eta^r = {round(nz.real,3)}{'+' if nz.imag>=0 else ''}{round(nz.imag,3)}j   -n^r={-(n**r)}  match={abs(nz+n**r)<1e-2}")
