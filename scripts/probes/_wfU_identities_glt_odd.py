import cmath, math, itertools
from math import comb
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

# GLT: the FOURTH POWER (signed, not normed) sum over b!=0
print("=== GLT V_4 = sum_{b} eta_b^4 (signed real power) ===")
for (p,n) in [(257,8),(97,4),(17,4),(41,8)]:
    ps=psi(p); S=subgroup(p,n)
    tot = sum(eta(p,S,b,ps)**4 for b in range(p)).real
    eta0 = float(n)**4
    nonzero = tot - eta0
    pred = 3*p*(n-1)-n**3
    print(f"p={p} n={n}: sum_all eta^4 ={round(tot,2)}  sum_{{b!=0}} eta^4 ={round(nonzero,2)}  3p(n-1)-n^3 ={pred}  match={abs(nonzero-pred)<1e-2}")

# odd moments: sum_b eta_b^{2k+1}  (signed). Find the closed form.
print("\n=== odd moments sum_b eta_b^{2k+1} ===")
for (p,n) in [(257,8),(97,4),(41,8)]:
    ps=psi(p); S=subgroup(p,n)
    for k in [1,2,3]:
        r=2*k+1
        tot=sum(eta(p,S,b,ps)**r for b in range(p)).real
        eta0=float(n)**r
        nonzero=tot-eta0
        # candidate: total = q * (#signed solutions). Let N = #{v in S^r : sum v =0} - ... 
        # try sum_all / q :
        Nall = tot/p
        print(f"p={p} n={n} k={k}: sum_all={round(tot,2)}  /q={round(Nall,4)}  sum_{{b!=0}}={round(nonzero,2)}  -n^{{2k}}={-(n**(2*k))}  -n^{{2k}}match={abs(nonzero+n**(2*k))<1e-2}")
