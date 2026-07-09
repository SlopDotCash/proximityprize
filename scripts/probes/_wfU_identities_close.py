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
def E_r(p,S,r):
    sums={}
    for v in itertools.product(S,repeat=r):
        s=sum(v)%p; sums[s]=sums.get(s,0)+1
    return sum(c*c for c in sums.values())

# CONFIRM: sum_{b!=0} ||eta_b||^4 = q*E_2 - n^4   (the master form, exact)
print("=== sum_{b!=0} ||eta_b||^4 = q*E_2 - n^4 ===")
for (p,n) in [(257,8),(97,4),(17,4),(41,8)]:
    ps=psi(p); S=subgroup(p,n)
    nz=sum(abs(eta(p,S,b,ps))**4 for b in range(1,p))
    pred=p*E_r(p,S,2)-n**4
    print(f"p={p} n={n}: {round(nz,2)} vs q*E2-n^4={pred}  match={abs(nz-pred)<1e-3}")

# Identify what 3p(n-1)-n^3 is: maybe it's E_2 expressed via Stepanov count V_4 = #{(x1,x2,x3,x4) in mu_n^4: x1+x2=x3+x4}?
# addEnergy(mu_n) counts exactly that = E_2. 3p(n-1)-n^3 -- check at the GLT 'centered' normalization /something.
# Try: the SIGNED 4th power moment sum_{b} eta_b^4 (real) over b!=0 already computed. Let me see q*E2 - n^4 vs sum signed.
print("\n=== signed sum_b eta_b^4 (all) should also = q*E_2 (since eta_b^4 sums real by symmetry) ===")
for (p,n) in [(257,8),(97,4)]:
    ps=psi(p); S=subgroup(p,n)
    signed=sum(eta(p,S,b,ps)**4 for b in range(p)).real
    normed=sum(abs(eta(p,S,b,ps))**4 for b in range(p))
    print(f"p={p} n={n}: signed sum eta^4={round(signed,2)}  normed sum ||eta||^4={round(normed,2)}  qE2={p*E_r(p,S,2)}")

# ODD moment closed form: sum_{b!=0} eta_b^{2k+1} (signed, real). Tabulate and seek formula in n.
print("\n=== odd-moment sum_{b!=0} eta_b^{2k+1} (signed) vs candidate -(stuff) ===")
for n in [4,8]:
    # use a large prime p = 2^n+1-ish or any p with p-1 divisible by n and p>large
    cand_p={4:97,8:257}[n]
    p=cand_p; ps=psi(p); S=subgroup(p,n)
    for k in [1,2,3]:
        r=2*k+1
        nz=sum(eta(p,S,b,ps)**r for b in range(1,p)).real
        # signed r-fold count: N_signed = #{v in S^r : sum=0}. sum_all eta^r = q*N_signed
        allm=sum(eta(p,S,b,ps)**r for b in range(p)).real
        Ns=allm/p
        # so nz = q*N_signed - n^r
        print(f"n={n} k={k} r={r}: sum_{{b!=0}}={round(nz,2)}  N_signed(#sum0)={round(Ns,4)}  -n^r={-(n**r)}  q*Ns-n^r={round(p*Ns-n**r,2)}")
