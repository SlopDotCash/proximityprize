"""
_wfU_identities_catalog.py  (LENS: identities)
Numerically confirm the exact algebraic identities recurring across the ProximityGap cone.
All over a prime field F_p, mu_n = order-n multiplicative subgroup, psi(x)=e^{2pi i x/p}.
"""
import cmath, math, itertools
from math import comb

def primitive_root(p):
    # smallest primitive root mod p
    if p == 2: return 1
    fac = []
    n = p-1; d=2
    while d*d<=n:
        if n%d==0:
            fac.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: fac.append(n)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    return None

def psi(p):
    w = cmath.exp(2j*math.pi/p)
    return lambda x: w**(x%p)

def subgroup(p,n):
    assert (p-1)%n==0
    g = primitive_root(p)
    h = pow(g,(p-1)//n,p)
    S=[]; x=1
    for _ in range(n):
        S.append(x); x=(x*h)%p
    assert len(set(S))==n
    return S

def eta(p, S, b, ps):
    return sum(ps((b*y)%p) for y in S)

results = {}

# ---- IDENTITY 1: master moment  sum_b ||eta_b||^{2r} = q * E_r(G) ----
def E_r(p,S,r):
    # #{(v,w) in S^r x S^r : sum v = sum w mod p}
    sums = {}
    for v in itertools.product(S, repeat=r):
        s = sum(v)%p
        sums[s]=sums.get(s,0)+1
    return sum(c*c for c in sums.values())

def check_master_moment(p,n,rmax=3):
    ps=psi(p); S=subgroup(p,n)
    ok=True; detail=[]
    for r in range(1,rmax+1):
        lhs = sum(abs(eta(p,S,b,ps))**(2*r) for b in range(p))
        rhs = p*E_r(p,S,r)
        good = abs(lhs-rhs) < 1e-5*max(1,abs(rhs))
        ok &= good
        detail.append((r, round(lhs,3), rhs, good))
    return ok, detail

results['I1_master_moment p=17 n=4'] = check_master_moment(17,4,3)
results['I1_master_moment p=41 n=8'] = check_master_moment(41,8,2)

# ---- IDENTITY 2: E_2(mu_n) = 3n^2 - 3n  (n=2^m, p>2^n) ; second moment E_1=n ----
def check_E2(p,n):
    S=subgroup(p,n)
    return E_r(p,S,1)==n, E_r(p,S,2), 3*n*n-3*n
results['I2_E2_3n2-3n p=257 n=8'] = (check_E2(257,8)[1]==3*64-24, check_E2(257,8))
results['I2_E2_3n2-3n p=97 n=4']  = (check_E2(97,4)[1]==3*16-12, check_E2(97,4))

# ---- IDENTITY 3: four-term Parseval  sum_{x in mu_n} ||x^i+x^j-x^k-x^l||^2 = 4n  (distinct powers) ----
def check_parseval4(n, i,j,k,l):
    w = cmath.exp(2j*math.pi/n)
    roots=[w**t for t in range(n)]
    val = sum(abs(x**i+x**j-x**k-x**l)**2 for x in roots)
    return abs(val-4*n)<1e-7, round(val,6), 4*n
results['I3_parseval4 n=8 (0,1,2,3)'] = check_parseval4(8,0,1,2,3)
results['I3_parseval4 n=16 (1,5,2,9)'] = check_parseval4(16,1,5,2,9)

# ---- IDENTITY 4: E_r({1,-1}) = C(2r,r) (central binomial) ----
def E_r_pm1(r):
    # sum over tuples in {+1,-1}, equal-sum pairs; in char 0
    from collections import Counter
    c=Counter()
    for v in itertools.product([1,-1],repeat=r):
        c[sum(v)]+=1
    return sum(x*x for x in c.values())
results['I4_centralBinom r=1..6'] = ([E_r_pm1(r) for r in range(1,7)],
                                     [comb(2*r,r) for r in range(1,7)],
                                     [E_r_pm1(r)==comb(2*r,r) for r in range(1,7)])

# ---- IDENTITY 5: GLT 4th moment  V_4 = sum_b eta_b^4 ... and = q*E_2 ; also 3p(n-1)-n^3 form ----
# Here check the in-tree fourth moment claim sum_b ||eta_b||^4 = q*addEnergy(mu_n)
# and the GLT prediction E_2 numeric equals (q*E_2 - ...) — we directly check 3p(n-1)-n^3 form for V_4=sum_{b!=0}.
def check_glt(p,n):
    ps=psi(p); S=subgroup(p,n)
    m4_all = sum(abs(eta(p,S,b,ps))**4 for b in range(p))      # = q*E_2
    qE2 = p*E_r(p,S,2)
    # the "centered" 4th moment over b!=0 :
    eta0 = abs(eta(p,S,0,ps))**4  # = n^4
    m4_nonzero = m4_all - eta0
    # GLT V_4 (nonzero freqs) prediction 3p(n-1)-n^3  (from C010 / Fermat257EnergyCrossover)
    pred = 3*p*(n-1)-n**3
    return (abs(m4_all-qE2)<1e-4, round(m4_all,2), qE2,
            round(m4_nonzero,2), pred, abs(m4_nonzero-pred)<1e-3)
results['I5_GLT_V4 p=257 n=8'] = check_glt(257,8)
results['I5_GLT_V4 p=97 n=4']  = check_glt(97,4)

# ---- IDENTITY 6: tangent-sum Jacobi average  m*T(phi) = sum_{i<m} J(chi^i, phi) ----
# chi multiplicative char of order m=n on F_p*; ker chi = subgroup of index... actually order (p-1)/m.
# We test: T(phi)=sum_{w: chi(w)=1} phi(1-w),  J(a,b)=sum_x a(x)b(1-x).
def mulchar(p, exps):
    # character chi: x -> zeta_{p-1}^{e * dlog(x)}; returns function on F_p (0 -> 0)
    g=primitive_root(p)
    dlog={}
    x=1
    for k in range(p-1):
        dlog[x]=k; x=(x*g)%p
    zp = cmath.exp(2j*math.pi/(p-1))
    def chi(e):
        def f(v):
            v%=p
            if v==0: return 0
            return zp**((e*dlog[v])%(p-1))
        return f
    return chi
def check_tangent_jacobi(p, m):
    # chi of order m: e = (p-1)//m
    assert (p-1)%m==0
    e0=(p-1)//m
    chi = mulchar(p,None)
    chiF = chi(e0)         # order m
    # pick phi of some order, say e=1 char raised: phi = chi(some e1)
    e_phi = 2
    phi = chi(e_phi)
    ker = [w for w in range(1,p) if abs(chiF(w)-1)<1e-9]
    T = sum(phi((1-w)%p) for w in ker)
    def jacobi(a_e,b_e):
        a=chi(a_e); b=chi(b_e)
        return sum(a(x)*b((1-x)%p) for x in range(p))
    S = sum(jacobi((e0*i)%(p-1), e_phi) for i in range(m))
    return abs(m*T - S)<1e-6, round(m*T.real,4)+1j*round(m*T.imag,4), round(S.real,4)+1j*round(S.imag,4)
results['I6_tangent_jacobi p=13 m=3'] = check_tangent_jacobi(13,3)
results['I6_tangent_jacobi p=31 m=5'] = check_tangent_jacobi(31,5)

# ---- IDENTITY 7: DFT eta_b = (1/m) sum_chi chibar(b) tau(chi), chi in mu_n^perp, m=(p-1)/n ----
# eta_b = sum_{y in mu_n} psi(b y). Decompose indicator of mu_n via multiplicative chars trivial on mu_n.
# 1_{mu_n}(x) = (n/(p-1)) sum_{chi: chi|mu_n=1} chi(x).  Then eta_b = sum_x 1_{mu_n}(x) psi(bx)
#   = (n/(p-1)) sum_{chi triv on mu_n} sum_x chi(x) psi(bx) = (n/(p-1)) sum_chi chibar(b)? tau...
# Gauss sum tau(chi)=sum_x chi(x) psi(x); sum_x chi(x)psi(bx) = chibar(b) tau(chi) for chi nontrivial.
def check_dft_eta(p,n,b):
    ps=psi(p); S=subgroup(p,n); m=(p-1)//n
    chi=mulchar(p,None)
    # chars trivial on mu_n  <=>  exponent e multiple of n  (since mu_n = <g^m>, chi_e(g^m)=zp^{e m}=1 iff (p-1)|e m iff n|e)
    eta_direct = sum(ps((b*y)%p) for y in S)
    acc=0
    for j in range(m):                 # e = j*n  ranges over chars trivial on mu_n, j=0..m-1
        e=(j*n)%(p-1)
        chie=chi(e)
        # sum_x chi_e(x) psi(b x)
        gb = sum(chie(x)*ps((b*x)%p) for x in range(1,p))
        acc += gb
    acc *= n/(p-1)
    return abs(eta_direct-acc)<1e-6, round(eta_direct.real,4)+1j*round(eta_direct.imag,4), round(acc.real,4)+1j*round(acc.imag,4)
results['I7_dft_eta p=41 n=8 b=3'] = check_dft_eta(41,8,3)
results['I7_dft_eta p=17 n=4 b=5'] = check_dft_eta(17,4,5)

# ---- IDENTITY 8: odd-moment negativity  sum_{b} eta_b^{2k+1} = ? ; claim sum_{b!=0} = -n^{2k} (real) ----
# Use the real part since eta_b can be complex; test sum_b eta_b^{odd}.
def check_odd_moment(p,n,k):
    ps=psi(p); S=subgroup(p,n)
    r=2*k+1
    tot = sum(eta(p,S,b,ps)**r for b in range(p))
    eta0 = (n)**r
    nonzero = tot-eta0
    pred = -(n**(2*k))
    # sum over ALL b of eta^r = q*N where N = #{(v) in S^r: sum=0}? For odd r it's signed; test against memory claim
    return round(tot.real,4), round(nonzero.real,4), pred
results['I8_odd_moment p=257 n=8 k=1'] = check_odd_moment(257,8,1)
results['I8_odd_moment p=257 n=8 k=2'] = check_odd_moment(257,8,2)

# ---- print ----
for k,v in results.items():
    print(k, "::", v)
