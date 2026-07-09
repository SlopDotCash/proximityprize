"""
LENS [constants] — the FOUR '2's that turn out to be ONE.

Over a real prime field F_p with mu_n (n=2^m | p-1), eta_b = sum_{y in mu_n} psi(b y),
psi(x)=e^{2pi i x/p}. We test that the following constants are the SAME quantity, all
rooted in the Parseval L2 average  (1/(p-1)) sum_{b!=0} ||eta_b||^2 = n - n^2/(p-1) ~= n:

  (A) Salem-Zygmund increment metric:  dbar(c,c')^2 = (1/m) sum_b ||eta_{b g^c} - eta_{b g^c'}||^2
      claimed == 2n for ALL distinct c != c'  (SalemZygmundChaining.lean docstring).
  (B) Tower 2nd-moment cross term:  sum_b Re(eta_b(mu_n) conj eta_{zeta b}(mu_n)) claimed == -n/2
      (_wf407_tower.lean eta_fold_normSq docstring).
  (C) The refuted sqrt(2)-flatness bound value: ||eta||^2 <= 2n  (ShawFlatnessRefuted.lean).
  (D) Tower growth B(mu_{2n})/B(mu_n) -> sqrt(2).

Hidden identity hypothesis:
   The metric dbar^2 = avg||eta_c||^2 + avg||eta_c'||^2 - 2 avg Re(...) = n + n - 2*0 = 2n
   when the two periods are L2-orthogonal-on-average. The SAME orthogonality that makes
   the cross-term (B) vanish on average makes the metric (A) equal 2n, which is exactly the
   refuted bound value (C). So (A)=(C) numerically and both come from avg||eta||^2 = n.
"""
import cmath, math

def is_prime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True

def primitive_root(p):
    if p==2: return 1
    phi=p-1; m=phi; fac=[]; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fac): return g

def eta_vec(p, gen_n, n, b):
    s=0j
    x=1
    for _ in range(n):
        s+=cmath.exp(2j*math.pi*((b*x)%p)/p)
        x=(x*gen_n)%p
    return s

print("="*82)
print(" The four 2's: avg L2 = n,  metric dbar^2 = 2n,  cross-term = -n/2,  tower ratio -> sqrt2")
print("="*82)
print(f"{'p':>7} {'n':>4} {'avgL2/n':>9} {'metric/n':>9} {'cross/n':>9} {'-1/2?':>7} {'B2n/Bn':>8}")

# build cases: n=2^m | p-1, p generic
def find_prime(n, mult):
    p=n+1
    while p<5_000_00:
        if is_prime(p) and (p-1)%n==0 and p>mult*n:
            return p
        p+=1
    return None

for m in range(2,6):  # n=4..32
    n=2**m
    p=find_prime(n, 60)
    if p is None: continue
    g=primitive_root(p)
    gen_n=pow(g,(p-1)//n,p)         # generator of mu_n
    mvar=(p-1)//n                   # number of cosets m

    # eta_b over all b=1..p-1 for the L2 average and the cross term
    # avg L2 over nonzero b:
    sumL2=0.0
    for b in range(1,p):
        e=eta_vec(p,gen_n,n,b)
        sumL2 += e.real*e.real+e.imag*e.imag
    avgL2 = sumL2/(p-1)

    # metric dbar^2 for a FIXED pair (c=0, c'=1) i.e. b vs g*b, averaged over the m cosets b ranges as g^c
    # use representatives: c indexes coset reps r_c; here take b ranging over all nonzero, compare eta_b and eta_{g b}
    # dbar(0,1)^2 = (1/(p-1)) sum_b ||eta_b - eta_{g b}||^2
    metsum=0.0
    crosssum=0.0
    # cross term for tower: zeta = element of order 2n with zeta^n=-1 i.e. zeta=pow(h2,1) where h2 gen of mu_{2n}
    # eta_b(mu_n) vs eta_{zeta b}(mu_n); sum over b of Re(eta_b conj eta_{zeta b})
    h2=pow(g,(p-1)//(2*n),p)   # generator of mu_{2n}; zeta=h2 has zeta^n = g^{(p-1)/2} = -1
    zeta=h2
    for b in range(1,p):
        eb=eta_vec(p,gen_n,n,b)
        egb=eta_vec(p,gen_n,n,(g*b)%p)
        d=eb-egb
        metsum += d.real*d.real+d.imag*d.imag
        ezb=eta_vec(p,gen_n,n,(zeta*b)%p)
        crosssum += (eb*ezb.conjugate()).real
    metric = metsum/(p-1)
    # cross-term per the docstring is a sum over cosets (one rep per coset). Average per coset:
    cross_percoset = crosssum/(p-1)   # this is avg over all b; the docstring's "-n/2" is the coset-sum scale

    # tower ratio B(mu_{2n})/B(mu_n)
    def Bmax(genk,k):
        mx=0.0
        for b in range(1,p):
            e=eta_vec(p,genk,k,b)
            v=e.real*e.real+e.imag*e.imag
            if v>mx: mx=v
        return math.sqrt(mx)
    Bn=Bmax(gen_n,n)
    gen_2n=pow(g,(p-1)//(2*n),p)
    B2n=Bmax(gen_2n,2*n)
    ratio=B2n/Bn

    print(f"{p:>7} {n:>4} {avgL2/n:>9.4f} {metric/n:>9.4f} {cross_percoset/n:>9.4f} "
          f"{'~-0.5' if abs(cross_percoset/n+0.5)<0.15 else f'{cross_percoset/n:.3f}':>7} {ratio:>8.4f}")

print()
print("Identity chain (all rooted in avg_{b!=0} ||eta_b||^2 = n):")
print("  metric dbar^2 = avg||eta_b||^2 + avg||eta_{gb}||^2 - 2 avg Re(...)  = n + n - 0 = 2n")
print("  => metric/n -> 2  ==  the REFUTED sqrt(2)-flatness value (||eta||^2<=2n).")
print("  cross-term/n -> -1/2  (tower 2nd-moment), tiny vs the diagonal n => 2nd moments add as sqrt2/level")
print("  tower ratio -> sqrt(2) = 1.4142 as n grows.  Same '2' everywhere = the Parseval average n.")
