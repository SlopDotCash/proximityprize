"""
SYMMETRIES lens probe 2: does the bad-scalar set / Gauss-period multiset inherit the
FULL dihedral D_n symmetry (cyclic Z/n already proven via e_t-homogeneity / coset-invariance;
the NEW Mobius involution sigma: x -> -x^{-1})?

Two distinct objects carry symmetry:
  (1) lacBad(mu_n, a, t) = { e_t(S) : S subset mu_n, |S|=a, e_1..e_{t-1}=0 }  (the #407 floor object)
      -- proven closed under gamma -> g^t gamma (cyclic). Does sigma induce an extra map on lacBad?
  (2) The Gauss-period multiset {eta_b : b}  -- proven constant on cosets (cyclic).
      Does the Mobius/antipodal symmetry act on the eta values?

KEY TEST: e_t under the inversion x -> x^{-1} on mu_n.
  On mu_n, x^{-1} = conj(x) (since |x|=1). Vieta: if S has char poly prod(X - s),
  then S^{-1} = {1/s} has char poly with REVERSED coeffs. Specifically
     e_t(S^{-1}) = e_{a-t}(S) / e_a(S),  where a=|S|, e_a(S)=prod(S).
  So inversion maps e_t  <->  e_{a-t}/prod(S). This is the GRS / negRev duality (MobiusMCASymmetry).
  Combined with x -> -x (antipodal, e_t -> (-1)^t e_t), the Mobius x -> -x^{-1} acts as:
     e_t(sigma S) = (-1)^t e_{a-t}(S)/e_a(S).
  Test this identity numerically.

If true: the vanishing variety {e_1=..=e_{t-1}=0} is mapped by sigma to {e_{a-1}=..=e_{a-t+1}=0},
i.e. the gap-t-at-TOP direction <-> gap-t-at-BOTTOM direction. This is a NEW symmetry of the
lacBad family: direction (a,b)=(k+t,k) <-> a reflected direction. Could halve the floor search.
"""
import cmath, math, itertools, random

def e_t(S, t):
    if t == 0: return complex(1.0)
    if t > len(S): return complex(0.0)
    return sum(math.prod(c) for c in itertools.combinations(S, t))

def test_inversion_et():
    print("=== e_t(S^{-1}) = e_{a-t}(S)/e_a(S)  (Vieta reversal / GRS duality) ===")
    maxerr=0.0
    for trial in range(200):
        a = random.randint(2,7)
        S = [cmath.exp(2j*math.pi*random.random()) for _ in range(a)]  # unit circle = mu_inf
        ea = e_t(S, a)
        if abs(ea) < 1e-9: continue
        Sinv = [1/x for x in S]
        for t in range(a+1):
            lhs = e_t(Sinv, t)
            rhs = e_t(S, a-t)/ea
            maxerr=max(maxerr, abs(lhs-rhs))
    print(f"  maxerr over 200 trials = {maxerr:.2e}")

def test_mobius_et():
    print("=== e_t(sigma S) = (-1)^t e_{a-t}(S)/e_a(S),  sigma x = -x^{-1} ===")
    maxerr=0.0
    for trial in range(200):
        a = random.randint(2,7)
        S = [cmath.exp(2j*math.pi*random.random()) for _ in range(a)]
        ea = e_t(S, a)
        if abs(ea) < 1e-9: continue
        sigS = [-1/x for x in S]
        for t in range(a+1):
            lhs = e_t(sigS, t)
            rhs = ((-1)**t) * e_t(S, a-t)/ea
            maxerr=max(maxerr, abs(lhs-rhs))
    print(f"  maxerr over 200 trials = {maxerr:.2e}")

def test_vanishing_variety_reflection(p, n, a, t):
    """
    Over F_p with mu_n: build the vanishing variety V(a,t) = {S subset mu_n : |S|=a, e_1..e_{t-1}=0}.
    sigma S = {-x^{-1}} should map V(a,t) to V(a, ?) -- specifically the constraints
    e_1..e_{t-1}=0 on sigma S correspond, via e_t(sigma S) ~ e_{a-t}(S), to
    e_{a-1}..e_{a-t+1}=0 on S. So sigma : V_constraints-at-bottom  <->  V_constraints-at-top.
    We test: sigma maps the variety V(a,t) onto V(a,t) IFF the set is also top-constrained;
    more simply we test the bijection of |lacBad| under the reflection of constraints.
    Here just confirm sigma permutes mu_n and check the e_t image-set sizes match between
    'gap t at bottom' and the reflected family.
    """
    if (p-1)%n: return None
    g=None
    for cand in range(2,p):
        x,o=cand%p,1
        while x!=1:
            x=(x*cand)%p; o+=1
            if o>p: break
        if o==n: g=cand; break
    if g is None: return None
    mu=sorted({pow(g,j,p) for j in range(n)})
    inv=lambda x:pow(x,p-2,p)
    def esym(S,t):
        if t==0: return 1%p
        if t>len(S): return 0
        acc=0
        for c in itertools.combinations(S,t):
            term=1
            for x in c: term=(term*x)%p
            acc=(acc+term)%p
        return acc%p
    # vanishing variety: e_1..e_{t-1}=0  (bottom gap t)
    Vbot=[]
    for S in itertools.combinations(mu,a):
        if all(esym(S,j)==0 for j in range(1,t)):
            Vbot.append(S)
    # reflected variety: e_{a-1}..e_{a-t+1}=0  (top gap t)
    Vtop=[]
    for S in itertools.combinations(mu,a):
        if all(esym(S,j)==0 for j in range(a-t+1,a)):
            Vtop.append(S)
    # sigma should biject Vbot <-> Vtop
    sig=lambda x:(p-inv(x))%p
    # check closure of mu under sigma
    if not all(sig(x) in mu for x in mu):
        return ("mu not sigma-closed",)
    def applysig(S): return tuple(sorted(sig(x) for x in S))
    img=set(applysig(S) for S in Vbot)
    Vtop_set=set(tuple(sorted(S)) for S in Vtop)
    bijects = (img == Vtop_set)
    return ("|Vbot|",len(Vbot),"|Vtop|",len(Vtop),"sigma(Vbot)==Vtop",bijects)

if __name__=="__main__":
    test_inversion_et()
    test_mobius_et()
    print("=== sigma reflects bottom-gap variety to top-gap variety over F_p ===")
    for (p,n,a,t) in [(41,8,3,2),(41,10,4,2),(97,8,4,2),(241,12,4,3),(241,16,5,2)]:
        print(f"  p={p} n={n} a={a} t={t}: {test_vanishing_variety_reflection(p,n,a,t)}")
