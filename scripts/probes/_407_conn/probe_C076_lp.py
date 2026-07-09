"""
C076 probe step 2: the Chebyshev-Markov max-atom LP, with and without odd-moment rows.

QUESTION (the connection): does adding the proven odd-moment equalities
   Sum_i eta_i^{2k+1} = -n^{2k}    (k=1..R, char-0)
to the even-moment Chebyshev-Markov LP for the max far-atom B = max_i |eta_i| SHRINK B below
what the even moments alone allow?

MODEL.  The m period values eta_0..eta_{m-1} are real numbers (n=2^mu => -1 in mu_n => real
periods). One special atom is eta_0 = n (the FULL-group / principal value); the rest are the
'off-diagonal' spectrum.  Treat the empirical distribution as a (counting) measure mu on R
with total mass m, supported in [-n, n] (trivially |eta_b|<=n), with known power-sums
   p_t = sum_i eta_i^t.
We KNOW (exact, char-0):
   p_{2k+1} = -n^{2k}            (odd law)
   p_{2r}   = E_r  (>=0, the Bessel-ish even moments, computed exactly below)
We want:  max over feasible measures of the RIGHT endpoint of support that carries >=1 unit of
mass at a far location x (a single far atom), i.e. is there a feasible mu with an atom at some
|x| close to n.  The classic Markov bound: a far atom at x with mass >=1 needs
   x^{2r} <= p_{2r}  (one atom contributes x^{2r} to a nonneg sum).  -> B <= E_r^{1/(2r)}.
The LP refinement: maximize t (the location of a unit-mass atom) s.t. there EXISTS a nonneg
measure nu on a grid with nu({t})>=1 and ALL moment rows (even AND odd) matched.

We discretize support [-n,n] on a fine grid and solve:
   variables w_j >= 0 (mass at grid point x_j), plus a forced unit atom at candidate location c.
   constraints: sum_j w_j * x_j^t  (+ c^t for the forced atom) = p_t   for t in chosen rows
   feasibility => candidate far-atom location c is admissible.
Find the LARGEST feasible |c| with EVEN-only rows, vs EVEN+ODD rows. Compare.
"""
import numpy as np
from scipy.optimize import linprog

def subgroup(q,n):
    # the order-n subgroup mu_n = { x : x^n = 1 }: find any element of order exactly n.
    assert (q-1)%n==0
    def order(a):
        o=1;x=a%q
        while x!=1:
            x=(x*a)%q;o+=1
            if o>q: raise RuntimeError("order overflow")
        return o
    g=None
    for c in range(2,q):
        if order(c)==q-1:g=c;break
    assert g is not None,"no generator"
    h=pow(g,(q-1)//n,q)          # element of order exactly n
    sub=[pow(h,i,q) for i in range(n)]
    assert len(set(sub))==n,"subgroup wrong size"
    assert (q-1) in sub,"mu_n must contain -1 for n even"
    return sub,g

def count_tuples_sum_zero(residues,t,q):
    # exact integer DP (verified in probe_C076_moments_exact.py)
    dp=[0]*q; dp[0]=1
    for _ in range(t):
        ndp=[0]*q
        for s in range(q):
            v=dp[s]
            if v==0: continue
            for r in residues:
                ndp[(s+r)%q]+=v
        dp=ndp
    return dp[0]

def power_sums(q,n,tmax):
    sub,g=subgroup(q,n)
    m=(q-1)//n
    p={}
    for t in range(1,tmax+1):
        T=count_tuples_sum_zero(sub,t,q)
        S=q*T-n**t
        assert S%n==0
        p[t]=S//n
    return p,m

def feasible_atom(p, rows, c, n, m, ngrid=400):
    """Is there a nonneg measure on grid [-n,n] (mass total m) with a forced unit atom at c,
       matching the moment rows `rows` (list of t)?  LP feasibility."""
    xs=np.linspace(-n,n,ngrid)
    # variables: w_j>=0 ; equality A w = b  where b_t = p_t - c^t (atom contributes c^t)
    A=np.array([[x**t for x in xs] for t in rows],dtype=float)
    b=np.array([p[t]-c**t for t in rows],dtype=float)
    # also total mass: sum w + 1(atom) = m
    A=np.vstack([A,np.ones(ngrid)])
    b=np.append(b,m-1.0)
    # scale rows for conditioning
    sc=np.maximum(np.abs(b),1.0)
    A=A/sc[:,None]; b=b/sc
    res=linprog(c=np.zeros(ngrid),A_eq=A,b_eq=b,bounds=[(0,None)]*ngrid,method='highs')
    return res.success

def max_atom(p,rows,n,m,lo=0.0,ngrid=400):
    """Binary search the largest c in [0,n] admitting a feasible far atom at +c."""
    hi=float(n)
    if not feasible_atom(p,rows,lo,n,m,ngrid): return None
    for _ in range(40):
        mid=(lo+hi)/2
        if feasible_atom(p,rows,mid,n,m,ngrid): lo=mid
        else: hi=mid
    return lo

if __name__=="__main__":
    for q,n,Rmax in [(32833,8,3),(65537,16,2),(8089,8,3),(8161,32,2)]:
        tmax=2*Rmax+1
        p,m=power_sums(q,n,tmax)
        beta=np.log(q)/np.log(n)
        # actual B from exact periods (for ground truth)
        print(f"\n=== q={q} n={n} m={m} beta={beta:.2f}  power-sums:")
        for t in sorted(p): print(f"    p_{t} = {p[t]}")
        # Markov even-moment bound on max |eta|:  B <= E_r^{1/2r}, take min over r
        markov=min((p[2*r])**(1.0/(2*r)) for r in range(1,Rmax+1))
        print(f"  Markov even-moment bound  min_r E_r^(1/2r) = {markov:.4f}  (trivial cap n={n})")
        even_rows=[2*r for r in range(1,Rmax+1)]
        odd_rows =[2*k+1 for k in range(0,Rmax+1)]
        all_rows=sorted(even_rows+odd_rows)
        be=max_atom(p,even_rows,n,m,ngrid=600)
        ba=max_atom(p,all_rows,n,m,ngrid=600)
        print(f"  EVEN-only rows {even_rows}: max far atom B_even = {be}")
        print(f"  EVEN+ODD rows  {all_rows}: max far atom B_all  = {ba}")
        if be is not None and ba is not None:
            print(f"  ==> odd constraints {'SHRINK' if ba<be-1e-3 else 'do NOT shrink (INACTIVE)'} the max atom"
                  f"  (B_all/B_even = {ba/be:.4f})")
