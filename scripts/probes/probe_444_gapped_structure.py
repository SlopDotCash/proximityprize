"""
probe_444_gapped_structure.py  (#444 -- crack O_P=1 via the canonical gapped poly)

From probe_444_gapped_product: bad gamma <=> psi_f - gamma = V_T * W is GAPPED
(support {0,2} U [n/2+1, n/2+k]), and O_P=1 (all 8 nonzero gamma form one w^2-orbit).

Hypothesis to crack the PROOF: there is essentially ONE psi_f up to dilation. Extract the
distinct (f, gamma) [dedup the T-overcount], reduce mod dilation x->w*x, and inspect:
  - how many DISTINCT psi_f (mod dilation)?
  - factor psi_f - gamma over F_p : what is W?  does W's root set + T fill a structured set?
  - is the FULL level set {x : psi_f(x)=gamma} a coset / coset-union of a subgroup?
If the full level set is a coset of mu_d for fixed d, O_P=1 reduces to a clean coset statement.
"""
import itertools

p = 65537; n = 16; k = 4
a, b = n//2 + 1, n//2 - 1   # 9, 7
c = 3; s = k + c            # 7

def order(x):
    o, cur = 1, x
    while cur != 1: cur = cur*x % p; o += 1
    return o
g = 3
while order(g) != p-1: g += 1
w = pow(g, (p-1)//n, p)
mu = [pow(w, i, p) for i in range(n)]

def solve_system(T):
    rows, rhs = [], []
    for t in T:
        rows.append([pow(t,i,p) for i in range(k)] + [(-pow(t,b,p))%p]); rhs.append(pow(t,a,p))
    A = [r[:]+[rhs[i]] for i,r in enumerate(rows)]; ncol=k+1; piv=[]; r=0
    for col in range(ncol):
        pr=None
        for rr in range(r,len(A)):
            if A[rr][col]%p!=0: pr=rr; break
        if pr is None: continue
        A[r],A[pr]=A[pr],A[r]; inv=pow(A[r][col],p-2,p); A[r]=[x*inv%p for x in A[r]]
        for rr in range(len(A)):
            if rr!=r and A[rr][col]%p!=0:
                f=A[rr][col]; A[rr]=[(A[rr][j]-f*A[r][j])%p for j in range(ncol+1)]
        piv.append(col); r+=1
        if r==len(A): break
    for rr in range(len(A)):
        if all(A[rr][j]%p==0 for j in range(ncol)) and A[rr][ncol]%p!=0: return None
    if k not in piv: return 'free'
    sol=[0]*ncol
    for idx,col in enumerate(piv): sol[col]=A[idx][ncol]%p
    return (sol[k], tuple(sol[:k]))

# collect distinct (gamma, fcoef)
configs = set()
for T in itertools.combinations(mu, s):
    res = solve_system(T)
    if res in (None,'free'): continue
    gamma, fcoef = res
    if gamma % p == 0: continue
    configs.add((gamma, fcoef))
print(f"distinct (gamma, f) configs (nonzero gamma): {len(configs)}")

# dilation: x->w x sends f(x)->? psi_{f}(wx) relationship. Under T->wT, gamma->w^{a-b} gamma=w^2 gamma,
# and f's coeffs transform c_i -> w^{?} c_i. Let's just group configs by gamma-orbit and by f up to dilation.
def psi_level_set(fcoef, gamma):
    """full set of x in F_p^* (we check on mu only, plus count total roots) where psi_f(x)=gamma."""
    co = {}
    for i,ci in enumerate(fcoef):
        e=n//2+1+i; co[e]=(co.get(e,0)+ci)%p
    co[2]=(co.get(2,0)-1)%p; co[0]=(co.get(0,0)-gamma)%p
    co={e:v for e,v in co.items() if v%p!=0}
    roots_mu = [x for x in mu if sum(v*pow(x,e,p) for e,v in co.items())%p==0]
    return co, roots_mu

# inspect a few
shown=0
levelset_sizes=[]
for gamma, fcoef in sorted(configs):
    co, roots_mu = psi_level_set(fcoef, gamma)
    levelset_sizes.append(len(roots_mu))
    if shown < 8:
        logs = sorted(mu.index(x) for x in roots_mu)
        print(f"  gamma={gamma}: |level set in mu_n|={len(roots_mu)}, "
              f"root-exponents(base w)={logs}, support={sorted(co.keys())}")
        shown+=1

from collections import Counter
print("level-set-size distribution over mu_n:", dict(Counter(levelset_sizes)))

# Is each level set a UNION OF COSETS of some mu_d?  check: for each config, the gcd-structure
# of root exponents. If exponents form an arithmetic progression with common difference n/d
# (a coset of mu_d shifted), that's coset structure.
def coset_structure(logs):
    if len(logs) < 2: return None
    diffs = sorted(set((logs[i+1]-logs[i]) % n for i in range(len(logs)-1)))
    return diffs
print("\nper-config root-exponent gap patterns (first 8):")
shown=0
for gamma, fcoef in sorted(configs):
    co, roots_mu = psi_level_set(fcoef, gamma)
    logs = sorted(mu.index(x) for x in roots_mu)
    if shown<8:
        print(f"  gamma={gamma}: exps={logs} gaps={coset_structure(logs)}")
        shown+=1
