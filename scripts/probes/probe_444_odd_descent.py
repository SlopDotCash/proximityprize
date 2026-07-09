"""
probe_444_odd_descent.py  (#444 -- the O_P=1 CRACK: bad f are ODD, level set descends)

NEW finding from probe_444_gapped_structure: the gapped poly psi_f - gamma has support
{0,2,10,12} = ALL EVEN.  =>  bad f are ODD: f = c1 X + c3 X^3.  =>  psi_f - gamma is an
EVEN polynomial  =>  descends to Phi_gamma(y), y=x^2, on mu_{n/2}=mu_8, and the level set
is ANTIPODAL-SYMMETRIC (refuting the earlier 'non-symmetric T' obstruction: the size-7 T
were sub-sets of a size-8 SYMMETRIC level set).

Tests:
 (1) every bad config has c0=c2=0 (f odd).
 (2) reciprocity: is the gapped poly (anti-)palindromic? i.e. c1, c3 pinned by gamma?
 (3) descend to mu_8: Phi_gamma(y) = c3 y^6 + c1 y^5 - y - gamma; its roots in mu_8 =
     the descended level set (4 points). Define when 'gamma = rho(y)' is a SINGLE rational
     map (=> O_P=1 is a fiber-count of one map on mu_8).
 (4) O_P on mu_8 directly: how many dilation(w^2)-orbits of bad gamma.
"""
import itertools

p = 65537; n = 16; k = 4
a, b = n//2 + 1, n//2 - 1
c = 3; s = k + c

def order(x):
    o,cur=1,x
    while cur!=1: cur=cur*x%p; o+=1
    return o
g=3
while order(g)!=p-1: g+=1
w=pow(g,(p-1)//n,p)
mu=[pow(w,i,p) for i in range(n)]

def solve_system(T):
    rows,rhs=[],[]
    for t in T:
        rows.append([pow(t,i,p) for i in range(k)]+[(-pow(t,b,p))%p]); rhs.append(pow(t,a,p))
    A=[r[:]+[rhs[i]] for i,r in enumerate(rows)]; ncol=k+1; piv=[]; r=0
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

configs=set()
for T in itertools.combinations(mu,s):
    res=solve_system(T)
    if res in (None,'free'): continue
    gamma,fc=res
    if gamma%p==0: continue
    configs.add((gamma,fc))

print(f"{len(configs)} distinct nonzero-gamma configs (n={n},k={k},binding x^{a}+g x^{b})\n")

# (1) f odd?
all_odd=True
for gamma,fc in configs:
    c0,c1,c2,c3=fc
    if c0%p!=0 or c2%p!=0: all_odd=False
print(f"(1) f ODD for all configs (c0=c2=0): {all_odd}")

# (2) reciprocity / pinning: print (gamma, c1, c3); test c1==-1 and c3==-gamma (the palindrome guess)
print("\n(2) config table (gamma, c1, c3); test palindrome c1=-1, c3=-gamma:")
pin_ok=True
for gamma,fc in sorted(configs):
    c1,c3=fc[1],fc[3]
    test = (c1==(p-1)) and (c3==(p-gamma)%p)
    pin_ok = pin_ok and test
    print(f"   gamma={gamma:5d}  c1={c1:5d}  c3={c3:5d}  palindrome[c1=-1,c3=-gamma]={test}")
print(f"   => palindrome pinning holds for all: {pin_ok}")

# (3) descended single rational map on mu_8.  If pinned, psi_f-gamma = c3 X^12 + c1 X^10 - X^2 - gamma
# with c1=-1,c3=-gamma: = -gamma X^12 - X^10 - X^2 - gamma = -(gamma(X^12+1) + X^2(X^8+1)).
# Root <=> gamma(X^12+1) + X^2(X^8+1) = 0 <=> gamma = -X^2(X^8+1)/(X^12+1).  In y=X^2 on mu_8:
#   gamma = rho(y) = -y(y^4+1)/(y^6+1).
mu8=[pow(w,2*i,p) for i in range(n//2)]   # mu_8 = <w^2>
def rho(y):
    num=(-y*((pow(y,4,p)+1)%p))%p
    den=(pow(y,6,p)+1)%p
    if den%p==0: return None  # pole
    return num*pow(den,p-2,p)%p
print("\n(3) descended single map rho(y) = -y(y^4+1)/(y^6+1) on mu_8:")
from collections import Counter
vals=[]
for y in mu8:
    r=rho(y)
    vals.append(r)
    print(f"   y=w^{2*mu8.index(y)}: rho={r}")
fibers=Counter(v for v in vals if v is not None)
print(f"   fiber sizes of rho (nonzero-gamma): {dict(Counter(fibers.values()))}")
print(f"   distinct nonzero rho-values: {sorted(set(v for v in vals if v not in (None,0)))}")

# (4) cross-check: do these rho-values match the bad gammas, and is it ONE w^2-orbit?
badset=set(g_ for g_,_ in configs)
rhoset=set(v for v in vals if v not in (None,0))
print(f"\n(4) rho-values == bad gammas? {rhoset==badset}  (|rho|={len(rhoset)}, |bad|={len(badset)})")
# orbit under multiplication by w^2 (=gamma-dilation):
mult=pow(w,a-b,p)
rem=set(badset); orbs=0
while rem:
    x0=next(iter(rem)); cur=x0; o=set()
    for _ in range(n//2):
        o.add(cur); cur=cur*mult%p
    orbs+=1; rem-=o
print(f"   O_P (w^2-orbits of bad gamma) = {orbs}")
