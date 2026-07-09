import itertools, cmath, math
from sympy import isprime, primitive_root
def subgroup_idx(n,p):
    # return dict x->idx and list of elts
    g=primitive_root(p); z=pow(g,(p-1)//n,p)
    elts=[]; x=1
    for i in range(n): elts.append(x); x=(x*z)%p
    return elts
def find_defect(n,p,sz,c):
    """find non-antipodal-balanced T (size sz) with first c power sums =0 mod p."""
    elts=subgroup_idx(n,p)
    negmap={x:(p-x)%p for x in elts}
    for T in itertools.combinations(range(n),sz):
        Tel=[elts[i] for i in T]
        if all(sum(pow(x,j,p) for x in Tel)%p==0 for j in range(1,c+1)):
            # antipodal-balanced? every x has -x in T
            Tset=set(Tel)
            bal=all(negmap[x] in Tset for x in Tel)
            if not bal:
                return T  # the index set
    return None
def conj_mags(n,T_idx):
    """|sigma_j(beta_T)| for odd j, beta_T=sum zeta^{idx}, zeta=e^{2pi i/n}."""
    mags=[]
    for j in range(1,n,2):  # odd j = Galois autos
        s=sum(cmath.exp(2j*0+2*cmath.pi*1j*j*idx/n) for idx in T_idx)
        mags.append(abs(s))
    return mags
print("### SHARPER-NORM TEST: do defect conjugates have sqrt-cancellation (|sigma|~sqrt(s)) or align (~s)? ###",flush=True)
n=32
for p in [97,193,257,353,449,577,641,769]:
    if (p-1)%n: continue
    for sz in [6,8,10]:
        for c in [2,3]:
            T=find_defect(n,p,sz,c)
            if T:
                mags=conj_mags(n,T)
                Nabs=math.prod(mags)
                s=sz
                print(f"  n={n} p={p} size={s} c={c}: defect T(idx)={T}",flush=True)
                print(f"     |sigma_j| range [{min(mags):.2f},{max(mags):.2f}], mean={sum(mags)/len(mags):.2f}  (sqrt(s)={math.sqrt(s):.2f}, s={s})",flush=True)
                print(f"     |N(beta_T)|={Nabs:.3g}  vs s^(n/4)={s**(n//4):.3g} (sqrt-cancel) vs s^(n/2)={float(s**(n//2)):.3g} (AM-GM ceiling)",flush=True)
                print(f"     => N is ~{math.log(Nabs)/math.log(s):.2f}-th power of s (n/4={n//4}=sqrt-ideal, n/2={n//2}=AM-GM)",flush=True)
                break
        else: continue
        break
