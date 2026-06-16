import itertools, cmath, math
from sympy import isprime, primitive_root
def subgroup_idx(n,p):
    g=primitive_root(p); z=pow(g,(p-1)//n,p)
    elts=[]; x=1
    for i in range(n): elts.append(x); x=(x*z)%p
    return elts
def find_defect(n,p,sz,c):
    elts=subgroup_idx(n,p); negmap={x:(p-x)%p for x in elts}
    for T in itertools.combinations(range(n),sz):
        Tel=[elts[i] for i in T]
        if all(sum(pow(x,j,p) for x in Tel)%p==0 for j in range(1,c+1)):
            Tset=set(Tel)
            if not all(negmap[x] in Tset for x in Tel): return T
    return None
def conj_sq_sum(n,T_idx):
    # M = phi(n) = n/2 conjugates (odd j); sum |sigma_j(beta)|^2  vs trace identity M*|T|
    M = n//2
    total=0
    for j in range(1,n,2):  # odd j
        s=sum(cmath.exp(2*cmath.pi*1j*j*idx/n) for idx in T_idx)
        total += abs(s)**2
    return total, M*len(T_idx)
print("### TRACE IDENTITY: sum_{j odd} |sigma_j(beta_T)|^2 =?= M*|T| = (n/2)*s  (the free sqrt-cancellation) ###",flush=True)
n=32
for p,sz,c in [(97,6,2),(193,6,2),(257,8,2),(449,6,2)]:
    if (p-1)%n: continue
    T=find_defect(n,p,sz,c)
    if T:
        s2, trace = conj_sq_sum(n,T)
        print(f"  n={n} p={p} |T|={sz}: sum|sigma|^2={s2:.2f}  M*|T|={trace}  match={abs(s2-trace)<1e-6}",flush=True)
print("\n### CEILING with trace identity: |N|<=s^{M/2}=s^{n/4}, p^{c/2}<=s^{n/4} => p<=s^{1/(2eta)} ###",flush=True)
print("  eta_crit' = mu/(2(128+mu)) (the IDEALIZED bound); delta* at eta=1/mu",flush=True)
for mu in [25,30,35]:
    etac = mu/(2*(128+mu)); etad = 1/mu
    print(f"  mu={mu}: eta_crit'={etac:.4f}  eta_delta*={etad:.4f}  delta*-in-wall={etad<etac}",flush=True)
