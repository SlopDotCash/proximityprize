"""
probe_444_e2_reduction.py  (#444 -- O_P=1 reduces to a CLEAN closed e_2=0 subset problem)

CLAIM (derived): the binding far-line O_P=1 on mu_n (direction x^{n/2+1}+gamma x^{n/2-1})
reduces, via 'bad f are ODD => psi_f-gamma even => descend y=x^2 + reciprocal trick', to:

   bad gamma  <=>  exists 4-subset {eta_1..eta_4} of mu_{n/2} with e_2(eta)=0,
                   and gamma = -e_1(eta) = -(eta_1+..+eta_4).
   O_P = # distinct dilation-orbits of such gamma.

Verify at n=16 (=> mu_8) that this matches the direct bad-gamma set, and check O_P=1.
Then probe n=32,64 (=> mu_16, mu_32): is the descended condition still 'e_2=0 on a 4-subset',
or does the binding depth grow (e_2=...=e_j=0)?  This tells us if O_P=1 is uniformly this clean.
"""
import itertools
from collections import Counter

def run(p, n, k, c):
    a,b=n//2+1,n//2-1; s=k+c
    def order(x):
        o,cur=1,x
        while cur!=1: cur=cur*x%p; o+=1
        return o
    g=2
    while order(g)!=p-1: g+=1
    w=pow(g,(p-1)//n,p)
    mu=[pow(w,i,p) for i in range(n)]
    # direct bad gamma (interpolation) -- reuse the solver
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
        return sol[k]
    direct=set()
    for T in itertools.combinations(mu,s):
        gv=solve_system(T)
        if gv in (None,'free'): continue
        if gv%p!=0: direct.add(gv)
    # descended e_2=0 model on mu_{n/2}
    nh=n//2; muh=[pow(w,2*i,p) for i in range(nh)]   # mu_{n/2} = <w^2>
    def esym(S, j):
        # e_j of list S, mod p
        acc=[0]*(len(S)+1); acc[0]=1
        for x in S:
            for t in range(len(S),0,-1):
                acc[t]=(acc[t]+acc[t-1]*x)%p
        return acc[j]
    model=set()
    for S in itertools.combinations(muh,4):
        if esym(S,2)%p==0:
            gamma=(-esym(S,1))%p
            if gamma%p!=0: model.add(gamma)
    match = (direct==model)
    # O_P on the model
    mult=pow(w,a-b,p)
    rem=set(model); orbs=0
    while rem:
        x0=next(iter(rem)); cur=x0; o=set()
        for _ in range(nh):
            o.add(cur); cur=cur*mult%p
        orbs+=1; rem-=o
    print(f"n={n} k={k} c={c} (mu_{nh}): direct |bad|={len(direct)}  model(e2=0) |bad|={len(model)}  "
          f"MATCH={match}  O_P(model)={orbs}")
    return match, orbs

print("=== verifying the e_2=0 descent reduction for O_P=1 ===")
run(65537, 16, 4, 3)        # the pinned binding case (p=2^16+1)
# other rates at n=16 (binding direction is the SAME x^9+g x^7, vary k=rho*n and binding depth c)
run(65537, 16, 2, 3)        # rho=1/8
run(65537, 16, 6, 3)        # rho=3/8
