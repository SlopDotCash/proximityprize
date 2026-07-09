"""
probe_444_descent_n32.py  (#444 -- does the odd-descent O_P=1 proof generalize?)

n=16 binding O_P=1 reduced (char-0, PROVEN) to: 4-subsets of mu_8 with e_2=0 form one
shift-orbit of e_1 (8 nonzero) + 2 with e_1=0 (mu_4-cosets, gamma=0).

General-n derivation (reciprocal-to-monic on the EVEN descended poly):
  binding x^{n/2+1}+g x^{n/2-1}, f odd deg<k  =>  monic M(y)=y^{n/4}+g y^{n/4-1}+ (e_2..e_J=0)
  - c... over mu_{n/2}.  #forced-zero conditions = n/4 - k/2 - 1 = (n-2k)/4 - 1.
    n=16,k=4: 1 cond (e_2=0).   n=32,k=8: 3 conds (e_2=e_3=e_4=0).   [verified by hand]
  bad gamma <=> (n/4)-subset of mu_{n/2} with e_2=...=e_{J+1}=0, gamma=-e_1.

TEST n=32, rho=1/4 (k=8): 8-subsets of mu_16 with e_2=e_3=e_4=0.  Questions:
  (1) char-0? (p-independent: cyclotomic vanishing, agrees across primes)
  (2) O_P=1?  (nonzero-e_1 subsets = single shift-orbit J->J+1)
  (3) how many e_1=0 (trivial) subsets?
If yes+yes, the odd-descent + cyclotomic-rigidity proof of the proxy O_P=1 generalizes.
"""
import itertools
from collections import Counter

def mu_zeta(p, order_n):
    def order(x):
        o,cur=1,x
        while cur!=1: cur=cur*x%p; o+=1
        return o
    g=2
    while order(g)!=p-1: g+=1
    return pow(g,(p-1)//order_n, p)

def esym_mod(S, j, p):
    acc=[0]*(len(S)+1); acc[0]=1
    for x in S:
        for t in range(len(S),0,-1):
            acc[t]=(acc[t]+acc[t-1]*x)%p
    return acc[j]

def test(N, halfsize, conds, primes):
    """N = n/2 (work in mu_N). subsets of size 'halfsize'. conds = list of e_j to vanish.
       returns dict per prime: (count, O_P_nonzero, num_zero_e1)."""
    nh=N
    results={}
    zsets_ref=None
    for p in primes:
        z=mu_zeta(p, nh)
        mu=[pow(z,i,p) for i in range(nh)]
        bad=[]   # exponent-sets J with all e_j=0
        for J in itertools.combinations(range(nh), halfsize):
            S=[mu[j] for j in J]
            if all(esym_mod(S,j,p)%p==0 for j in conds):
                bad.append(J)
        badset=set(bad)
        # split by e_1
        e1zero=[J for J in bad if esym_mod([mu[j] for j in J],1,p)%p==0]
        e1nz=[J for J in bad if J not in set(e1zero)]
        # O_P: shift-orbit count of nonzero-e_1 subsets under J->J+1 (dilation)
        rem=set(e1nz); orbs=0; orbsizes=[]
        while rem:
            J=next(iter(rem)); cur=J; o=set()
            for _ in range(nh):
                o.add(cur); cur=tuple(sorted((j+1)%nh for j in cur))
            orbs+=1; orbsizes.append(len(o & set(e1nz))); rem-=o
        results[p]=(len(bad), len(e1zero), len(e1nz), orbs, sorted(set(orbsizes)))
        if zsets_ref is None: zsets_ref=badset
        same = (badset==zsets_ref)
        results[p]=results[p]+(same,)
    return results

print("=== n=16 (mu_8), e_2=0 on 4-subsets [reconfirm] ===")
r=test(8, 4, [2], [17,97,65537])
for p,v in r.items():
    print(f"  p={p}: total={v[0]} (e1=0:{v[1]}, e1!=0:{v[2]}) O_P_nonzero={v[3]} orbsizes={v[4]} charP==charP_ref:{v[5]}")

print("\n=== n=32 (mu_16), sweep J = #conditions e_2..e_{J+1}=0 on 8-subsets ===")
for J in [1,2,3]:
    conds=list(range(2,2+J))
    print(f"  -- J={J} (conds e_{conds[0]}..e_{conds[-1]}=0, rate k=2*(7-J)={2*(7-J)}, rho={2*(7-J)/32:.3f}) --")
    r=test(16, 8, conds, [97,193,65537])
    for p,v in r.items():
        print(f"     p={p}: total={v[0]} (e1=0:{v[1]}, e1!=0:{v[2]}) O_P_nonzero={v[3]} orbsizes={v[4]} charP_consistent:{v[5]}")
