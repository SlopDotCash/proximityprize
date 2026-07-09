"""
C076 probe step 1 (EXACT): verify the moment laws via exact tuple-counting.

Key identity (exact integer arithmetic, no floats):
  Sum_{b != 0} S_b^t = p * T_t - n^t,   where  T_t = #{ (y_1..y_t) in mu_n^t : sum y_i ≡ 0 (mod p) }.
Then since S_b is constant on each coset of mu_n (n values of b per period), the m DISTINCT
period values eta_i satisfy
  Sum_{i=0}^{m-1} eta_i^t = (1/n) * Sum_{b != 0} S_b^t = (p*T_t - n^t)/n.

Odd-moment law claim: for t = 2k+1, in char-0 regime (p > n^t), T_t = 0, so
  Sum eta_i^{2k+1} = -n^{2k+1}/n = -n^{2k}.   <-- the claim.
Even-moment law (Bessel): Sum eta_i^{2r} = (p*T_{2r} - n^{2r})/n = E_r.

We compute T_t EXACTLY by counting tuples (feasible for small n, t up to ~6 via DP on the
multiset of residues of mu_n elements). This pins both laws with integer arithmetic.
"""
from functools import lru_cache

def subgroup(q,n):
    assert (q-1)%n==0
    def order(a):
        o=1;x=a%q
        while x!=1:x=(x*a)%q;o+=1
        return o
    g=None
    for c in range(2,q):
        if order(c)==q-1:g=c;break
    assert g is not None,"no generator"
    h=pow(g,(q-1)//n,q)
    sub=[pow(h,i,q) for i in range(n)]
    assert len(set(sub))==n
    return sub

def count_tuples_sum_zero(residues, t, q):
    """ T_t = # t-tuples from `residues` (with repetition, ordered) summing to 0 mod q.
        DP over count distribution mod q. residues has length n. """
    n=len(residues)
    # dp[s] = number of ways (ordered) to pick i elements summing to s mod q
    dp=[0]*q
    dp[0]=1
    for _ in range(t):
        ndp=[0]*q
        for s in range(q):
            v=dp[s]
            if v==0: continue
            for r in residues:
                ndp[(s+r)%q]+=v
        dp=ndp
    return dp[0]

def moments(q,n,maxk=3):
    sub=subgroup(q,n)
    m=(q-1)//n
    rows=[]
    print(f"q={q} n={n} m={m} beta=log_n(q)={__import__('math').log(q,n):.2f}")
    for k in range(0,maxk+1):
        t=2*k+1
        T=count_tuples_sum_zero(sub,t,q)
        Ssum=q*T - n**t           # Sum_{b!=0} S_b^t
        eta_sum=Ssum//n           # Sum eta_i^t   (must be exact integer)
        assert Ssum%n==0, (q,n,t,Ssum)
        claim=-(n**(2*k))
        char0 = q > n**t
        print(f"  ODD t={t}: T_t={T}  Sum eta^t={eta_sum}  claim -n^{2*k}={claim}  match={eta_sum==claim}  char0(p>n^t)={char0}")
    for r in range(1,maxk+1):
        t=2*r
        T=count_tuples_sum_zero(sub,t,q)
        Ssum=q*T - n**t
        eta_sum=Ssum//n
        char0 = q > n**t
        print(f"  EVEN t={t}: T_t={T}  E_r=Sum eta^t={eta_sum}  Bessel(2r-1)!!*n^r={__import__('math').prod(range(1,2*r,2))*n**r}  char0={char0}")
    return sub,m

if __name__=="__main__":
    cases=[(769,8),(8089,8),(32833,8),(4129,16),(8081,16),(65537,16),
           (8161,32),(65921,64)]
    for q,n in cases:
        try:
            moments(q,n,maxk=3)
        except AssertionError as e:
            print(f"q={q} n={n}: ASSERT {e}")
        print()
