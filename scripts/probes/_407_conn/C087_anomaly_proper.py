"""
C087 attack, CORRECTED crossover definition.

The W-anomaly is NOT 'E_r != Bessel' (that fires trivially at r=1 via antipodal pairs,
since -1 in mu_n for dyadic n). The anomaly is the EXTRA mod-p vanishing tuples that do
NOT vanish over the integers Z (= the genuinely char-p coincidences = the BGK/defect
content). Split:

  T_t(mod p) = T_t^Z (tuples of mu_n-elements, viewed as the actual roots of unity images
               in Z[zeta]? -> NOT integers). Better operationalization that is EXACT and
  prize-faithful: the char-0 value of the moment is the LARGEST that holds for ALL primes
  p > n^t (genuine char-0 regime, no wraparound possible). The ANOMALY at radius r is the
  ONSET of mod-p-only solutions, which is exactly when q <= n^t (t=2r), i.e. r > beta/2.

So r*_anomaly = ceil(beta/2)+ : the first r with q <= n^{2r}, i.e. T_{2r} contains
wraparound (mod-p-only) solutions beyond the char-0 ones.

To make this EXACT and not a heuristic, we directly separate, for each tuple summing to
0 mod p, whether its REAL (integer) sum of the actual root-of-unity VALUES is 0. But the
mu_n elements are residues mod p, not roots of unity, so the faithful char-0 object is:
count tuples whose sum is 0 mod p AND whose representative-integer sum (using the canonical
0..p-1 residues) forces a 'wrap' (sum = k*p, k != 0) vs no-wrap (sum = 0 exactly as integers,
impossible for positive residues unless all-zero) -- that operationalization fails because
residues are all positive.

CLEAN operationalization (the one the KB uses): char-0 validity of the moment bound
(2r-1)!! n^r holds iff q > n^{2r} (the norm/wraparound bound). The anomaly onset r* is
the LARGEST r with q > n^{2r}, plus one. We ALSO measure it intrinsically: the ratio
E_r / Bessel. In genuine char-0 (q > n^{2r}) the bound E_r <= (2r-1)!! n^r should hold;
once q <= n^{2r}, E_r BLOWS PAST it. We locate the first r where E_r > Bessel
(over-the-bound), the TRUE anomaly, distinct from E_r != Bessel.
"""
import math

def find_gen(q):
    def order(a):
        o=1;x=a%q
        while x!=1:x=(x*a)%q;o+=1
        return o
    for c in range(2,q):
        if order(c)==q-1:return c
    raise RuntimeError("no gen")

def subgroup(q,n):
    assert (q-1)%n==0,(q,n)
    g=find_gen(q); h=pow(g,(q-1)//n,q)
    sub=[pow(h,i,q) for i in range(n)]
    assert len(set(sub))==n
    return sub

def count_tuples_sum_zero(residues, t, q):
    dp=[0]*q; dp[0]=1
    for _ in range(t):
        ndp=[0]*q
        for s in range(q):
            v=dp[s]
            if v==0: continue
            for r in residues: ndp[(s+r)%q]+=v
        dp=ndp
    return dp[0]

def count_subsets_sum_zero(residues, t, q):
    n=len(residues)
    dp=[[0]*q for _ in range(t+1)]; dp[0][0]=1
    for r in residues:
        for p in range(min(t-1,n),-1,-1):
            row=dp[p]; nrow=dp[p+1]
            for s in range(q):
                v=row[s]
                if v: nrow[(s+r)%q]+=v
    return dp[t][0]

def analyze(q,n,maxr=4):
    sub=subgroup(q,n); beta=math.log(q,n)
    print(f"\nq={q} n={n} beta={beta:.3f}")
    print(f"  ADDITIVE: r*_overbound = first r with E_r > Bessel(2r-1)!!n^r  (TRUE anomaly; predicted r*~ceil(beta/2)+1, where q<=n^{{2r}})")
    rstar=None
    for r in range(1,maxr+1):
        t=2*r
        T=count_tuples_sum_zero(sub,t,q)
        E=(q*T-n**t)//n
        bessel=math.prod(range(1,2*r,2))*n**r
        char0 = q>n**t
        over = E>bessel
        if over and rstar is None: rstar=r
        print(f"    r={r}(t={t}): E_r={E:>14}  Bessel={bessel:>12}  E/Bessel={E/bessel:7.2f}  char0(q>n^t)={char0}  OVER={over}")
    # supply: zero-sum subset onset AFTER the trivial pair t=2
    print(f"  SUPPLY: zero-sum t-subset counts (tower x^t cores); look for the NONTRIVIAL onset (t>2, beyond antipodal pairs)")
    first_nontrivial=None
    for t in range(2,maxr*2+1):
        Z=count_subsets_sum_zero(sub,t,q)
        tag=""
        if t>2 and Z>0 and first_nontrivial is None and t%2==1:
            first_nontrivial=t; tag="  <== first ODD nontrivial (not a pure pairing)"
        print(f"    t={t}: zero-sum {t}-subsets={Z}{tag}")
    print(f"  => additive r*_overbound={rstar} (t=2r*={2*rstar if rstar else None}); first ODD nontrivial supply subset t={first_nontrivial}")
    return beta,rstar,first_nontrivial

if __name__=="__main__":
    cases=[(769,8),(8089,8),(32833,8),(4129,16),(8081,16),(65537,16),(8161,32)]
    results=[]
    for q,n in cases:
        results.append((q,n)+analyze(q,n,maxr=4))
    print("\n"+"="*90)
    print("SUMMARY: additive over-the-bound anomaly r* vs supply structure")
    print("="*90)
    print(f"{'q':>7}{'n':>5}{'beta':>7}{'r*_over':>9}{'2r*':>6}{'pred ceil(b/2)+1':>18}{'supply odd onset':>18}")
    for (q,n,beta,rstar,fnt) in results:
        pred=math.ceil(beta/2)+1
        print(f"{q:>7}{n:>5}{beta:>7.2f}{str(rstar):>9}{str(2*rstar if rstar else None):>6}{pred:>18}{str(fnt):>18}")
