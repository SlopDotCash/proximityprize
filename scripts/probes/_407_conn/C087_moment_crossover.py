"""
C087 attack: explainableCoreSupply_iff_moment — is the F4 supply-moment crossover t*
the SAME wall as the F5 additive deep-moment anomaly r*?

The connection claims an EXACT dictionary:
  F4 supply moment  M_t(w) = Sum_c C(|A_c|, t)   (agreement-spectrum binomial moment)
  F5 additive moment E_r   = Sum_b eta_b^{2r}/q  (additive deep moment)
both "frozen at a base, coupled only above it"; and that the supply crossover (where
M_t exceeds its frozen-base extrapolation) lands at the same t* ~ beta+1 as the
W-anomaly r* (where E_r departs the char-0 Bessel value).

We compute BOTH exactly, at proper dyadic subgroups mu_n < F_q* in the PRIZE regime
(n = 2^mu proper, q prime = 1 mod n, q ~ n^beta, beta in 4-5, multiple primes), and
locate each crossover.

ADDITIVE SIDE (exact integer):
  Sum_{b!=0} S_b^t = p*T_t - n^t,   T_t = #{ y in mu_n^t : sum y_i = 0 mod p }
  E_r = (p*T_{2r} - n^{2r})/n.  char-0 Bessel value = (2r-1)!! * n^r.
  ANOMALY: E_r departs Bessel exactly when T_{2r} != 0, i.e. when there is a vanishing
  2r-term subset-sum of mu_n mod p. For thin mu_n the FIRST such relation is the
  negation pairs (needs n even -> y + (-y) = 0 uses 2 terms but with the SAME root only
  if -1 in mu_n; for dyadic n, -1 in mu_n, so antipodal pairs exist) -> char-0 bound is
  (2r-1)!!*n^r counting the negation-pair matchings; the EXTRA (anomaly) solutions are
  the non-pairing vanishing sums, which first appear once q <= n^{2r} roughly,
  i.e. 2r >= beta, i.e. r* ~ beta/2.

SUPPLY SIDE (exact integer):
  M_t(w) = Sum_{c in RS[dom,k]} C(|agreeSet(c,w)|, t)  for j=t >= k.
  Identity: = N_t(w) = # degenerate t-sets. Base (t=k): = C(n,k) frozen (every k-set).
  For the FORCING tower word w = x^{k+1} on the subgroup domain, the explainable
  (k+1)-cores are exactly the zero-sum (k+1)-subsets of dom (supply_ge_towerZeroSum /
  tower_degenerateSets_eq). So the supply at t=k+1 IS a zero-sum SUBSET count of mu_n.

The decisive comparison: the supply zero-sum object counts (k+1)-SUBSETS (distinct
elements, unordered) summing to 0; the additive moment T_t counts t-TUPLES (ordered,
with repetition) summing to 0. The connection asserts these have the SAME crossover.

We test: location of supply crossover t* (first t>k where N_t(w) for w=x^{k+1} exceeds
the char-0 / generic-position extrapolation) vs additive r* (first r where E_r departs
Bessel). Dictionary t <-> 2r. If t* = 2 r* they are one wall; if not, the dictionary
mislocates the wall.
"""
import math
from itertools import combinations

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
    g=find_gen(q)
    h=pow(g,(q-1)//n,q)
    sub=[pow(h,i,q) for i in range(n)]
    assert len(set(sub))==n
    return sub

def count_tuples_sum_zero(residues, t, q):
    """T_t = # ordered t-tuples (with repetition) from residues summing to 0 mod q."""
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

def count_subsets_sum_zero(residues, t, q):
    """# DISTINCT-element t-SUBSETS (unordered) of residues summing to 0 mod q.
       This is the supply zero-sum object for the tower word x^{t} cores."""
    # DP over elements, tracking (#chosen, sum mod q). residues distinct (subgroup).
    n=len(residues)
    # dp[(picked, s)] but cap picked at t
    dp=[[0]*q for _ in range(t+1)]
    dp[0][0]=1
    for r in residues:
        for p in range(min(t-1, n), -1, -1):
            row=dp[p]
            nrow=dp[p+1]
            for s in range(q):
                v=row[s]
                if v: nrow[(s+r)%q]+=v
    return dp[t][0]

def additive_anomaly(q,n,maxr=4):
    """Locate r*: first r where E_r != char-0 Bessel value (2r-1)!! n^r."""
    sub=subgroup(q,n)
    beta=math.log(q,n)
    res=[]
    for r in range(1,maxr+1):
        t=2*r
        T=count_tuples_sum_zero(sub,t,q)
        Ssum=q*T-n**t
        assert Ssum%n==0
        E=Ssum//n
        bessel=math.prod(range(1,2*r,2))*n**r
        char0 = q>n**t          # genuine char-0 (no nonzero vanishing tuple forced)
        anomaly = (E!=bessel)
        res.append((r,t,T,E,bessel,char0,anomaly))
    # first anomalous r
    rstar=next((r for (r,_,_,_,_,_,a) in res if a),None)
    return beta,res,rstar

def supply_crossover(q,n,kmax=3):
    """For the tower word x^{k+1}: N_{k+1} = zero-sum (k+1)-SUBSET count of mu_n.
       'frozen base' is t=k where N_k=C(n,k). Crossover t* = first t>k where the
       zero-sum subset count is NONZERO (= word geometry kicks in / coupling)."""
    sub=subgroup(q,n)
    rows=[]
    for t in range(2, kmax+3):
        Z=count_subsets_sum_zero(sub,t,q)
        rows.append((t,Z))
    # crossover: first t with a zero-sum t-subset existing
    tstar=next((t for (t,Z) in rows if Z>0),None)
    return rows,tstar

if __name__=="__main__":
    # PRIZE-REGIME proper dyadic subgroups: n=2^mu proper, q prime =1 mod n, q~n^beta.
    cases=[
        (769,8),    # beta ~ 3.2
        (8089,8),   # beta ~ 4.3
        (32833,8),  # beta ~ 5.0
        (4129,16),  # beta ~ 3.0
        (8081,16),  # beta ~ 3.24
        (65537,16), # beta ~ 4.0
        (8161,32),  # beta ~ 2.6
    ]
    print("="*100)
    print("ADDITIVE SIDE (F5): E_r vs char-0 Bessel; r* = anomaly onset")
    print("="*100)
    add={}
    for q,n in cases:
        beta,res,rstar=additive_anomaly(q,n,maxr=4)
        add[(q,n)]=(beta,rstar)
        print(f"\nq={q} n={n} beta={beta:.2f}  -> predicted r*~beta/2={beta/2:.2f}, t~beta={beta:.2f}")
        for (r,t,T,E,bessel,char0,anom) in res:
            flag = "  <== ANOMALY (E != Bessel)" if anom else ""
            print(f"   r={r} (t={t}): T_t={T:>4}  E_r={E:>12}  Bessel={bessel:>12}  char0={char0}{flag}")
        print(f"   => additive r* = {rstar}  (t=2r* = {2*rstar if rstar else None})")

    print()
    print("="*100)
    print("SUPPLY SIDE (F4): zero-sum t-SUBSET count of mu_n (tower-word x^t cores); t* = onset")
    print("="*100)
    sup={}
    for q,n in cases:
        rows,tstar=supply_crossover(q,n,kmax=4)
        sup[(q,n)]=tstar
        beta=math.log(q,n)
        print(f"\nq={q} n={n} beta={beta:.2f}")
        for (t,Z) in rows:
            flag=""
            if Z>0 and tstar==t: flag="  <== first zero-sum subset"
            print(f"   t={t}: zero-sum {t}-subsets = {Z}{flag}")
        print(f"   => supply t* = {tstar}")

    print()
    print("="*100)
    print("DICTIONARY TEST: does supply t* equal additive 2*r* (the claimed identification)?")
    print("="*100)
    for q,n in cases:
        beta,rstar=add[(q,n)]
        tstar=sup[(q,n)]
        twice = 2*rstar if rstar else None
        match = (tstar==twice)
        print(f"q={q} n={n} beta={beta:.2f}: supply t*={tstar}  additive 2r*={twice}  (r*={rstar})  SAME WALL={match}")
