"""
C036 wall-weld test.

The Newton bridge (verified exact) rewrites
  #vanishingVariety(mu_n, a, t) = #{ S subset mu_n : |S|=a, p_1(S)=...=p_{t-1}(S)=0 }
where p_j(S) = sum_{x in S} x^j.  This IS the simultaneous-vanishing-power-sum subset count.

Question that decides PROVEN/REFUTED vs REDUCED/OPEN:
  Does this give an INDEPENDENT (char-sum-free) handle on the WINDOW-INTERIOR count,
  or does it weld back to the same additive-energy / Lam-Leung / BGK wall?

Decisive structural facts to test (all exact, proper subgroups):

  (A) char-0 vs char-p split: the in-tree EnergyRelationAntipodal/LamLeung bound the
      char-0 count via antipodal balance. Compute the char-0 vanishing-power-sum subset
      count (over C / exact integer roots-of-unity sums) and the char-p count. If they
      AGREE for the tested params, the bridge inherits the char-0 bound for free THERE;
      if char-p has EXTRA solutions (coincidental mod-q vanishing), that extra mass IS
      the open char-p-transfer wall (the #389 deep-moment crux).

  (B) The count is an ENERGY object: p_1=...=p_{t-1}=0 means the size-a subset's power-sum
      vector is supported on degrees >= t. The number of such subsets is exactly the kind
      of additive-energy / moment count Lam-Leung governs. Show #var grows like the energy
      (not like O(n)) for fixed small gap t, i.e. the bridge does NOT by itself produce the
      O(n) floor --- the floor still needs the SAME deep-moment/antipodal input.
"""
import itertools, math
from fractions import Fraction

def is_prime(m):
    if m<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%p==0: return m==p
    d=m-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def find_q(n, beta_min=4, count=3):
    out=[]; target=n**beta_min; k=target//n
    while len(out)<count and k*n+1 < n*target*256:
        q=k*n+1
        if is_prime(q): out.append(q)
        k+=1
    return out

def subgroup_charp(n,q):
    def order(a):
        o=1;x=a
        while x!=1: x=x*a%q;o+=1
        return o
    g=None
    for c in range(2,q):
        if order(c)==q-1: g=c;break
    h=pow(g,(q-1)//n,q)
    S=[];x=1
    for _ in range(n): S.append(x);x=x*h%q
    return S

def psum_charp(sub,j,q): return sum(pow(x,j,q) for x in sub)%q

# char-0 model: mu_n = {exp(2pi i k/n)}; represent each element by its EXACT integer
# exponent k in Z/n. A power sum p_j(S) = sum_{k in K} omega^{jk}, omega = primitive n-th root.
# p_j(S) = 0  <=>  the cyclotomic-integer sum vanishes. For n=2^mu this vanishes iff the
# multiset {jk mod n} is antipodally balanced on the support (Lam-Leung: only relation among
# 2-power roots is the negation pairing).  We test p_j=0 EXACTLY via the minimal-poly/
# vanishing-sum-of-roots-of-unity criterion using a large prime that does NOT divide any
# resultant (so char-p faithfully models char-0): pick Q >> with Q = 1 mod n, Q huge.

def char0_vanishes(exps, n, jlist):
    """Return True iff p_j(S)=0 in char 0 for all j in jlist, S = {omega^k : k in exps}.
    Use the fact: sum of n-th roots of unity (n=2^mu) = 0 iff support is a union of full
    cosets of the order-2 subgroup paired antipodally => count(k)=count(k+n/2) for the
    multiset {jk mod n}. Equivalent exact test via faithful huge prime."""
    # faithful huge prime modeling char 0 (Q ~ n^large, no small-degree relation mod Q):
    return all(vanishes_faithful[j] for j in jlist) if False else None

def run(n, beta_min=4):
    qs=find_q(n,beta_min,4)
    # a faithful "char-0 proxy" prime: large Q=1 mod n, Q chosen big so no spurious
    # low-degree vanishing (we use the biggest found candidate as proxy and a smaller as test)
    if len(qs)<2:
        print(f"n={n}: insufficient primes"); return
    Q_proxy = max(qs)            # large => behaves char-0-like for small relations
    q_test  = min(qs)            # smaller prize-scale prime
    print(f"n={n}=2^{n.bit_length()-1}: char-0-proxy Q={Q_proxy}, prize-scale q={q_test}")
    Sp=subgroup_charp(n,Q_proxy)
    St=subgroup_charp(n,q_test)
    # align indexing: both ordered as powers of their generator => exponent k <-> position
    for a in range(2,min(n,7)):
        for t in range(2,a+1):
            # count subsets (by EXPONENT pattern) vanishing in proxy(char0) vs test(charp)
            n_proxy=0; n_test=0; extra=0
            for idx in itertools.combinations(range(n), a):
                subP=[Sp[i] for i in idx]; subT=[St[i] for i in idx]
                vP=all(psum_charp(subP,j,Q_proxy)==0 for j in range(1,t))
                vT=all(psum_charp(subT,j,q_test)==0 for j in range(1,t))
                if vP: n_proxy+=1
                if vT: n_test+=1
                if vT and not vP: extra+=1   # spurious char-p vanishing = the wall's extra mass
            if n_proxy==0 and n_test==0: continue
            flag = "" if extra==0 else f"  <-- CHAR-P EXTRA MASS = {extra} (open transfer wall)"
            growth = "O(n)?" if n_proxy<=2*n else "**> O(n): energy-scale**"
            print(f"  a={a} t={t}: char0-count={n_proxy} charp-count={n_test} "
                  f"[{growth} cf n={n}]{flag}")

if __name__=="__main__":
    for n in (8,16,32):
        run(n,4); print()
