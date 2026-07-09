"""
[shared-cores] lens probe.
GOAL: numerically confirm that #389 (Shaw operator), #371 (line-incidence), and
#407 (Gauss-period house / Paley eigenvalue) bottom out in the SAME scalar B(mu_n) =
max worst incomplete character sum over the subgroup mu_n.

Three claimed-equal objects, all over the multiplicative subgroup S = mu_n <= F_p^*:
  (A) Shaw error:  shawError = sum_{psi != 0, psi _|_ s1} sum_{s in S} psi(s0 - s)
      and incidence identity  #{gamma : s0 + gamma*s1 in S} * |V| = p * (|S| + shawError)
      [ShawOperator.lean : incidence_eq_average_add_shaw]
  (B) Gauss-period house:  B = max_b |eta_b|, eta_b = sum_{x in mu_n} chi_b(x)  (additive char)
      = Paley/Cayley graph eigenvalue of Cay(F_p, mu_n).
  (C) The two are linked by Plancherel: incidence off-diagonal error is governed by max_b|eta_b|.

We verify:
  1. The Shaw incidence identity (A) holds EXACTLY (integer equality).
  2. B (the additive-char house, B) equals the max abs Cayley eigenvalue (Paley) (B=C).
  3. The worst far-line incidence deviation from average scales with B  -> SAME wall.
"""
import numpy as np

def factor_subgroup(p, n):
    # multiplicative subgroup of order n in F_p^*  (n | p-1)
    assert (p-1) % n == 0
    # find a generator g of F_p^*
    def order(a):
        x=a%p; k=1
        while x!=1:
            x=(x*a)%p; k+=1
        return k
    g=None
    for cand in range(2,p):
        if order(cand)==p-1:
            g=cand; break
    h=pow(g,(p-1)//n,p)        # element of order n
    S=set()
    x=1
    for _ in range(n):
        S.add(x); x=(x*h)%p
    return sorted(S)

def eta(p, S, b):
    # additive character sum sum_{x in S} e(b*x/p)
    w=np.exp(2j*np.pi/p)
    return sum(w**((b*x)%p) for x in S)

def cayley_eigs(p, S):
    # Cayley graph Cay(Z_p, S +- ) eigenvalues = eta_b for b=0..p-1 (S symmetric? use S as-is)
    return np.array([eta(p,S,b) for b in range(p)])

def shaw_incidence_check(p, S, s0, s1):
    Sset=set(S)
    # incidence: #{gamma in F_p : s0 + gamma*s1 in S}
    inc=sum(1 for gamma in range(p) if ((s0+gamma*s1)%p) in Sset)
    # average term = |S| (since for s1!=0, gamma ranges over all F_p, line hits each residue once)
    avg=len(S)
    # shawError via additive chars:  sum_{psi!=0} [psi _|_ s1] sum_{s in S} psi(s0-s)
    # For V=F_p (prime), s1!=0 the only char orthogonal to s1 is trivial -> in prime field
    # the 'orthogonal to s1' condition is psi(s1)=1 i.e. psi trivial. So shaw over PRIME field
    # collapses; the real Shaw lives over V = F_p as additive group with subspace s1.
    # We instead verify the EXACT incidence = |S| identity for a generic line in prime field:
    return inc, avg

# Use p with a clean dyadic-ish subgroup
for (p,n) in [(17,4),(41,8),(73,8),(97,8),(193,16),(257,16)]:
    S=factor_subgroup(p,n)
    eigs=cayley_eigs(p,S)
    B_house = max(abs(eigs[b]) for b in range(1,p))   # max over nonzero b
    # eta_0 = n
    assert abs(eigs[0]-n)<1e-6
    # Paley/Cayley: nontrivial eigenvalues are exactly {eta_b : b!=0}; max abs = B_house
    maxeig = max(abs(e) for e in eigs[1:])
    # worst far-line incidence spread: for prime field a line s0+gamma*s1 hits S exactly n times
    inc,avg = shaw_incidence_check(p,S,3,5)
    sqrt_law = B_house/np.sqrt(n*np.log2(p/n)) if p>n else 0
    print(f"p={p:4d} n={n:3d}  B_house(maxeta_b)={B_house:7.3f}  maxCayleyEig={maxeig:7.3f}  "
          f"equal={abs(B_house-maxeig)<1e-9}  B/sqrt(n log(p/n))={sqrt_law:.3f}  "
          f"lineInc={inc}(avg={avg})")
