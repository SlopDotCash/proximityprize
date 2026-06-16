import numpy as np, itertools, math
from collections import Counter
from math import comb

# ============================================================
# PROBE 2: The Li-Wan ADDITIVE transport (subsetSum_fibre_card_mul:
#   |G|*N(k,b) = C(|G|,k) when c->k*c surjective) -- is there an
#   under-exploited MULTIPLICATIVE analogue that maps the OPEN prize
#   subset-sum count onto the SOLVED additive Li-Wan count?
#
# The prize object: mu_n = {n-th roots of unity} subset F_p^*,
#   r-fold "subset sum" coincidences = E_r(mu_n) = #{ k-subsets summing to fixed b }
#   weighted -- governed by VANISHING SUMS of roots of unity.
#
# Li-Wan (additive, SOLVED): in (Z/s, +), N_fib(s,k)=C(s,k)/s when p∤k.
#
# CLAIM TO TEST (transport candidate): for mu_n = <zeta> with zeta a
#   primitive n-th root in F_p, the EXPONENT VECTOR map e: mu_n -> Z/n
#   (zeta^j -> j) is a GROUP ISO mu_n ≅ (Z/n,+) MULTIPLICATIVELY,
#   but the additive structure a+b in F_p is NOT the image of j+k.
#   So the additive energy of mu_n is NOT the Li-Wan additive count of Z/n.
#   QUESTION: does the char-0 ADDITIVE energy E(mu_n) match a Li-Wan-style
#   closed form anyway?  Known in-tree: E(mu_n)=3n^2-3n (n even), 2n^2-n? 
#   Test the exact char-0 additive energy formula and compare to Li-Wan C(n,2)/n style.
# ============================================================

def char0_additive_energy(n):
    # roots of unity zeta^j = exp(2pi i j/n), j=0..n-1, on unit circle in C
    pts=[np.exp(2j*np.pi*j/n) for j in range(n)]
    c=Counter()
    # a+b=c+d  <=> count pairs with same sum; use rounded complex sums
    sums=[]
    for a in pts:
        for b in pts:
            sums.append((a+b))
    # bucket by rounded value
    cc=Counter()
    for s in sums:
        cc[(round(s.real,6),round(s.imag,6))]+=1
    return sum(v*v for v in cc.values())

print("=== PROBE 2: char-0 additive energy of mu_n (unit circle) vs closed forms ===")
print(f"{'n':>4}{'E(mu_n)':>10}{'3n^2-3n':>10}{'2n^2-n':>10}{'match':>8}")
for n in [2,3,4,5,6,7,8,9,10,12,16]:
    E=char0_additive_energy(n)
    f_even=3*n*n-3*n
    f_odd=2*n*n-n
    if n%2==0:
        m = "even:3n^2-3n" if E==f_even else "??"
    else:
        m = "odd:2n^2-n" if E==f_odd else "??"
    print(f"{n:>4}{E:>10}{f_even:>10}{f_odd:>10}  {m}")

# ============================================================
# PROBE 3: the RESULTANT THRESHOLD transport (char-0 -> char-p).
#  ManyTermResultant: |Res(Phi_n, manyTerm_r)| <= (2r)^{phi(n)}.
#  So a NEW r-fold relation appears mod p only if p | Res, i.e. p <= (2r)^{phi(n)}.
#  Verify: for n=2^a, phi(n)=n/2, threshold = (2r)^{n/2}.
#  Cross-check the SHARPNESS claim: does p just above (2r)^{n/2} guarantee
#  E_r(mu_n) = char-0 value?  Test small case n=4 (phi=2), r=2:
#  threshold (2*2)^2 = 16.  primes p>16 with 4|p-1: 17,29,...
#  E_2(mu_4) char-0 should equal E_2 over F_p for p=17.
# ============================================================
print()
print("=== PROBE 3: resultant threshold (2r)^phi(n), char0=charp above it ===")
def mu_n_Fp(p,n):
    for cand in range(2,p):
        o=1;x=cand%p
        while x!=1:
            x=(x*cand)%p;o+=1
        if o==n:
            S=set();x=1
            for _ in range(n): S.add(x);x=(x*cand)%p
            return sorted(S)
    # try generator powers
    for cand in range(2,p):
        o=1;x=cand%p
        while x!=1:
            x=(x*cand)%p;o+=1
        if o%n==0:
            gen=pow(cand,o//n,p)
            S=set();x=1
            for _ in range(n):S.add(x);x=(x*gen)%p
            if len(S)==n: return sorted(S)
    return None

def addE_Fp(S,p):
    cc=Counter()
    for a in S:
        for b in S: cc[(a+b)%p]+=1
    return sum(v*v for v in cc.values())

for n in [4,8]:
    phi=n//2
    for r in [2]:
        thr=(2*r)**phi
        print(f" n={n} phi={phi} r={r} threshold(2r)^phi={thr}")
        for p in [pp for pp in range(5,400) if all(pp%k for k in range(2,pp)) and (pp-1)%n==0][:8]:
            S=mu_n_Fp(p,n)
            if S is None or len(S)!=n: continue
            E=addE_Fp(S,p)
            above = "ABOVE thr" if p>thr else "below thr"
            print(f"   p={p:>4} E_2(mu_n)={E:>6}  {above}")
