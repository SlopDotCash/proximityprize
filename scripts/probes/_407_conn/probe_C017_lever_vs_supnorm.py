"""
C017 attack, PART 3: the decisive lever test.

C017's load-bearing INSIGHT claim:
  "its sign-oscillation could give cancellation the raw |η_b| sup-norm misses"
  "measure whether the Krawtchouk weight DECAYS high-|b| periods (new lever for reverse bound)"

We test this honestly. There are TWO competing effects when you weight the Gauss periods
η_b by the Krawtchouk ball factor W(wt ψ_b):
  (+) sign oscillation of W could create cancellation across b, AND
  (-) W's MAGNITUDE varies by factors of q^{δN}, so the weighted sum is DOMINATED by the
      single largest-|W| frequency -> NO cancellation, and the bound gets MULTIPLIED by max|W|.

The relevant question for a REVERSE / sup-norm-beating bound is whether
   |Σ_b W_b η_b|   <<   (Σ_b |W_b|) * max_b|η_b|      (i.e. Krawtchouk cancellation helps)
or whether it's governed by the dominant term (no help, and the prize wall is untouched).

We ALSO answer: do the surviving far-line frequencies even form the thin set {b·μ_n}?
In the product space F_q^N the surviving set is the FULL hyperplane s₁^⊥ (q^{N-1}-ish chars),
NOT the n-element Gauss-period set. The Gauss-period reduction (F2) only happens for the
RS-DUAL agreement set (linear code H = dual RS), where ψ must ALSO lie in H^⊥. We test the
combined constraint ψ∈H^⊥∩s₁^⊥ to see what actually survives.
"""
import itertools, cmath, math
from math import comb

def krawtchouk(q, N, x, k):
    return sum(comb(N-x, j)*(q-1)**j*comb(x, k-j)*((-1)**(k-j)) for j in range(k+1))
def ball_weight(q, N, x, kfloor):
    return sum(krawtchouk(q, N, x, k) for k in range(kfloor+1))

print("="*78)
print("C017 PART 3: does the Krawtchouk weight BEAT the sup-norm, and what survives?")
print("="*78)

# ---- 3A: the magnitude-dominance test (Krawtchouk weight kills cancellation) ----
print("\n[3A] |Σ_b W_b η_b| vs Σ|W_b|·max|η_b|: does Krawtchouk weighting help or hurt?")
print("     We model η_b as the EXACT Gauss-period sums of a subgroup μ_n ⊂ F_q*, and")
print("     W_b as the ball factor at the charWeight of frequency b. Prize regime.\n")

def gauss_periods(q, n):
    """eta_b = Σ_{y∈μ_n} ω^{b y} for b=1..q-1, ω=exp(2πi/q). Returns list of |eta_b|."""
    # μ_n = n-th roots of unity in F_q* : need a generator g, μ_n = {g^{m j}}, m=(q-1)/n.
    # find primitive root
    def primroot(q):
        from sympy.ntheory import primitive_root
        return primitive_root(q)
    g = primroot(q)
    m = (q-1)//n
    sub = [pow(g, m*j, q) for j in range(n)]   # μ_n
    w = cmath.exp(2j*math.pi/q)
    etas = []
    for b in range(1, q):
        s = sum(w**((b*y)%q) for y in sub)
        etas.append(abs(s))
    return etas, sub

from sympy import isprime
def find_prime(n, beta, count=1):
    center=int(round(n**beta)); t0=max(2,center//n); out=[]; t=t0
    while len(out)<count and t<t0+200000:
        q=1+n*t
        if isprime(q) and (q-1)//n>1: out.append(q)
        t+=1
    return out

for n in [8, 16]:
    q = find_prime(n, 3.0, 1)[0]    # smaller beta=3 to keep eta enumeration feasible (q<~4k,65k)
    etas, sub = gauss_periods(q, n)
    B = max(etas)                    # the BGK sup-norm object max|η_b|
    N = n
    for delta in [0.25, 0.5]:
        kfloor = int(delta*N)
        # weight each b by W(charWeight). In the thin Gauss-period model the relevant
        # charWeight for frequency "b·μ_n" as an RS-dual vector is ~ N - O(1) (MDS, full wt).
        # Realistically charWeight varies; we sample wt uniformly in the high MDS band [N-3,N].
        import random; random.seed(1)
        # assign each b a charWeight in the high band, then form Σ W_b η_b (with random signs of η)
        weighted = 0+0j; sumabsW=0;
        w = cmath.exp(2j*math.pi/q)
        g = __import__('sympy').ntheory.primitive_root(q); m=(q-1)//n
        # exact complex eta_b (not just magnitude) for an honest signed sum:
        for b in range(1, q):
            wt = N - (b % 4)                     # vary charWeight in high band [N-3,N]
            Wt = ball_weight(q, N, wt, kfloor)
            eta = sum(w**((b*y)%q) for y in sub)
            weighted += Wt*eta
            sumabsW += abs(Wt)
        lhs = abs(weighted)
        rhs = sumabsW * B
        # also the UNWEIGHTED coherent reference and the per-term dominant
        maxW = max(abs(ball_weight(q,N,N-(b%4),kfloor)) for b in range(1,q))
        print(f"  n={n} q={q} N={N} delta={delta} kfloor={kfloor}: B=max|eta|={B:.3f}")
        print(f"     |Σ_b W_b η_b| = {lhs:.4e}")
        print(f"     Σ|W_b|·B      = {rhs:.4e}   ratio(lhs/rhs)={lhs/rhs:.4f}")
        print(f"     max|W_b|·B    = {maxW*B:.4e}   (single dominant term)")
        print(f"     -> Krawtchouk-weighted house vs sup-norm: lhs/(max|W|·B) = {lhs/(maxW*B):.4f}")
        print(f"        (if ~1, NO cancellation beyond a single dominant term: weight is a")
        print(f"         magnitude AMPLIFIER, not a sign-cancellation LEVER)")
    print()
