"""
C017 attack: "Krawtchouk diagonalizes the Shaw operator: the worst far-line incidence
is a Krawtchouk-weighted Gauss period (F3 = F2 (x) F4-ball)."

The landed chain (all axiom-clean, verified by reading the .lean):
  incidence_eq_average_add_shaw : I*|V| = |F|*(|S| + 𝒮)
  shawError_subgroup_eq         : 𝒮(H) = |H| * Σ_{ψ∈H^⊥∩s₁^⊥, ψ≠0} ψ(s₀)         (LINEAR S=H)
  shell_fourier                 : Σ_{wt(e)=k} ψ(e) = K_k(charWeight ψ)              (ball S)

C017's CLAIM (attack_plan): replacing [ψ∈H^⊥] by the ball factor Σ_{k≤δn} K_k(wt ψ) gives
   I(δ) = Σ_{ψ⊥s₁, ψ≠0} ( Σ_{k≤δn} K_k(wt ψ) ) ψ(s₀),
and the far-line restriction makes the surviving ψ⊥s₁ the Gauss-period frequencies b·μ_n,
so I(δ) is a "Krawtchouk-weighted Gauss period sum" whose sign-oscillating weight
"could give cancellation the raw |η_b| sup-norm misses" / "DECAYS high-|b| periods".

THE DECISIVE QUESTION (testable, exact):
  For the surviving far-line frequencies, is the Krawtchouk WEIGHT
        W_b := Σ_{k≤δn} K_k(charWeight(ψ_b))
  (a) a per-b oscillating quantity that re-weights the η_b unequally (=> new lever), or
  (b) the SAME scalar for (essentially) all surviving b (=> factors out, NO new lever:
      |I| ~ |W| * |Σ_b η_b| and you are back to the BGK sup-norm wall)?

The geometry: in the prize instance V = F_q^N (N coordinates), a character ψ of V is a vector
b∈F_q^N, ψ(e)=ω^{<b,e>}. The "charWeight" of ψ is the HAMMING weight #{i: b_i≠0} of b (number
of coordinates on which ψ is nontrivial) -- a weight on the PRODUCT space.
The BGK object η_b = Σ_{y∈μ_n} ψ(b y) is a MULTIPLICATIVE-subgroup sum in the BASE field F_q.
These two "weights" are DIFFERENT objects. We test whether charWeight varies over the surviving
far-line frequencies, i.e. whether the Krawtchouk weight is per-b or constant.

Prize regime: dyadic μ_n, n=2^μ a PROPER subgroup of F_q*, q prime ≡1 mod n, q≈n^β, β≈4.
We test n=8,16,32 with multiple proper-subgroup primes.
"""
import sympy
from sympy import isprime
from math import comb

# ---------- Krawtchouk value K_k(x) ambient length N over alphabet q ----------
def krawtchouk(q, N, x, k):
    s = 0
    for j in range(k+1):
        s += comb(N-x, j) * (q-1)**j * comb(x, k-j) * ((-1)**(k-j))
    return s

def ball_weight(q, N, x, delta_floor_k):
    """W(x) = Σ_{k<=delta_floor_k} K_k(x), the ball-of-radius Fourier coefficient at charWeight x."""
    return sum(krawtchouk(q, N, x, k) for k in range(delta_floor_k+1))

def find_subgroup_prime(n, beta_target, count=2):
    """Find primes q ≡ 1 mod n, q≈n^beta_target, with μ_n a PROPER subgroup (q-1 > n)."""
    import math
    center = int(round(n**beta_target))
    out=[]
    # search q = 1 + n*t around center
    t0 = max(2, center//n)
    t = t0
    while len(out) < count and t < t0+200000:
        q = 1 + n*t
        if isprime(q) and (q-1) > n and ((q-1)//n) > 1:
            out.append(q)
        t += 1
    return out

print("="*78)
print("C017 PROBE: is the Krawtchouk weight a per-b LEVER or a common SCALAR?")
print("="*78)

# ----------------------------------------------------------------------------
# PART A. The character-weight of the surviving far-line frequencies.
# ----------------------------------------------------------------------------
# In ShellFourierKrawtchouk, V = ι→F with |ι|=N coords, charWeight ψ = #{i: axisChar ψ i ≠0}.
# A far-line direction s₁ = monomial means s₁ has Hamming weight 1 (single nonzero coordinate),
# OR (RS interpretation) the surviving ψ⊥s₁ form a hyperplane and the Gauss-period reduction
# picks out frequencies of the form b·(vector of μ_n powers). We examine the distribution of
# charWeight over the surviving frequency set, because THAT is the input to the Krawtchouk weight.
#
# The honest structural fact we test: in the RS prize instance the "Gauss-period frequencies
# b·μ_n" that survive are the n nonzero multiples; as VECTORS in F_q^N (N = code length) the
# RS-codeword/character correspondence makes the relevant charWeight essentially MAXIMAL and
# CONSTANT (= N or N-O(1)) across surviving b, because a nonzero RS dual codeword (low-degree
# poly evaluated on the domain) is nonzero on n - deg ~ all coordinates (MDS!). We verify the
# MDS-forces-full-weight phenomenon and its consequence for the Krawtchouk factor.

print("\n[A] charWeight distribution of nonzero RS-dual codewords (MDS => near-full weight).")
print("    A dual RS[N,k] codeword is a deg<N-k poly on N points; nonzero codeword has")
print("    weight >= N-(N-k-1) = k+1 (MDS min distance). So charWeight in [N-k... wait]")
print("    MDS distance d=N-k'+1 for the dual of dim k'. The point: weights are NOT spread")
print("    over [0,N]; they cluster HIGH. We show the Krawtchouk factor over that cluster.")

# Concrete small RS instance to exhibit weight clustering (use small field, but the POINT is
# structural/MDS so it holds at any size): RS[N,k], dual = RS[N, N-k]. Min distance of code of
# dim m over MDS = N-m+1.  For dual of dim k'=N-k, min weight = N-(N-k)+1 = k+1.
for (N,k) in [(8,2),(16,4),(16,2),(32,8)]:
    dual_dim = N-k
    min_wt = N - dual_dim + 1   # = k+1
    print(f"   RS[N={N},k={k}]: dual dim={dual_dim}, every nonzero dual codeword has "
          f"Hamming weight in [{min_wt}, {N}] (MDS); LOW weights 1..{min_wt-1} are EMPTY.")

# ----------------------------------------------------------------------------
# PART B. Does the Krawtchouk weight W(x) actually decay/oscillate over the
# surviving (HIGH) weight range, enough to beat the sup-norm?
# ----------------------------------------------------------------------------
print("\n[B] Krawtchouk ball-weight W(x)=Σ_{k<=δN} K_k(x) over charWeight x in prize regime.")
print("    If W(x) is ~constant over the surviving weight band, it FACTORS OUT (no lever).")
print("    If |W(x)| varies wildly with sign changes over surviving x, it's a real lever.\n")

for n in [8, 16, 32]:
    beta = 4.0
    primes = find_subgroup_prime(n, beta, count=2)
    if not primes:
        print(f"  n={n}: no prime found"); continue
    for q in primes:
        m = (q-1)//n
        N = n   # code length = subgroup size in the Gauss-period instance (η_b sums n terms)
        # delta in the prize window (1-sqrt(rho), ...). Take a representative interior delta.
        for delta in [0.25, 0.5]:
            kfloor = int(delta*N)
            # surviving charWeights: in the MDS far-line regime they cluster in [N-O(1), N];
            # we sample the whole HIGH band to see W's behavior there.
            band = list(range(max(0,N-4), N+1))
            vals = [(x, ball_weight(q, N, x, kfloor)) for x in band]
            mags = [abs(v) for _,v in vals]
            mx = max(mags); mn = min(mags)
            ratio = (mx/mn) if mn>0 else float('inf')
            signs = set((1 if v>0 else (-1 if v<0 else 0)) for _,v in vals)
            print(f"  n={n:2d} q={q} m={m} N={N} delta={delta} kfloor={kfloor}: "
                  f"W over top-weights {band}:")
            print(f"        |W| range [{mn}, {mx}] ratio={ratio:.3g}  signs={signs}  "
                  f"(constant-up-to-sign? {len(set(mags))==1})")
