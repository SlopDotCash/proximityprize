"""
C017 attack, PART 2: end-to-end EXACT verification of the composed identity, and the
honest structural test of whether the Krawtchouk weight is a NEW LEVER.

We test the composed claim
   I(delta) = average + (|F|/|V|) * Shaw
            = average + (|F|/|V|) * Σ_{ψ⊥s₁, ψ≠0} ( Σ_{k<=δN} K_k(charWeight ψ) ) ψ(s₀)
on a SMALL but real instance V = F_q^N where we can enumerate exactly, AND we examine the
distribution of the Krawtchouk weight over the SURVIVING far-line frequencies.

KEY structural observations to nail down (these decide PROVEN/REDUCED/OPEN):

(1) The shell/Krawtchouk machinery lives over V=F_q^N (q^N elements). The "Hamming ball" S
    of radius δN has |S| ~ Σ_{k<=δN} C(N,k)(q-1)^k -- an enormous set, NOT the thin μ_n object.
    The 1̂_S(ψ)=Σ_{k<=δN}K_k(wt ψ) factor has MAGNITUDE ~ q^{δN} (dominated by (q-1)^k).
    The "η_b" BGK object is Σ_{y∈μ_n}ψ(by), a sum of n terms with |η_b|~√n -- a DIFFERENT,
    far smaller object in the BASE field F_q.

(2) The charWeight that feeds K_k is a Hamming weight on the PRODUCT-space dual (a vector in
    F_q^N). For the far-line "monomial" restriction the surviving ψ⊥s₁ are a HYPERPLANE; their
    charWeights take MANY values across [d_dual, N]. So W_b := Σ K_k(wt ψ_b) does vary per b.
    BUT: does that variation help? We compute, for each surviving b:
        ratio of the Krawtchouk-weighted Gauss sum to the raw |Σ η_b| sup-norm bound.

The test: compute BOTH
    LHS_exact = the true incidence I(delta) on F_q^N (enumerated), and
    the Krawtchouk-weighted character sum,
and ALSO the naive sup-norm bound B*|#surviving|, to see if the Krawtchouk weight buys
cancellation. We use a TINY q (full enumeration) -- this is a STRUCTURE check, the prize-regime
numerics (huge W) come from probe_C017_krawtchouk_lever.py.
"""
import itertools, cmath, math
from math import comb

def krawtchouk(q, N, x, k):
    return sum(comb(N-x, j)*(q-1)**j*comb(x, k-j)*((-1)**(k-j)) for j in range(k+1))

def ball_weight(q, N, x, kfloor):
    return sum(krawtchouk(q, N, x, k) for k in range(kfloor+1))

# tiny prime field F_q, q prime. character ω^{a} = exp(2πi a/q) on F_q.
def run(q, N, delta, verbose=True):
    assert all(q % d for d in range(2,int(q**0.5)+1)), "q must be prime"
    w = cmath.exp(2j*math.pi/q)
    kfloor = int(delta*N)
    # ----- enumerate Hamming ball S in F_q^N of radius kfloor -----
    S = []
    for e in itertools.product(range(q), repeat=N):
        wt = sum(1 for x in e if x != 0)
        if wt <= kfloor:
            S.append(e)
    # ----- pick a far-line: s₀, s₁ with s₁ = monomial (Hamming weight 1) -----
    s1 = tuple([1]+[0]*(N-1))         # monomial direction
    s0 = tuple([1]*N)                  # generic base point
    # ----- EXACT incidence: #{γ∈F_q : s₀+γ s₁ ∈ S} -----
    Sset = set(S)
    inc = 0
    for g in range(q):
        pt = tuple((s0[i]+g*s1[i]) % q for i in range(N))
        if pt in Sset:
            inc += 1
    Vcard = q**N
    Fcard = q
    avg = Fcard * len(S) / Vcard          # average incidence = q*|S|/q^N
    # ----- spectral side: Shaw = Σ_{ψ⊥s₁, ψ≠0} (Σ_{k<=kfloor}K_k(wt ψ)) ψ(s₀) -----
    # characters ψ = vector b∈F_q^N, ψ(e)=ω^{<b,e>}. ψ⊥s₁ <=> <b,s₁>≡0 <=> b_0=0.
    # charWeight ψ = #{i: b_i≠0}.
    shaw = 0+0j
    surviving = []
    for b in itertools.product(range(q), repeat=N):
        if (sum(b[i]*s1[i] for i in range(N)) % q) != 0:   # not ⊥ s₁
            continue
        if all(x==0 for x in b):                            # ψ≠0
            continue
        wt = sum(1 for x in b if x!=0)
        Wt = ball_weight(q, N, wt, kfloor)                  # Krawtchouk ball weight
        psi_s0 = w**(sum(b[i]*s0[i] for i in range(N)) % q)
        shaw += Wt * psi_s0
        surviving.append((b, wt, Wt))
    # incidence reconstructed = avg + (F/V)*shaw  ... but careful: the ball-Fourier identity
    # gives  I*|V| = |F|*(|S| + Shaw)  with Shaw = Σ_{ψ⊥s₁,ψ≠0} 1̂_S(ψ) ψ(s₀), and
    # 1̂_S(ψ)=Σ_e∈S ψ(e). For the BALL, Σ_e∈S ψ(e) = Σ_{k<=kfloor} K_k(wt ψ). Check it.
    recon = avg + (Fcard/Vcard)*shaw
    if verbose:
        print(f"  q={q} N={N} delta={delta} kfloor={kfloor}: |S|={len(S)} |V|={Vcard}")
        print(f"     EXACT incidence       = {inc}")
        print(f"     avg + (F/V)*Shaw      = {recon.real:.6f}  (imag {recon.imag:.2e})")
        print(f"     match exact? {abs(recon.real-inc)<1e-6 and abs(recon.imag)<1e-6}")
        # the Krawtchouk-weight distribution over surviving frequencies:
        Ws = [abs(Wt) for _,_,Wt in surviving]
        print(f"     #surviving freqs={len(surviving)}  |W| range=[{min(Ws)},{max(Ws)}]")
        print(f"     => the ball-Fourier factor magnitude spans {max(Ws)/max(1,min(Ws)):.3g}x")
        print(f"        (dominated by (q-1)^k ~ q^kfloor = {q**kfloor}; NOT an O(1) reweight)")
    return inc, recon, surviving

print("="*78)
print("C017 PART 2: end-to-end EXACT chain check + Krawtchouk-weight magnitude")
print("="*78)
print("\nVerifying the composed identity I = avg + (F/V)*Krawtchouk-weighted-Gauss-sum exactly")
print("(tiny q for full enumeration; this is the STRUCTURE check of C017's central identity):\n")

# Tiny fully-enumerable instances. (q^N <= ~3^4 .. 5^3 to keep it instant.)
for (q,N,delta) in [(3,3,0.5),(3,4,0.5),(5,3,0.4),(2,4,0.5),(3,3,0.34)]:
    run(q,N,delta)
    print()
