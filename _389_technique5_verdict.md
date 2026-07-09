# Technique 5 (effective sum-product via the 2-power tower) — VERDICT: does not reach n < p^{1/4}

Attempt to prove B(μ_n) ≤ C·√(n·log(q/n)) for n = 2^a, n < p^{1/4}, via an EFFECTIVE
sum-product exponent specialized to the 2-power tower, beating the ineffective BGK ε.

## What the moment (sum-product amplification) method actually gives — quantified, honest

The only effective handle is the L^{2k}→L^∞ amplification, exact in-tree for k=2
(`subgroup_gaussSum_fourthMoment`: ∑_b|η_b|^{2k} = q·E_k):

    B^{2k} = max_b|η_b|^{2k} ≤ ∑_b|η_b|^{2k} = q·E_k(μ_n).

With E_k at its char-0 (random/Sidon) value E_k ≈ n^{2k}/q + a_k·n^k (a_k ~ k!):
in the prize regime p = n^c (c ≈ 5), the DIAGONAL term q·a_k·n^k dominates n^{2k} for
k < c, giving

    B ≤ (a_k)^{1/2k} · p^{1/2k} · √n,   exponent of n in B = 1/2 + c/(2k).

The energy threshold law (probe-confirmed below) caps the usable k: E_k reaches its char-0
value only for p > n^{(k+3)/2}, i.e. k ≤ 2c−3. Plugging k* = 2c−3:

    best B-exponent = 1/2 + c/(2(2c−3))  →  3/4 as c→∞;  = 0.857 at c=5 (prize).

So even with PERFECT energy knowledge at every moment up to threshold, the moment method
proves only B ≤ n^{0.857} at c=5, and NEVER better than B ≤ n^{3/4+o(1)}. It does not reach
√(n·log) = n^{1/2+o(1)}. The p^{1/2k} factor with k capped at Θ(c) is an intrinsic floor.
This IS a genuine effective power saving (beats trivial n; unconditional given the threshold
law), and unlike the published n^{1−31/2880} it holds for ALL n > p^ε — but the exponent
3/4 is far from the target 1/2.

## The 2-power tower makes it WORSE, not better (the decisive negative)

Technique 5's premise — exploit the 2-adic tower μ_2<μ_4<…<μ_{2^a} and the squaring
2-to-1 descent for extra cancellation — is backwards. Probe (same c=5, p≈n^5):

    n=32 (2-power):  B/√(n ln(p/n))=1.215  E_2/n²=2.91  E_4/n⁴=86.7
    n=27,31,33 (odd): B/√(n ln(p/n))≈0.96–1.07  E_2/n²≈1.97  E_4/n⁴≈21–23

The 2-power subgroup has ~2× the second-moment energy and ~4× the fourth-moment energy of
an odd subgroup of comparable size, and a LARGER character sum. Reason: 2^a even ⟹ −1∈μ_{2^a},
so y↦−y is an involution of the group, forcing antipodal additive collisions a+(−a)=b+(−b)=0.
This is the exact char-0 split already in-tree (E=3n²−3n even vs 2n²−n odd,
`RootsOfUnityAdditiveEnergyExact`). The tower injects ANTIPODAL RIGIDITY that raises energy;
the squaring descent gives no compensating cancellation in the additive (character-sum) world,
because squaring is a multiplicative map and the obstruction is additive.

## Empirical facts confirmed (all probes, FFT over indicator of μ_n)

1. B/√(n·ln(p/n)) ≈ 1 at the prize exponent c=5 (NOT B/√n — the log factor is real and the
   prize statement already includes it). B/√n GROWS like √(log(p/n)).
2. B/n → 1 as p→∞ for fixed n. At c=5, B/n ≈ 0.80–0.91 and climbing (μ_n looks MORE like a
   single phase, not LESS, as the gap p/n widens at fixed n — the deep-moment / L^∞ wall).
3. Energy threshold law: E_k/n^k plateaus at p ≈ n^{(k+3)/2}, exactly as stated. The plateau
   VALUES a_k (E_2/n²→2.625 at n=8, etc.) are the char-0 Sidon-on-circle constants.

## Where the saving would have to come from, and why it doesn't (regime check)

To beat 3/4 one must either (i) push k past the energy threshold 2c−3 — but there E_k blows up
toward n^{2k}/(stuff) and the bound degrades; or (ii) prove a SHARP (not L^{2k}-averaged)
phase-cancellation in the Gauss-sum expansion S(b)=(n/(p−1))∑_{χ∈H^⊥}χ̄(b)τ(χ) — i.e. genuine
square-root cancellation among the (p−1)/n Gauss-sum phases. That is the Weil-on-curves /
absolute-irreducibility content, which the in-tree Stepanov substrate (`StepanovNonVanishing`,
`MomentCollisionTower`) bottoms out at as a single named genus hypothesis Mathlib lacks. The
2-power tower does not supply it; if anything it adds antipodal structure to fight through.

## Net

Technique 5 yields an HONEST conditional/effective result — B ≤ n^{1/2 + c/(2(2c−3))} ≤ n^{3/4+o(1)}
for all n>p^ε, conditional on the energy threshold law (itself Weil-equivalent) — strictly better
shape than ineffective BGK but NOT reaching the prize n^{1/2}·polylog, and provably so: 3/4 is the
ceiling of the L^{2k} method, and the 2-power structure RAISES rather than lowers the energy. No
closure. The wall is the deep-moment/L^∞ gap, untouched by the tower.
