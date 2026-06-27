# Attack #01 — Paley/BGK direct via the smooth 2-power subgroup structure (#464)

**Date:** 2026-06-27 · **Angle:** prove the generalized-Paley near-Ramanujan bound
`M(n) ≤ C·√(n log m)` for the SPECIFIC dyadic subgroup `μ_n`, `n = 2^μ`, exploiting its
2-power self-similarity (NOT a general subgroup).

## Target theorem (what would close the prize from this angle)

For `q = p` prime with `2^μ ∣ p-1`, `G = μ_{2^μ} ⊂ F_p^×`, `η_b = Σ_{y∈G} ψ(by)`, prove
`WorstCaseIncidenceBounded` via the per-frequency sup bound

> `M(2^μ) := max_{b≠0} ‖η_b‖ ≤ C · √(2^μ · log(p/2^μ))` (near-Ramanujan-up-to-√log),

UNCONDITIONALLY using only the dyadic tower structure
`μ_{2^k} = μ_{2^{k-1}} ⊔ ζ_k·μ_{2^{k-1}}`. This discharges input (1); the hyperplane upgrade
(input (2), BCHKS 1.12) would follow by the existing incidence chain.

## The structural lever (genuine, exact)

The smooth subgroup has an **FFT butterfly** decomposition. With `ζ_k` a primitive `2^k`-th
root of unity, `μ_{2^k}` is the disjoint union of `μ_{2^{k-1}}` (the squares) and its coset
`ζ_k·μ_{2^{k-1}}` (the non-squares of order `2^k`). Hence the incomplete Gauss period satisfies
the exact identity

> **butterfly:** `η_k(b) = η_{k-1}(b) + η_{k-1}(b·ζ_k)`.

This is real, exact (errors ~1e-15 in `probe_dyadic_cocycle_recursion.py`), and now formalized
axiom-clean in `Frontier/_Attack01DyadicButterfly.lean` as
`eta_split_of_disjoint_coset` (general two-coset version: `G = H ⊔ c·H ⟹ η_G(b) = η_H(b) + η_H(bc)`).
The L²-orthogonality `Σ_b η_{k-1}(b)·conj(η_{k-1}(bζ_k)) = 0` (disjoint cosets) recovers the
Parseval AVERAGE `√n` for free.

## Proof attempt

Iterate the butterfly. Two natural inductive routes to a per-step `√2` gain:

1. **Transfer-cocycle / Lyapunov.** Express `(η_k(b), η_k(bζ_k))` as a `2×2` linear image of
   `(η_{k-1}(b), η_{k-1}(bζ_k), …)`; then `M_μ ~ 2^{μ·λ}` with `λ` the top Lyapunov exponent of
   the resulting multiplicative cocycle. Square-root cancellation `⟺ λ = ½ log 2`
   (the "non-resonant" value). To PROVE `M(n) = O(√(n log))` it suffices to prove a per-step
   contraction `‖η_k(b)‖ ≤ √2 · M_{k-1}` uniform in `b` (formalized as the named predicate
   `DyadicPerStepContraction`, with the conditional telescoping `eta_le_of_perStepContraction`).

2. **Self-similar energy.** Feed the disjoint-coset split into the additive-energy recursion to
   try `E_r(μ_{2^k}) ≤ 2 · E_r(μ_{2^{k-1}}) + (Wick cross terms)`, aiming at a Wick-like
   `E_r ≤ (2r-1)‼·n^r` by induction on `μ`.

## Adversarial refutation (the obstruction, numerically sharp)

**The per-step contraction is FALSE per-step.** I computed the exact butterfly ratio
`ρ_k = M_k / M_{k-1}` at primes with large `v₂(p-1)` (the ceiling-bad family), all `k`:

| p (v₂) | ρ₂ | ρ₃ | ρ₄ | ρ₅ | ρ₆ | ρ₇ | ρ₈ | ρ₉ |
|---|---|---|---|---|---|---|---|---|
| 193 (6) | 1.95 | 1.54 | 1.24 | 1.06 | 1.19 | — | — | — |
| 257 (8) | 1.96 | 1.55 | 1.51 | 1.28 | 0.85 | 0.84 | 0.12 | — |
| 769 (8) | 1.99 | 1.73 | 1.32 | 1.06 | **1.67** | 1.04 | 1.07 | — |
| 3329 (8)| 2.00 | 1.87 | 1.49 | 1.39 | 1.33 | 1.24 | 1.10 | — |
| 12289 (12)| 2.00 | 1.92 | 1.58 | 1.56 | 1.06 | **1.63** | 1.05 | 1.47 |
| 40961 (13)| 2.00 | 1.97 | 1.61 | 1.60 | 1.55 | 1.26 | 1.05 | 1.48 |

The ratio is `≈ 2` (fully RESONANT, no cancellation) at small `k`, then oscillates wildly in
`[0.12, 2.0]` — it exceeds `√2 ≈ 1.414` at MANY deep steps (769 k=6: 1.67; 12289 k=7: 1.63;
40961 k=4,5,6: ~1.6). So **no uniform per-step bound `ρ_k ≤ c < 2` holds.** The cocycle is
*non-uniformly hyperbolic*: `λ = ½ log 2` only as a long-run average, with large fluctuations.
The recursion (route 1) cannot deliver it — the telescoped product only gives the trivial
`M_μ ≤ 2^μ = n`, formalized as `eta_le_two_mul_of_split` (`‖η_G(b)‖ ≤ 2·M_H`).

**Route 2 (self-similar energy) collapses to the same wall.** The cross terms in
`E_r(μ_{2^k})` are exactly the char-`p` nontrivial-period surplus over the Wick value, i.e. the
DC-subtracted moment of `DCEnergyCorrection`; making them Wick-like for `r ≈ ln q` IS the open
core. The 2-power split does not control the cross terms because the wraparound mod `p`
(the only source of cancellation) is invisible to the char-0 disjoint-coset algebra — same
mechanism as `DCEnergyEssential`. Worse: the floor-bad Linnik least primes
(`97=1+3·32, 193=1+3·64, 257=1+2·128`) make `M/√(n log)` benign (≈1), while the ceiling-bad
high-`v₂` primes (Fermat-like) push `M/√n` up to ~3.9 (40961, k=6) — the worst case is NOT
dyadic-recursion-controllable; the asymptotic depends on the arithmetic of `p`, which the
butterfly is blind to.

**Why 2-power is not special.** Hanson–Petridis / BGK exponents do not improve for `n = 2^μ`:
the BGK bound is `n^{1-o(1)}` for any thin multiplicative subgroup, and the only place the
subgroup index enters is the doubling/energy estimate, which the dyadic algebra leaves at the
trivial `E_2 ≤ n³` (already in `EtaQuarticUncond.rEnergy_two_le_card_cubed`). Stepanov-type
polynomial-method bounds for `2^μ`-th roots (`probe_i008_walsh_dyadic_stepanov`,
`probe_cubic_vacuous_2power`) are vacuous below `q^{1/3}`, far above the prize regime
`n = q^{1/5}`. The antipodal/squaring map is fully formalized (`_AntipodalDyadicSymmetric.lean`)
and gives algebraic rigidity (`1 + ζ^{n/2} = 0`, Lam–Leung) but only in char 0 — the prize prime
makes short `±1`-relations of `2^μ`-th roots vanish mod `p`, which is the wall.

## Verdict

The 2-power structure gives a genuine, exact, clean inductive handle (the butterfly identity,
now an axiom-clean brick) but **NO analytic lever beyond BGK.** The recursion telescopes only to
the trivial `M ≤ n`; the `√2` per-step gain it would need is the square-root-cancellation
conjecture restated as a Lyapunov exponent, and is refuted as a *per-step* statement by the
non-uniform cocycle ratios above. This is an honest reduction to the same Paley/BGK wall, with a
sharp new diagnosis: **the dyadic cocycle is non-uniformly hyperbolic, so the inductive route is
structurally barred** (you cannot get a worst-case bound from an average-only Lyapunov exponent).

- **proofStatus:** conditional-on-named-input (`DyadicPerStepContraction`, which is refuted
  per-step ⟹ the route is dead, not merely open).
- **bypassesPaley:** NO — reduces to the same wall.
- **Lean brick:** `Frontier/_Attack01DyadicButterfly.lean` (axiom-clean: butterfly identity,
  trivial doubling, named per-step obligation + conditional telescope).
- **Probes:** `probe_dyadic_cocycle_recursion.py` (identity), scratch cocycle-ratio computation
  (the refutation table above).
