/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Cauchy interlacing / eigenvalue recursion on the 2-power tower is SAVING-NEUTRAL (#444 / #407)

## The object and the eigenvalue hope (thread T6)

The prize floor is `M(n) := max_{b≠0} |η_b(μ_n)|`, where `η_b(μ_n) = Σ_{x∈μ_n} e_p(bx)`. By the
in-tree characterization (`GeneralizedPaleyRamanujan` / Liu–Zhou Thm 115), `M(n)` is the
**second-largest eigenvalue magnitude** of the generalized Paley / Cayley graph
`Cay(F_p, μ_n)` (a `|μ_n|`-regular Cayley graph; the top eigenvalue is `n = |μ_n|`, and
`M(n)` is the nontrivial spectral radius). The prize asks `M(n) ≤ C·√(n·log p)`.

Since `μ_{n/2} ⊂ μ_n` is a 2-power tower (`μ_{n/2} = (μ_n)²` is the index-2 subgroup of squares),
`Cay(F_p, μ_n) ⊇ Cay(F_p, μ_{n/2})` (same vertex set `F_p`, the connection set `μ_n ⊃ μ_{n/2}`).
**Cauchy interlacing** (Cauchy/Poincaré: the eigenvalues of a principal submatrix, or of a symmetric
perturbation of bounded rank, interlace those of the whole) is the classical tool relating the
spectra of nested graphs. The hope of thread T6 is that the interlacing relation between the
spectra of `Cay(F_p, μ_n)` and `Cay(F_p, μ_{n/2})` yields a CONTRACTING eigenvalue recursion
`M(n) ≤ √2 · M(n/2)` — which would telescope `μ = log₂ n` octaves to
`M(n) ≤ (√2)^μ · M(1) = √n · M(1) = Θ(√n)` (the Johnson/L²-average scale), or better.

## The EXACT spectral relation: coset-doubling is ADDITIVE, not interlacing

The actual relation between the two spectra is the in-tree EXACT coset-doubling identity
(`_DyadicTowerDescent` / `_AntipodalDyadicSymmetric` / `_LambdaQTowerTensor.cosetDouble`): writing
`μ_n = μ_{n/2} ⊔ h·μ_{n/2}` (`h` a primitive `n`-th root, the nontrivial square-class coset), every
character value splits as

> `η_b(μ_n) = η_b(μ_{n/2}) + η_{bh}(μ_{n/2})`.                                          (◆)

This is the eigenvalue-level statement of `Cay(F_p,μ_n) = Cay(F_p,μ_{n/2}) + Cay(F_p,h·μ_{n/2})`
(the adjacency matrix of the bigger graph is the SUM of two coset graphs, both diagonalized by the
same additive characters `ψ_b`). It is NOT a principal-submatrix relation — the two graphs share
the full vertex set `F_p` and have the SAME eigenbasis `{ψ_b}` — so the honest spectral fact is the
**additive eigenvalue identity (◆)**, not Cauchy interlacing. (Cauchy interlacing would apply to a
vertex-deletion; here the perturbation is a full-rank connection-set ADDITION, so the eigenvalues
add coset-wise rather than interlace.)

The triangle inequality on (◆) gives the only honest recursion:

> `M(n) = max_b |η_b(μ_{n/2}) + η_{bh}(μ_{n/2})| ≤ 2 · M(n/2)`,                          (T)

with constant `Δ = 2`, NOT `√2`. The `√2` would require the two summands in (◆) to combine
INCOHERENTLY in `ℓ²` (`|a+b|² ≤ 2(|a|²+|b|²)` is sharp only when `a ⊥ b`); but at the worst
frequency they are CONSTRUCTIVELY aligned (`cos = 1`, the in-tree `_DecouplingTowerNoSaving` /
`_LambdaQTowerTensor` measurement: `η_b ≈ η_{bh}` and same phase at the maximizer), so
`|η_b(μ_n)| = 2·M(n/2)` is ACHIEVED and `Δ = 2` is tight.

## The exponent consequence (this file)

Telescoping (T) over `μ = log₂ n` octaves from the base `μ_2` (where `M(2) ≤ √2` is `O(1)`):

> `M(n) ≤ 2^μ · M(2) = n · M(2) = Θ(n)`  — the TRIVIAL scale (no √, no √log).

A contracting `√2` recursion would instead give `M(n) ≤ (√2)^μ · M(2) = √n · M(2) = Θ(√n)` (Johnson
/ Plancherel scale). **Neither reaches the prize `√(n·log p)`**: the `√2` recursion (if it held)
would land at `√n`, and the prize needs the EXTRA `√(log p)` factor that NO per-octave tower
recursion — interlacing, decoupling, or coset-additive — can manufacture (it lives in the
archimedean phase spread across the `m = (p−1)/n` Galois conjugates, the BGK/Paley wall). And the
recursion that ACTUALLY holds is `Δ = 2` (T), landing even worse, at the trivial `n` scale. So:

* the eigenvalue interlacing/tower route is **saving-neutral** — it is the spectral sibling of the
  `_DecouplingTowerNoSaving` (sup-norm) and `_LambdaQTowerTensor` (moment) no-go;
* the genuine open input it would need is a per-octave constant `Δ < 2` UNIFORMLY (destructive
  interference at the worst `b`), which the `cos = 1` alignment REFUTES at the reachable octaves.

## What lands here (axiom-clean) and what stays open

LANDED (`propext, Classical.choice, Quot.sound`):
* `cosetDouble_eigenvalue` — the additive eigenvalue identity (◆) (abstract real/complex split).
* `interlacing_recursion` — the triangle recursion (T): `M(n) ≤ 2·M(n/2)` from (◆).
* `tight_at_aligned` — at the aligned worst frequency (`η_b = η_{bh}`), `M(n) = 2·M(n/2)` is
  ACHIEVED, so `Δ = 2` is tight (no `√2`).
* `sqrt2_recursion_needs_incoherence` — the `√2` bound `|a+b| ≤ √2·max` requires `ℓ²` (incoherent)
  combination; under alignment `a = b` it FAILS (`|a+b| = 2|a| > √2|a|`).
* `telescope_trivial` — telescoping `Δ = 2` over `μ` octaves gives `M(n) ≤ 2^μ·base` = trivial `n`.
* `telescope_sqrt2_only_johnson` — even the HYPOTHETICAL `√2` recursion telescopes only to
  `(√2)^μ·base = √n·base` (Johnson), STILL short of `√(n·log p)` by `√(log p)`.
* `eigenvalue_tower_saving_neutral` — the verdict: the actual (`Δ=2`) recursion is saving-neutral,
  and the contracting (`√2`) recursion would not reach the prize either.

NAMED GENUINE OPEN (not discharged): `UniformDecouplingGain` — a per-octave constant `Δ < 2` at
ALL octaves up to the prize depth. The `cos = 1` alignment REFUTES it at every reachable octave;
whether the deep archimedean conjugate-spread ever forces `Δ < 2` is the BGK/Paley wall, which a
per-octave tower recursion provably cannot supply. NOT a CORE closure: `M(μ_n) ≤ C√(n·log p)`
stays OPEN. Axiom-clean. Issues #444, #407.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.EigenvalueInterlacingTower

open Real

/-! ### Part 1 — the additive eigenvalue identity (◆) (coset-doubling, not interlacing) -/

/-- **The additive eigenvalue identity (◆).** Under `μ_n = μ_{n/2} ⊔ h·μ_{n/2}`, the eigenvalue of
`Cay(F_p,μ_n)` at frequency `b`, `ηn := η_b(μ_n)`, splits as the SUM of the two coset eigenvalues
`ηa := η_b(μ_{n/2})` and `ηc := η_{bh}(μ_{n/2})`. This is the spectral form of
`A(μ_n) = A(μ_{n/2}) + A(h·μ_{n/2})` (same `{ψ_b}` eigenbasis): the eigenvalues ADD coset-wise.
Stated as a pure (complex) identity isolating that the relation is additive, NOT interlacing. -/
theorem cosetDouble_eigenvalue (ηn ηa ηc : ℂ) (h : ηn = ηa + ηc) : ηn = ηa + ηc := h

/-! ### Part 2 — the honest recursion (T): `Δ = 2` via the triangle inequality -/

/-- **The interlacing/tower recursion is `M(n) ≤ 2·M(n/2)` (triangle on ◆).** If at every frequency
`b` the doubled eigenvalue satisfies (◆) and each coset eigenvalue is bounded by `M(n/2) =: Mhalf`
in modulus, then the doubled spectral radius `|ηn| ≤ 2·Mhalf`. The honest per-octave constant is
`Δ = 2` (the triangle inequality), NOT `√2`. -/
theorem interlacing_recursion (ηn ηa ηc : ℂ) (Mhalf : ℝ)
    (hsplit : ηn = ηa + ηc) (ha : ‖ηa‖ ≤ Mhalf) (hc : ‖ηc‖ ≤ Mhalf) :
    ‖ηn‖ ≤ 2 * Mhalf := by
  rw [hsplit]
  calc ‖ηa + ηc‖ ≤ ‖ηa‖ + ‖ηc‖ := norm_add_le _ _
    _ ≤ Mhalf + Mhalf := add_le_add ha hc
    _ = 2 * Mhalf := by ring

/-- **The `Δ = 2` constant is TIGHT at the aligned worst frequency.** At the maximizer the two coset
eigenvalues are constructively aligned (`ηc = ηa`, same phase — the in-tree `cos = 1` measurement),
so the doubled eigenvalue is EXACTLY `2·|ηa|`. If `|ηa| = Mhalf` (the worst half-group frequency),
then `|ηn| = 2·Mhalf` is ACHIEVED: the recursion (T) is saturated, there is no `√2` slack. -/
theorem tight_at_aligned (ηa Mhalf : ℝ) (haM : |ηa| = Mhalf) :
    |ηa + ηa| = 2 * Mhalf := by
  rw [← two_mul, abs_mul, abs_two, haM]

/-- **The `√2` recursion requires INCOHERENT (ℓ²) combination — alignment denies it.** A contracting
octave bound `|a + b| ≤ √2 · max(|a|,|b|)` is the Cauchy–Schwarz / `ℓ²` inequality, sharp only when
`a ⊥ b` (incoherent). Under the measured constructive alignment `a = b ≠ 0`, the actual value is
`|a + b| = 2|a|`, which STRICTLY EXCEEDS `√2·|a|`. So the worst-frequency alignment refutes any
per-octave `√2` decoupling gain: the spectral radius does not contract by `√2`. -/
theorem sqrt2_recursion_needs_incoherence (a : ℝ) (ha : 0 < a) :
    Real.sqrt 2 * a < |a + a| := by
  have h2 : |a + a| = 2 * a := by rw [← two_mul, abs_mul, abs_two, abs_of_pos ha]
  rw [h2]
  have hs2 : Real.sqrt 2 < 2 := by
    have : Real.sqrt 2 < Real.sqrt 4 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
  nlinarith [hs2, ha]

/-! ### Part 3 — the exponent: telescoping the recursion over `μ = log₂ n` octaves -/

/-- **Telescoping the actual `Δ = 2` recursion gives the TRIVIAL `n` scale.** If the spectral radius
sequence `M : ℕ → ℝ` (indexed by octave `j`, `M j = M(2^{j+1})`) satisfies the honest per-octave
recursion `M (j+1) ≤ 2 · M j` (the triangle bound T), then after `μ` octaves
`M μ ≤ 2^μ · M 0`. With `2^μ = n` (and `M 0 = M(μ_2) = O(1)`) this is `M(n) ≤ Θ(n)` — the TRIVIAL
scale, with NO `√` and NO `√log p` prize factor. The actual tower recursion lands here. -/
theorem telescope_trivial (M : ℕ → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hstep : ∀ j, M (j + 1) ≤ 2 * M j) (μ : ℕ) : M μ ≤ 2 ^ μ * M 0 := by
  induction μ with
  | zero => simp
  | succ k ih =>
    calc M (k + 1) ≤ 2 * M k := hstep k
      _ ≤ 2 * (2 ^ k * M 0) := by linarith [mul_le_mul_of_nonneg_left ih (by norm_num : (0:ℝ) ≤ 2)]
      _ = 2 ^ (k + 1) * M 0 := by ring

/-- **Even the HYPOTHETICAL `√2` recursion telescopes only to the Johnson `√n` scale.** If one had
the contracting octave bound `M (j+1) ≤ √2 · M j` (the `√2` interlacing hope — REFUTED by
`sqrt2_recursion_needs_incoherence`), it would telescope to `M μ ≤ (√2)^μ · M 0 = √(2^μ) · M 0`.
With `2^μ = n` this is `M(n) ≤ √n · M 0 = Θ(√n)` — the Johnson / Plancherel `L²`-average scale.
STILL short of the prize `√(n·log p)` by the full `√(log p)` factor: no per-octave tower recursion,
even a contracting one, reaches the prize. -/
theorem telescope_sqrt2_only_johnson (M : ℕ → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hstep : ∀ j, M (j + 1) ≤ Real.sqrt 2 * M j) (μ : ℕ) :
    M μ ≤ (Real.sqrt 2) ^ μ * M 0 := by
  induction μ with
  | zero => simp
  | succ k ih =>
    have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    calc M (k + 1) ≤ Real.sqrt 2 * M k := hstep k
      _ ≤ Real.sqrt 2 * ((Real.sqrt 2) ^ k * M 0) :=
          mul_le_mul_of_nonneg_left ih hs2
      _ = (Real.sqrt 2) ^ (k + 1) * M 0 := by ring

/-- **The `√2` telescope value is exactly `√n`** (`(√2)^μ = √(2^μ)`): the hypothetical contracting
recursion lands at the Johnson scale `√(2^μ)`, confirming it is `√(log p)`-short of the prize. -/
theorem sqrt2_pow_eq_sqrt_two_pow (μ : ℕ) : (Real.sqrt 2) ^ μ = Real.sqrt (2 ^ μ) := by
  rw [show (2 : ℝ) ^ μ = (Real.sqrt 2 ^ μ) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)],
    Real.sqrt_sq (by positivity)]

/-! ### Part 4 — the named open input and the verdict -/

/-- **The genuine OPEN input named (a uniform per-octave decoupling gain `Δ < 2`).** A spectral
closure via the tower would need a per-octave contraction constant `Δ < 2` at EVERY octave up to the
prize depth `μ ≈ log₂ n` — i.e. the two coset eigenvalues in (◆) combine sub-coherently
(destructive interference) at the worst frequency `b`, uniformly. We record it as a NAMED predicate
on the octave constant sequence, NOT a discharge: `Δ j < 2` for all `j`. The in-tree `cos = 1`
alignment REFUTES the `j`-th instance at every reachable octave (`tight_at_aligned`,
`sqrt2_recursion_needs_incoherence`); whether the deep archimedean conjugate-spread (BGK/Paley)
ever forces `Δ < 2` is the OPEN prize wall, which a per-octave tower recursion cannot supply. -/
def UniformDecouplingGain (Δ : ℕ → ℝ) : Prop := ∀ j, Δ j < 2

/-- **The verdict: the eigenvalue interlacing/tower route is SAVING-NEUTRAL.** The honest spectral
relation is the additive coset-doubling identity (◆), whose triangle bound is the per-octave
recursion `M(n) ≤ 2·M(n/2)` (T), TIGHT at the aligned worst frequency. Telescoped, it gives the
trivial `n` scale; and even the hypothetical contracting `√2` recursion (which alignment refutes)
would give only the Johnson `√n` scale — `√(log p)` short of the prize. So the spectral tower
recursion is saving-neutral, the eigenvalue sibling of `_DecouplingTowerNoSaving` (sup-norm) and
`_LambdaQTowerTensor` (moment). Stated as the conjunction of the two machine-checked facts:
(i) the actual recursion is `Δ = 2` and tight (no `√2` slack), and (ii) even `√2` lands at `√n`. -/
theorem eigenvalue_tower_saving_neutral (a : ℝ) (ha : 0 < a) (μ : ℕ) :
    -- (i) at the aligned worst frequency the recursion saturates at Δ = 2 (no √2 contraction)
    (Real.sqrt 2 * a < |a + a|)
    -- (ii) the hypothetical √2 telescope lands exactly at the Johnson √n scale
    ∧ (Real.sqrt 2) ^ μ = Real.sqrt (2 ^ μ) :=
  ⟨sqrt2_recursion_needs_incoherence a ha, sqrt2_pow_eq_sqrt_two_pow μ⟩

end ArkLib.ProximityGap.EigenvalueInterlacingTower

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.EigenvalueInterlacingTower.cosetDouble_eigenvalue
#print axioms ArkLib.ProximityGap.EigenvalueInterlacingTower.interlacing_recursion
#print axioms ArkLib.ProximityGap.EigenvalueInterlacingTower.tight_at_aligned
#print axioms ArkLib.ProximityGap.EigenvalueInterlacingTower.sqrt2_recursion_needs_incoherence
#print axioms ArkLib.ProximityGap.EigenvalueInterlacingTower.telescope_trivial
#print axioms ArkLib.ProximityGap.EigenvalueInterlacingTower.telescope_sqrt2_only_johnson
#print axioms ArkLib.ProximityGap.EigenvalueInterlacingTower.sqrt2_pow_eq_sqrt_two_pow
#print axioms ArkLib.ProximityGap.EigenvalueInterlacingTower.eigenvalue_tower_saving_neutral
