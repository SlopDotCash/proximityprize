/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R297HasseDavenportCosetTriple

/-!
# LANE B2 (#466, r=3 rung, route ii successor): (I3) as a change of variables inside
  the sextic energy — the coset-diagonal split and the two-sided localization of
  `TripleConvEnergyBound` to the off-coset remainder

## The move (math + probe; this session, 2026-07-10)

Inside `tripleConv J d = ∑_{j₁+j₂+j₃=d, jᵢ≠0} J_{j₁}J_{j₂}J_{j₃}` the ordered triples
that are permutations of a FULL coset `{j, j+u, j+2u}` (`u = m/3`) all have index sum
`3j`, and the fiber `{j : 3j = d}` is itself exactly that one coset.  So the
coset-diagonal stratum, as a function of `d`, is

  **(P1)**  `A(d) = 2·∑_{j : 3j = d, d ≠ 0} J_j J_{j+u} J_{j+2u}`
  (6 orderings = 2 × the 3-element fiber; `d = 0` vanishes because the only candidate
  coset is `H ∋ 0`, excluded by the nonzero-index convention), and under HD (I3)

  **(M1)**  `A(d) = 6·κ·J₃(d)` on `3ℤ/m ∖ {0}`, `A = 0` elsewhere —

`tripleConv = A + R` with `A` a pure DEPTH-1 object.  Probe
`scripts/probes/probe_466_r3_mixed_depth_correlation.py`: (P1), (M1) and the energy
split hold EXACTLY in all 18 nondegenerate (q,m,χ) instances (q ≤ 73, m ≤ 36).

**Refutation half (M3):** the candidate mixed-depth orthogonality
`∑_d A(d)·conj(R(d)) = 0` is FALSE in 18/18 instances (normalized correlation
0.08–0.63, cross term of size ≈ m²q³) — the strata are NOT orthogonal, so no exact
Pythagoras; the calibrated corrected form is the ℓ²-triangle two-sided reduction
below.

## What this brick lands (all axiom-clean)

* `cosetDiag` / `offCosetRemainder` — the exact stratum split (definitional:
  `tripleConv_eq_cosetDiag_add_offCosetRemainder`);
* `cosetDiag_collapse` — under `HDCosetTripleCollapse`, `A(d)` is an explicit
  depth-1 object: `2·(fiber d).card·κ·J₃(d)` for `d ≠ 0`;
* `card_fiber_le_card_kernel` — the fiber of `j ↦ 3j` is at most the 3-torsion
  kernel (`= gcd(3,m) ≤ 3`; the `≤ 3` cap enters as the explicit hypothesis `hk₀`,
  decidable per instance);
* `cosetDiag_energy_le` — `∑_d ‖A(d)‖² ≤ 4·K²·k₀²·m·B` (at classical values
  `= 36·m·q³`: the diagonal stratum costs `1/m²` of the Wick budget);
* **`tripleConvEnergyBound_of_offCosetRemainder`** and
  **`offCosetRemainderEnergyBound_of_tripleConvEnergyBound`** — THE TWO-SIDED
  LOCALIZATION: given (I3), the calibrated r=3 open core `TripleConvEnergyBound`
  holds with constant `2C_R + 72` iff-style against the off-coset remainder bound
  (and conversely with `2C + 72`).  The open content of the r=3 rung is EXACTLY
  the off-coset stratum energy `OffCosetRemainderEnergyBound` — a strict
  sub-object of the original input.

Honest scope: `HDCosetTripleCollapse` remains the named classical input (Gauss-sum
product relation, not yet in Mathlib); `OffCosetRemainderEnergyBound` is the new
calibrated open core for the rung, strictly weaker in mass than the original
(probe: the remainder carries essentially all of the energy, ER/wick ≈ 0.1–0.6,
so the localization is structural, not a mass reduction).  CORE OPEN, ON-BGK.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R298MixedDepthCorrelation

open ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R297HasseDavenportCosetTriple

variable {m : ℕ} [NeZero m]

/-- The fiber of the tripling map over `d`. -/
def tripleFiber (m : ℕ) [NeZero m] (d : ZMod m) : Finset (ZMod m) :=
  Finset.univ.filter (fun j => 3 * j = d)

/-- **The coset-diagonal stratum of the triple convolution** (probe identity (P1)):
twice the sum of coset triple products over the tripling fiber, vanishing at `d = 0`
(the nonzero-index convention kills the unique candidate coset `H ∋ 0`). -/
noncomputable def cosetDiag (J : ZMod m → ℂ) (u : ZMod m) (d : ZMod m) : ℂ :=
  if d = 0 then 0 else 2 * ∑ j ∈ tripleFiber m d, cosetTripleProduct J u j

/-- The off-coset remainder: everything in `tripleConv` that HD does not see. -/
noncomputable def offCosetRemainder (J : ZMod m → ℂ) (u : ZMod m) (d : ZMod m) : ℂ :=
  tripleConv J d - cosetDiag J u d

/-- **The exact stratum split** (definitional). -/
theorem tripleConv_eq_cosetDiag_add_offCosetRemainder (J : ZMod m → ℂ) (u : ZMod m)
    (d : ZMod m) :
    tripleConv J d = cosetDiag J u d + offCosetRemainder J u d := by
  unfold offCosetRemainder
  ring

/-- **The collapse of the diagonal stratum** (probe identity (M1) in fiber form):
under HD, `A(d) = 2·(fiber d).card·κ·J₃(d)` for `d ≠ 0` — a pure depth-1 object. -/
theorem cosetDiag_collapse {J J₃ : ZMod m → ℂ} {u : ZMod m} {κ : ℂ}
    (h : HDCosetTripleCollapse J J₃ u κ) {d : ZMod m} (hd : d ≠ 0) :
    cosetDiag J u d = 2 * ((tripleFiber m d).card : ℂ) * (κ * J₃ d) := by
  unfold cosetDiag
  rw [if_neg hd]
  have hpt : ∀ j ∈ tripleFiber m d, cosetTripleProduct J u j = κ * J₃ d := by
    intro j hj
    have h3j : 3 * j = d := (Finset.mem_filter.mp hj).2
    rw [h j, h3j]
  rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The tripling fiber injects into the 3-torsion kernel: `card ≤ k₀` where
`k₀ = card {j : 3j = 0} (= gcd(3,m))`. -/
theorem card_fiber_le_card_kernel (d : ZMod m) :
    (tripleFiber m d).card ≤ (tripleFiber m 0).card := by
  classical
  rcases (tripleFiber m d).eq_empty_or_nonempty with he | ⟨j₀, hj₀⟩
  · rw [he]
    exact Nat.zero_le _
  · have h3j₀ : 3 * j₀ = d := (Finset.mem_filter.mp hj₀).2
    apply Finset.card_le_card_of_injOn (fun j => j - j₀)
    · intro j hj
      have h3j : 3 * j = d := (Finset.mem_filter.mp hj).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [mul_sub, h3j, h3j₀, sub_self]
    · intro a _ b _ hab
      have : a - j₀ = b - j₀ := hab
      linear_combination this

/-- **Energy of the diagonal stratum** at ladder scale: `∑_d ‖A(d)‖² ≤ 4K²k₀²·m·B`.
At the classical values (`K = q`, `B = q`, `k₀ = 3`) this is `36·m·q³` — `1/m²` of
the Wick budget `C·m³·q³`. -/
theorem cosetDiag_energy_le {J J₃ : ZMod m → ℂ} {u : ZMod m} {κ : ℂ} {K B : ℝ}
    {k₀ : ℕ} (h : HDCosetTripleCollapse J J₃ u κ) (hκ : ‖κ‖ ≤ K)
    (hB : ∀ c : ZMod m, ‖J₃ c‖ ^ 2 ≤ B)
    (hk₀ : (tripleFiber m 0).card ≤ k₀) :
    ∑ d : ZMod m, ‖cosetDiag J u d‖ ^ 2
      ≤ 4 * K ^ 2 * (k₀ : ℝ) ^ 2 * (m : ℝ) * B := by
  have hK0 : (0 : ℝ) ≤ K := le_trans (norm_nonneg _) hκ
  have hB0 : (0 : ℝ) ≤ B := le_trans (sq_nonneg _) (hB 0)
  have hpt : ∀ d : ZMod m, ‖cosetDiag J u d‖ ^ 2 ≤ 4 * K ^ 2 * (k₀ : ℝ) ^ 2 * B := by
    intro d
    by_cases hd : d = 0
    · rw [hd]
      unfold cosetDiag
      rw [if_pos rfl, norm_zero]
      have h0 : (0 : ℝ) ≤ 4 * K ^ 2 * (k₀ : ℝ) ^ 2 * B := by positivity
      nlinarith
    · rw [cosetDiag_collapse h hd]
      have hcard : ((tripleFiber m d).card : ℝ) ≤ (k₀ : ℝ) := by
        exact_mod_cast le_trans (card_fiber_le_card_kernel d) hk₀
      have hcard0 : (0 : ℝ) ≤ ((tripleFiber m d).card : ℝ) := Nat.cast_nonneg _
      rw [norm_mul, norm_mul, norm_mul]
      have hnn : ‖(2 : ℂ)‖ = 2 := by norm_num
      have hcastn : ‖((tripleFiber m d).card : ℂ)‖ = ((tripleFiber m d).card : ℝ) := by
        rw [Complex.norm_natCast]
      rw [hnn, hcastn]
      have hexp : (2 * ((tripleFiber m d).card : ℝ) * (‖κ‖ * ‖J₃ d‖)) ^ 2
          = 4 * ((tripleFiber m d).card : ℝ) ^ 2 * (‖κ‖ ^ 2 * ‖J₃ d‖ ^ 2) := by ring
      rw [hexp]
      have h1 : ((tripleFiber m d).card : ℝ) ^ 2 ≤ (k₀ : ℝ) ^ 2 :=
        pow_le_pow_left₀ hcard0 hcard 2
      have h2 : ‖κ‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hκ 2
      have h3 : ‖κ‖ ^ 2 * ‖J₃ d‖ ^ 2 ≤ K ^ 2 * B :=
        mul_le_mul h2 (hB d) (sq_nonneg _) (by positivity)
      calc 4 * ((tripleFiber m d).card : ℝ) ^ 2 * (‖κ‖ ^ 2 * ‖J₃ d‖ ^ 2)
          ≤ 4 * (k₀ : ℝ) ^ 2 * (K ^ 2 * B) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left h1 (by norm_num)
            · exact h3
            · positivity
            · positivity
        _ = 4 * K ^ 2 * (k₀ : ℝ) ^ 2 * B := by ring
  calc ∑ d : ZMod m, ‖cosetDiag J u d‖ ^ 2
      ≤ ∑ _d : ZMod m, 4 * K ^ 2 * (k₀ : ℝ) ^ 2 * B :=
        Finset.sum_le_sum (fun d _ => hpt d)
    _ = ((Finset.univ : Finset (ZMod m)).card : ℝ) * (4 * K ^ 2 * (k₀ : ℝ) ^ 2 * B) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 4 * K ^ 2 * (k₀ : ℝ) ^ 2 * (m : ℝ) * B := by
        simp [ZMod.card]
        ring

/-- **The new calibrated open core for the r=3 rung**: the off-coset remainder energy
at Wick scale — a strict sub-object of `TripleConvEnergyBound` (the diagonal stratum
is removed exactly by HD).  Probe: the remainder carries ~all of the energy
(ER/wick ≈ 0.1–0.6 across instances), so this is a structural localization. -/
def OffCosetRemainderEnergyBound (J : ZMod m → ℂ) (u : ZMod m) (q : ℕ) (C : ℝ) : Prop :=
  ∑ d : ZMod m, ‖offCosetRemainder J u d‖ ^ 2 ≤ C * (m : ℝ) ^ 3 * (q : ℝ) ^ 3

section Localization

variable {J J₃ : ZMod m → ℂ} {u : ZMod m} {κ : ℂ} {q : ℕ}

/-- ℓ²-triangle helper: `‖a‖² ≤ 2‖a−b‖² + 2‖b‖²` shaped sums. -/
private theorem sq_norm_add_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- **FORWARD LOCALIZATION.**  Under HD (with the classical envelopes `‖κ‖ ≤ q`,
`‖J₃‖² ≤ q`, `k₀ ≤ 3`), an off-coset remainder bound with constant `C_R` supplies the
calibrated R23 open core with constant `2·C_R + 72`. -/
theorem tripleConvEnergyBound_of_offCosetRemainder
    (h : HDCosetTripleCollapse J J₃ u κ) (hκ : ‖κ‖ ≤ (q : ℝ))
    (hB : ∀ c : ZMod m, ‖J₃ c‖ ^ 2 ≤ (q : ℝ))
    (hk₀ : (tripleFiber m 0).card ≤ 3)
    {C_R : ℝ} (hR : OffCosetRemainderEnergyBound J u q C_R) :
    TripleConvEnergyBound J q (2 * C_R + 72) := by
  unfold TripleConvEnergyBound
  unfold OffCosetRemainderEnergyBound at hR
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    exact_mod_cast this
  have hq3 : (0 : ℝ) ≤ (q : ℝ) ^ 3 := by positivity
  have hdiag' : ∑ d : ZMod m, ‖cosetDiag J u d‖ ^ 2
      ≤ 36 * (m : ℝ) * (q : ℝ) ^ 3 := by
    calc ∑ d : ZMod m, ‖cosetDiag J u d‖ ^ 2
        ≤ 4 * (q : ℝ) ^ 2 * ((3 : ℕ) : ℝ) ^ 2 * (m : ℝ) * (q : ℝ) :=
          cosetDiag_energy_le h hκ hB hk₀
      _ = 36 * (m : ℝ) * (q : ℝ) ^ 3 := by push_cast; ring
  have hsplit : ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2
      ≤ 2 * (∑ d : ZMod m, ‖cosetDiag J u d‖ ^ 2)
        + 2 * (∑ d : ZMod m, ‖offCosetRemainder J u d‖ ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun d _ => ?_)
    rw [tripleConv_eq_cosetDiag_add_offCosetRemainder J u d]
    exact sq_norm_add_le _ _
  have hm2 : (1 : ℝ) ≤ (m : ℝ) * (m : ℝ) := by nlinarith
  have hm3 : (m : ℝ) ≤ (m : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (le_trans zero_le_one hm1) (sub_nonneg.mpr hm2)]
  have key : (0 : ℝ) ≤ ((m : ℝ) ^ 3 - (m : ℝ)) * (q : ℝ) ^ 3 :=
    mul_nonneg (by linarith) hq3
  nlinarith [hsplit, hdiag', hR, key]

/-- **REVERSE LOCALIZATION.**  Conversely, the R23 open core with constant `C` bounds
the off-coset remainder with constant `2·C + 72`.  Together with the forward
direction: given HD, the r=3 rung and the off-coset stratum bound are the SAME open
problem up to explicit absolute constants. -/
theorem offCosetRemainderEnergyBound_of_tripleConvEnergyBound
    (h : HDCosetTripleCollapse J J₃ u κ) (hκ : ‖κ‖ ≤ (q : ℝ))
    (hB : ∀ c : ZMod m, ‖J₃ c‖ ^ 2 ≤ (q : ℝ))
    (hk₀ : (tripleFiber m 0).card ≤ 3)
    {C : ℝ} (hT : TripleConvEnergyBound J q C) :
    OffCosetRemainderEnergyBound J u q (2 * C + 72) := by
  unfold OffCosetRemainderEnergyBound
  unfold TripleConvEnergyBound at hT
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    exact_mod_cast this
  have hq3 : (0 : ℝ) ≤ (q : ℝ) ^ 3 := by positivity
  have hdiag' : ∑ d : ZMod m, ‖cosetDiag J u d‖ ^ 2
      ≤ 36 * (m : ℝ) * (q : ℝ) ^ 3 := by
    calc ∑ d : ZMod m, ‖cosetDiag J u d‖ ^ 2
        ≤ 4 * (q : ℝ) ^ 2 * ((3 : ℕ) : ℝ) ^ 2 * (m : ℝ) * (q : ℝ) :=
          cosetDiag_energy_le h hκ hB hk₀
      _ = 36 * (m : ℝ) * (q : ℝ) ^ 3 := by push_cast; ring
  have hsplit : ∑ d : ZMod m, ‖offCosetRemainder J u d‖ ^ 2
      ≤ 2 * (∑ d : ZMod m, ‖tripleConv J d‖ ^ 2)
        + 2 * (∑ d : ZMod m, ‖cosetDiag J u d‖ ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun d _ => ?_)
    have hEq : offCosetRemainder J u d = tripleConv J d + (- cosetDiag J u d) := by
      unfold offCosetRemainder
      ring
    rw [hEq]
    have := sq_norm_add_le (tripleConv J d) (- cosetDiag J u d)
    rwa [norm_neg] at this
  have hm2 : (1 : ℝ) ≤ (m : ℝ) * (m : ℝ) := by nlinarith
  have hm3 : (m : ℝ) ≤ (m : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (le_trans zero_le_one hm1) (sub_nonneg.mpr hm2)]
  have key : (0 : ℝ) ≤ ((m : ℝ) ^ 3 - (m : ℝ)) * (q : ℝ) ^ 3 :=
    mul_nonneg (by linarith) hq3
  nlinarith [hsplit, hdiag', hT, key]

end Localization

end ArkLib.ProximityGap.Frontier.R298MixedDepthCorrelation

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R298MixedDepthCorrelation in
#print axioms tripleConv_eq_cosetDiag_add_offCosetRemainder
open ArkLib.ProximityGap.Frontier.R298MixedDepthCorrelation in
#print axioms cosetDiag_collapse
open ArkLib.ProximityGap.Frontier.R298MixedDepthCorrelation in
#print axioms card_fiber_le_card_kernel
open ArkLib.ProximityGap.Frontier.R298MixedDepthCorrelation in
#print axioms cosetDiag_energy_le
open ArkLib.ProximityGap.Frontier.R298MixedDepthCorrelation in
#print axioms tripleConvEnergyBound_of_offCosetRemainder
open ArkLib.ProximityGap.Frontier.R298MixedDepthCorrelation in
#print axioms offCosetRemainderEnergyBound_of_tripleConvEnergyBound
