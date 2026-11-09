/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._R18SigmaEquidistribution
import ArkLib.Research.ProximityGap.Frontier._R19ChiDecomposition
import ArkLib.Research.ProximityGap.Frontier._R19DepletedConstant

/-!
# R19 explicit character-family consumer

This lane wires the explicit `χ`-generated family from `_R19ChiDecomposition` into the R18
sigma-equidistribution consumers.

The payoff is a narrower r = 2 interface for the concrete subgroup `Gχ`: the
`ChiDecompositionOff`, `GaussSumSizeBound`, and `hSig` inputs are all discharged.  The remaining
nontrivial analytic input is the fourth-moment twist bound plus the explicit constant gate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longFile 2700

open Finset
open ArkLib.ProximityGap.ConstantIndexGaussSum
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R16DiagonalExactValue
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R18SigmaEquidistribution
open ArkLib.ProximityGap.Frontier.R19ChiDecomposition
open ArkLib.ProximityGap.Frontier.R19DepletedConstant
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

namespace ArkLib.ProximityGap.Frontier.R19ExplicitCharacterRung

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `MulChar F ℂ` needs classical decidable equality for thinned `Finset` operations. -/
noncomputable local instance localInstance_R19ExplicitCharacterRung_1 : DecidableEq (MulChar F ℂ) := Classical.decEq _

/-- The explicit nontrivial character family has size at most the character order. -/
theorem chiFamily_card_le_order (χ : MulChar F ℂ) :
    ((chiFamily χ).card : ℝ) ≤ (orderOf χ : ℝ) := by
  rw [chiFamily_card]
  exact_mod_cast Nat.sub_le (orderOf χ) 1

/-- For a nontrivial generated family (`orderOf χ ≥ 2`), `chiFamily χ` is nonempty. -/
theorem chiFamily_nonempty_of_two_le_order (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) :
    (chiFamily χ).Nonempty := by
  exact Finset.card_pos.mp (by rw [chiFamily_card]; omega)

/-- The full explicit family is too large for the R18 exact-rung size gate:
`15 * |chiFamily χ|² ≤ orderOf χ` is impossible once `orderOf χ ≥ 2`.

This records an important obstruction: the current `15|X|² ≤ m` exact-rung consumer cannot be
closed by simply taking all nontrivial powers of `χ`; a depleted/thinned family or a stronger
constant route is needed. -/
theorem not_fifteen_chiFamily_card_sq_le_order (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) :
    ¬ 15 * (chiFamily χ).card ^ 2 ≤ orderOf χ := by
  intro h
  rw [chiFamily_card] at h
  have hreal : ((15 * (orderOf χ - 1) ^ 2 : ℕ) : ℝ) ≤ (orderOf χ : ℝ) := by
    exact_mod_cast h
  have hsub : ((orderOf χ - 1 : ℕ) : ℝ) = (orderOf χ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ orderOf χ), Nat.cast_one]
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, hsub] at hreal
  have hmreal : (2 : ℝ) ≤ (orderOf χ : ℝ) := by exact_mod_cast hm
  nlinarith [sq_nonneg ((orderOf χ : ℝ) - 2)]

/-- Real-valued companion to `not_fifteen_chiFamily_card_sq_le_order`. -/
theorem not_fifteen_chiFamily_card_sq_le_order_real (χ : MulChar F ℂ)
    (hm : 2 ≤ orderOf χ) :
    ¬ 15 * (((chiFamily χ).card : ℝ) ^ 2) ≤ (orderOf χ : ℝ) := by
  intro h
  rw [chiFamily_card] at h
  have hsub : ((orderOf χ - 1 : ℕ) : ℝ) = (orderOf χ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ orderOf χ), Nat.cast_one]
  rw [hsub] at h
  have hmreal : (2 : ℝ) ≤ (orderOf χ : ℝ) := by exact_mod_cast hm
  nlinarith [sq_nonneg ((orderOf χ : ℝ) - 2)]

/-! ### Audit obstructions: unsatisfiable hypothesis combinations (CW-B10-01/02/03)

The following lemmas record, axiom-clean, that several hypothesis combinations used by exact-rung
consumers cannot be met.  Consumers whose hypotheses are jointly unsatisfiable have been removed
from this file and replaced by these obstruction lemmas. -/

/-- **Depth-two vs. the R18 regime.**  The depth tie `2 = ⌈log q⌉₊` forces `q ≤ e² < 8`, while the
regime `16·m²·n² ≤ q` with `m ≥ 2`, `n ≥ 1` forces `q ≥ 64`; the two cannot hold together.  Every
`r = 2` consumer that assumed both (`incidence_le_of_*`/`approxB_away_of_*` with
`hdepth : 2 = ⌈log q⌉₊` and `hreg`) was vacuous and has been removed. -/
theorem not_depth_two_of_regime (χ : MulChar F ℂ) (G : Finset F)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ 2 = ⌈Real.log (Fintype.card F : ℝ)⌉₊ := by
  intro hdepth
  have hm' : (2 : ℝ) ≤ (orderOf χ : ℝ) := by exact_mod_cast hm
  have hn' : (1 : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hn
  have hm2 : (4 : ℝ) ≤ (orderOf χ : ℝ) ^ 2 := by nlinarith
  have hn2 : (1 : ℝ) ≤ (G.card : ℝ) ^ 2 := by nlinarith
  have hmn : (4 : ℝ) ≤ (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 := by nlinarith
  have hq64 : (64 : ℝ) ≤ (Fintype.card F : ℝ) := by nlinarith
  have hlog : Real.log (Fintype.card F : ℝ) ≤ 2 := by
    have h := Nat.le_ceil (Real.log (Fintype.card F : ℝ))
    rw [← hdepth] at h
    exact_mod_cast h
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hle : (Fintype.card F : ℝ) ≤ Real.exp 2 := (Real.log_le_iff_le_exp hqpos).mp hlog
  have he : Real.exp 2 < 64 := by
    have h1 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
      have := Real.add_one_le_exp (-(1 / 2) : ℝ)
      linarith
    have h2 : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by
      rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (1 / 2) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2)]
    have h4 : Real.exp 2 = Real.exp (1 / 2) ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h5 : Real.exp (1 / 2) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le h3 4
    rw [h4]
    linarith
  linarith

/-- Real second moment of a nontrivial thin twisted sum over the full offset line:
`∑_t ‖T_χ(t)‖² = |G|·q − |G|²` (from `R17TchiMomentIdentities.sum_shiftedCharSum_mul_conj`). -/
theorem sum_norm_sq_twistedThinSum {χ' : MulChar F ℂ} (hne : χ' ≠ 1) (G : Finset F) :
    ∑ t : F, ‖twistedThinSum χ' G t‖ ^ 2
      = (G.card : ℝ) * (Fintype.card F : ℝ) - (G.card : ℝ) ^ 2 := by
  have h := ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.sum_shiftedCharSum_mul_conj
    hne G
  have hpt : ∀ t : F,
      ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G t
        * (starRingEnd ℂ)
          (ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G t)
        = ((‖twistedThinSum χ' G t‖ ^ 2 : ℝ) : ℂ) := by
    intro t
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_twistedThinSum_eq_shiftedCharSum]
  simp only [hpt] at h
  exact_mod_cast h

/-- Trivial pointwise bound `‖T_χ(t)‖ ≤ |G|`. -/
theorem norm_twistedThinSum_le_card (χ' : MulChar F ℂ) (G : Finset F) (t : F) :
    ‖twistedThinSum χ' G t‖ ≤ (G.card : ℝ) := by
  unfold twistedThinSum
  calc ‖∑ x ∈ G, (starRingEnd ℂ) (χ' (t - x))‖
      ≤ ∑ x ∈ G, ‖(starRingEnd ℂ) (χ' (t - x))‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ G, (1 : ℝ) := Finset.sum_le_sum fun x _ => by
        simpa using
          ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.norm_mulChar_le_one χ' (t - x)
    _ = (G.card : ℝ) := by simp

/-- **Averaging lower bound.**  If a nontrivial thin twisted sum is bounded by `T` at every offset
outside `D`, then `|G|·q − |G|² ≤ |D|·|G|² + q·T²`.  (The RMS scale of `‖T_χ‖` is `√|G|`; in
particular a uniform off-`D` bound with `|D|` small forces `T² ≳ |G|`.) -/
theorem card_mul_card_sub_sq_le_of_offset_bound {χ' : MulChar F ℂ} (hne : χ' ≠ 1)
    (G D : Finset F) {T : ℝ}
    (hT : ∀ s₀ : F, s₀ ∉ D → ‖twistedThinSum χ' G s₀‖ ≤ T) :
    (G.card : ℝ) * (Fintype.card F : ℝ) - (G.card : ℝ) ^ 2
      ≤ (D.card : ℝ) * (G.card : ℝ) ^ 2 + (Fintype.card F : ℝ) * T ^ 2 := by
  classical
  rw [← sum_norm_sq_twistedThinSum hne G,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => t ∈ D)]
  have h1 : ∑ t ∈ Finset.univ.filter (fun t => t ∈ D), ‖twistedThinSum χ' G t‖ ^ 2
      ≤ (D.card : ℝ) * (G.card : ℝ) ^ 2 := by
    calc ∑ t ∈ Finset.univ.filter (fun t => t ∈ D), ‖twistedThinSum χ' G t‖ ^ 2
        ≤ ∑ _t ∈ Finset.univ.filter (fun t => t ∈ D), (G.card : ℝ) ^ 2 :=
          Finset.sum_le_sum fun t _ =>
            pow_le_pow_left₀ (norm_nonneg _) (norm_twistedThinSum_le_card χ' G t) 2
      _ = ((Finset.univ.filter (fun t => t ∈ D)).card : ℝ) * (G.card : ℝ) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (D.card : ℝ) * (G.card : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2)
  have h2 : ∑ t ∈ Finset.univ.filter (fun t => ¬ t ∈ D), ‖twistedThinSum χ' G t‖ ^ 2
      ≤ (Fintype.card F : ℝ) * T ^ 2 := by
    calc ∑ t ∈ Finset.univ.filter (fun t => ¬ t ∈ D), ‖twistedThinSum χ' G t‖ ^ 2
        ≤ ∑ _t ∈ Finset.univ.filter (fun t => ¬ t ∈ D), T ^ 2 :=
          Finset.sum_le_sum fun t ht =>
            pow_le_pow_left₀ (norm_nonneg _) (hT t (Finset.mem_filter.mp ht).2) 2
      _ = ((Finset.univ.filter (fun t => ¬ t ∈ D)).card : ℝ) * T ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card F : ℝ) * T ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Finset.card_le_univ _
  linarith

/-- **Fourth-moment constant lower bound.**  Cauchy–Schwarz on the exact second moment: if
`FourthMomentTwistBound G X Cw` and `X` contains a nontrivial character, then
`(|G|q − |G|²)² ≤ Cw·|G|²·q²`, i.e. `Cw ≥ (1 − |G|/q)²`. -/
theorem sq_sub_le_const_of_fourthMomentTwistBound {G : Finset F} {X : Finset (MulChar F ℂ)}
    {Cw : ℝ} (h4 : FourthMomentTwistBound G X Cw) {χ' : MulChar F ℂ} (hχ' : χ' ∈ X)
    (hne : χ' ≠ 1) :
    ((G.card : ℝ) * (Fintype.card F : ℝ) - (G.card : ℝ) ^ 2) ^ 2
      ≤ Cw * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 2 := by
  have hCS := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset F))
    (f := fun t => ‖twistedThinSum χ' G t‖ ^ 2)
  rw [sum_norm_sq_twistedThinSum hne G, Finset.card_univ] at hCS
  have hpow : ∀ t : F, (‖twistedThinSum χ' G t‖ ^ 2) ^ 2 = ‖twistedThinSum χ' G t‖ ^ 4 :=
    fun t => by ring
  simp only [hpow] at hCS
  have h4' := h4 χ' hχ'
  have hq0 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left h4' hq0
  nlinarith [hmul, hCS]

/-- The normalized full-family gate `32(Cw·|chiFamily χ|⁴+1)/m²/3 ≤ 1` is impossible once
`Cw ≥ 1/2` (in particular for the quartic-Weil constant `Cw = 6`). -/
theorem not_chiFamily_constant_gate_of_half_le (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ)
    {Cw : ℝ} (hCw : 1 / 2 ≤ Cw) :
    ¬ 32 * (Cw * ((chiFamily χ).card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1 := by
  intro h
  rw [chiFamily_card] at h
  have hcast : ((orderOf χ - 1 : ℕ) : ℝ) = (orderOf χ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ orderOf χ), Nat.cast_one]
  rw [hcast, div_div] at h
  set x : ℝ := (orderOf χ : ℝ) with hxdef
  have hx : (2 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hm
  have h' : 32 * (Cw * (x - 1) ^ 4 + 1) ≤ x ^ 2 * 3 := by
    have := (div_le_one (by positivity : (0 : ℝ) < x ^ 2 * 3)).mp h
    linarith
  have hy : (1 : ℝ) ≤ x - 1 := by linarith
  have ht2 : (1 : ℝ) ≤ (x - 1) ^ 2 := by nlinarith
  have ht4 : (x - 1) ^ 2 ≤ (x - 1) ^ 4 := by nlinarith [sq_nonneg ((x - 1) ^ 2 - 1)]
  have hx2 : x ^ 2 ≤ 4 * (x - 1) ^ 2 := by nlinarith
  have hcw4 : (1 / 2) * (x - 1) ^ 4 ≤ Cw * (x - 1) ^ 4 :=
    mul_le_mul_of_nonneg_right hCw (by positivity)
  nlinarith

/-- **The full-family constant gate is unsatisfiable for every admissible `Cw`.**  In the R18
regime, `FourthMomentTwistBound G (chiFamily χ) Cw` forces `Cw ≥ (63/64)² > 1/2` (via
`sq_sub_le_const_of_fourthMomentTwistBound`), and then the gate fails by
`not_chiFamily_constant_gate_of_half_le`.  Hence every full-family `*_of_constant_le_one`
consumer (generic `Cw`, or quartic-Weil `Cw = 6`) was vacuous; those consumers have been removed. -/
theorem not_chiFamily_constant_gate_of_fourthMomentTwistBound (χ : MulChar F ℂ) (G : Finset F)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) {Cw : ℝ}
    (h4 : FourthMomentTwistBound G (chiFamily χ) Cw)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ 32 * (Cw * ((chiFamily χ).card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1 := by
  obtain ⟨χ', hχ'⟩ := chiFamily_nonempty_of_two_le_order χ hm
  have hlow := sq_sub_le_const_of_fourthMomentTwistBound h4 hχ' (chiFamily_ne_one χ hχ')
  apply not_chiFamily_constant_gate_of_half_le χ hm
  set n : ℝ := (G.card : ℝ) with hndef
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hm' : (2 : ℝ) ≤ (orderOf χ : ℝ) := by exact_mod_cast hm
  have hn1 : (1 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn
  have hm2 : (4 : ℝ) ≤ (orderOf χ : ℝ) ^ 2 := by nlinarith
  have hq : 64 * n ≤ q := by nlinarith
  have hA : (63 / 64) * (n * q) ≤ n * q - n ^ 2 := by nlinarith
  have hB : ((63 / 64) * (n * q)) ^ 2 ≤ (n * q - n ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA 2
  by_contra hlt'
  have hlt : Cw < 1 / 2 := lt_of_not_ge hlt'
  have hpos : 0 < n ^ 2 * q ^ 2 := by positivity
  have hmul := mul_lt_mul_of_pos_right hlt hpos
  nlinarith [hB, hlow, hmul]

/-- Numeric helper: `(k − 1)⁴ ≤ 3k²` forces `k ≤ 3`. -/
theorem le_three_of_sub_one_pow_four_le {k : ℕ}
    (h : ((k : ℝ) - 1) ^ 4 ≤ 3 * (k : ℝ) ^ 2) : k ≤ 3 := by
  by_contra hgt
  have hk : 4 ≤ k := by omega
  have hx4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hy9 : (9 : ℝ) ≤ ((k : ℝ) - 1) ^ 2 := by nlinarith
  have hxy : 3 * (k : ℝ) ^ 2 < 9 * ((k : ℝ) - 1) ^ 2 := by nlinarith
  have hy4 : 9 * ((k : ℝ) - 1) ^ 2 ≤ ((k : ℝ) - 1) ^ 4 := by nlinarith
  linarith

/-- **All-omitted `K`-scale endpoints are limited to order `m ≤ 3`.**  Suppose every member of
`chiFamily χ` is bounded by `T` at every offset outside `D`, where `2|G|(|D|+1) ≤ q`, and the
all-omitted budget `|G| + (m−1)√q·T ≤ K` meets the constant-`≤ 1` fourth-scale gate
`4K⁴ ≤ 3C·m²|G|²q²`.  Then the averaging bound forces `T² ≥ |G|/2`, hence `(m−1)⁴ ≤ 3m²`, i.e.
`orderOf χ ≤ 3`. -/
theorem orderOf_le_three_of_all_omitted_K_scale (χ : MulChar F ℂ) (G D : Finset F)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) {T K C : ℝ} (hT0 : 0 ≤ T) (hC : C ≤ 1)
    (hT : ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ chiFamily χ, ‖twistedThinSum χ' G s₀‖ ≤ T)
    (hD : 2 * (G.card : ℝ) * ((D.card : ℝ) + 1) ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T ≤ K)
    (hK :
      4 * K ^ 4
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 2) :
    orderOf χ ≤ 3 := by
  obtain ⟨χ', hχ'⟩ := chiFamily_nonempty_of_two_le_order χ hm
  have havg := card_mul_card_sub_sq_le_of_offset_bound (chiFamily_ne_one χ hχ') G D
    (fun s₀ hs₀ => hT s₀ hs₀ χ' hχ')
  have hcast : ((orderOf χ - 1 : ℕ) : ℝ) = (orderOf χ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ orderOf χ), Nat.cast_one]
  rw [hcast] at hKbound
  set n : ℝ := (G.card : ℝ) with hndef
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set d : ℝ := (D.card : ℝ) with hddef
  set x : ℝ := (orderOf χ : ℝ) with hxdef
  have hx : (2 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hm
  have hn1 : (1 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn
  have hd0 : (0 : ℝ) ≤ d := by rw [hddef]; positivity
  have hq0 : (0 : ℝ) < q := by nlinarith
  -- `T² ≥ n/2`
  have hT2 : n / 2 ≤ T ^ 2 := by
    have h1 : n * q / 2 ≤ q * T ^ 2 := by nlinarith
    have h2 : q * (n / 2) ≤ q * T ^ 2 := by linarith
    exact le_of_mul_le_mul_left h2 hq0
  set s : ℝ := Real.sqrt q with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg q
  have hs2 : s ^ 2 = q := Real.sq_sqrt hq0.le
  have hbase0 : 0 ≤ (x - 1) * s * T := by
    have : (0 : ℝ) ≤ x - 1 := by linarith
    positivity
  have hbaseK : (x - 1) * s * T ≤ K := by linarith
  have hpow : ((x - 1) * s * T) ^ 4 ≤ K ^ 4 := pow_le_pow_left₀ hbase0 hbaseK 4
  have hexp : ((x - 1) * s * T) ^ 4 = (x - 1) ^ 4 * q ^ 2 * (T ^ 2) ^ 2 := by
    rw [← hs2]; ring
  have hT4 : (n / 2) ^ 2 ≤ (T ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hT2 2
  have hy0 : (0 : ℝ) ≤ (x - 1) ^ 4 * q ^ 2 := by positivity
  have hlow : (x - 1) ^ 4 * q ^ 2 * (n / 2) ^ 2 ≤ K ^ 4 := by
    have := mul_le_mul_of_nonneg_left hT4 hy0
    nlinarith [hpow, hexp, this]
  have hC' : 3 * C * x ^ 2 * n ^ 2 * q ^ 2 ≤ 3 * x ^ 2 * n ^ 2 * q ^ 2 := by
    have : 0 ≤ 3 * x ^ 2 * n ^ 2 * q ^ 2 := by positivity
    nlinarith
  have hkey : (x - 1) ^ 4 * (n ^ 2 * q ^ 2) ≤ 3 * x ^ 2 * (n ^ 2 * q ^ 2) := by
    nlinarith [hlow, hK, hC']
  have hnq : 0 < n ^ 2 * q ^ 2 := by positivity
  have hfin : (x - 1) ^ 4 ≤ 3 * x ^ 2 := le_of_mul_le_mul_right hkey hnq
  exact le_three_of_sub_one_pow_four_le hfin

/-! ### Thin subfamilies: what survives restriction -/

/-- Gauss-sum size bounds restrict from the full explicit `chiFamily` to any subfamily. -/
theorem gaussSumSizeBound_chiSubfamily (χ : MulChar F ℂ) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) :
    GaussSumSizeBound Y (fun χ' => gaussSum χ' ψ) := by
  intro χ' hχ'
  exact gaussSumSizeBound_holds χ hψ χ' (hY hχ')

/-- Fourth-moment twist bounds restrict to subfamilies. -/
theorem fourthMomentTwistBound_mono {G : Finset F} {X Y : Finset (MulChar F ℂ)} {Cw : ℝ}
    (hY : Y ⊆ X) (h4 : FourthMomentTwistBound G X Cw) :
    FourthMomentTwistBound G Y Cw := by
  intro χ' hχ'
  exact h4 χ' (hY hχ')

/-- The per-character quartic-Weil input restricts to subfamilies. -/
theorem quarticWeilInput_mono {G : Finset F} {X Y : Finset (MulChar F ℂ)}
    (hY : Y ⊆ X)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G) :
    ∀ χ' ∈ Y,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G := by
  intro χ' hχ'
  exact hW χ' (hY hχ')

/-- The quartic-Weil-to-fourth-moment adapter is compatible with thinning the explicit
`chiFamily`: any subfamily inherits `FourthMomentTwistBound` with constant `6`. -/
theorem fourthMomentTwistBound_chiSubfamily_of_quarticWeilInput
    (χ : MulChar F ℂ) (G : Finset F) {Y : Finset (MulChar F ℂ)}
    (hY : Y ⊆ chiFamily χ)
    (hW :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    FourthMomentTwistBound G Y 6 :=
  ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.fourthMomentTwistBound_of_quarticWeilInput
    G Y (quarticWeilInput_mono hY hW) hn4q

/-- The omitted-character residual for a proposed thinned `chiFamily` decomposition. -/
noncomputable def chiSubfamilyResidual (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G : Finset F)
    (Y : Finset (MulChar F ℂ)) (s₀ : F) : ℂ :=
  ∑ χ' ∈ chiFamily χ \ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀

/-- The omitted-character residual vanishes at every offset outside `D`. -/
def ChiSubfamilyResidualVanishesOff (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (G D : Finset F) (Y : Finset (MulChar F ℂ)) : Prop :=
  ∀ s₀ : F, s₀ ∉ D → chiSubfamilyResidual χ ψ G Y s₀ = 0

/-- The residual vanishes identically for the full explicit family. -/
theorem chiSubfamilyResidual_full_eq_zero
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G : Finset F) (s₀ : F) :
    chiSubfamilyResidual χ ψ G (chiFamily χ) s₀ = 0 := by
  classical
  unfold chiSubfamilyResidual
  rw [Finset.sdiff_self, Finset.sum_empty]

/-- Off-set vanishing base case for the full explicit family. -/
theorem chiSubfamilyResidualVanishesOff_full
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G D : Finset F) :
    ChiSubfamilyResidualVanishesOff χ ψ G D (chiFamily χ) := by
  intro s₀ _hs₀
  exact chiSubfamilyResidual_full_eq_zero χ ψ G s₀

/-- Exact decomposition for a thinned subfamily plus the explicit omitted-character residual.
This is the precise identity behind the thinned-family route: proving `ChiDecompositionOff` for
`Y` alone is equivalent to controlling or canceling this residual. -/
theorem chiSubfamily_decomposition_with_residual
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} (hGD : G ⊆ D) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    {s₀ : F} (hs₀ : s₀ ∉ D) :
    (orderOf χ : ℂ) * incidenceSum ψ G (Gchi χ) s₀
      = -(G.card : ℂ)
        + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
        + chiSubfamilyResidual χ ψ G Y s₀ := by
  classical
  have hfull := chiDecompositionOff_holds χ hψ hGD s₀ hs₀
  unfold chiSubfamilyResidual
  calc (orderOf χ : ℂ) * incidenceSum ψ G (Gchi χ) s₀
      = -(G.card : ℂ)
          + ∑ χ' ∈ chiFamily χ, gaussSum χ' ψ * twistedThinSum χ' G s₀ := hfull
    _ = -(G.card : ℂ)
          + (∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
            + ∑ χ' ∈ chiFamily χ \ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀) := by
        rw [← Finset.sum_sdiff hY]
        ring_nf
    _ = -(G.card : ℂ)
        + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
        + ∑ χ' ∈ chiFamily χ \ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀ := by
        ring

/-- A thinned `chiFamily` has an exact `ChiDecompositionOff` identity iff its omitted-character
residual vanishes off the deleted set.  This is the formal target exposed by the thinning route. -/
theorem chiSubfamily_chiDecompositionOff_iff_residual_vanishes
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} (hGD : G ⊆ D) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) :
    ChiDecompositionOff ψ G (Gchi χ) D Y (fun χ' => gaussSum χ' ψ) (orderOf χ)
      ↔ ChiSubfamilyResidualVanishesOff χ ψ G D Y := by
  constructor
  · intro hdec s₀ hs₀
    have hres := chiSubfamily_decomposition_with_residual χ hψ hGD hY hs₀
    have hthin := hdec s₀ hs₀
    set A : ℂ := -(G.card : ℂ) + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
    have hA : A + chiSubfamilyResidual χ ψ G Y s₀ = A + 0 := by
      calc A + chiSubfamilyResidual χ ψ G Y s₀
          = (orderOf χ : ℂ) * incidenceSum ψ G (Gchi χ) s₀ := by
            exact hres.symm
        _ = A := by
            exact hthin
        _ = A + 0 := by rw [add_zero]
    exact add_left_cancel hA
  · intro hzero s₀ hs₀
    rw [chiSubfamily_decomposition_with_residual χ hψ hGD hY hs₀, hzero s₀ hs₀, add_zero]

/-- The residual framework recovers the full-family decomposition as the zero-residual base
case.  This is a sanity check for the thinned-family formulation. -/
theorem chiDecompositionOff_holds_of_residual_full
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} (hGD : G ⊆ D) :
    ChiDecompositionOff ψ G (Gchi χ) D (chiFamily χ) (fun χ' => gaussSum χ' ψ) (orderOf χ) :=
  (chiSubfamily_chiDecompositionOff_iff_residual_vanishes χ hψ hGD (Subset.rfl)).2
    (chiSubfamilyResidualVanishesOff_full χ ψ G D)

/-- Crude but useful residual norm bound: if every omitted character has
`‖T_χ(s₀)‖ ≤ T`, then the omitted-character residual is at most
`#(chiFamily χ \ Y) * √q * T`.  This turns the thinned-family decomposition residual into a
rate target. -/
theorem norm_chiSubfamilyResidual_le_card_mul
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (Y : Finset (MulChar F ℂ)) (s₀ : F) {T : ℝ}
    (hT : ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T) :
    ‖chiSubfamilyResidual χ ψ G Y s₀‖
      ≤ ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
  classical
  unfold chiSubfamilyResidual
  have hterm : ∀ χ' ∈ chiFamily χ \ Y,
      ‖gaussSum χ' ψ * twistedThinSum χ' G s₀‖
        ≤ Real.sqrt (Fintype.card F : ℝ) * T := by
    intro χ' hχ'
    have hχfam : χ' ∈ chiFamily χ := (Finset.mem_sdiff.mp hχ').1
    rw [norm_mul]
    have hg := gaussSumSizeBound_holds χ hψ χ' hχfam
    have hthin := hT χ' hχ'
    have hgnonneg : 0 ≤ ‖gaussSum χ' ψ‖ := norm_nonneg _
    have htnonneg : 0 ≤ ‖twistedThinSum χ' G s₀‖ := norm_nonneg _
    have hsqrt : 0 ≤ Real.sqrt (Fintype.card F : ℝ) := Real.sqrt_nonneg _
    exact mul_le_mul hg hthin htnonneg hsqrt
  calc ‖∑ χ' ∈ chiFamily χ \ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
      ≤ ∑ χ' ∈ chiFamily χ \ Y, ‖gaussSum χ' ψ * twistedThinSum χ' G s₀‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _χ' ∈ chiFamily χ \ Y, Real.sqrt (Fintype.card F : ℝ) * T := by
        exact Finset.sum_le_sum (fun χ' hχ' => hterm χ' hχ')
    _ = ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

/-- High-moment rate version of the residual bound.  If every omitted character has an away-Wick
bound at rung `r` strong enough to force `‖T_χ(s₀)‖ ≤ T`, then the residual obeys the same
cardinality times `√q·T` estimate. -/
theorem norm_chiSubfamilyResidual_le_card_mul_of_shifted_awayWickAt_rate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) (Y : Finset (MulChar F ℂ)) {s₀ : F} (hs₀ : s₀ ∉ D)
    (r : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hr : 1 ≤ r)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r)) :
    ‖chiSubfamilyResidual χ ψ G Y s₀‖
      ≤ ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
  exact norm_chiSubfamilyResidual_le_card_mul χ hψ G Y s₀
    (fun χ' hχ' =>
      twistedThinSum_le_of_shifted_awayWickAt_rate χ' G D r hT0 hr (hwick χ' hχ') hrate hs₀)

/-- Pointwise incidence bound from a thinned character family plus a residual norm cap.  This is
the approximate analogue of the R17 pointwise bound: the thin contribution costs
`|Y|√q·T`, while omitted characters enter only through `R`. -/
theorem incidenceSum_le_of_chiSubfamily_residual_bound
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {s₀ : F} (hs₀ : s₀ ∉ D) {T R : ℝ}
    (hT : ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T)
    (hR : ‖chiSubfamilyResidual χ ψ G Y s₀‖ ≤ R) :
    (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ (G.card : ℝ) + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T + R := by
  classical
  have hdecs := chiSubfamily_decomposition_with_residual χ hψ hGD hY hs₀
  have hnorm : (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ (G.card : ℝ)
        + ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
        + ‖chiSubfamilyResidual χ ψ G Y s₀‖ := by
    have heq : ‖(orderOf χ : ℂ) * incidenceSum ψ G (Gchi χ) s₀‖
        = ‖-(G.card : ℂ)
            + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
            + chiSubfamilyResidual χ ψ G Y s₀‖ := by rw [hdecs]
    calc (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖
        = ‖(orderOf χ : ℂ) * incidenceSum ψ G (Gchi χ) s₀‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ = ‖-(G.card : ℂ)
            + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
            + chiSubfamilyResidual χ ψ G Y s₀‖ := heq
      _ ≤ ‖-(G.card : ℂ)‖
            + ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
            + ‖chiSubfamilyResidual χ ψ G Y s₀‖ := by
          calc ‖-(G.card : ℂ)
                + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
                + chiSubfamilyResidual χ ψ G Y s₀‖
              ≤ ‖-(G.card : ℂ)
                    + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
                  + ‖chiSubfamilyResidual χ ψ G Y s₀‖ := norm_add_le _ _
            _ ≤ (‖-(G.card : ℂ)‖
                    + ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖)
                  + ‖chiSubfamilyResidual χ ψ G Y s₀‖ := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_right
                    (norm_add_le (-(G.card : ℂ))
                      (∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀))
                    ‖chiSubfamilyResidual χ ψ G Y s₀‖
            _ = ‖-(G.card : ℂ)‖
                    + ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
                    + ‖chiSubfamilyResidual χ ψ G Y s₀‖ := by ring
      _ = (G.card : ℝ)
            + ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
            + ‖chiSubfamilyResidual χ ψ G Y s₀‖ := by
          rw [norm_neg, Complex.norm_natCast]
  have hsum : ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
      ≤ (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
    calc ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
        ≤ ∑ χ' ∈ Y, ‖gaussSum χ' ψ * twistedThinSum χ' G s₀‖ := norm_sum_le Y _
      _ ≤ ∑ _χ' ∈ Y, Real.sqrt (Fintype.card F : ℝ) * T := by
          refine Finset.sum_le_sum fun χ' hχ' => ?_
          rw [norm_mul]
          have hg := gaussSumSizeBound_holds χ hψ χ' (hY hχ')
          have htw := hT χ' hχ'
          exact mul_le_mul hg htw (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
  linarith

/-- Pointwise incidence bound with the residual cap discharged by direct pointwise bounds on the
kept and omitted character sums.  This is the practical approximate-thinning estimate:
kept characters cost `|Y|√q·T_in`, omitted characters cost
`|chiFamily χ \ Y|√q·T_out`. -/
theorem incidenceSum_le_of_chiSubfamily_pointwise_bounds
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {s₀ : F} (hs₀ : s₀ ∉ D) {T_in T_out : ℝ}
    (hTin : ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout : ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out) :
    (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out := by
  exact incidenceSum_le_of_chiSubfamily_residual_bound χ hψ G D hGD hY hs₀ hTin
    (norm_chiSubfamilyResidual_le_card_mul χ hψ G Y s₀ hTout)

/-- High-moment-rate version of
`incidenceSum_le_of_chiSubfamily_pointwise_bounds`, with the omitted-character bound supplied by
shifted away-Wick hypotheses. -/
theorem incidenceSum_le_of_chiSubfamily_shifted_omitted_rate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {s₀ : F} (hs₀ : s₀ ∉ D) (r : ℕ) {T_in T_out : ℝ}
    (hTout0 : 0 ≤ T_out) (hr : 1 ≤ r)
    (hTin : ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r)) :
    (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out := by
  exact incidenceSum_le_of_chiSubfamily_residual_bound χ hψ G D hGD hY hs₀ hTin
    (norm_chiSubfamilyResidual_le_card_mul_of_shifted_awayWickAt_rate χ hψ G D Y hs₀
      r hTout0 hr hwick hrate)

/-- A crude pointwise-to-away-fourth bridge for approximate decompositions.  If every surviving
offset obeys `m‖I(s₀)‖ ≤ B`, then the diagonal-subtracted fourth moment obeys
`m⁴ S₂^D ≤ |F \ D| B⁴`.  This is intentionally elementary: it exposes exactly what a
pointwise residual estimate buys before any Wick-scale averaging is recovered. -/
theorem incidenceMomentAway_two_mul_le_of_pointwise_order_bound
    (ψ : AddChar F ℂ) (χ : MulChar F ℂ) (G D : Finset F) {B : ℝ}
    (hpoint :
      ∀ s₀ : F, s₀ ∉ D →
        (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖ ≤ B) :
    (orderOf χ : ℝ) ^ 4 * incidenceMomentAway ψ G (Gchi χ) D 2
      ≤ (((Finset.univ : Finset F) \ D).card : ℝ) * B ^ 4 := by
  classical
  unfold incidenceMomentAway
  rw [mul_sum]
  calc ∑ s₀ ∈ (Finset.univ : Finset F) \ D,
        (orderOf χ : ℝ) ^ 4 * ‖incidenceSum ψ G (Gchi χ) s₀‖ ^ (2 * 2)
      ≤ ∑ _s₀ ∈ (Finset.univ : Finset F) \ D, B ^ 4 := by
        refine Finset.sum_le_sum fun s₀ hs₀ => ?_
        have hsD : s₀ ∉ D := (Finset.mem_sdiff.mp hs₀).2
        have hpt := hpoint s₀ hsD
        have hnonneg :
            0 ≤ (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖ := by positivity
        have hpow :
            ((orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖) ^ 4 ≤ B ^ 4 :=
          pow_le_pow_left₀ hnonneg hpt 4
        calc (orderOf χ : ℝ) ^ 4 * ‖incidenceSum ψ G (Gchi χ) s₀‖ ^ 4
            = ((orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖) ^ 4 := by ring
          _ ≤ B ^ 4 := hpow
    _ = (((Finset.univ : Finset F) \ D).card : ℝ) * B ^ 4 := by
        simp only [Finset.sum_const, nsmul_eq_mul]

/-- Away-fourth-moment consequence of uniform thin-family pointwise bounds.  This is the
fully composed crude residual route: prove pointwise bounds for the kept characters and the
omitted residual characters on every surviving offset, and get an explicit fourth-moment bound
for the incidence sum. -/
theorem incidenceMomentAway_two_mul_le_of_chiSubfamily_pointwise_bounds
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {T_in T_out : ℝ}
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout :
      ∀ s₀ : F, s₀ ∉ D →
        ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out) :
    (orderOf χ : ℝ) ^ 4 * incidenceMomentAway ψ G (Gchi χ) D 2
      ≤ (((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4 := by
  exact incidenceMomentAway_two_mul_le_of_pointwise_order_bound ψ χ G D
    (fun s₀ hs₀ =>
      incidenceSum_le_of_chiSubfamily_pointwise_bounds χ hψ G D hGD hY hs₀
        (hTin s₀ hs₀) (hTout s₀ hs₀))

/-- Away-fourth-moment consequence when the omitted-character side is supplied by shifted
away-Wick rate hypotheses.  The remaining pointwise input is only on the kept subfamily `Y`. -/
theorem incidenceMomentAway_two_mul_le_of_chiSubfamily_shifted_omitted_rate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    (r : ℕ) {T_in T_out : ℝ} (hTout0 : 0 ≤ T_out) (hr : 1 ≤ r)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r)) :
    (orderOf χ : ℝ) ^ 4 * incidenceMomentAway ψ G (Gchi χ) D 2
      ≤ (((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4 := by
  exact incidenceMomentAway_two_mul_le_of_pointwise_order_bound ψ χ G D
    (fun s₀ hs₀ =>
      incidenceSum_le_of_chiSubfamily_shifted_omitted_rate χ hψ G D hGD hY hs₀ r
        hTout0 hr (hTin s₀ hs₀) hwick hrate)

/-- Constant-rung bridge from a pointwise order-scaled incidence bound.  The only numerical
content is the explicit gate comparing the crude pointwise fourth-moment total to the desired
R16 constant-`C` Wick scale. -/
theorem wickAwayAtWithConstant_two_of_pointwise_order_bound
    (ψ : AddChar F ℂ) (χ : MulChar F ℂ) (G D : Finset F) {B C : ℝ}
    (hm : 1 ≤ orderOf χ)
    (hpoint :
      ∀ s₀ : F, s₀ ∉ D →
        (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖ ≤ B)
    (hgate :
      (((Finset.univ : Finset F) \ D).card : ℝ) * B ^ 4
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2))) :
    WickAwayAtWithConstant ψ G (Gchi χ) D 2 C := by
  unfold WickAwayAtWithConstant
  have hmreal : (0 : ℝ) < (orderOf χ : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp hm
  have hm4 : (0 : ℝ) < (orderOf χ : ℝ) ^ 4 := by positivity
  have hmoment := incidenceMomentAway_two_mul_le_of_pointwise_order_bound ψ χ G D hpoint
  have hmul :
      (orderOf χ : ℝ) ^ 4 * incidenceMomentAway ψ G (Gchi χ) D 2
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2)) :=
    le_trans hmoment hgate
  exact le_of_mul_le_mul_left hmul hm4

/-- Constant-rung bridge with the pointwise bound supplied by uniform thin-family estimates. -/
theorem wickAwayAtWithConstant_two_of_chiSubfamily_pointwise_bounds
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {T_in T_out C : ℝ} (hm : 1 ≤ orderOf χ)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout :
      ∀ s₀ : F, s₀ ∉ D →
        ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out)
    (hgate :
      (((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2))) :
    WickAwayAtWithConstant ψ G (Gchi χ) D 2 C := by
  exact wickAwayAtWithConstant_two_of_pointwise_order_bound ψ χ G D hm
    (fun s₀ hs₀ =>
      incidenceSum_le_of_chiSubfamily_pointwise_bounds χ hψ G D hGD hY hs₀
        (hTin s₀ hs₀) (hTout s₀ hs₀))
    hgate

/-- Constant-rung bridge for the residual route with omitted characters controlled by shifted
away-Wick rate hypotheses. -/
theorem wickAwayAtWithConstant_two_of_chiSubfamily_shifted_omitted_rate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    (r : ℕ) {T_in T_out C : ℝ} (hm : 1 ≤ orderOf χ)
    (hTout0 : 0 ≤ T_out) (hr : 1 ≤ r)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r))
    (hgate :
      (((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2))) :
    WickAwayAtWithConstant ψ G (Gchi χ) D 2 C := by
  exact wickAwayAtWithConstant_two_of_pointwise_order_bound ψ χ G D hm
    (fun s₀ hs₀ =>
      incidenceSum_le_of_chiSubfamily_shifted_omitted_rate χ hψ G D hGD hY hs₀ r
        hTout0 hr (hTin s₀ hs₀) hwick hrate)
    hgate

/-- Σ-lower-bound simplification of the constant-rung numeric gate.  If
`nq ≤ 2mΣ`, then the R16 target
`m⁴·C·q·3·Σ²` is implied by the cleaner scale gate
`4·L ≤ 3·C·m²·n²·q³`. -/
theorem pointwise_order_gate_of_hSig
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G D : Finset F) {B C : ℝ}
    (hm : 1 ≤ orderOf χ) (hC0 : 0 ≤ C)
    (hSig :
      (G.card : ℝ) * (Fintype.card F : ℝ)
        ≤ 2 * (orderOf χ : ℝ) * ∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2)
    (hscale :
      4 * ((((Finset.univ : Finset F) \ D).card : ℝ) * B ^ 4)
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
          * (Fintype.card F : ℝ) ^ 3) :
    (((Finset.univ : Finset F) \ D).card : ℝ) * B ^ 4
      ≤ (orderOf χ : ℝ) ^ 4
        * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
          * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2)) := by
  classical
  set L : ℝ := (((Finset.univ : Finset F) \ D).card : ℝ) * B ^ 4 with hLdef
  set m : ℝ := (orderOf χ : ℝ) with hmdef
  set n : ℝ := (G.card : ℝ) with hndef
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set Sig : ℝ := ∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2 with hSigdef
  have hm0 : 0 < m := by
    rw [hmdef]
    exact_mod_cast Nat.succ_le_iff.mp hm
  have hn0 : 0 ≤ n := by rw [hndef]; positivity
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hSig0 : 0 ≤ Sig := by rw [hSigdef]; positivity
  have hSig' : n * q ≤ 2 * m * Sig := by
    simpa [hndef, hqdef, hmdef, hSigdef] using hSig
  have hSig2 : n ^ 2 * q ^ 2 ≤ 4 * m ^ 2 * Sig ^ 2 := by
    have hlhs0 : 0 ≤ n * q := mul_nonneg hn0 hq0
    have hsq : (n * q) ^ 2 ≤ (2 * m * Sig) ^ 2 :=
      pow_le_pow_left₀ hlhs0 hSig' 2
    nlinarith
  have htarget4 :
      4 * (m ^ 4 * (C * (q * (Nat.doubleFactorial (2 * 2 - 1) : ℝ) * Sig ^ 2)))
        = 12 * C * m ^ 4 * q * Sig ^ 2 := by norm_num; ring
  have hmiddle :
      3 * C * m ^ 2 * n ^ 2 * q ^ 3
        ≤ 12 * C * m ^ 4 * q * Sig ^ 2 := by
    have hcoef : 0 ≤ 3 * C * m ^ 2 * q := by positivity
    have hmul :
        (3 * C * m ^ 2 * q) * (n ^ 2 * q ^ 2)
          ≤ (3 * C * m ^ 2 * q) * (4 * m ^ 2 * Sig ^ 2) :=
      mul_le_mul_of_nonneg_left hSig2 hcoef
    nlinarith [hmul, hcoef]
  have hscaled : 4 * L ≤ 4 * (m ^ 4 * (C * (q * (Nat.doubleFactorial (2 * 2 - 1) : ℝ) * Sig ^ 2))) := by
    have hs : 4 * L ≤ 3 * C * m ^ 2 * n ^ 2 * q ^ 3 := by
      simpa [L, m, n, q] using hscale
    nlinarith [hs, hmiddle, htarget4]
  have hfour : (0 : ℝ) < 4 := by norm_num
  have hfinal : L ≤ m ^ 4 * (C * (q * (Nat.doubleFactorial (2 * 2 - 1) : ℝ) * Sig ^ 2)) :=
    le_of_mul_le_mul_left hscaled hfour
  simpa [L, m, q, Sig] using hfinal

/-- Cardinality simplification for the scale gate.  Since `|F \ D| ≤ q`, it is enough to prove
the pointwise-order bound at the scale
`4·B⁴ ≤ 3·C·m²·n²·q²`. -/
theorem scale_gate_of_pointwise_fourth_scale
    (χ : MulChar F ℂ) (G D : Finset F) {B C : ℝ}
    (hB :
      4 * B ^ 4
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
          * (Fintype.card F : ℝ) ^ 2) :
    4 * ((((Finset.univ : Finset F) \ D).card : ℝ) * B ^ 4)
      ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
        * (Fintype.card F : ℝ) ^ 3 := by
  have hcard : (((Finset.univ : Finset F) \ D).card : ℝ) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast Finset.card_le_univ ((Finset.univ : Finset F) \ D)
  have hpow0 : 0 ≤ B ^ 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcard hpow0
  nlinarith [hB, hmul]

/-- If a pointwise-order budget `B` is dominated by a cleaner budget `K`, it is enough to prove
the fourth-scale inequality for `K`. -/
theorem pointwise_fourth_scale_of_le
    (χ : MulChar F ℂ) (G : Finset F) {B K C : ℝ} (hB0 : 0 ≤ B) (hBK : B ≤ K)
    (hK :
      4 * K ^ 4
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
          * (Fintype.card F : ℝ) ^ 2) :
    4 * B ^ 4
      ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
        * (Fintype.card F : ℝ) ^ 2 := by
  have hpow : B ^ 4 ≤ K ^ 4 := pow_le_pow_left₀ hB0 hBK 4
  nlinarith

/-- Dimensionless version of the `K` fourth-scale gate.  If the clean budget is at most
`A·|G|·√q`, it suffices to prove `4A⁴|G|² ≤ 3Cm²`. -/
theorem pointwise_fourth_scale_of_le_const_mul_card_sqrt
    (χ : MulChar F ℂ) (G : Finset F) {A K C : ℝ} (hK0 : 0 ≤ K)
    (hKbound : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hA :
      4 * A ^ 4 * (G.card : ℝ) ^ 2
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2) :
    4 * K ^ 4
      ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
        * (Fintype.card F : ℝ) ^ 2 := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set n : ℝ := (G.card : ℝ) with hndef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hpow : K ^ 4 ≤ (A * n * Real.sqrt q) ^ 4 := by
    simpa [hndef, hqdef] using pow_le_pow_left₀ hK0 hKbound 4
  have hsqrt4 : (Real.sqrt q) ^ 4 = q ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hq0]
  have hexpand : 4 * (A * n * Real.sqrt q) ^ 4 = 4 * A ^ 4 * n ^ 4 * q ^ 2 := by
    rw [mul_pow, mul_pow, hsqrt4]
    ring
  have hmain :
      4 * (A * n * Real.sqrt q) ^ 4
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * n ^ 2 * q ^ 2 := by
    have hfac0 : 0 ≤ n ^ 2 * q ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hA hfac0
    nlinarith [hmul, hexpand]
  have hstep : 4 * K ^ 4 ≤ 4 * (A * n * Real.sqrt q) ^ 4 := by nlinarith
  have hfinal : 4 * K ^ 4 ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * n ^ 2 * q ^ 2 :=
    le_trans hstep hmain
  simpa [hndef, hqdef] using hfinal

/-- The exact-constant (`C = 1`) dimensionless reducer. -/
theorem pointwise_fourth_scale_of_le_const_mul_card_sqrt_one
    (χ : MulChar F ℂ) (G : Finset F) {A K : ℝ} (hK0 : 0 ≤ K)
    (hKbound : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hA :
      4 * A ^ 4 * (G.card : ℝ) ^ 2
        ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    4 * K ^ 4
      ≤ 3 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
        * (Fintype.card F : ℝ) ^ 2 := by
  simpa using
    (pointwise_fourth_scale_of_le_const_mul_card_sqrt (χ := χ) (G := G) (C := 1)
      hK0 hKbound (by simpa using hA))

/-- If the dimensionless budget constant is at most `1`, the exact-constant scale gate follows
from `4|G|² ≤ 3m²`. -/
theorem pointwise_fourth_scale_one_of_A_le_one
    (χ : MulChar F ℂ) (G : Finset F) {A K : ℝ} (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hKbound : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hsize : 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    4 * K ^ 4
      ≤ 3 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
        * (Fintype.card F : ℝ) ^ 2 := by
  have hA4 : A ^ 4 ≤ 1 := by
    have hpow := pow_le_pow_left₀ hA0 hA1 4
    simpa using hpow
  have hdim : 4 * A ^ 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2 := by
    have hcoef0 : 0 ≤ 4 * (G.card : ℝ) ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hA4 hcoef0
    nlinarith
  exact pointwise_fourth_scale_of_le_const_mul_card_sqrt_one χ G hK0 hKbound hdim

/-- Raw fourth-moment endpoint from an abstract pointwise order-scaled incidence bound and the
explicit constant-`≤ 1` numerical gate. -/
theorem rawFourthMomentWithDiagonal_of_pointwise_order_bound_gate
    (ψ : AddChar F ℂ) (χ : MulChar F ℂ) (G D : Finset F) {B C : ℝ}
    (hm : 1 ≤ orderOf χ) (hC : C ≤ 1)
    (hpoint :
      ∀ s₀ : F, s₀ ∉ D →
        (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖ ≤ B)
    (hgate :
      (((Finset.univ : Finset F) \ D).card : ℝ) * B ^ 4
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2))) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_wickAwayAtWithConstant_two_le_one G (Gchi χ) D hC
    (wickAwayAtWithConstant_two_of_pointwise_order_bound ψ χ G D hm hpoint hgate)

/-- Raw fourth-moment endpoint from uniform thin-family pointwise bounds and the explicit
constant-`≤ 1` numerical gate. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_gate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {T_in T_out C : ℝ} (hm : 1 ≤ orderOf χ) (hC : C ≤ 1)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout :
      ∀ s₀ : F, s₀ ∉ D →
        ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out)
    (hgate :
      (((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2))) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_wickAwayAtWithConstant_two_le_one G (Gchi χ) D hC
    (wickAwayAtWithConstant_two_of_chiSubfamily_pointwise_bounds χ hψ G D hGD hY
      hm hTin hTout hgate)

/-! ### Applicability limits of the pointwise-residual endpoints (audit CW-B10-03)

The endpoints below are correct implications, but their hypotheses are very restrictive:

* **Averaging.**  `sum_norm_sq_twistedThinSum` gives `∑_s ‖T_χ'(s)‖² = |G|q − |G|²` and
  `‖T_χ'‖ ≤ |G|`, so a uniform off-`D` bound `T` with `|D|` small forces `T² ≳ |G|`
  (`card_mul_card_sub_sq_le_of_offset_bound`).  Consequently the `K`/fourth-scale/`A`-scale gates
  `4K⁴ ≤ 3C·m²|G|²q²` with `C ≤ 1` can only be met for order `m ≤ 3` when
  `2|G|(|D|+1) ≤ q`; this is proved for the all-omitted budget in
  `orderOf_le_three_of_all_omitted_K_scale`.
* **`A ≤ 1` endpoints.**  For `s ∉ D` (so `s ∉ G`) and `|G| < m`, some coset of `ker χ` misses
  `G − s`, and orthogonality gives `∑_{χ' ∈ chiFamily χ} ‖T_χ'(s)‖ ≥ |G|`; then every budget
  `K ≥ |G| + √q·∑ T` exceeds `|G|√q ≥ A|G|√q`.  So the `A ≤ 1` endpoints (with `4|G|² ≤ 3m²`) are
  unsatisfiable whenever `D ≠ univ`.  This argument is recorded here as documentation; it is not
  yet a Lean theorem.

No positive instance of these endpoints at order `m ≥ 4` is known. -/

/-- Regime-form raw fourth-moment endpoint for direct kept/omitted pointwise bounds.  This is
the non-shifted companion to
`rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_scale_gate`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_scale_gate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {T_in T_out C : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hC0 : 0 ≤ C) (hC : C ≤ 1)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout :
      ∀ s₀ : F, s₀ ∉ D →
        ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hscale :
      4 * ((((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4)
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
          * (Fintype.card F : ℝ) ^ 3) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_gate χ hψ G D hGD hY
    (le_trans (by norm_num) hm) hC hTin hTout
    (pointwise_order_gate_of_hSig χ ψ G D (le_trans (by norm_num) hm) hC0
      (hSig_of_regime hψ G hm hn hreg) hscale)

/-- Regime-form raw fourth-moment endpoint with the deleted-offset cardinality also discharged
by `|F \ D| ≤ q`.  The remaining numeric target is the per-offset scale
`4B⁴ ≤ 3Cm²n²q²`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_fourth_scale
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {T_in T_out C : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hC0 : 0 ≤ C) (hC : C ≤ 1)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout :
      ∀ s₀ : F, s₀ ∉ D →
        ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hB :
      4 * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
          * (Fintype.card F : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_scale_gate χ hψ G D hGD hY
    hm hn hC0 hC hTin hTout hreg
    (scale_gate_of_pointwise_fourth_scale χ G D hB)

/-- `K`-budget version of
`rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_fourth_scale`: it is enough to
upper-bound the concrete residual budget by a cleaner nonnegative `K`, then prove the fourth-scale
inequality for `K`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_K_scale
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {T_in T_out C K : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hC0 : 0 ≤ C) (hC : C ≤ 1)
    (hTin0 : 0 ≤ T_in) (hTout0 : 0 ≤ T_out)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout :
      ∀ s₀ : F, s₀ ∉ D →
        ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ K)
    (hK :
      4 * K ^ 4
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
          * (Fintype.card F : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D := by
  have hB0 :
      0 ≤ (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out := by
    positivity
  exact rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_fourth_scale χ hψ G D
    hGD hY hm hn hC0 hC hTin hTout hreg
    (pointwise_fourth_scale_of_le χ G hB0 hKbound hK)

/-- Dimensionless `A`-scale version of the direct pointwise residual endpoint.  The concrete
budget is first bounded by `K`, then by `A·|G|·√q`; the remaining scale obligation is
`4A⁴|G|² ≤ 3Cm²`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_A_scale
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {T_in T_out C K A : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hC0 : 0 ≤ C) (hC : C ≤ 1)
    (hTin0 : 0 ≤ T_in) (hTout0 : 0 ≤ T_out) (hK0 : 0 ≤ K)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout :
      ∀ s₀ : F, s₀ ∉ D →
        ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ K)
    (hKdim : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hA :
      4 * A ^ 4 * (G.card : ℝ) ^ 2
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_K_scale χ hψ G D hGD hY
    hm hn hC0 hC hTin0 hTout0 hTin hTout hreg hKbound
    (pointwise_fourth_scale_of_le_const_mul_card_sqrt χ G hK0 hKdim hA)

/-- Exact-constant (`C = 1`) direct pointwise endpoint in dimensionless `A`-scale form. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_A_scale_one
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {T_in T_out K A : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hTin0 : 0 ≤ T_in) (hTout0 : 0 ≤ T_out) (hK0 : 0 ≤ K)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout :
      ∀ s₀ : F, s₀ ∉ D →
        ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ K)
    (hKdim : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hA :
      4 * A ^ 4 * (G.card : ℝ) ^ 2
        ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  have hC0 : (0 : ℝ) ≤ 1 := by norm_num
  have hC1 : (1 : ℝ) ≤ 1 := by norm_num
  have hA' : 4 * A ^ 4 * (G.card : ℝ) ^ 2
      ≤ 3 * (1 : ℝ) * (orderOf χ : ℝ) ^ 2 := by
    simpa using hA
  rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_A_scale χ hψ G D hGD hY
    hm hn hC0 hC1 hTin0 hTout0 hK0 hTin hTout hreg hKbound hKdim hA'

/-- Direct pointwise endpoint with `C = 1` and `A ≤ 1`; only the size gate
`4|G|² ≤ 3m²` remains on the dimensionless side. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_A_le_one
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {T_in T_out K A : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hTin0 : 0 ≤ T_in) (hTout0 : 0 ≤ T_out) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout :
      ∀ s₀ : F, s₀ ∉ D →
        ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ K)
    (hKdim : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hsize : 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  have hC0 : (0 : ℝ) ≤ 1 := by norm_num
  have hC1 : (1 : ℝ) ≤ 1 := by norm_num
  have hK :
      4 * K ^ 4
        ≤ 3 * (1 : ℝ) * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
          * (Fintype.card F : ℝ) ^ 2 := by
    simpa using pointwise_fourth_scale_one_of_A_le_one χ G hK0 hA0 hA1 hKdim hsize
  rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_K_scale χ hψ G D hGD hY
    hm hn hC0 hC1 hTin0 hTout0 hTin hTout hreg hKbound
    hK

/-- Raw fourth-moment endpoint for the approximate residual route.  Once the explicit numeric
gate puts the pointwise-residual constant at `C ≤ 1`, R16 collapses the constant-rung statement
back to the exact R15 `RawFourthMomentWithDiagonal` target. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_gate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    (r : ℕ) {T_in T_out C : ℝ} (hm : 1 ≤ orderOf χ) (hC : C ≤ 1)
    (hTout0 : 0 ≤ T_out) (hr : 1 ≤ r)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r))
    (hgate :
      (((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2))) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_wickAwayAtWithConstant_two_le_one G (Gchi χ) D hC
    (wickAwayAtWithConstant_two_of_chiSubfamily_shifted_omitted_rate χ hψ G D hGD hY
      r hm hTout0 hr hTin hwick hrate hgate)

/-- Regime-form raw fourth-moment endpoint for the shifted omitted-character route.  R18
discharges the Σ lower bound, so the remaining numerical target is the cleaner scale gate
`4 |F \ D| B⁴ ≤ 3 C m² n² q³`, where
`B = |G| + |Y|√q T_in + |chiFamily χ \ Y|√q T_out`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_scale_gate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    (r : ℕ) {T_in T_out C : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hC0 : 0 ≤ C) (hC : C ≤ 1) (hTout0 : 0 ≤ T_out) (hr : 1 ≤ r)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hscale :
      4 * ((((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4)
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
          * (Fintype.card F : ℝ) ^ 3) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_gate χ hψ G D hGD hY
    r (le_trans (by norm_num) hm) hC hTout0 hr hTin hwick hrate
    (pointwise_order_gate_of_hSig χ ψ G D (le_trans (by norm_num) hm) hC0
      (hSig_of_regime hψ G hm hn hreg) hscale)

/-- Shifted-omitted-rate endpoint with both Σ and deleted-offset cardinality discharged.  This is
the cleanest current residual-route target: prove the kept-character pointwise bound, the omitted
shifted-Wick rate, and the per-offset scale inequality
`4B⁴ ≤ 3Cm²n²q²`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_fourth_scale
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    (r : ℕ) {T_in T_out C : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hC0 : 0 ≤ C) (hC : C ≤ 1) (hTout0 : 0 ≤ T_out) (hr : 1 ≤ r)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hB :
      4 * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
          * (Fintype.card F : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_scale_gate χ hψ G D
    hGD hY r hm hn hC0 hC hTout0 hr hTin hwick hrate hreg
    (scale_gate_of_pointwise_fourth_scale χ G D hB)

/-- `K`-budget version of the shifted-omitted-rate endpoint.  This is currently the most compact
formal residual target: prove a kept-family pointwise bound, an omitted-family shifted Wick rate,
and a clean budget `K` with `4K⁴ ≤ 3Cm²n²q²`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_K_scale
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    (r : ℕ) {T_in T_out C K : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hC0 : 0 ≤ C) (hC : C ≤ 1) (hTin0 : 0 ≤ T_in) (hTout0 : 0 ≤ T_out) (hr : 1 ≤ r)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ K)
    (hK :
      4 * K ^ 4
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
          * (Fintype.card F : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D := by
  have hB0 :
      0 ≤ (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out := by
    positivity
  exact rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_fourth_scale χ hψ G D
    hGD hY r hm hn hC0 hC hTout0 hr hTin hwick hrate hreg
    (pointwise_fourth_scale_of_le χ G hB0 hKbound hK)

/-- Dimensionless `A`-scale version of the shifted-omitted residual endpoint.  This is the
current compact target for the route: prove the analytic bounds, dominate the resulting budget by
`A·|G|·√q`, and close `4A⁴|G|² ≤ 3Cm²`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_A_scale
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    (r : ℕ) {T_in T_out C K A : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hC0 : 0 ≤ C) (hC : C ≤ 1)
    (hTin0 : 0 ≤ T_in) (hTout0 : 0 ≤ T_out) (hK0 : 0 ≤ K) (hr : 1 ≤ r)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ K)
    (hKdim : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hA :
      4 * A ^ 4 * (G.card : ℝ) ^ 2
        ≤ 3 * C * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_K_scale χ hψ G D hGD hY
    r hm hn hC0 hC hTin0 hTout0 hr hTin hwick hrate hreg hKbound
    (pointwise_fourth_scale_of_le_const_mul_card_sqrt χ G hK0 hKdim hA)

/-- Exact-constant (`C = 1`) shifted-omitted endpoint in dimensionless `A`-scale form. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_A_scale_one
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    (r : ℕ) {T_in T_out K A : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hTin0 : 0 ≤ T_in) (hTout0 : 0 ≤ T_out) (hK0 : 0 ≤ K) (hr : 1 ≤ r)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ K)
    (hKdim : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hA :
      4 * A ^ 4 * (G.card : ℝ) ^ 2
        ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  have hC0 : (0 : ℝ) ≤ 1 := by norm_num
  have hC1 : (1 : ℝ) ≤ 1 := by norm_num
  have hA' : 4 * A ^ 4 * (G.card : ℝ) ^ 2
      ≤ 3 * (1 : ℝ) * (orderOf χ : ℝ) ^ 2 := by
    simpa using hA
  rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_A_scale χ hψ G D hGD hY
    r hm hn hC0 hC1 hTin0 hTout0 hK0 hr hTin hwick hrate hreg
    hKbound hKdim hA'

/-- Shifted-omitted endpoint with `C = 1` and `A ≤ 1`; only the size gate
`4|G|² ≤ 3m²` remains after the analytic budget is normalized. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_A_le_one
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    (r : ℕ) {T_in T_out K A : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hTin0 : 0 ≤ T_in) (hTout0 : 0 ≤ T_out) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hr : 1 ≤ r)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ K)
    (hKdim : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hsize : 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  have hC0 : (0 : ℝ) ≤ 1 := by norm_num
  have hC1 : (1 : ℝ) ≤ 1 := by norm_num
  have hK :
      4 * K ^ 4
        ≤ 3 * (1 : ℝ) * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2
          * (Fintype.card F : ℝ) ^ 2 := by
    simpa using pointwise_fourth_scale_one_of_A_le_one χ G hK0 hA0 hA1 hKdim hsize
  rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_K_scale χ hψ G D hGD hY
    r hm hn hC0 hC1 hTin0 hTout0 hr hTin hwick hrate hreg hKbound
    hK

/-- Two-sided shifted-rate version of the approximate thinned-family endpoint.  The kept
subfamily `Y` and omitted residual family `chiFamily χ \ Y` may use different rungs and
different pointwise budgets; both pointwise inputs are produced from corrected-away shifted-Wick
rate hypotheses.  After that, the remaining target is the same normalized `A ≤ 1` budget. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_rates_A_le_one
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    (r_in r_out : ℕ) {T_in T_out K A : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hTin0 : 0 ≤ T_in) (hTout0 : 0 ≤ T_out) (hK0 : 0 ≤ K)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hr_in : 1 ≤ r_in) (hr_out : 1 ≤ r_out)
    (hwickIn :
      ∀ χ' ∈ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt
          χ' G D r_in)
    (hwickOut :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt
          χ' G D r_out)
    (hrateIn :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r_in - 1) : ℝ)
          * (G.card : ℝ) ^ r_in
        ≤ T_in ^ (2 * r_in))
    (hrateOut :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r_out - 1) : ℝ)
          * (G.card : ℝ) ^ r_out
        ≤ T_out ^ (2 * r_out))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ K)
    (hKdim : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hsize : 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_A_le_one χ hψ G D
    hGD hY r_out hm hn hTin0 hTout0 hK0 hA0 hA1 hr_out
    (fun _s₀ hs₀ χ' hχ' =>
      twistedThinSum_le_of_shifted_awayWickAt_rate χ' G D r_in hTin0 hr_in
        (hwickIn χ' hχ') hrateIn hs₀)
    hwickOut hrateOut hreg hKbound hKdim hsize

/-- Necessary-condition obstruction for the two-sided shifted-rate thinned route.  If the kept
subfamily is nonempty, the normalized `A ≤ 1` budget cannot coexist with the assumed `r = 1`
shifted-rate lower scale for the kept side in the R18 size regime, regardless of how the omitted
side is handled. -/
theorem not_chiSubfamily_shifted_rates_budget_A_le_one_of_nonempty_kept_r_one_regime
    (χ : MulChar F ℂ) (G : Finset F) {Y : Finset (MulChar F ℂ)}
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hYne : Y.Nonempty)
    {T_in T_out A : ℝ} (hTin0 : 0 ≤ T_in) (hTout0 : 0 ≤ T_out) (hA1 : A ≤ 1)
    (hrateIn : (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T_in ^ 2)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hbudget :
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :
    False := by
  set n : ℝ := (G.card : ℝ) with hndef
  set y : ℝ := (Y.card : ℝ) with hydef
  set o : ℝ := ((chiFamily χ \ Y).card : ℝ) with hodef
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set m : ℝ := (orderOf χ : ℝ) with hmdef
  set s : ℝ := Real.sqrt q with hsdef
  have hnpos : 0 < n := by rw [hndef]; exact_mod_cast hn
  have hn0 : 0 ≤ n := le_of_lt hnpos
  have hn_ge_one : 1 ≤ n := by rw [hndef]; exact_mod_cast hn
  have hm_ge_two : 2 ≤ m := by rw [hmdef]; exact_mod_cast hm
  have hqpos_nat : 0 < Fintype.card F := Fintype.card_pos
  have hqpos : 0 < q := by rw [hqdef]; exact_mod_cast hqpos_nat
  have hspos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 hqpos
  have hs0 : 0 ≤ s := le_of_lt hspos
  have hy_ge_one : 1 ≤ y := by
    rw [hydef]
    exact_mod_cast Finset.card_pos.mpr hYne
  have ho0 : 0 ≤ o := by rw [hodef]; positivity
  have hbudget' :
      n + y * s * T_in + o * s * T_out ≤ A * n * s := by
    simpa [hndef, hydef, hodef, hqdef, hsdef, mul_comm, mul_left_comm, mul_assoc] using
      hbudget
  have hA_scale : A * n * s ≤ n * s := by
    nlinarith [mul_le_mul_of_nonneg_right hA1 (mul_nonneg hn0 hs0)]
  have hmain_le : y * s * T_in ≤ n * s := by
    have homit_nonneg : 0 ≤ o * s * T_out := by positivity
    nlinarith
  have hsT_le : s * T_in ≤ n * s := by
    have hmono : s * T_in ≤ y * s * T_in := by
      have hmul := mul_le_mul_of_nonneg_right hy_ge_one (mul_nonneg hs0 hTin0)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact le_trans hmono hmain_le
  have hTin_le_n : T_in ≤ n := by
    have hsT_le' : s * T_in ≤ s * n := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsT_le
    exact le_of_mul_le_mul_left hsT_le' hspos
  have hTin_sq_le : T_in ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hTin0 hTin_le_n 2
  have hrate' : q * n ≤ T_in ^ 2 := by
    simpa [hqdef, hndef, mul_comm, mul_left_comm, mul_assoc] using hrateIn
  have hq_gt_n : n < q := by
    have hreg' : 16 * m ^ 2 * n ^ 2 ≤ q := by
      simpa [hmdef, hndef, hqdef] using hreg
    have hlarge : n < 16 * m ^ 2 * n ^ 2 := by
      have hfactor : 1 < 16 * m ^ 2 * n := by
        have hn_ge_one : 1 ≤ n := by rw [hndef]; exact_mod_cast hn
        have hm_sq_ge_four : 4 ≤ m ^ 2 := by nlinarith [sq_nonneg (m - 2)]
        have hm_sq_nonneg : 0 ≤ m ^ 2 := by nlinarith
        have hprod : 4 ≤ m ^ 2 * n :=
          le_trans (by norm_num : (4 : ℝ) ≤ 4 * 1)
            (mul_le_mul hm_sq_ge_four hn_ge_one (by norm_num) hm_sq_nonneg)
        nlinarith
      calc
        n = n * 1 := by ring
        _ < n * (16 * m ^ 2 * n) := mul_lt_mul_of_pos_left hfactor hnpos
        _ = 16 * m ^ 2 * n ^ 2 := by ring
    exact lt_of_lt_of_le hlarge hreg'
  have hqn_gt : n ^ 2 < q * n := by nlinarith [mul_lt_mul_of_pos_right hq_gt_n hnpos]
  nlinarith

/-- Existential form of the nonempty-kept `r = 1` shifted-rate obstruction. -/
theorem not_exists_chiSubfamily_shifted_rates_budget_A_le_one_of_nonempty_kept_r_one_regime
    (χ : MulChar F ℂ) (G : Finset F) {Y : Finset (MulChar F ℂ)}
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hYne : Y.Nonempty)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ ∃ T_in T_out A : ℝ,
      0 ≤ T_in ∧ 0 ≤ T_out ∧ A ≤ 1 ∧
      (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T_in ^ 2 ∧
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  rintro ⟨T_in, T_out, A, hTin0, hTout0, hA1, hrateIn, hbudget⟩
  exact not_chiSubfamily_shifted_rates_budget_A_le_one_of_nonempty_kept_r_one_regime
    χ G hm hn hYne hTin0 hTout0 hA1 hrateIn hreg hbudget

/-- Normalized-one specialization of the nonempty-kept `r = 1` shifted-rate obstruction. -/
theorem not_exists_chiSubfamily_shifted_rates_budget_one_of_nonempty_kept_r_one_regime
    (χ : MulChar F ℂ) (G : Finset F) {Y : Finset (MulChar F ℂ)}
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hYne : Y.Nonempty)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ ∃ T_in T_out : ℝ,
      0 ≤ T_in ∧ 0 ≤ T_out ∧
      (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T_in ^ 2 ∧
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  rintro ⟨T_in, T_out, hTin0, hTout0, hrateIn, hbudget⟩
  exact not_exists_chiSubfamily_shifted_rates_budget_A_le_one_of_nonempty_kept_r_one_regime
    χ G hm hn hYne hreg
    ⟨T_in, T_out, 1, hTin0, hTout0, le_rfl, hrateIn, by simpa using hbudget⟩

/-- Public-interface no-go for the two-sided shifted-rate adapter at kept rung `r_in = 1`.
For a nonempty kept subfamily, the adapter's own `K ≤ A·|G|√q` and `A ≤ 1` budget hypotheses
already imply the forbidden direct budget, so the input package is inconsistent in the R18
regime. -/
theorem not_chiSubfamily_shifted_rates_A_le_one_inputs_of_nonempty_kept_r_one_regime
    (χ : MulChar F ℂ) (G : Finset F) {Y : Finset (MulChar F ℂ)}
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hYne : Y.Nonempty)
    {T_in T_out K A : ℝ} (hTin0 : 0 ≤ T_in) (hTout0 : 0 ≤ T_out)
    (_hK0 : 0 ≤ K) (_hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hrateIn : (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T_in ^ 2)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ K)
    (hKdim : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :
    False := by
  exact not_chiSubfamily_shifted_rates_budget_A_le_one_of_nonempty_kept_r_one_regime
    χ G hm hn hYne hTin0 hTout0 hA1 hrateIn hreg (le_trans hKbound hKdim)

/-- Existential public-interface form of the nonempty-kept `r_in = 1` obstruction. -/
theorem not_exists_chiSubfamily_shifted_rates_A_le_one_inputs_of_nonempty_kept_r_one_regime
    (χ : MulChar F ℂ) (G : Finset F) {Y : Finset (MulChar F ℂ)}
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hYne : Y.Nonempty)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ ∃ T_in T_out K A : ℝ,
      0 ≤ T_in ∧ 0 ≤ T_out ∧ 0 ≤ K ∧ 0 ≤ A ∧ A ≤ 1 ∧
      (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T_in ^ 2 ∧
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ K ∧
      K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  rintro ⟨T_in, T_out, K, A, hTin0, hTout0, hK0, hA0, hA1, hrateIn, hKbound, hKdim⟩
  exact not_chiSubfamily_shifted_rates_A_le_one_inputs_of_nonempty_kept_r_one_regime
    χ G hm hn hYne hTin0 hTout0 hK0 hA0 hA1 hrateIn hreg hKbound hKdim

/-- The exact input-shape obstruction for
`rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_rates_A_le_one` when the kept-side rung is
`r_in = 1`.  The Wick witnesses themselves are irrelevant: the rate lower bound and normalized
budget already contradict the R18 regime for every nonempty kept subfamily. -/
theorem not_rawFourthMoment_chiSubfamily_shifted_rates_A_le_one_inputs_r_in_one_regime
    (χ : MulChar F ℂ) (G D : Finset F) {Y : Finset (MulChar F ℂ)}
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hYne : Y.Nonempty)
    (r_out : ℕ) {T_in T_out K A : ℝ}
    (hTin0 : 0 ≤ T_in) (hTout0 : 0 ≤ T_out) (hK0 : 0 ≤ K)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (_hr_out : 1 ≤ r_out)
    (_hwickIn :
      ∀ χ' ∈ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt
          χ' G D 1)
    (_hwickOut :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt
          χ' G D r_out)
    (hrateIn :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 1 - 1) : ℝ)
          * (G.card : ℝ) ^ 1
        ≤ T_in ^ (2 * 1))
    (_hrateOut :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r_out - 1) : ℝ)
          * (G.card : ℝ) ^ r_out
        ≤ T_out ^ (2 * r_out))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out
        ≤ K)
    (hKdim : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (_hsize : 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    False := by
  have hrateIn' : (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T_in ^ 2 := by
    norm_num at hrateIn ⊢
    exact hrateIn
  exact not_chiSubfamily_shifted_rates_A_le_one_inputs_of_nonempty_kept_r_one_regime
    χ G hm hn hYne hTin0 hTout0 hK0 hA0 hA1 hrateIn' hreg hKbound hKdim

/-- Empty-kept-family specialization of the direct pointwise endpoint.  This exposes the
all-residual route with the compact budget `|G| + |chiFamily χ|√q·T ≤ K`. -/
theorem rawFourthMomentWithDiagonal_of_chiFamily_pointwise_all_omitted_A_le_one
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) (hGD : G ⊆ D)
    {T K A : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hT0 : 0 ≤ T) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hT :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ chiFamily χ, ‖twistedThinSum χ' G s₀‖ ≤ T)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ) + ((chiFamily χ).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ K)
    (hKdim : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hsize : 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D := by
  classical
  exact rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_A_le_one χ hψ G D
    hGD (Y := (∅ : Finset (MulChar F ℂ))) (T_in := 0) (T_out := T)
    (by simp) hm hn (by norm_num) hT0 hK0 hA0 hA1
    (fun _s₀ _hs₀ χ' hχ' => by simp at hχ')
    (fun s₀ hs₀ χ' hχ' => by
      exact hT s₀ hs₀ χ' (by simpa using hχ'))
    hreg
    (by simpa using hKbound)
    hKdim hsize

/-- Empty-kept-family specialization of the shifted-Wick omitted endpoint.  The analytic work is
entirely on `chiFamily χ`, through a shifted-away Wick rate and the same normalized budget. -/
theorem rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_A_le_one
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) (hGD : G ⊆ D)
    (r : ℕ) {T K A : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hT0 : 0 ≤ T) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hr : 1 ≤ r)
    (hwick :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ) + ((chiFamily χ).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ K)
    (hKdim : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hsize : 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D := by
  classical
  exact rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_A_le_one χ hψ G D
    hGD (Y := (∅ : Finset (MulChar F ℂ))) (T_in := 0) (T_out := T)
    (by simp) r hm hn (by norm_num) hT0 hK0 hA0 hA1 hr
    (fun _s₀ _hs₀ χ' hχ' => by simp at hχ')
    (fun χ' hχ' => hwick χ' (by simpa using hχ'))
    hrate hreg
    (by simpa using hKbound)
    hKdim hsize

/-- Closed-cardinality form of
`rawFourthMomentWithDiagonal_of_chiFamily_pointwise_all_omitted_A_le_one`, using
`|chiFamily χ| = orderOf χ - 1` in the residual budget. -/
theorem rawFourthMomentWithDiagonal_of_chiFamily_pointwise_all_omitted_order_budget_A_le_one
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) (hGD : G ⊆ D)
    {T K A : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hT0 : 0 ≤ T) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hT :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ chiFamily χ, ‖twistedThinSum χ' G s₀‖ ≤ T)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ K)
    (hKdim : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hsize : 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_chiFamily_pointwise_all_omitted_A_le_one χ hψ G D hGD
    hm hn hT0 hK0 hA0 hA1 hT hreg
    (by simpa [chiFamily_card] using hKbound)
    hKdim hsize

/-- Closed-cardinality form of
`rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_A_le_one`, using
`|chiFamily χ| = orderOf χ - 1` in the residual budget. -/
theorem rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_order_budget_A_le_one
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) (hGD : G ⊆ D)
    (r : ℕ) {T K A : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hT0 : 0 ≤ T) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hr : 1 ≤ r)
    (hwick :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hKbound :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ K)
    (hKdim : K ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hsize : 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_A_le_one χ hψ G D hGD
    r hm hn hT0 hK0 hA0 hA1 hr hwick hrate hreg
    (by simpa [chiFamily_card] using hKbound)
    hKdim hsize

/-- Normalized-budget pointwise all-omitted endpoint.  This removes the auxiliary `K`: it is
enough to prove the explicit residual budget is at most `A·|G|·√q`. -/
theorem rawFourthMomentWithDiagonal_of_chiFamily_pointwise_all_omitted_normalized_budget_A_le_one
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) (hGD : G ⊆ D)
    {T A : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hT0 : 0 ≤ T) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hT :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ chiFamily χ, ‖twistedThinSum χ' G s₀‖ ≤ T)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hsize : 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D := by
  have hK0 : 0 ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
    positivity
  exact
    rawFourthMomentWithDiagonal_of_chiFamily_pointwise_all_omitted_order_budget_A_le_one
      χ hψ G D hGD hm hn hT0 hK0 hA0 hA1 hT hreg hbudget (le_rfl) hsize

/-- Normalized-budget shifted-Wick all-omitted endpoint.  The open analytic target is now just:
prove shifted Wick on every character, a rate bound for `T`, and
`|G| + (m-1)√q·T ≤ A·|G|√q`. -/
theorem rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_normalized_budget_A_le_one
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) (hGD : G ⊆ D)
    (r : ℕ) {T A : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hT0 : 0 ≤ T) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hr : 1 ≤ r)
    (hwick :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hsize : 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D := by
  have hK0 : 0 ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
    positivity
  exact
    rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_order_budget_A_le_one
      χ hψ G D hGD r hm hn hT0 hK0 hA0 hA1 hr hwick hrate hreg
      hbudget (le_rfl) hsize

/-- Exact normalized-budget pointwise all-omitted endpoint (`A = 1`).  The remaining budget is
`|G| + (m-1)√q·T ≤ |G|√q`. -/
theorem rawFourthMomentWithDiagonal_of_chiFamily_pointwise_all_omitted_normalized_budget_one
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) (hGD : G ⊆ D)
    {T : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hT0 : 0 ≤ T)
    (hT :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ chiFamily χ, ‖twistedThinSum χ' G s₀‖ ≤ T)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hsize : 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_chiFamily_pointwise_all_omitted_normalized_budget_A_le_one
    χ hψ G D hGD (A := 1) hm hn hT0 (by norm_num) (by norm_num) hT
    hreg
    (by simpa using hbudget) hsize

/-- Exact normalized-budget shifted-Wick all-omitted endpoint (`A = 1`). -/
theorem rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_normalized_budget_one
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) (hGD : G ⊆ D)
    (r : ℕ) {T : ℝ} (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hT0 : 0 ≤ T) (hr : 1 ≤ r)
    (hwick :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hsize : 4 * (G.card : ℝ) ^ 2 ≤ 3 * (orderOf χ : ℝ) ^ 2) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_normalized_budget_A_le_one
    χ hψ G D hGD r (A := 1) hm hn hT0 (by norm_num) (by norm_num) hr
    hwick hrate hreg
    (by simpa using hbudget) hsize

/-- Necessary `T`-cap encoded by the exact normalized all-omitted budget.  Any route using
`|G| + (m-1)√q·T ≤ |G|√q` must in particular prove
`(m-1)√q·T ≤ |G|(√q - 1)`. -/
theorem chiFamily_all_omitted_T_cap_of_normalized_budget_one
    (χ : MulChar F ℂ) (G : Finset F) {T : ℝ}
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :
    ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
      ≤ (G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1) := by
  nlinarith

/-- `A ≤ 1` version of the all-omitted `T` cap.  Any normalized budget with
`A·|G|√q` on the right is at least as restrictive as the exact `A = 1` budget. -/
theorem chiFamily_all_omitted_T_cap_of_normalized_budget_A_le_one
    (χ : MulChar F ℂ) (G : Finset F) {T A : ℝ} (hA : A ≤ 1)
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :
    ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
      ≤ (G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1) := by
  have hscale_nonneg : 0 ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
    positivity
  have hbudget_one :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
    have hA_scale :
        A * ((G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
          ≤ 1 * ((G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :=
      mul_le_mul_of_nonneg_right hA hscale_nonneg
    nlinarith [hbudget, hA_scale]
  exact chiFamily_all_omitted_T_cap_of_normalized_budget_one χ G hbudget_one

/-- Divided form of `chiFamily_all_omitted_T_cap_of_normalized_budget_one`.  This is the
pointwise size an all-omitted route must force on every twisted thin sum. -/
theorem chiFamily_all_omitted_T_le_of_normalized_budget_one
    (χ : MulChar F ℂ) (G : Finset F) {T : ℝ}
    (hden :
      0 < ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :
    T ≤ ((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
        / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ)) := by
  have hcap := chiFamily_all_omitted_T_cap_of_normalized_budget_one χ G hbudget
  rw [le_div_iff₀ hden]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcap

/-- Divided `A ≤ 1` form of the all-omitted `T` cap. -/
theorem chiFamily_all_omitted_T_le_of_normalized_budget_A_le_one
    (χ : MulChar F ℂ) (G : Finset F) {T A : ℝ}
    (hden :
      0 < ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))
    (hA : A ≤ 1)
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :
    T ≤ ((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
        / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ)) := by
  have hcap := chiFamily_all_omitted_T_cap_of_normalized_budget_A_le_one χ G hA hbudget
  rw [le_div_iff₀ hden]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcap

/-- The denominator in the divided all-omitted `T` cap is positive in the nontrivial
`orderOf χ ≥ 2` regime. -/
theorem chiFamily_all_omitted_den_pos (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) :
    0 < ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  have hm1_nat : 0 < orderOf χ - 1 := by omega
  have hm1 : (0 : ℝ) < ((orderOf χ - 1 : ℕ) : ℝ) := by exact_mod_cast hm1_nat
  have hqpos_nat : 0 < Fintype.card F := Fintype.card_pos
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hqpos_nat
  have hsqrt : 0 < Real.sqrt (Fintype.card F : ℝ) := Real.sqrt_pos.2 hqpos
  exact mul_pos hm1 hsqrt

/-- Divided `T` cap with the denominator positivity discharged from `orderOf χ ≥ 2`. -/
theorem chiFamily_all_omitted_T_le_of_normalized_budget_one_of_two_le_order
    (χ : MulChar F ℂ) (G : Finset F) {T : ℝ} (hm : 2 ≤ orderOf χ)
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :
    T ≤ ((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
        / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :=
  chiFamily_all_omitted_T_le_of_normalized_budget_one χ G
    (chiFamily_all_omitted_den_pos χ hm) hbudget

/-- Divided `A ≤ 1` all-omitted `T` cap with denominator positivity discharged from
`orderOf χ ≥ 2`. -/
theorem chiFamily_all_omitted_T_le_of_normalized_budget_A_le_one_of_two_le_order
    (χ : MulChar F ℂ) (G : Finset F) {T A : ℝ} (hm : 2 ≤ orderOf χ) (hA : A ≤ 1)
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :
    T ≤ ((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
        / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :=
  chiFamily_all_omitted_T_le_of_normalized_budget_A_le_one χ G
    (chiFamily_all_omitted_den_pos χ hm) hA hbudget

/-- Combining the shifted-Wick rate lower requirement with the exact all-omitted budget cap
forces a purely numerical inequality.  This is the obstruction shape for the all-omitted shifted
route: the moment-derived lower scale for `T` must fit under the budget cap. -/
theorem shifted_all_omitted_rate_le_budget_cap_pow
    (χ : MulChar F ℂ) (G : Finset F) {T : ℝ} (r : ℕ)
    (hm : 2 ≤ orderOf χ) (hT0 : 0 ≤ T)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r))
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :
    (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
      ≤ (((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
          / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))) ^ (2 * r) := by
  have hTcap :=
    chiFamily_all_omitted_T_le_of_normalized_budget_one_of_two_le_order χ G hm hbudget
  have hpow := pow_le_pow_left₀ hT0 hTcap (2 * r)
  exact le_trans hrate hpow

/-- `A ≤ 1` version of `shifted_all_omitted_rate_le_budget_cap_pow`.  The same cap controls every
normalized all-omitted budget whose right side is `A·|G|√q` with `A ≤ 1`. -/
theorem shifted_all_omitted_rate_le_budget_cap_pow_of_A_le_one
    (χ : MulChar F ℂ) (G : Finset F) {T A : ℝ} (r : ℕ)
    (hm : 2 ≤ orderOf χ) (hT0 : 0 ≤ T) (hA : A ≤ 1)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r))
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :
    (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
      ≤ (((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
          / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))) ^ (2 * r) := by
  have hTcap :=
    chiFamily_all_omitted_T_le_of_normalized_budget_A_le_one_of_two_le_order χ G hm hA
      hbudget
  have hpow := pow_le_pow_left₀ hT0 hTcap (2 * r)
  exact le_trans hrate hpow

/-- No-go corollary for the all-omitted shifted route: if the numeric shifted-rate lower bound
is strictly larger than the budget cap to the same power, then the exact normalized budget cannot
hold. -/
theorem not_shifted_all_omitted_budget_of_rate_cap_lt
    (χ : MulChar F ℂ) (G : Finset F) {T : ℝ} (r : ℕ)
    (hm : 2 ≤ orderOf χ) (hT0 : 0 ≤ T)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r))
    (hcap_lt :
      (((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
          / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))) ^ (2 * r)
        < (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
          * (G.card : ℝ) ^ r) :
    ¬ (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  intro hbudget
  have hle := shifted_all_omitted_rate_le_budget_cap_pow χ G r hm hT0 hrate hbudget
  exact not_lt_of_ge hle hcap_lt

/-- `A ≤ 1` no-go corollary for the all-omitted shifted route. -/
theorem not_shifted_all_omitted_budget_A_le_one_of_rate_cap_lt
    (χ : MulChar F ℂ) (G : Finset F) {T A : ℝ} (r : ℕ)
    (hm : 2 ≤ orderOf χ) (hT0 : 0 ≤ T) (hA : A ≤ 1)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r))
    (hcap_lt :
      (((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
          / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))) ^ (2 * r)
        < (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
          * (G.card : ℝ) ^ r) :
    ¬ (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  intro hbudget
  have hle :=
    shifted_all_omitted_rate_le_budget_cap_pow_of_A_le_one χ G r hm hT0 hA hrate hbudget
  exact not_lt_of_ge hle hcap_lt

/-- The `r = 1` specialization of `shifted_all_omitted_rate_le_budget_cap_pow`: the exact
all-omitted shifted route already forces `q·|G|` to fit below the square of the budget cap. -/
theorem shifted_all_omitted_rate_one_le_budget_cap_sq
    (χ : MulChar F ℂ) (G : Finset F) {T : ℝ}
    (hm : 2 ≤ orderOf χ) (hT0 : 0 ≤ T)
    (hrate :
      (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T ^ 2)
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :
    (Fintype.card F : ℝ) * (G.card : ℝ)
      ≤ (((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
          / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))) ^ 2 := by
  have hrate' :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 1 - 1) : ℝ) * (G.card : ℝ) ^ 1
        ≤ T ^ (2 * 1) := by
    norm_num at hrate ⊢
    exact hrate
  simpa using shifted_all_omitted_rate_le_budget_cap_pow χ G 1 hm hT0 hrate' hbudget

/-- `A ≤ 1` version of `shifted_all_omitted_rate_one_le_budget_cap_sq`. -/
theorem shifted_all_omitted_rate_one_le_budget_cap_sq_of_A_le_one
    (χ : MulChar F ℂ) (G : Finset F) {T A : ℝ}
    (hm : 2 ≤ orderOf χ) (hT0 : 0 ≤ T) (hA : A ≤ 1)
    (hrate :
      (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T ^ 2)
    (hbudget :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :
    (Fintype.card F : ℝ) * (G.card : ℝ)
      ≤ (((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
          / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))) ^ 2 := by
  have hrate' :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 1 - 1) : ℝ) * (G.card : ℝ) ^ 1
        ≤ T ^ (2 * 1) := by
    norm_num at hrate ⊢
    exact hrate
  simpa using shifted_all_omitted_rate_le_budget_cap_pow_of_A_le_one χ G 1 hm hT0 hA
    hrate' hbudget

/-- `r = 1` no-go for the all-omitted shifted route.  If the square of the exact normalized
budget cap is below `q·|G|`, the budget cannot coexist with the `r = 1` shifted-rate lower bound. -/
theorem not_shifted_all_omitted_budget_of_rate_one_cap_sq_lt
    (χ : MulChar F ℂ) (G : Finset F) {T : ℝ}
    (hm : 2 ≤ orderOf χ) (hT0 : 0 ≤ T)
    (hrate :
      (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T ^ 2)
    (hcap_lt :
      (((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
          / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))) ^ 2
        < (Fintype.card F : ℝ) * (G.card : ℝ)) :
    ¬ (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  intro hbudget
  have hle := shifted_all_omitted_rate_one_le_budget_cap_sq χ G hm hT0 hrate hbudget
  exact not_lt_of_ge hle hcap_lt

/-- `A ≤ 1` no-go for the `r = 1` all-omitted shifted route. -/
theorem not_shifted_all_omitted_budget_A_le_one_of_rate_one_cap_sq_lt
    (χ : MulChar F ℂ) (G : Finset F) {T A : ℝ}
    (hm : 2 ≤ orderOf χ) (hT0 : 0 ≤ T) (hA : A ≤ 1)
    (hrate :
      (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T ^ 2)
    (hcap_lt :
      (((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
          / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))) ^ 2
        < (Fintype.card F : ℝ) * (G.card : ℝ)) :
    ¬ (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  intro hbudget
  have hle := shifted_all_omitted_rate_one_le_budget_cap_sq_of_A_le_one χ G hm hT0 hA
    hrate hbudget
  exact not_lt_of_ge hle hcap_lt

/-- A convenient upper bound for the squared exact all-omitted budget cap.  The factor
`(√q - 1)^2 / q` is at most `1`, so the cap is no larger than `|G|/(m-1)`. -/
theorem shifted_all_omitted_budget_cap_sq_le_card_div_order_sub_sq
    (χ : MulChar F ℂ) (G : Finset F) (hm : 2 ≤ orderOf χ) :
    (((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
          / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))) ^ 2
      ≤ (G.card : ℝ) ^ 2 / (((orderOf χ - 1 : ℕ) : ℝ) ^ 2) := by
  set n : ℝ := (G.card : ℝ) with hndef
  set a : ℝ := ((orderOf χ - 1 : ℕ) : ℝ) with hadef
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set s : ℝ := Real.sqrt q with hsdef
  have ha0 : 0 < a := by
    rw [hadef]
    have hm1_nat : 0 < orderOf χ - 1 := by omega
    exact_mod_cast hm1_nat
  have hqpos_nat : 0 < Fintype.card F := Fintype.card_pos
  have hqpos : 0 < q := by rw [hqdef]; exact_mod_cast hqpos_nat
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 hqpos
  have hs_sq : s ^ 2 = q := by rw [hsdef, Real.sq_sqrt (le_of_lt hqpos)]
  have hq1 : (1 : ℝ) ≤ q := by
    rw [hqdef]
    exact_mod_cast (Nat.succ_le_iff.mp hqpos_nat)
  have hs_ge_one : 1 ≤ s := by
    have hs1 := Real.sqrt_le_sqrt hq1
    simpa [hsdef] using hs1
  have hratio_sq : (s - 1) ^ 2 ≤ s ^ 2 := by
    nlinarith [hs_ge_one]
  have hnonneg : 0 ≤ n ^ 2 / a ^ 2 := by positivity
  calc
    (n * (s - 1) / (a * s)) ^ 2
        = (n ^ 2 / a ^ 2) * ((s - 1) ^ 2 / s ^ 2) := by
          field_simp [ne_of_gt ha0, ne_of_gt hs0]
    _ ≤ (n ^ 2 / a ^ 2) * 1 := by
          have hs2pos : 0 < s ^ 2 := sq_pos_of_pos hs0
          have hfrac : (s - 1) ^ 2 / s ^ 2 ≤ 1 := by
            rw [div_le_one hs2pos]
            exact hratio_sq
          exact mul_le_mul_of_nonneg_left hfrac hnonneg
    _ = n ^ 2 / a ^ 2 := by ring

/-- In the R18 regime, the `r = 1` all-omitted shifted budget cap is automatically too small:
`cap^2 < q·|G|`.  This turns the `r = 1` no-go into a direct regime obstruction. -/
theorem shifted_all_omitted_budget_cap_sq_lt_rate_one_of_regime
    (χ : MulChar F ℂ) (G : Finset F) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    (((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
          / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))) ^ 2
        < (Fintype.card F : ℝ) * (G.card : ℝ) := by
  set n : ℝ := (G.card : ℝ) with hndef
  set m : ℝ := (orderOf χ : ℝ) with hmdef
  set a : ℝ := ((orderOf χ - 1 : ℕ) : ℝ) with hadef
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hnpos : 0 < n := by rw [hndef]; exact_mod_cast hn
  have hn_ge_one : (1 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn
  have hmpos : 0 < m := by rw [hmdef]; exact_mod_cast (lt_of_lt_of_le (by norm_num) hm)
  have hm_ge_two : (2 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hm
  have ha_eq : a = m - 1 := by
    rw [hadef, hmdef]
    rw [Nat.cast_sub (by omega : 1 ≤ orderOf χ), Nat.cast_one]
  have ha_ge_one : 1 ≤ a := by
    rw [ha_eq]
    have hmreal : (2 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hm
    linarith
  have ha_pos : 0 < a := lt_of_lt_of_le (by norm_num) ha_ge_one
  have hcap_le :=
    shifted_all_omitted_budget_cap_sq_le_card_div_order_sub_sq χ G hm
  have hcap_le' :
      (((G.card : ℝ) * (Real.sqrt (Fintype.card F : ℝ) - 1))
            / (((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ))) ^ 2
        ≤ n ^ 2 / a ^ 2 := by
    simpa [hndef, hadef] using hcap_le
  have hreg' : 16 * m ^ 2 * n ^ 2 ≤ q := by
    simpa [hmdef, hndef, hqdef] using hreg
  have hupper_lt : n ^ 2 / a ^ 2 < q * n := by
    have ha2_ge_one : 1 ≤ a ^ 2 := by nlinarith [ha_ge_one]
    have hdiv_le : n ^ 2 / a ^ 2 ≤ n ^ 2 := by
      rw [div_le_iff₀ (by positivity : 0 < a ^ 2)]
      nlinarith [ha2_ge_one]
    have hq_lower : n ^ 2 < q * n := by
      have hq_gt_n : n < q := by
        have hlarge : n < 16 * m ^ 2 * n ^ 2 := by
          have hfactor : 1 < 16 * m ^ 2 * n := by
            nlinarith [hn_ge_one, hm_ge_two]
          calc
            n = n * 1 := by ring
            _ < n * (16 * m ^ 2 * n) := mul_lt_mul_of_pos_left hfactor hnpos
            _ = 16 * m ^ 2 * n ^ 2 := by ring
        exact lt_of_lt_of_le hlarge hreg'
      nlinarith [mul_lt_mul_of_pos_right hq_gt_n hnpos]
    exact lt_of_le_of_lt hdiv_le hq_lower
  exact lt_of_le_of_lt hcap_le' hupper_lt

/-- Regime-level `r = 1` no-go: under the R18 size regime, the exact normalized all-omitted
budget is incompatible with the `r = 1` shifted-rate lower bound. -/
theorem not_shifted_all_omitted_budget_of_rate_one_regime
    (χ : MulChar F ℂ) (G : Finset F) {T : ℝ}
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hT0 : 0 ≤ T)
    (hrate : (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T ^ 2)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) :=
  not_shifted_all_omitted_budget_of_rate_one_cap_sq_lt χ G hm hT0 hrate
    (shifted_all_omitted_budget_cap_sq_lt_rate_one_of_regime χ G hm hn hreg)

/-- Existential form of the regime-level `r = 1` no-go.  In the R18 regime there is no
nonnegative `T` that simultaneously satisfies the `r = 1` shifted-rate lower bound and the exact
all-omitted normalized budget. -/
theorem not_exists_shifted_all_omitted_rate_one_budget_regime
    (χ : MulChar F ℂ) (G : Finset F)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ ∃ T : ℝ,
      0 ≤ T ∧
      (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T ^ 2 ∧
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  rintro ⟨T, hT0, hrate, hbudget⟩
  exact not_shifted_all_omitted_budget_of_rate_one_regime χ G hm hn hT0 hrate hreg hbudget

/-- Existential `A ≤ 1` form of the regime-level `r = 1` no-go.  In the R18 regime no
nonnegative `T` can satisfy the assumed `r = 1` lower scale `q|G| ≤ T²` and any normalized
all-omitted
budget with right side `A·|G|√q`, `A ≤ 1`. -/
theorem not_exists_shifted_all_omitted_rate_one_budget_A_le_one_regime
    (χ : MulChar F ℂ) (G : Finset F)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ ∃ A T : ℝ,
      0 ≤ A ∧ A ≤ 1 ∧ 0 ≤ T ∧
      (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T ^ 2 ∧
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  rintro ⟨A, T, _hA0, hA1, hT0, hrate, hbudget⟩
  exact not_shifted_all_omitted_budget_A_le_one_of_rate_one_cap_sq_lt χ G hm hT0 hA1
    hrate (shifted_all_omitted_budget_cap_sq_lt_rate_one_of_regime χ G hm hn hreg) hbudget

/-- Interface-level form of the `r = 1` all-omitted shifted no-go.  These are exactly the
`T`-nonnegativity, `r = 1` rate, and normalized-budget assumptions appearing in
`rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_normalized_budget_one`; the shifted
Wick hypothesis itself is irrelevant because the numeric side is already inconsistent. -/
theorem not_shifted_all_omitted_normalized_budget_one_inputs_r_one_regime
    (χ : MulChar F ℂ) (G D : Finset F)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ ∃ T : ℝ,
      0 ≤ T ∧
      (∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D 1) ∧
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 1 - 1) : ℝ) * (G.card : ℝ) ^ 1
        ≤ T ^ (2 * 1) ∧
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  rintro ⟨T, hT0, _hwick, hrate, hbudget⟩
  have hrate_one : (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T ^ 2 := by
    norm_num at hrate ⊢
    exact hrate
  exact not_shifted_all_omitted_budget_of_rate_one_regime χ G hm hn hT0 hrate_one hreg hbudget

/-- Interface-level `A ≤ 1` form of the `r = 1` all-omitted shifted no-go.  This matches the
dimensionless normalized endpoint before specializing `A = 1`: any `A ≤ 1` budget is stronger
than the exact normalized budget, so the same R18-regime obstruction applies. -/
theorem not_shifted_all_omitted_normalized_budget_A_inputs_r_one_regime
    (χ : MulChar F ℂ) (G D : Finset F)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ ∃ A T : ℝ,
      0 ≤ A ∧ A ≤ 1 ∧ 0 ≤ T ∧
      (∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D 1) ∧
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 1 - 1) : ℝ) * (G.card : ℝ) ^ 1
        ≤ T ^ (2 * 1) ∧
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  rintro ⟨A, T, _hA0, hA1, hT0, _hwick, hrate, hbudgetA⟩
  have hbudget_one :
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
    have hscale_nonneg : 0 ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
      positivity
    have hA_scale :
        A * ((G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ))
          ≤ 1 * ((G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ)) :=
      mul_le_mul_of_nonneg_right hA1 hscale_nonneg
    nlinarith [hbudgetA, hA_scale]
  have hrate_one : (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T ^ 2 := by
    norm_num at hrate ⊢
    exact hrate
  exact not_shifted_all_omitted_budget_of_rate_one_regime χ G hm hn hT0 hrate_one hreg
    hbudget_one

/-- Raw-endpoint-shaped no-go for the `r = 1`, all-omitted, normalized shifted route.  The
parameters `ψ`, `hψ`, and `hGD` are included so this theorem is easy to find from attempts to use
`rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_normalized_budget_A_le_one`; they are
not needed for the numeric contradiction. -/
theorem not_rawFourthMoment_shifted_all_omitted_normalized_A_inputs_r_one_regime
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (_hψ : ψ.IsPrimitive)
    (G D : Finset F) (_hGD : G ⊆ D)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ ∃ A T : ℝ,
      0 ≤ A ∧ A ≤ 1 ∧ 0 ≤ T ∧
      (∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D 1) ∧
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 1 - 1) : ℝ) * (G.card : ℝ) ^ 1
        ≤ T ^ (2 * 1) ∧
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) :=
  not_shifted_all_omitted_normalized_budget_A_inputs_r_one_regime χ G D hm hn hreg

/-- Raw-endpoint-shaped no-go for the exact `A = 1` shifted all-omitted normalized route. -/
theorem not_rawFourthMoment_shifted_all_omitted_normalized_one_inputs_r_one_regime
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (_hψ : ψ.IsPrimitive)
    (G D : Finset F) (_hGD : G ⊆ D)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ ∃ T : ℝ,
      0 ≤ T ∧
      (∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D 1) ∧
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 1 - 1) : ℝ) * (G.card : ℝ) ^ 1
        ≤ T ^ (2 * 1) ∧
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) :=
  not_shifted_all_omitted_normalized_budget_one_inputs_r_one_regime χ G D hm hn hreg

/-- Predicate-free numeric no-go for the direct pointwise all-omitted route at the assumed
`sqrt(q * |G|)` scale.  In the R18 regime, no `A ≤ 1` normalized budget can coexist with the
lower scale `q|G| ≤ T²`.  (Caveat: `sqrt(q|G|)` is NOT the natural second-moment scale — it exceeds
the trivial bound `‖T_χ‖ ≤ |G|` once `q > |G|`; the RMS scale is `√|G|`, see
`sum_norm_sq_twistedThinSum`.  So this no-go is about a hypothesis that can only hold when
`q ≤ |G|`.) -/
theorem not_exists_pointwise_all_omitted_sqrt_scale_budget_A_le_one_regime
    (χ : MulChar F ℂ) (G : Finset F)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ ∃ A T : ℝ,
      0 ≤ A ∧ A ≤ 1 ∧ 0 ≤ T ∧
      (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T ^ 2 ∧
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  exact not_exists_shifted_all_omitted_rate_one_budget_A_le_one_regime χ G hm hn hreg

/-- Interface-level `A ≤ 1` no-go for the direct pointwise all-omitted route at the natural
`sqrt(q * |G|)` scale.  The pointwise upper-bound hypothesis does not enter the contradiction:
once `T` is at least the `sqrt(q|G|)` scale (which is above the trivial bound `|G|`, not the RMS
scale `√|G|`), the same normalized-budget obstruction as in
the shifted `r = 1` route applies in the R18 regime. -/
theorem not_pointwise_all_omitted_normalized_budget_A_inputs_sqrt_scale_regime
    (χ : MulChar F ℂ) (G D : Finset F)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ ∃ A T : ℝ,
      0 ≤ A ∧ A ≤ 1 ∧ 0 ≤ T ∧
      (∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ chiFamily χ, ‖twistedThinSum χ' G s₀‖ ≤ T) ∧
      (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T ^ 2 ∧
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  rintro ⟨A, T, hA0, hA1, hT0, _hpointwise, hrate, hbudgetA⟩
  exact not_exists_pointwise_all_omitted_sqrt_scale_budget_A_le_one_regime χ G hm hn hreg
    ⟨A, T, hA0, hA1, hT0, hrate, hbudgetA⟩

/-- Raw-endpoint-shaped no-go for the direct pointwise all-omitted normalized route at the
assumed `sqrt(q * |G|)` scale (not the RMS scale `√|G|`).  The additive character data is included
to mirror attempts to feed
the hypotheses into the raw fourth-moment endpoint; the contradiction is purely numeric. -/
theorem not_rawFourthMoment_pointwise_all_omitted_normalized_A_inputs_sqrt_scale_regime
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (_hψ : ψ.IsPrimitive)
    (G D : Finset F) (_hGD : G ⊆ D)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ ∃ A T : ℝ,
      0 ≤ A ∧ A ≤ 1 ∧ 0 ≤ T ∧
      (∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ chiFamily χ, ‖twistedThinSum χ' G s₀‖ ≤ T) ∧
      (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T ^ 2 ∧
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ A * (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) :=
  not_pointwise_all_omitted_normalized_budget_A_inputs_sqrt_scale_regime χ G D hm hn hreg

/-- Raw-endpoint-shaped no-go for the exact `A = 1` pointwise all-omitted normalized route. -/
theorem not_rawFourthMoment_pointwise_all_omitted_normalized_one_inputs_sqrt_scale_regime
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (_hψ : ψ.IsPrimitive)
    (G D : Finset F) (_hGD : G ⊆ D)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ¬ ∃ T : ℝ,
      0 ≤ T ∧
      (∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ chiFamily χ, ‖twistedThinSum χ' G s₀‖ ≤ T) ∧
      (Fintype.card F : ℝ) * (G.card : ℝ) ≤ T ^ 2 ∧
      (G.card : ℝ) + ((orderOf χ - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T
        ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  rintro ⟨T, hT0, hpointwise, hrate, hbudget⟩
  exact not_exists_pointwise_all_omitted_sqrt_scale_budget_A_le_one_regime χ G hm hn hreg
    ⟨1, T, by norm_num, by norm_num, hT0, hrate, by simpa using hbudget⟩

/-- **Thin-subfamily exact-rung consumer.**  If a subfamily `Y ⊆ chiFamily χ` has its own exact
`ChiDecompositionOff` identity, then all other explicit-character inputs are discharged:
Gauss-sum sizes come from `_R19ChiDecomposition`, the fourth-moment twist from the per-character
quartic-Weil input on the full family, and `hSig` from R18 sigma-equidistribution.  This isolates
the true missing ingredient for a thinned route: proving the decomposition with the deleted
characters accounted for. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)}
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hY : Y ⊆ chiFamily χ)
    (hX : Y.Nonempty) (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (hdec : ChiDecompositionOff ψ G (Gchi χ) D Y (fun χ' => gaussSum χ' ψ) (orderOf χ))
    (hW :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) D 2 := by
  exact wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    ψ hψ G D Y (fun χ' => gaussSum χ' ψ) χ hm hn hX horder hdec
    (gaussSumSizeBound_chiSubfamily χ hψ hY)
    (quarticWeilInput_mono hY hW) hq1 hnq hn4q hreg

/-- Raw fourth-moment companion to
`wickForIncidenceAwayAt_two_of_chiSubfamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)}
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hY : Y ⊆ chiFamily χ)
    (hX : Y.Nonempty) (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (hdec : ChiDecompositionOff ψ G (Gchi χ) D Y (fun χ' => gaussSum χ' ψ) (orderOf χ))
    (hW :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D := by
  exact rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    ψ hψ G D Y (fun χ' => gaussSum χ' ψ) χ hm hn hX horder hdec
    (gaussSumSizeBound_chiSubfamily χ hψ hY)
    (quarticWeilInput_mono hY hW) hq1 hnq hn4q hreg











/-! ### Removed vacuous consumers (audit CW-B10-01/02)

* The four `r = 2` depth consumers
  `incidence_le_of_chi{Subfamily,Family}_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat` and
  `approxB_away_of_chi{Subfamily,Family}_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat`
  assumed both `hdepth : 2 = ⌈log q⌉₊` and `hreg`; `not_depth_two_of_regime` proves these are
  contradictory, so the consumers were removed.
* The six full-family exact-rung consumers `*_of_chiFamily_of_constant_le_one`,
  `*_of_chiFamily_quarticWeil_of_constant_le_one`, and
  `*_of_chiFamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat` could never fire: the gate
  fails for every admissible `Cw` (`not_chiFamily_constant_gate_of_fourthMomentTwistBound`,
  `not_chiFamily_constant_gate_of_half_le`) and the nat-order gate is refuted by
  `not_fifteen_chiFamily_card_sq_le_order`.  The thinned-subfamily `WickForIncidenceAwayAt` /
  raw-moment consumers (`*_of_chiSubfamily_*`) and the `WickAwayAtWithConstant` forms are kept.
-/

/-- **Explicit-character R19 linear-`K` depleted rung.**  For `H = Gχ`, the decomposition,
Gauss-sum size bound, `|X| ≤ m`, and Σ lower bound are discharged for `chiFamily χ`; only the
cubic quadruple-family mass bound remains as analytic input. -/
theorem r19_linearK_incidenceMomentAway_of_chiFamily
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G D : Finset F) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ D)
    {C₄ : ℝ} (hC₄ : 0 ≤ C₄)
    (hfam : FamilyQuarticCubicBound G (chiFamily χ) C₄)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    incidenceMomentAway ψ G (Gchi χ) D 2
      ≤ 32 * (C₄ + 1) * (orderOf χ : ℝ) * (Fintype.card F : ℝ)
          * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2 := by
  exact r19_linearK_rung ψ G (Gchi χ) D (chiFamily χ)
    (fun χ' => gaussSum χ' ψ) (orderOf χ) (le_trans (by norm_num) hm) hC₄
    (chiDecompositionOff_holds χ hψ hGD)
    (gaussSumSizeBound_holds χ hψ)
    hfam
    (chiFamily_card_le_order χ)
    hq1 hnq
    (hSig_of_regime hψ G hm hn hreg)

#print axioms chiFamily_card_le_order
#print axioms chiFamily_nonempty_of_two_le_order
#print axioms not_fifteen_chiFamily_card_sq_le_order
#print axioms not_fifteen_chiFamily_card_sq_le_order_real
#print axioms gaussSumSizeBound_chiSubfamily
#print axioms fourthMomentTwistBound_mono
#print axioms quarticWeilInput_mono
#print axioms fourthMomentTwistBound_chiSubfamily_of_quarticWeilInput
#print axioms chiSubfamilyResidual_full_eq_zero
#print axioms chiSubfamilyResidualVanishesOff_full
#print axioms chiSubfamily_decomposition_with_residual
#print axioms chiSubfamily_chiDecompositionOff_iff_residual_vanishes
#print axioms chiDecompositionOff_holds_of_residual_full
#print axioms norm_chiSubfamilyResidual_le_card_mul
#print axioms norm_chiSubfamilyResidual_le_card_mul_of_shifted_awayWickAt_rate
#print axioms incidenceSum_le_of_chiSubfamily_residual_bound
#print axioms incidenceSum_le_of_chiSubfamily_pointwise_bounds
#print axioms incidenceSum_le_of_chiSubfamily_shifted_omitted_rate
#print axioms incidenceMomentAway_two_mul_le_of_pointwise_order_bound
#print axioms incidenceMomentAway_two_mul_le_of_chiSubfamily_pointwise_bounds
#print axioms incidenceMomentAway_two_mul_le_of_chiSubfamily_shifted_omitted_rate
#print axioms wickAwayAtWithConstant_two_of_pointwise_order_bound
#print axioms wickAwayAtWithConstant_two_of_chiSubfamily_pointwise_bounds
#print axioms wickAwayAtWithConstant_two_of_chiSubfamily_shifted_omitted_rate
#print axioms pointwise_order_gate_of_hSig
#print axioms scale_gate_of_pointwise_fourth_scale
#print axioms pointwise_fourth_scale_of_le
#print axioms pointwise_fourth_scale_of_le_const_mul_card_sqrt
#print axioms pointwise_fourth_scale_of_le_const_mul_card_sqrt_one
#print axioms pointwise_fourth_scale_one_of_A_le_one
#print axioms rawFourthMomentWithDiagonal_of_pointwise_order_bound_gate
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_gate
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_scale_gate
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_fourth_scale
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_K_scale
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_A_scale
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_A_scale_one
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_A_le_one
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_gate
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_scale_gate
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_fourth_scale
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_K_scale
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_A_scale
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_A_scale_one
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_A_le_one
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_rates_A_le_one
#print axioms not_chiSubfamily_shifted_rates_budget_A_le_one_of_nonempty_kept_r_one_regime
#print axioms not_exists_chiSubfamily_shifted_rates_budget_A_le_one_of_nonempty_kept_r_one_regime
#print axioms not_exists_chiSubfamily_shifted_rates_budget_one_of_nonempty_kept_r_one_regime
#print axioms not_chiSubfamily_shifted_rates_A_le_one_inputs_of_nonempty_kept_r_one_regime
#print axioms not_exists_chiSubfamily_shifted_rates_A_le_one_inputs_of_nonempty_kept_r_one_regime
#print axioms not_rawFourthMoment_chiSubfamily_shifted_rates_A_le_one_inputs_r_in_one_regime
#print axioms rawFourthMomentWithDiagonal_of_chiFamily_pointwise_all_omitted_A_le_one
#print axioms rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_A_le_one
#print axioms rawFourthMomentWithDiagonal_of_chiFamily_pointwise_all_omitted_order_budget_A_le_one
#print axioms rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_order_budget_A_le_one
#print axioms
  rawFourthMomentWithDiagonal_of_chiFamily_pointwise_all_omitted_normalized_budget_A_le_one
#print axioms
  rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_normalized_budget_A_le_one
#print axioms rawFourthMomentWithDiagonal_of_chiFamily_pointwise_all_omitted_normalized_budget_one
#print axioms rawFourthMomentWithDiagonal_of_chiFamily_shifted_all_omitted_normalized_budget_one
#print axioms chiFamily_all_omitted_T_cap_of_normalized_budget_one
#print axioms chiFamily_all_omitted_T_cap_of_normalized_budget_A_le_one
#print axioms chiFamily_all_omitted_T_le_of_normalized_budget_one
#print axioms chiFamily_all_omitted_T_le_of_normalized_budget_A_le_one
#print axioms chiFamily_all_omitted_den_pos
#print axioms chiFamily_all_omitted_T_le_of_normalized_budget_one_of_two_le_order
#print axioms chiFamily_all_omitted_T_le_of_normalized_budget_A_le_one_of_two_le_order
#print axioms shifted_all_omitted_rate_le_budget_cap_pow
#print axioms shifted_all_omitted_rate_le_budget_cap_pow_of_A_le_one
#print axioms not_shifted_all_omitted_budget_of_rate_cap_lt
#print axioms not_shifted_all_omitted_budget_A_le_one_of_rate_cap_lt
#print axioms shifted_all_omitted_rate_one_le_budget_cap_sq
#print axioms shifted_all_omitted_rate_one_le_budget_cap_sq_of_A_le_one
#print axioms not_shifted_all_omitted_budget_of_rate_one_cap_sq_lt
#print axioms not_shifted_all_omitted_budget_A_le_one_of_rate_one_cap_sq_lt
#print axioms shifted_all_omitted_budget_cap_sq_le_card_div_order_sub_sq
#print axioms shifted_all_omitted_budget_cap_sq_lt_rate_one_of_regime
#print axioms not_shifted_all_omitted_budget_of_rate_one_regime
#print axioms not_exists_shifted_all_omitted_rate_one_budget_regime
#print axioms not_exists_shifted_all_omitted_rate_one_budget_A_le_one_regime
#print axioms not_shifted_all_omitted_normalized_budget_one_inputs_r_one_regime
#print axioms not_shifted_all_omitted_normalized_budget_A_inputs_r_one_regime
#print axioms not_rawFourthMoment_shifted_all_omitted_normalized_A_inputs_r_one_regime
#print axioms not_rawFourthMoment_shifted_all_omitted_normalized_one_inputs_r_one_regime
#print axioms not_exists_pointwise_all_omitted_sqrt_scale_budget_A_le_one_regime
#print axioms not_pointwise_all_omitted_normalized_budget_A_inputs_sqrt_scale_regime
#print axioms not_rawFourthMoment_pointwise_all_omitted_normalized_A_inputs_sqrt_scale_regime
#print axioms not_rawFourthMoment_pointwise_all_omitted_normalized_one_inputs_sqrt_scale_regime
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
#print axioms r19_linearK_incidenceMomentAway_of_chiFamily
#print axioms not_depth_two_of_regime
#print axioms sum_norm_sq_twistedThinSum
#print axioms norm_twistedThinSum_le_card
#print axioms card_mul_card_sub_sq_le_of_offset_bound
#print axioms sq_sub_le_const_of_fourthMomentTwistBound
#print axioms not_chiFamily_constant_gate_of_half_le
#print axioms not_chiFamily_constant_gate_of_fourthMomentTwistBound
#print axioms le_three_of_sub_one_pow_four_le
#print axioms orderOf_le_three_of_all_omitted_K_scale

end ArkLib.ProximityGap.Frontier.R19ExplicitCharacterRung
