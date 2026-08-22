/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS4Depth3PatternDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E3StrataCharZero
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R53Depth3ExcessHeadroom

/-!
# LANE FS5 (#466, Fable session 2026-07-09): THE TRIVIAL COUNT IS THE CLOSED FORM —
  `trivialCount m = negSymCount G 6 = 15n³ − 45n² + 40n`, making the depth-3 excess
  decomposition FULLY UNCONDITIONAL

FS4 proved `addEnergy3 G = trivialCount m + wraparoundExcess ζ m` with `trivialCount`
field-free.  The swarm's E3 strata arc (`E3StrataCharZero.negSymCount_six_closed`) proved the
EXACT count of antipodally count-balanced 6-tuples over any negation-closed `G`:
`negSymCount G 6 = 15|G|³ − 45|G|² + 40|G|`.  This brick supplies the missing identification:

* `trivialCount_eq_negSymCount` — the sign-twisted exponent bijection
  `(a₁,…,a₆) ↦ (ζ^{a₁}, ζ^{a₂}, ζ^{a₃}, −ζ^{a₄}, −ζ^{a₅}, −ζ^{a₆})` carries
  `patternPoly = 0` (coefficientwise vanishing in `ℤ[X]`, degree `< m`) exactly onto the
  count-balance condition `∀ z, #{i : cᵢ = z} = #{i : cᵢ = −z}` — coefficient `r` of the
  pattern polynomial IS the signed multiplicity `#(c = ζ^r) − #(c = −ζ^r)`.
* `addEnergy3_eq_closedForm_add_excess` — the UNCONDITIONAL exact decomposition
  `addEnergy3 G = (15n³ − 45n² + 40n) + wraparoundExcess ζ m`  (`n = 2m = |G|`).
* `depth3ExcessBounded_wraparound` — hence `Depth3ExcessBounded G (wraparoundExcess ζ m)`
  holds UNCONDITIONALLY, and (r53 weld) `wraparoundExcess ≤ 45n² − 40n ⟹` the EXACT Wick
  bound `GaussianEnergyBound G 3` (`gaussianEnergyBound_three_of_wraparound_headroom`).

With FS1 (ledger cap) + FS2/FS3 (per-pattern annihilators of dyadic height, `b = 3`) + FS4
(decomposition) + this brick, the almost-all-primes r=3 Wick rung has NO remaining
mathematical inputs — only the per-prime-family packaging (FS6).  Honest scope unchanged:
almost-all-primes at `β ≳ 6`, not the per-prime prize rung.

Issue #466, lane FS5.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm

open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open ArkLib.ProximityGap.Frontier.E3StrataCount (negSymCount)
open ArkLib.ProximityGap.Frontier.E3StrataCharZero
open ArkLib.ProximityGap.Frontier.R53Depth3ExcessHeadroom
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound

open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

section Setup

variable {ζ : F} {m : ℕ}

/-- `ζ ≠ 0` for a primitive root of positive order. -/
theorem zeta_ne_zero (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) : ζ ≠ 0 := by
  intro h
  have := hprim.pow_eq_one
  rw [h, zero_pow (by omega : 2 * m ≠ 0)] at this
  exact zero_ne_one this

/-- Characteristic is not 2 when a primitive `2m`-th root exists (`m ≥ 1`). -/
theorem two_ne_zero_of_prim (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    (2 : F) ≠ 0 := by
  intro h2
  have hneg : (-1 : F) = 1 := by linear_combination -h2
  have hζm : ζ ^ m = 1 := by
    have hsq : ζ ^ m * ζ ^ m = 1 := by
      rw [← pow_add, show m + m = 2 * m by ring]
      exact hprim.pow_eq_one
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact h
    · rw [h, hneg]
  exact hprim.pow_ne_one_of_pos_of_lt hm.ne' (by omega) hζm

/-- `ζ^m = −1`. -/
theorem zeta_pow_m (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) : ζ ^ m = -1 := by
  have hsq : ζ ^ m * ζ ^ m = 1 := by
    rw [← pow_add, show m + m = 2 * m by ring]
    exact hprim.pow_eq_one
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd h (hprim.pow_ne_one_of_pos_of_lt hm.ne' (by omega))
  · exact h

/-- Power injectivity as an iff, below `2m`. -/
theorem pow_eq_pow_iff (hprim : IsPrimitiveRoot ζ (2 * m)) {a b : ℕ}
    (ha : a < 2 * m) (hb : b < 2 * m) : ζ ^ a = ζ ^ b ↔ a = b :=
  ⟨fun h => hprim.pow_inj ha hb h, fun h => by rw [h]⟩

/-- The negated power: `−ζ^r = ζ^{r+m}` for `r < m`. -/
theorem neg_pow_eq (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) {r : ℕ} :
    -ζ ^ r = ζ ^ (r + m) := by
  rw [pow_add, zeta_pow_m hm hprim]
  ring

/-- The subgroup as an image. -/
abbrev Gset (ζ : F) (m : ℕ) : Finset F := (range (2 * m)).image (ζ ^ ·)

theorem Gset_neg_closed (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    ∀ z ∈ Gset ζ m, -z ∈ Gset ζ m := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
  rw [mem_range] at ha
  by_cases h : a < m
  · refine Finset.mem_image.mpr ⟨a + m, ?_, ?_⟩
    · rw [mem_range]; omega
    · rw [← neg_pow_eq hm hprim]
  · refine Finset.mem_image.mpr ⟨a - m, ?_, ?_⟩
    · rw [mem_range]; omega
    · have : -ζ ^ (a - m) = ζ ^ (a - m + m) := neg_pow_eq hm hprim
      have hh : a - m + m = a := by omega
      rw [hh] at this
      rw [← this, neg_neg]

theorem zero_notMem_Gset (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    (0 : F) ∉ Gset ζ m := by
  intro h
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
  exact pow_ne_zero a (zeta_ne_zero hm hprim) ha

theorem Gset_card (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    (Gset ζ m).card = 2 * m := by
  rw [Finset.card_image_of_injOn, card_range]
  intro x hx y hy hxy
  exact hprim.pow_inj (mem_range.mp hx) (mem_range.mp hy) hxy

end Setup

section Bijection

variable {ζ : F} {m : ℕ}

/-- The sign-twisted value vector of an exponent sextuple. -/
noncomputable def cvec (ζ : F) (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Fin 6 → F :=
  ![ζ ^ t.1, ζ ^ t.2.1, ζ ^ t.2.2.1,
    -ζ ^ t.2.2.2.1, -ζ ^ t.2.2.2.2.1, -ζ ^ t.2.2.2.2.2]

@[simp] theorem cvec_0 (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : cvec ζ t 0 = ζ ^ t.1 := rfl
@[simp] theorem cvec_1 (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : cvec ζ t 1 = ζ ^ t.2.1 := rfl
@[simp] theorem cvec_2 (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : cvec ζ t 2 = ζ ^ t.2.2.1 := rfl
@[simp] theorem cvec_3 (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : cvec ζ t 3 = -ζ ^ t.2.2.2.1 := rfl
@[simp] theorem cvec_4 (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : cvec ζ t 4 = -ζ ^ t.2.2.2.2.1 := rfl
@[simp] theorem cvec_5 (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : cvec ζ t 5 = -ζ ^ t.2.2.2.2.2 := rfl

/-- **The coefficient–multiplicity identity**: for `r < m`, the `r`-th coefficient of the
pattern polynomial is the signed multiplicity of `±ζ^r` in the value vector. -/
theorem coeff_pp_eq_count (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (ht : t ∈ tupleSet (2 * m)) {r : ℕ} (hr : r < m) :
    (pp m t).coeff r
      = ((univ.filter (fun i => cvec ζ t i = ζ ^ r)).card : ℤ)
        - ((univ.filter (fun i => cvec ζ t i = -ζ ^ r)).card : ℤ) := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := t
  simp only [tupleSet, Finset.mem_product, mem_range] at ht
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := ht
  -- per-item helper: the signed indicator equals the monomF coefficient
  have item : ∀ a : ℕ, a < 2 * m →
      (monomF m a).coeff r
        = ((if ζ ^ a = ζ ^ r then (1 : ℤ) else 0)
            - (if ζ ^ a = -ζ ^ r then (1 : ℤ) else 0)) := by
    intro a ha
    have hpow1 : (ζ ^ a = ζ ^ r) ↔ a = r := pow_eq_pow_iff hprim ha (by omega)
    have hpow2 : (ζ ^ a = -ζ ^ r) ↔ a = r + m := by
      rw [neg_pow_eq hm hprim]
      exact pow_eq_pow_iff hprim ha (by omega)
    simp only [hpow1, hpow2]
    unfold monomF
    by_cases hcase : a < m
    · rw [if_pos hcase, coeff_X_pow]
      by_cases har : a = r
      · rw [if_pos har.symm, if_pos har, if_neg (by omega)]; ring
      · rw [if_neg (fun h => har h.symm), if_neg har, if_neg (by omega)]; ring
    · rw [if_neg hcase, coeff_neg, coeff_X_pow]
      by_cases har : a = r + m
      · rw [if_pos (by omega : r = a - m), if_neg (by omega), if_pos har]; ring
      · rw [if_neg (by omega : ¬ r = a - m), if_neg (by omega), if_neg har]; ring
  -- expand both sides into six explicit items
  have hcount : ∀ z : F,
      ((univ.filter (fun i => cvec ζ (a₁,a₂,a₃,a₄,a₅,a₆) i = z)).card : ℤ)
        = (if ζ ^ a₁ = z then (1:ℤ) else 0) + (if ζ ^ a₂ = z then 1 else 0)
          + (if ζ ^ a₃ = z then 1 else 0) + (if -ζ ^ a₄ = z then 1 else 0)
          + (if -ζ ^ a₅ = z then 1 else 0) + (if -ζ ^ a₆ = z then 1 else 0) := by
    intro z
    rw [Finset.card_filter]
    push_cast
    rw [Fin.sum_univ_six]
    simp only [cvec_0, cvec_1, cvec_2, cvec_3, cvec_4, cvec_5]
    push_cast
    ring
  rw [hcount (ζ ^ r), hcount (-ζ ^ r)]
  -- neg-side items: −ζ^a = ζ^r ↔ ζ^a = −ζ^r, and −ζ^a = −ζ^r ↔ ζ^a = ζ^r
  have hnegflip : ∀ a : ℕ, ((-ζ ^ a = ζ ^ r) ↔ (ζ ^ a = -ζ ^ r)) := by
    intro a
    constructor <;> intro h <;> linear_combination -h
  have hnegneg : ∀ a : ℕ, ((-ζ ^ a = -ζ ^ r) ↔ (ζ ^ a = ζ ^ r)) := by
    intro a
    constructor <;> intro h <;> linear_combination -h
  simp only [pp, patternPoly, coeff_sub, coeff_add]
  rw [item a₁ h₁, item a₂ h₂, item a₃ h₃, item a₄ h₄, item a₅ h₅, item a₆ h₆]
  simp only [hnegflip, hnegneg]
  ring

/-- **Pattern vanishing ⟺ count balance** along the bijection. -/
theorem pp_eq_zero_iff_balanced (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (ht : t ∈ tupleSet (2 * m)) :
    pp m t = 0
      ↔ ∀ z : F, (univ.filter (fun i => cvec ζ t i = z)).card
          = (univ.filter (fun i => cvec ζ t i = -z)).card := by
  have htup : ∀ i : Fin 6, ∃ a < 2 * m, (cvec ζ t i = ζ ^ a ∨ cvec ζ t i = -ζ ^ a) := by
    obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := t
    have ht' := ht
    simp only [tupleSet, Finset.mem_product, mem_range] at ht'
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := ht'
    intro i
    fin_cases i
    · exact ⟨a₁, h₁, Or.inl rfl⟩
    · exact ⟨a₂, h₂, Or.inl rfl⟩
    · exact ⟨a₃, h₃, Or.inl rfl⟩
    · exact ⟨a₄, h₄, Or.inr rfl⟩
    · exact ⟨a₅, h₅, Or.inr rfl⟩
    · exact ⟨a₆, h₆, Or.inr rfl⟩
  have key : ∀ a : ℕ, m ≤ a → ζ ^ a = -ζ ^ (a - m) := by
    intro a ham
    rw [neg_pow_eq hm hprim, show a - m + m = a by omega]
  constructor
  · -- vanishing ⟹ balance
    intro hzero z
    by_cases hzG : ∃ r < m, z = ζ ^ r ∨ z = -ζ ^ r
    · obtain ⟨r, hr, hcase⟩ := hzG
      have hkey := coeff_pp_eq_count hm hprim t ht hr
      rw [hzero, coeff_zero] at hkey
      rcases hcase with rfl | rfl
      · omega
      · rw [neg_neg]
        omega
    · -- z is not ±ζ^r for r < m: both counts are zero
      push_neg at hzG
      have hz1 : (univ.filter (fun i => cvec ζ t i = z)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _
        obtain ⟨a, ha, hcv⟩ := htup i
        intro hzi
        rcases hcv with hcv | hcv
        · -- cvec i = ζ^a; z = ζ^a: write ζ^a as ±ζ^{a mod m}
          by_cases ham : a < m
          · exact (hzG a ham).1 (by rw [← hzi, hcv])
          · have : z = -ζ ^ (a - m) := by
              rw [← hzi, hcv]
              exact key a (by omega)
            exact (hzG (a - m) (by omega)).2 this
        · by_cases ham : a < m
          · exact (hzG a ham).2 (by rw [← hzi, hcv])
          · have : z = ζ ^ (a - m) := by
              rw [← hzi, hcv, key a (by omega), neg_neg]
            exact (hzG (a - m) (by omega)).1 this
      have hz2 : (univ.filter (fun i => cvec ζ t i = -z)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _
        obtain ⟨a, ha, hcv⟩ := htup i
        intro hzi
        have hzi' : z = -(cvec ζ t i) := by linear_combination hzi
        rcases hcv with hcv | hcv
        · by_cases ham : a < m
          · exact (hzG a ham).2 (by rw [hzi', hcv])
          · have : z = ζ ^ (a - m) := by
              rw [hzi', hcv, key a (by omega), neg_neg]
            exact (hzG (a - m) (by omega)).1 this
        · by_cases ham : a < m
          · exact (hzG a ham).1 (by rw [hzi', hcv, neg_neg])
          · have : z = -ζ ^ (a - m) := by
              rw [hzi', hcv, neg_neg]
              exact key a (by omega)
            exact (hzG (a - m) (by omega)).2 this
      rw [hz1, hz2]
  · -- balance ⟹ vanishing
    intro hbal
    ext r
    rw [coeff_zero]
    by_cases hr : r < m
    · have hkey := coeff_pp_eq_count hm hprim t ht hr
      rw [hbal (ζ ^ r)] at hkey
      omega
    · -- degree < m kills high coefficients
      have hbounds := ht
      simp only [tupleSet, Finset.mem_product, mem_range] at hbounds
      have hdeg : (pp m t).natDegree < m :=
        patternPoly_natDegree_lt hm
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- **THE IDENTIFICATION.**  The field-free trivial count equals the antipodally balanced
census of the subgroup. -/
theorem trivialCount_eq_negSymCount (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    trivialCount m = negSymCount (Gset ζ m) 6 := by
  unfold trivialCount negSymCount
  refine Finset.card_bij (fun t _ => cvec ζ t) ?_ ?_ ?_
  · -- maps to
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htup, hzero⟩ := ht
    rw [Finset.mem_filter]
    constructor
    · rw [Fintype.mem_piFinset]
      have hbounds := htup
      simp only [tupleSet, Finset.mem_product, mem_range] at hbounds
      have hmemG : ∀ a : ℕ, a < 2 * m → ζ ^ a ∈ Gset ζ m := fun a ha =>
        Finset.mem_image.mpr ⟨a, mem_range.mpr ha, rfl⟩
      have hmemGneg : ∀ a : ℕ, a < 2 * m → -ζ ^ a ∈ Gset ζ m := fun a ha =>
        Gset_neg_closed hm hprim _ (hmemG a ha)
      intro i
      fin_cases i
      · exact show ζ ^ t.1 ∈ Gset ζ m from hmemG _ (by omega)
      · exact show ζ ^ t.2.1 ∈ Gset ζ m from hmemG _ (by omega)
      · exact show ζ ^ t.2.2.1 ∈ Gset ζ m from hmemG _ (by omega)
      · exact show -ζ ^ t.2.2.2.1 ∈ Gset ζ m from hmemGneg _ (by omega)
      · exact show -ζ ^ t.2.2.2.2.1 ∈ Gset ζ m from hmemGneg _ (by omega)
      · exact show -ζ ^ t.2.2.2.2.2 ∈ Gset ζ m from hmemGneg _ (by omega)
    · exact (pp_eq_zero_iff_balanced hm hprim t htup).mp hzero
  · -- injective
    intro t ht t' ht' heq
    rw [Finset.mem_filter] at ht ht'
    have hb := ht.1; have hb' := ht'.1
    simp only [tupleSet, Finset.mem_product, mem_range] at hb hb'
    obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := hb
    obtain ⟨d₁, d₂, d₃, d₄, d₅, d₆⟩ := hb'
    have e0 := congrFun heq 0
    have e1 := congrFun heq 1
    have e2 := congrFun heq 2
    have e3 := congrFun heq 3
    have e4 := congrFun heq 4
    have e5 := congrFun heq 5
    simp only [cvec_0, cvec_1, cvec_2, cvec_3, cvec_4, cvec_5] at e0 e1 e2 e3 e4 e5
    have e3' : ζ ^ t.2.2.2.1 = ζ ^ t'.2.2.2.1 := by linear_combination -e3
    have e4' : ζ ^ t.2.2.2.2.1 = ζ ^ t'.2.2.2.2.1 := by linear_combination -e4
    have e5' : ζ ^ t.2.2.2.2.2 = ζ ^ t'.2.2.2.2.2 := by linear_combination -e5
    have := hprim.pow_inj c₁ d₁ e0
    have := hprim.pow_inj c₂ d₂ e1
    have := hprim.pow_inj c₃ d₃ e2
    have := hprim.pow_inj c₄ d₄ e3'
    have := hprim.pow_inj c₅ d₅ e4'
    have := hprim.pow_inj c₆ d₆ e5'
    obtain ⟨x₁, x₂, x₃, x₄, x₅, x₆⟩ := t
    obtain ⟨y₁, y₂, y₃, y₄, y₅, y₆⟩ := t'
    simp_all
  · -- surjective
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hpi, hbal⟩ := hc
    rw [Fintype.mem_piFinset] at hpi
    have hpick : ∀ i : Fin 6, ∃ a < 2 * m, ζ ^ a = c i := by
      intro i
      obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp (hpi i)
      exact ⟨a, mem_range.mp ha, hae⟩
    have hpickneg : ∀ i : Fin 6, ∃ a < 2 * m, -ζ ^ a = c i := by
      intro i
      have : -c i ∈ Gset ζ m := Gset_neg_closed hm hprim _ (hpi i)
      obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp this
      exact ⟨a, mem_range.mp ha, by rw [hae, neg_neg]⟩
    obtain ⟨a₁, h₁, e₁⟩ := hpick 0
    obtain ⟨a₂, h₂, e₂⟩ := hpick 1
    obtain ⟨a₃, h₃, e₃⟩ := hpick 2
    obtain ⟨a₄, h₄, e₄⟩ := hpickneg 3
    obtain ⟨a₅, h₅, e₅⟩ := hpickneg 4
    obtain ⟨a₆, h₆, e₆⟩ := hpickneg 5
    refine ⟨(a₁, a₂, a₃, a₄, a₅, a₆), ?_, ?_⟩
    · have hmemT : (a₁, a₂, a₃, a₄, a₅, a₆) ∈ tupleSet (2 * m) := by
        simp only [tupleSet, Finset.mem_product, mem_range]
        exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
      have hcv : cvec ζ (a₁, a₂, a₃, a₄, a₅, a₆) = c := by
        funext i
        fin_cases i
        · exact e₁
        · exact e₂
        · exact e₃
        · exact e₄
        · exact e₅
        · exact e₆
      rw [Finset.mem_filter]
      refine ⟨hmemT, ?_⟩
      rw [pp_eq_zero_iff_balanced hm hprim _ hmemT, hcv]
      exact hbal
    · funext i
      fin_cases i
      · exact e₁
      · exact e₂
      · exact e₃
      · exact e₄
      · exact e₅
      · exact e₆

end Bijection

section Composition

variable {ζ : F} {m : ℕ}

/-- **THE UNCONDITIONAL EXACT DECOMPOSITION** (`n = 2m = |G|`):
`addEnergy3 G = (15n³ − 45n² + 40n) + wraparoundExcess`. -/
theorem addEnergy3_eq_closedForm_add_excess (hm : 0 < m)
    (hprim : IsPrimitiveRoot ζ (2 * m)) :
    (addEnergy3 (Gset ζ m) : ℤ)
      = (15 * ((2 * m : ℕ) : ℤ) ^ 3 - 45 * ((2 * m : ℕ) : ℤ) ^ 2 + 40 * ((2 * m : ℕ) : ℤ))
        + (wraparoundExcess ζ m : ℤ) := by
  have hdec := addEnergy3_eq_trivial_add_excess (F := F) hm hprim
  have hident := trivialCount_eq_negSymCount (F := F) hm hprim
  have hclosed := negSymCount_six_closed (Gset ζ m)
    (two_ne_zero_of_prim hm hprim) (zero_notMem_Gset hm hprim) (Gset_neg_closed hm hprim)
  rw [Gset_card hm hprim] at hclosed
  have : (addEnergy3 (Gset ζ m) : ℤ)
      = (negSymCount (Gset ζ m) 6 : ℤ) + (wraparoundExcess ζ m : ℤ) := by
    rw [← hident]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hdec
  rw [this, hclosed]

/-- `Depth3ExcessBounded` holds UNCONDITIONALLY with the wraparound excess as the excess. -/
theorem depth3ExcessBounded_wraparound (hm : 0 < m)
    (hprim : IsPrimitiveRoot ζ (2 * m)) :
    Depth3ExcessBounded (Gset ζ m) ((wraparoundExcess ζ m : ℝ)) := by
  unfold Depth3ExcessBounded
  have h := addEnergy3_eq_closedForm_add_excess (F := F) hm hprim
  have hcard : ((Gset ζ m).card : ℝ) = ((2 * m : ℕ) : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Gset_card hm hprim)
  rw [hcard]
  have hreal : (addEnergy3 (Gset ζ m) : ℝ)
      = (15 * ((2 * m : ℕ) : ℝ) ^ 3 - 45 * ((2 * m : ℕ) : ℝ) ^ 2 + 40 * ((2 * m : ℕ) : ℝ))
        + (wraparoundExcess ζ m : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) h
  rw [hreal]

/-- **THE UNCONDITIONAL r=3 WICK WELD.**  If the wraparound excess fits the headroom, the
exact Wick bound `GaussianEnergyBound G 3` holds — no named inputs anywhere. -/
theorem gaussianEnergyBound_three_of_wraparound_headroom {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    (hhead : (wraparoundExcess ζ m : ℝ)
      ≤ 45 * ((Gset ζ m).card : ℝ) ^ 2 - 40 * ((Gset ζ m).card : ℝ)) :
    GaussianEnergyBound (Gset ζ m) 3 :=
  gaussianEnergyBound_three_of_excess_headroom hψ (Gset ζ m)
    (depth3ExcessBounded_wraparound hm hprim) hhead

end Composition

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms coeff_pp_eq_count
#print axioms pp_eq_zero_iff_balanced
#print axioms trivialCount_eq_negSymCount
#print axioms addEnergy3_eq_closedForm_add_excess
#print axioms depth3ExcessBounded_wraparound
#print axioms gaussianEnergyBound_three_of_wraparound_headroom

end ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
