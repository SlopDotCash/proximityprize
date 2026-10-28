/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# ABF26 T5.4 (BGKS20 Lemma 3.3): the strict-degree statement fails at `|F| = 8`

`CodingTheory.rs_epsCA_separation_bgks20` (ABF26 Theorem 5.4, [BGKS20, Lemma 3.3]) used to be
stated for the full-domain Reed-Solomon code of degree `< |F|/8`
(`ReedSolomon.code domain (|F|/8)`) with proximity-loss radius `δ_int = 1 - (1/8)^{2/3} = 3/4`.
That form is false over every field with `8` elements: there the code is the constants, and a
stack that is not jointly `3/4`-close has `8` pairwise distinct columns `(u₀ i, u₁ i)`. A scalar
`γ` makes `u₀ + γ·u₁` be `1/2`-close only if `4` of those points lie on one line of slope `-1/γ`;
two such lines for different `γ` share at most one point, so three would need `≥ 9` points.
Hence `ε_ca ≤ 2/8 < 7/8 = 1 - 1/|F|`.

The statement now uses the degree-`≤ |F|/8` code and `δ_int = 3/4 - 1/|F|`, which is what the
source proof constructs (see the docstring of `rs_epsCA_separation_bgks20`). This file keeps the
failure of the old form as a regression.

## Main results

* `epsCA_rs_one_le_two_div` — for `|L| = 8`, `ε_ca(RS[F, L, 1], 1/2, 3/4) ≤ 2/|F|`.
* `rs_epsCA_separation_strict_loss_false_of_card_eq_eight` — the old proximity-loss half fails
  whenever `|F| = |L| = 8`.
* `rs_epsCA_separation_strict_false_of_card_eq_eight` — the old two-part statement fails there.
* `nearCertainBadLine_strict_loss_false_of_card_eq_eight` — so does the issue #22
  `NearCertainBadLine` residual at the old radii.
* `exists_field_rs_epsCA_separation_strict_false` — concrete instance `F = L = GF(8)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open scoped NNReal ProbabilityTheory BigOperators
open ProximityGap Code

namespace CodingTheory.BGKS20SeparationRegime

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- `(1/8)^{1/3} = 1/2`. -/
theorem one_eighth_rpow_one_third : ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3) = 1 / 2 := by
  rw [show ((1 : ℝ) / 8) = (1 / 2) ^ (3 : ℕ) by norm_num,
    show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)

/-- `(1/8)^{2/3} = 1/4`. -/
theorem one_eighth_rpow_two_thirds : ((1 : ℝ) / 8) ^ ((2 : ℝ) / 3) = 1 / 4 := by
  rw [show ((2 : ℝ) / 3) = ((1 : ℝ) / 3) * ((2 : ℕ) : ℝ) by norm_num, Real.rpow_mul (by norm_num),
    one_eighth_rpow_one_third, Real.rpow_natCast]
  norm_num

/-- The T5.4 fold radius `1 - ρ^{1/3}` at `ρ = 1/8` is `1/2`. -/
theorem separation_fld_radius_eq : (1 - ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3)).toNNReal = 1 / 2 := by
  rw [one_eighth_rpow_one_third, show (1 : ℝ) - 1 / 2 = ((1 / 2 : ℝ≥0) : ℝ) by norm_num,
    Real.toNNReal_coe]

/-- The old T5.4 loss radius `1 - ρ^{2/3}` at `ρ = 1/8` is `3/4`. -/
theorem separation_strict_int_radius_eq : (1 - ((1 : ℝ) / 8) ^ ((2 : ℝ) / 3)).toNNReal = 3 / 4 := by
  rw [one_eighth_rpow_two_thirds, show (1 : ℝ) - 1 / 4 = ((3 / 4 : ℝ≥0) : ℝ) by norm_num,
    Real.toNNReal_coe]

/-- Codewords of `RS[F, L, 1]` (degree `< 1`) are constant. -/
theorem rs_code_one_const (domain : ι ↪ F) {c : ι → F}
    (hc : c ∈ ReedSolomon.code domain 1) (i j : ι) : c i = c j := by
  obtain ⟨p, hp, rfl⟩ := ReedSolomon.mem_code_iff_exists_polynomial.mp hc
  have hp0 : p.degree ≤ 0 := by
    have : p.degree < (1 : WithBot ℕ) := by exact_mod_cast hp
    exact Order.le_of_lt_succ this
  rw [Polynomial.eq_C_of_degree_le_zero hp0]
  simp [ReedSolomon.evalOnPoints]

/-- Three lines in distinct directions, each carrying `≥ 4` of `8` distinct points, are
impossible: two of them share at most one point. -/
theorem card_good_le_two (u0 u1 : ι → F)
    (hinj : ∀ i j, u0 i = u0 j → u1 i = u1 j → i = j)
    (hι : Fintype.card ι = 8) (G : Finset F)
    (hG : ∀ γ ∈ G, ∃ S : Finset ι, 4 ≤ S.card ∧
      ∀ i ∈ S, ∀ j ∈ S, u0 i + γ * u1 i = u0 j + γ * u1 j) :
    G.card ≤ 2 := by
  by_contra h
  push Not at h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h
  choose! S hS4 hSeq using hG
  have inter : ∀ x y, x ∈ G → y ∈ G → x ≠ y → (S x ∩ S y).card ≤ 1 := by
    intro x y hx hy hxy
    rw [Finset.card_le_one]
    intro i hi j hj
    rw [Finset.mem_inter] at hi hj
    have h1 := hSeq x hx i hi.1 j hj.1
    have h2 := hSeq y hy i hi.2 j hj.2
    have h3 : (x - y) * (u1 i - u1 j) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h) hxy
    · have e1 : u1 i = u1 j := sub_eq_zero.mp h
      have e0 : u0 i = u0 j := by rw [e1] at h1; linear_combination h1
      exact hinj i j e0 e1
  have hab' := inter a b ha hb hab
  have hac' := inter a c ha hc hac
  have hbc' := inter b c hb hc hbc
  have h1 := Finset.card_union_add_card_inter (S a) (S b)
  have h2 := Finset.card_union_add_card_inter (S a ∪ S b) (S c)
  have h3 : ((S a ∪ S b) ∩ S c).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    exact (Finset.card_union_le _ _).trans (by omega)
  have h4 := Finset.card_le_univ (S a ∪ S b ∪ S c)
  have := hS4 a ha
  have := hS4 b hb
  have := hS4 c hc
  omega

/-- `⌊(1/2)·8⌋ = 4`. -/
theorem floor_half_mul_eight : Nat.floor ((1 / 2 : ℝ≥0) * ((8 : ℕ) : ℝ≥0)) = 4 := by
  rw [show (1 / 2 : ℝ≥0) * ((8 : ℕ) : ℝ≥0) = ((4 : ℕ) : ℝ≥0) by norm_num, Nat.floor_natCast]

/-- `⌊(3/4)·8⌋ = 6`. -/
theorem floor_three_quarters_mul_eight : Nat.floor ((3 / 4 : ℝ≥0) * ((8 : ℕ) : ℝ≥0)) = 6 := by
  rw [show (3 / 4 : ℝ≥0) * ((8 : ℕ) : ℝ≥0) = ((6 : ℕ) : ℝ≥0) by norm_num, Nat.floor_natCast]

/-- Over `RS[F, L, 1]` with `|L| = 8`, a stack that is not jointly `3/4`-close has pairwise
distinct columns. -/
theorem injective_of_not_jointProximity (domain : ι ↪ F) (hι : Fintype.card ι = 8)
    (u : WordStack F (Fin 2) ι)
    (hjp : ¬ jointProximity (C := ((ReedSolomon.code domain 1 : Set (ι → F)))) (u := u) (3 / 4)) :
    ∀ i j, u 0 i = u 0 j → u 1 i = u 1 j → i = j := by
  intro i j h0 h1
  by_contra hij
  apply hjp
  unfold jointProximity
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨fun _ k => u k i, ?_, ?_⟩
  · intro k
    exact ReedSolomon.constantCode_mem_code (x := u k i) (α := domain) (n := 1)
  · rw [pairRelDist_le_iff_pairDist_le, hι, floor_three_quarters_mul_eight]
    have hsub : (Finset.univ.filter fun x => (⋈|u) x ≠ (fun (_ : ι) k => u k i) x) ⊆
        (Finset.univ.erase i).erase j := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      refine ⟨?_, ?_⟩
      · rintro rfl
        apply hx
        funext k
        fin_cases k
        · exact h0.symm
        · exact h1.symm
      · rintro rfl
        apply hx
        rfl
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by simp [Ne.symm hij]), Finset.card_erase_of_mem (by simp),
      Finset.card_univ, hι] at this
    unfold hammingDist
    omega

/-- A word `1/2`-close to `RS[F, L, 1]` with `|L| = 8` is constant on at least `4` positions. -/
theorem agree_of_close (domain : ι ↪ F) (hι : Fintype.card ι = 8) (w : ι → F)
    (h : δᵣ(w, ((ReedSolomon.code domain 1 : Set (ι → F)))) ≤ ((1 / 2 : ℝ≥0) : ENNReal)) :
    ∃ S : Finset ι, 4 ≤ S.card ∧ ∀ i ∈ S, ∀ j ∈ S, w i = w j := by
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at h
  obtain ⟨v, hv, hd⟩ := h
  rw [pairRelDist_le_iff_pairDist_le, hι, floor_half_mul_eight] at hd
  refine ⟨Finset.univ.filter fun i => w i = v i, ?_, ?_⟩
  · have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (fun i => w i = v i)
    rw [Finset.card_univ, hι] at hpart
    unfold hammingDist at hd
    simp only [ne_eq] at hd
    omega
  · intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rw [hi, hj]
    exact rs_code_one_const domain hv i j

/-- For `|L| = 8`, `ε_ca(RS[F, L, 1], 1/2, 3/4) ≤ 2/|F|`. -/
theorem epsCA_rs_one_le_two_div (domain : ι ↪ F) (hι : Fintype.card ι = 8) :
    epsCA (F := F) (A := F) ((ReedSolomon.code domain 1 : Set (ι → F))) (1 / 2) (3 / 4) ≤
      (2 : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  unfold epsCA
  refine iSup_le fun u => ?_
  split_ifs with hjp
  · exact zero_le _
  · have hinj := injective_of_not_jointProximity domain hι u hjp
    rw [prob_uniform_eq_card_filter_div_card]
    have hcard : (Finset.univ.filter fun γ : F =>
        δᵣ(u 0 + γ • u 1, ((ReedSolomon.code domain 1 : Set (ι → F)))) ≤
          ((1 / 2 : ℝ≥0) : ENNReal)).card ≤ 2 := by
      apply card_good_le_two (u 0) (u 1) hinj hι
      intro γ hγ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
      obtain ⟨S, hS, hSeq⟩ := agree_of_close domain hι _ hγ
      refine ⟨S, hS, fun i hi j hj => ?_⟩
      have := hSeq i hi j hj
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
    simp only [ENNReal.coe_natCast]
    gcongr
    exact_mod_cast hcard


/-- The old (strict-degree, `δ_int = 3/4`) proximity-loss half of ABF26 T5.4 fails whenever
`|F| = |L| = 8`. -/
theorem rs_epsCA_separation_strict_loss_false_of_card_eq_eight (domain : ι ↪ F)
    (hF : Fintype.card F = 8) (hι : Fintype.card ι = 8) :
    ¬ (epsCA (F := F) (A := F) ((ReedSolomon.code domain (Fintype.card F / 8) : Set (ι → F)))
        ((1 - ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3)).toNNReal)
        ((1 - ((1 : ℝ) / 8) ^ ((2 : ℝ) / 3)).toNNReal) ≥
      ENNReal.ofReal (1 - 1 / Fintype.card F)) := by
  intro h
  rw [separation_fld_radius_eq, separation_strict_int_radius_eq, hF] at h
  have hle := epsCA_rs_one_le_two_div (F := F) domain hι
  rw [hF] at hle
  have h2 := le_trans h hle
  rw [show ((8 : ℕ) : ℝ) = 8 by norm_num, show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num] at h2
  rw [show ((8 : ℕ) : ENNReal) = 8 by norm_num] at h2
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)] at h2
  rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_ofNat 2,
    ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h2
  norm_num at h2

/-- The old two-part ABF26 T5.4 statement (strict degree `< |F|/8`, `δ_int = 3/4`) fails whenever
`|F| = |L| = 8`. -/
theorem rs_epsCA_separation_strict_false_of_card_eq_eight (domain : ι ↪ F)
    (hF : Fintype.card F = 8) (hι : Fintype.card ι = 8) :
    ¬ ((epsCA (F := F) (A := F) ((ReedSolomon.code domain (Fintype.card F / 8) : Set (ι → F)))
        ((1 - ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3)).toNNReal)
        ((1 - ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3)).toNNReal) ≥
      ENNReal.ofReal (1 - 1 / Fintype.card F)) ∧
      (epsCA (F := F) (A := F) ((ReedSolomon.code domain (Fintype.card F / 8) : Set (ι → F)))
        ((1 - ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3)).toNNReal)
        ((1 - ((1 : ℝ) / 8) ^ ((2 : ℝ) / 3)).toNNReal) ≥
      ENNReal.ofReal (1 - 1 / Fintype.card F))) := fun h =>
  rs_epsCA_separation_strict_loss_false_of_card_eq_eight domain hF hι h.2

/-- The issue #22 `NearCertainBadLine` residual at the old code and radii is false whenever
`|F| = |L| = 8`. -/
theorem nearCertainBadLine_strict_loss_false_of_card_eq_eight (domain : ι ↪ F)
    (hF : Fintype.card F = 8) (hι : Fintype.card ι = 8) :
    ¬ Bridge.NearCertainBadLine (F := F)
        ((ReedSolomon.code domain (Fintype.card F / 8) : Set (ι → F)))
        ((1 - ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3)).toNNReal)
        ((1 - ((1 : ℝ) / 8) ^ ((2 : ℝ) / 3)).toNNReal) := fun h =>
  rs_epsCA_separation_strict_loss_false_of_card_eq_eight domain hF hι
    (Bridge.epsCA_separation_bridge_of_residual _ _ _ h)

/-- Concrete instance: over `F = L = GF(8)` (characteristic `2`) the old form of ABF26 T5.4
fails. -/
theorem exists_field_rs_epsCA_separation_strict_false :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (_ : CharP F 2),
      Fintype.card F = 8 ∧
      ¬ ((epsCA (F := F) (A := F)
          ((ReedSolomon.code (Function.Embedding.refl F) (Fintype.card F / 8) : Set (F → F)))
          ((1 - ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3)).toNNReal)
          ((1 - ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3)).toNNReal) ≥
        ENNReal.ofReal (1 - 1 / Fintype.card F)) ∧
        (epsCA (F := F) (A := F)
          ((ReedSolomon.code (Function.Embedding.refl F) (Fintype.card F / 8) : Set (F → F)))
          ((1 - ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3)).toNNReal)
          ((1 - ((1 : ℝ) / 8) ^ ((2 : ℝ) / 3)).toNNReal) ≥
        ENNReal.ofReal (1 - 1 / Fintype.card F))) := by
  letI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  letI : DecidableEq (GaloisField 2 3) := Classical.decEq _
  have hcard : Fintype.card (GaloisField 2 3) = 8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]; norm_num
  exact ⟨GaloisField 2 3, inferInstance, inferInstance, inferInstance, inferInstance, hcard,
    rs_epsCA_separation_strict_false_of_card_eq_eight _ hcard hcard⟩

#print axioms epsCA_rs_one_le_two_div
#print axioms rs_epsCA_separation_strict_loss_false_of_card_eq_eight
#print axioms rs_epsCA_separation_strict_false_of_card_eq_eight
#print axioms nearCertainBadLine_strict_loss_false_of_card_eq_eight
#print axioms exists_field_rs_epsCA_separation_strict_false

end CodingTheory.BGKS20SeparationRegime
