/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.Data.CodingTheory.JohnsonBound.Basic
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.ToMathlib.InformationTheory.Hamming

/-!
# Corrected list-budget Johnson bound over finite alphabets

Adapted from ArkLib main `35ddcaa83f683011f944f58904be779495a5709a`.
The corrected factor is `(ℓ - 1) / ℓ`. The existing `JohnsonBound.Jqℓ` uses its reciprocal
and has a retained counterexample, so these definitions occupy `JohnsonBound.Corrected`.
The bound uses the native finite-alphabet `ListDecodable.Lambda` (natural-cardinality lists).
The negative-radicand case is proved by a Plotkin bound, not assumed away.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26]
-/

namespace JohnsonBound.Corrected

open Real

/-- The `q`-ary, list-`ℓ` Johnson function

  `J_{q,ℓ}(δ) = (1 - 1/q) * (1 - √(1 - q/(q-1) * (ℓ-1)/ℓ * δ))` .

Since `1 - 1/q = 1/(q/(q-1))`, the list parameter only rescales the radius, so `Jqℓ` is
defined as `J q (((ℓ-1)/ℓ) * δ)` and the whole `J` API applies to it directly;
`Jqℓ_eq_mul_one_sub_sqrt` recovers the displayed form.

The list factor `(ℓ-1)/ℓ = 1 - 1/ℓ` increases in `ℓ`, so a smaller list budget gives a
smaller radius, and `Jqℓ q ℓ δ → J q δ` as `ℓ → ∞`. The alphabet size `q` and the list
budget `ℓ` are independent parameters: `Jqℓ 2 ℓ δ` is the binary radius, `Jqℓ q 2 δ` the
list-size-two radius. -/
noncomputable def Jqℓ (q ℓ : ℚ) (δ : ℚ) : ℝ := J q (((ℓ - 1) / ℓ) * δ)

/-- The list parameter of `Jqℓ` is a rescaling of the radius: `J_{q,ℓ}(δ) = J_q(((ℓ-1)/ℓ)·δ)`.
True by definition, and stated so that consumers need not unfold `Jqℓ`. -/
lemma Jqℓ_eq_J (q ℓ δ : ℚ) : Jqℓ q ℓ δ = J q (((ℓ - 1) / ℓ) * δ) := rfl

/-- `Jqℓ` in expanded form, `(1 - 1/q) * (1 - √(1 - q/(q-1) * (ℓ-1)/ℓ * δ))`.

The hypothesis `q ≠ 0` is what makes the outer factors agree, `1 - 1/q = 1/(q/(q-1))`
failing at `q = 0` under `ℚ`-division; every coding-theory instance has `q = |Σ| ≥ 2`. -/
lemma Jqℓ_eq_mul_one_sub_sqrt {q : ℚ} (hq : q ≠ 0) (ℓ δ : ℚ) :
    Jqℓ q ℓ δ =
      ((1 - 1 / q : ℚ) : ℝ) * (1 - √((1 - q / (q - 1) * ((ℓ - 1) / ℓ) * δ : ℚ))) := by
  have h1 : (1 / (q / (q - 1)) : ℚ) = 1 - 1 / q := by
    rcases eq_or_ne q 1 with rfl | hq1
    · norm_num
    · field_simp
  have hcast : ((1 - 1 / q : ℚ) : ℝ) = 1 / ((q / (q - 1) : ℚ) : ℝ) := by
    rw [← h1]; push_cast; ring
  rw [Jqℓ_eq_J, J, hcast]
  congr 2
  push_cast
  ring_nf

end JohnsonBound.Corrected

namespace CodingTheory.Corrected

open scoped NNReal
open Code JohnsonBound ListDecodable JohnsonBound.Corrected
open Real Finset Fintype

/-- Numeric core of `johnson_card_le_ell`: with `E ≤ 1 - √(1 - x)`, `x < b ≤ D`, the Johnson
denominator `(1 - E)² - (1 - D)` is positive and `D / denominator ≤ b / (b - x)`. -/
private lemma johnson_card_aux {x b E D : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hxb : x < b)
    (hE0 : 0 ≤ E) (hE : (E : ℝ) ≤ 1 - √(1 - (x : ℝ))) (hD : b ≤ D) :
    0 < (1 - E) ^ 2 - (1 - D) ∧ D / ((1 - E) ^ 2 - (1 - D)) ≤ b / (b - x) := by
  have hs0 := sqrt_nonneg (1 - (x : ℝ))
  have hsq : 1 - x ≤ (1 - E) ^ 2 := by
    have hs2 : √(1 - (x : ℝ)) ^ 2 = 1 - x := sq_sqrt (sub_nonneg.mpr (by exact_mod_cast hx1))
    have h : ((1 - x : ℚ) : ℝ) ≤ ((1 - E) ^ 2 : ℚ) := by
      push_cast
      rw [← hs2]
      exact pow_le_pow_left₀ hs0 (by linarith) 2
    exact_mod_cast h
  have hE1 : E ≤ 1 := by exact_mod_cast (by linarith : (E : ℝ) ≤ 1)
  have hsq1 : 0 ≤ E * (2 - E) := mul_nonneg hE0 (by linarith)
  have hden : 0 < (1 - E) ^ 2 - (1 - D) := by linarith
  refine ⟨hden, ?_⟩
  have hb : 0 < b := hx0.trans_lt hxb
  rw [div_le_div_iff₀ hden (by linarith)]
  have h1 : b * (1 - (1 - E) ^ 2) ≤ b * x := mul_le_mul_of_nonneg_left (by linarith) hb.le
  have h2 : b * x ≤ D * x := mul_le_mul_of_nonneg_right hD hx0
  linarith

/-- Numeric core of the Johnson list-size bound, stated for an arbitrary finite set of
words `B` rather than for a Hamming ball in a code. -/
lemma johnson_card_le_ell {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset (Fin n → α)) (v : Fin n → α) (ℓ : ℕ) (mDist : ℕ)
    (hℓ2 : 2 ≤ ℓ) (hn_pos : 0 < n) (hα2 : 2 ≤ Fintype.card α) (hmDist1 : 1 ≤ mDist)
    (e_fact : (JohnsonBound.e B v : ℝ) ≤ Jqℓ (Fintype.card α) ℓ (mDist / n) * n)
    (d_fact : (mDist : ℚ) ≤ JohnsonBound.d B)
    (hradicand : ((Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1))
        * (((ℓ : ℚ) - 1) / (ℓ : ℚ)) * ((mDist : ℚ) / n) ≤ 1) :
    B.card ≤ ℓ := by
  have hq2 : (2 : ℚ) ≤ Fintype.card α := by exact_mod_cast hα2
  have hℓ : (2 : ℚ) ≤ ℓ := by exact_mod_cast hℓ2
  have hn : (0 : ℚ) < n := by exact_mod_cast hn_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hf : (0 : ℚ) < (Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1) :=
    div_pos (by linarith) (by linarith)
  have hfR : (0 : ℝ) < (((Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1) : ℚ) : ℝ) := by
    exact_mod_cast hf
  have hl1 : ((ℓ : ℚ) - 1) / ℓ < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hδ : (0 : ℚ) < (mDist : ℚ) / n := div_pos (by exact_mod_cast hmDist1) hn
  have hb : 0 < (Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1) * ((mDist : ℚ) / n) :=
    mul_pos hf hδ
  have hx0 : 0 ≤ (Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1)
      * (((ℓ : ℚ) - 1) / (ℓ : ℚ)) * ((mDist : ℚ) / n) :=
    mul_nonneg (mul_nonneg hf.le (div_nonneg (by linarith) (by linarith))) hδ.le
  have hxb := mul_lt_mul_of_pos_left hl1 hb
  have heB : (0 : ℚ) ≤ JohnsonBound.e B v :=
    mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _)) (by exact_mod_cast Nat.zero_le _)
  have hE :
      ((((Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1)) * JohnsonBound.e B v / n :
        ℚ) : ℝ) ≤ 1 - √(1 - (((Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1)
        * (((ℓ : ℚ) - 1) / (ℓ : ℚ)) * ((mDist : ℚ) / n) : ℚ) : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left e_fact hfR.le
    simp only [Jqℓ, J] at h
    rw [← mul_assoc, ← mul_assoc, mul_one_div_cancel hfR.ne', one_mul] at h
    rw [mul_assoc _ (((ℓ : ℚ) - 1) / (ℓ : ℚ)), Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
      div_le_iff₀ hnR, Rat.cast_mul]
    exact h
  obtain ⟨hden, hle⟩ := johnson_card_aux hx0 hradicand (by linear_combination hxb)
    (div_nonneg (mul_nonneg hf.le heB) hn.le) hE
    (b := (Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1) * ((mDist : ℚ) / n))
    (D := (Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1) * JohnsonBound.d B / n)
    (by rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right d_fact hn.le) hf.le)
  have hjb := johnson_bound (B := B) (v := v) (sub_pos.mp hden)
  have hbx : (Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1) * ((mDist : ℚ) / n) /
      ((Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1) * ((mDist : ℚ) / n) -
        (Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1) * (((ℓ : ℚ) - 1) / (ℓ : ℚ)) *
          ((mDist : ℚ) / n)) = ℓ := by
    rw [show ∀ f l δ : ℚ, f * δ - f * l * δ = f * δ * (1 - l) from fun _ _ _ ↦ by ring,
      div_mul_cancel_left₀ hb.ne', one_sub_div (by positivity), sub_sub_cancel, inv_div, div_one]
  exact_mod_cast hjb.trans (hle.trans_eq hbx)

/-- The `q`-ary Plotkin bound, in list-factor form: if the average pairwise distance of `B`
(lower-bounded by `mDist`) exceeds the Plotkin radius `1 - 1/q` by the list factor
`ℓ/(ℓ-1)` — equivalently, if the `Jqℓ` radicand is negative at `ℓ` — then `B` itself has at
most `ℓ` elements.

Obtained from the Johnson counting lemma `JohnsonBound.johnson_bound_lemma` by dropping its
nonnegative square term: with `D := q/(q-1) * d(B)/n` the counting lemma gives
`|B| * (D - 1) ≤ D`, while the hypothesis pins `D > ℓ/(ℓ-1) > 1`, hence `|B| < ℓ`. The
bound is tight: repetition codes and the `[4,2,3]` code over `𝔽₃` attain
`|B| = δ/(δ - (1 - 1/q))`. -/
lemma plotkin_card_le_ell {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset (Fin n → α)) (ℓ : ℕ) (mDist : ℕ)
    (hℓ2 : 2 ≤ ℓ) (hn_pos : 0 < n) (hα2 : 2 ≤ Fintype.card α) (hB2 : 2 ≤ B.card)
    (d_fact : (mDist : ℚ) ≤ JohnsonBound.d B)
    (hguard : 1 < ((Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1))
        * (((ℓ : ℚ) - 1) / (ℓ : ℚ)) * ((mDist : ℚ) / n)) :
    B.card ≤ ℓ := by
  obtain ⟨a⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hjb := JohnsonBound.johnson_bound_lemma (B := B) (v := fun _ => a) hn_pos hB2 hα2
  have hq2 : (2 : ℚ) ≤ (Fintype.card α : ℚ) := by exact_mod_cast hα2
  have hq1_pos : (0 : ℚ) < (Fintype.card α : ℚ) - 1 := by linarith
  have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn_pos
  have hℓQ : (2 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ2
  have hℓQ_pos : (0 : ℚ) < (ℓ : ℚ) := by linarith
  set frac : ℚ := (Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1) with hfrac_def
  have hfrac_pos : (0 : ℚ) < frac := div_pos (by linarith) hq1_pos
  set D : ℚ := frac * (JohnsonBound.d B / n) with hD_def
  -- Square term of the counting lemma dropped: `|B| · (D - 1) ≤ D`.
  have hmain : (B.card : ℚ) * (D - 1) ≤ D := by
    have hsq : (0 : ℚ) ≤ (B.card : ℚ) *
        (1 - frac * (JohnsonBound.e B (fun _ => a) / n)) ^ 2 :=
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hD_eq : frac * JohnsonBound.d B / n = D := by rw [hD_def]; ring
    rw [hD_eq] at hjb
    calc
      (B.card : ℚ) * (D - 1) ≤
          (B.card : ℚ) * (1 - frac * (JohnsonBound.e B (fun _ => a) / n)) ^ 2 +
            B.card * (D - 1) := le_add_of_nonneg_left hsq
      _ = (B.card : ℚ) *
          ((1 - frac * (JohnsonBound.e B (fun _ => a) / n)) ^ 2 - (1 - D)) := by ring
      _ ≤ D := hjb
  -- Failed guard: `D > ℓ/(ℓ-1)`, i.e. `ℓ < D · (ℓ-1)`.
  have hDgt : (ℓ : ℚ) < D * ((ℓ : ℚ) - 1) := by
    have hmd : ((mDist : ℚ) / n) ≤ JohnsonBound.d B / n := by gcongr
    have h1 : 1 < frac * (((ℓ : ℚ) - 1) / ℓ) * (JohnsonBound.d B / n) :=
      lt_of_lt_of_le hguard (mul_le_mul_of_nonneg_left hmd
        (mul_nonneg hfrac_pos.le (div_nonneg (by linarith) (by linarith))))
    calc (ℓ : ℚ) = 1 * ℓ := (one_mul _).symm
      _ < frac * (((ℓ : ℚ) - 1) / ℓ) * (JohnsonBound.d B / n) * ℓ :=
          mul_lt_mul_of_pos_right h1 hℓQ_pos
      _ = D * ((ℓ : ℚ) - 1) := by rw [hD_def]; field_simp
  -- `D > 1`, then `|B| ≤ D/(D-1) < ℓ`.
  have hD1 : (1 : ℚ) < D := by
    by_contra hD1
    have hprod_le : D * ((ℓ : ℚ) - 1) ≤ 1 * (ℓ - 1) :=
      mul_le_mul_of_nonneg_right (le_of_not_gt hD1) (by linarith : (0 : ℚ) ≤ ℓ - 1)
    exact (not_lt_of_ge (hprod_le.trans (by linarith : (1 : ℚ) * (ℓ - 1) ≤ ℓ))) hDgt
  have hD_lt : D < (ℓ : ℚ) * (D - 1) := by
    rw [← sub_pos]
    convert sub_pos.mpr hDgt using 1
    all_goals ring
  have hfinal : (B.card : ℚ) < (ℓ : ℚ) := by
    by_contra hcard
    have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt hcard) (sub_nonneg.mpr hD1.le)
    exact (not_lt_of_ge (hmul.trans hmain)) hD_lt
  exact_mod_cast hfinal.le

/-- The Johnson list-size bound in the regime where the `Jqℓ` radicand is nonnegative, so
that `J_{q,ℓ}` is a genuine Johnson radius.

`Real.sqrt` truncates negative inputs to `0`, so where the radicand is negative the radius
inflates to `1 - 1/q` and the argument below no longer applies; the conclusion still holds
there, by `plotkin_card_le_ell`. Together the two prove the unconditional
`johnson_bound_lambda_le_ell`.

The proof ports the absolute-distance Johnson bound `JohnsonBound.johnson_bound` to the
`Lambda`/`Jqℓ` form. Its `JohnsonConditionStrong` precondition holds at the `Jqℓ` boundary
because the denominator simplifies to `frac * δ_min * (1 - (ℓ-1)/ℓ) = frac * δ_min / ℓ > 0`.
An arbitrary finite index type `ι` is reindexed to `Fin n` via `hammingDist_comp_equiv`,
and the numeric core is `johnson_card_le_ell`. -/
private lemma johnson_lambda_le_ell_of_radicand
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {α : Type*} [Fintype α] [DecidableEq α]
    (C : Set (ι → α)) (ℓ : ℕ) (hℓ_ge : 2 ≤ ℓ)
    (h_radicand :
        ((Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1))
            * (((ℓ : ℚ) - 1) / (ℓ : ℚ))
            * ((Code.minDist C : ℚ) / Fintype.card ι) ≤ 1) :
    let q : ℚ := Fintype.card α
    let δ_min : ℚ := Code.minDist C / Fintype.card ι
    Lambda C (Jqℓ q ℓ δ_min) ≤ (ℓ : ℕ∞) := by
  intro q δ_min
  set n : ℕ := Fintype.card ι with hn_def
  have hn_pos : 0 < n := Fintype.card_pos
  set radius : ℝ := Jqℓ q ℓ δ_min with hradius
  refine iSup_le fun f => ?_
  set S : Set (ι → α) := closeCodewordsRel C f radius with hS
  have hSfin : S.Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card S hSfin]
  set B0 : Finset (ι → α) := hSfin.toFinset with hB0
  -- membership fact
  classical
  have hmem : ∀ x ∈ B0, x ∈ C ∧ ((hammingDist f x : ℝ) / n ≤ radius) := by
    intro x hx
    rw [hB0, Set.Finite.mem_toFinset, hS] at hx
    simp only [closeCodewordsRel, ListDecodable.relHammingBall, Set.mem_ofPred_eq] at hx
    refine ⟨hx.1, ?_⟩
    have h2 := hx.2
    unfold Code.relHammingDist at h2
    push_cast at h2
    rw [hn_def]
    exact le_of_eq_of_le (by congr!) h2
  -- want (B0.card : ℕ∞) ≤ ℓ
  suffices hcard : B0.card ≤ ℓ by exact_mod_cast hcard
  -- trivial case
  rcases le_or_gt B0.card 1 with hle1 | hgt1
  · omega
  -- main case: 2 ≤ B0.card
  · -- reindex ι ≃ Fin n
    set e : ι ≃ Fin n := (Fintype.equivFin ι) with he
    set reIdx : (ι → α) → (Fin n → α) := fun x => x ∘ e.symm with hreIdx
    have hreIdx_inj : Function.Injective reIdx := by
      intro x y h
      funext i
      have := congrFun h (e i)
      simpa [hreIdx] using this
    set B : Finset (Fin n → α) := B0.image reIdx with hB
    set v : Fin n → α := reIdx f with hv
    have hBcard : B.card = B0.card := Finset.card_image_of_injective B0 hreIdx_inj
    have hB2 : 2 ≤ B.card := by rw [hBcard]; exact hgt1
    -- q ≥ 2  (α has ≥ 2 elements since B0 has 2 distinct words)
    have hα2 : 2 ≤ Fintype.card α := by
      obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hgt1
      obtain ⟨i, hi⟩ := Function.ne_iff.mp huw
      exact Fintype.one_lt_card_iff.mpr ⟨u i, w i, hi⟩
    have hcardF : card α = card α := rfl
    -- distance fact 1: e B v ≤ radius * n  (in ℝ)
    have hBcard_pos : (0 : ℝ) < B.card := by
      rw [hBcard]; exact_mod_cast (by omega : 0 < B0.card)
    -- each element of B is within absolute distance radius*n of v
    have hdist_le : ∀ x ∈ B, (Δ₀(v, x) : ℝ) ≤ radius * n := by
      intro x hx
      rw [hB, Finset.mem_image] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      have hdist : hammingDist v (reIdx c) = hammingDist f c := by
        rw [hv, hreIdx]
        exact hammingDist_comp_equiv e.symm f c
      have hle := (hmem c hc).2
      rw [div_le_iff₀ (by exact_mod_cast hn_pos)] at hle
      calc (Δ₀(v, reIdx c) : ℝ) = (hammingDist f c : ℝ) := by rw [hdist]
        _ ≤ radius * n := hle
    have e_fact : (JohnsonBound.e B v : ℝ) ≤ radius * n := by
      simp only [JohnsonBound.e]
      push_cast
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hBcard_pos]
      calc (∑ x ∈ B, (Δ₀(v, x) : ℝ))
          ≤ ∑ x ∈ B, (radius * n) := Finset.sum_le_sum hdist_le
        _ = B.card * (radius * n) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = radius * ↑n * ↑B.card := by ring
    -- distance fact 2: minDist C ≤ d B
    have d_fact : (Code.minDist C : ℚ) ≤ JohnsonBound.d B := by
      have hmin_le : sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d }
          ≤ JohnsonBound.d B :=
        min_dist_le_d hB2
      have hminDist_lb : Code.minDist C ≤
          sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d } := by
        apply le_csInf
        · obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hB2
          exact ⟨hammingDist u w, u, hu, w, hw, huw, rfl⟩
        · rintro m ⟨u, hu, w, hw, huw, rfl⟩
          rw [hB, Finset.mem_image] at hu hw
          obtain ⟨c1, hc1, rfl⟩ := hu
          obtain ⟨c2, hc2, rfl⟩ := hw
          have hc12 : c1 ≠ c2 := fun h => huw (by rw [h])
          have hd : hammingDist (reIdx c1) (reIdx c2) = hammingDist c1 c2 := by
            rw [hreIdx]; exact hammingDist_comp_equiv e.symm c1 c2
          rw [hd]
          -- c1, c2 ∈ C distinct ⟹ minDist C ≤ hammingDist c1 c2
          apply Nat.sInf_le
          exact ⟨c1, (hmem c1 hc1).1, c2, (hmem c2 hc2).1, hc12, rfl⟩
      calc (Code.minDist C : ℚ)
          ≤ ((sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d } : ℕ) : ℚ) := by
            exact_mod_cast hminDist_lb
        _ ≤ JohnsonBound.d B := hmin_le
    -- min distance ≥ 1
    have hminDist1 : 1 ≤ Code.minDist C := by
      obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hgt1
      rw [Code.minDist]
      apply le_csInf
      · exact ⟨hammingDist u w, u, (hmem u hu).1, w, (hmem w hw).1, huw, rfl⟩
      · rintro m ⟨a, _, b, _, hab, rfl⟩
        exact hammingDist_pos.mpr hab
    -- radicand for helper (matches `h_radicand`; q = card α, δ_min = minDist/n)
    have hrad : ((Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1))
        * (((ℓ : ℚ) - 1) / (ℓ : ℚ)) * ((Code.minDist C : ℚ) / n) ≤ 1 := by
      rw [hn_def]; exact h_radicand
    have hcard_le : B.card ≤ ℓ :=
      johnson_card_le_ell B v ℓ (Code.minDist C) hℓ_ge hn_pos hα2 hminDist1
        e_fact d_fact hrad
    rw [← hBcard]; exact_mod_cast hcard_le

/-- The Johnson bound on list size: for any code `C ⊆ α^n` over a finite alphabet of size
`q` and any `ℓ ≥ 1`,

  `Lambda C (J_{q,ℓ}(δ_min C)) ≤ ℓ` ,

where `δ_min C = Code.minDist C / n` is the relative minimum distance.

No algebraic structure on the alphabet is needed: the Johnson bound is a combinatorial fact
about Hamming distance.

The proof splits into three regimes. At `ℓ = 1` the radius degenerates to
`J_{q,1}(δ) = J_q 0 = 0`, and a radius-`0` list contains at most its centre. For `ℓ ≥ 2`
with the `Jqℓ` radicand `1 - q/(q-1) * (ℓ-1)/ℓ * δ_min` nonnegative, the radius is a genuine
Johnson radius and `johnson_lambda_le_ell_of_radicand` applies. For `ℓ ≥ 2` with the
radicand negative, `Real.sqrt` truncates and the radius inflates to `1 - 1/q`, but
`δ_min` then exceeds the Plotkin radius by the list factor, so `plotkin_card_le_ell` bounds
the whole code by `ℓ` and the conclusion holds at every radius.

The hypothesis `1 ≤ ℓ` is not removable: `ℚ`-division gives `Jqℓ q 0 δ = J q 0 = 0`, while
`Lambda C 0 ≥ 1` for every nonempty `C`. -/
theorem johnson_bound_lambda_le_ell
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {α : Type*} [Fintype α] [DecidableEq α]
    (C : Set (ι → α)) (ℓ : ℕ) (hℓ_ge : 1 ≤ ℓ) :
    let q : ℚ := Fintype.card α
    let δ_min : ℚ := Code.minDist C / Fintype.card ι
    Lambda C (Jqℓ q ℓ δ_min) ≤ (ℓ : ℕ∞) := by
  intro q δ_min
  classical
  set n : ℕ := Fintype.card ι with hn_def
  have hn_pos : 0 < n := Fintype.card_pos
  rcases (show ℓ = 1 ∨ 2 ≤ ℓ by omega) with rfl | hℓ2
  · -- `ℓ = 1`: the radius degenerates to `J_q(0) = 0`, and a radius-0 list contains at
    -- most the centre itself.
    have h0 : Jqℓ q 1 δ_min = 0 := by
      norm_num [Jqℓ, JohnsonBound.J]
    refine iSup_le fun f => ?_
    have hsub : closeCodewordsRel C f (Jqℓ q ((1 : ℕ) : ℚ) δ_min) ⊆ {f} := by
      intro c hc
      have h2 := hc.2
      simp only [ListDecodable.relHammingBall, Set.mem_ofPred_eq] at h2
      rw [show Jqℓ q ((1 : ℕ) : ℚ) δ_min = 0 by exact_mod_cast h0] at h2
      -- `closeCodewordsRel` bakes in a classical `DecidableEq α`, distinct from the section
      -- instance; every step below is instance-agnostic (the instance flows out of `h2`).
      have h3 := le_antisymm h2 (by positivity)
      have h3' := NNRat.cast_eq_zero.mp h3
      unfold Code.relHammingDist at h3'
      rw [div_eq_zero_iff] at h3'
      rcases h3' with h | h
      · refine Set.mem_singleton_iff.mpr (hammingDist_eq_zero.mp ?_).symm
        have h' := Nat.cast_eq_zero.mp h
        convert h' using 2
      · exact absurd h (by exact_mod_cast (Fintype.card_pos (α := ι)).ne')
    have hncard : (closeCodewordsRel C f (Jqℓ q ((1 : ℕ) : ℚ) δ_min)).ncard ≤ 1 := by
      simpa using Set.ncard_le_ncard hsub (Set.finite_singleton f)
    exact_mod_cast hncard
  rcases le_or_gt ((q / (q - 1)) * (((ℓ:ℚ) - 1) / ℓ) * δ_min) 1 with hrad | hguard
  · exact johnson_lambda_le_ell_of_radicand C ℓ hℓ2 hrad
  · -- Plotkin corner: the *whole code* has at most `ℓ` words, so any radius is covered.
    have hCfin : C.Finite := Set.toFinite _
    refine le_trans (Lambda_le_ncard _ hCfin) ?_
    rcases le_or_gt C.ncard 1 with hle1 | hgt1
    · exact_mod_cast le_trans hle1 (by omega : 1 ≤ ℓ)
    · set eqv : ι ≃ Fin n := Fintype.equivFin ι with heqv
      set reIdx : (ι → α) → (Fin n → α) := fun x => x ∘ eqv.symm with hreIdx
      have hreIdx_inj : Function.Injective reIdx := by
        intro x y h; funext i; simpa [hreIdx] using congrFun h (eqv i)
      set B : Finset (Fin n → α) := hCfin.toFinset.image reIdx with hB
      have hBcard : B.card = C.ncard := by
        rw [hB, Finset.card_image_of_injective _ hreIdx_inj, Set.ncard_eq_toFinset_card _ hCfin]
      have hB2 : 2 ≤ B.card := by omega
      have hα2 : 2 ≤ Fintype.card α := by
        obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hB2
        obtain ⟨i, hi⟩ := Function.ne_iff.mp huw
        exact Fintype.one_lt_card_iff.mpr ⟨u i, w i, hi⟩
      have d_fact : (Code.minDist C : ℚ) ≤ JohnsonBound.d B := by
        have hmin_le : sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d }
            ≤ JohnsonBound.d B := min_dist_le_d hB2
        have hminDist_lb : Code.minDist C ≤
            sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d } := by
          apply le_csInf
          · obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hB2
            exact ⟨hammingDist u w, u, hu, w, hw, huw, rfl⟩
          · rintro m ⟨u, hu, w, hw, huw, rfl⟩
            rw [hB, Finset.mem_image] at hu hw
            obtain ⟨c1, hc1, rfl⟩ := hu
            obtain ⟨c2, hc2, rfl⟩ := hw
            have hc12 : c1 ≠ c2 := fun h => huw (by rw [h])
            rw [show hammingDist (reIdx c1) (reIdx c2) = hammingDist c1 c2 from
              hammingDist_comp_equiv eqv.symm c1 c2]
            exact Nat.sInf_le ⟨c1, hCfin.mem_toFinset.mp hc1, c2, hCfin.mem_toFinset.mp hc2,
              hc12, rfl⟩
        calc (Code.minDist C : ℚ)
            ≤ ((sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d } : ℕ) : ℚ) := by
              exact_mod_cast hminDist_lb
          _ ≤ JohnsonBound.d B := hmin_le
      have hcard_le : B.card ≤ ℓ :=
        plotkin_card_le_ell B ℓ (Code.minDist C) hℓ2 hn_pos hα2 hB2 d_fact (by
          simpa [q, δ_min, hn_def] using hguard)
      rw [← hBcard]; exact_mod_cast hcard_le

end CodingTheory.Corrected
