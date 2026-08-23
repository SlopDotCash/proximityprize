/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# AGL23 list-decoding-capacity barrier helpers

Small standalone helpers toward the [AGL23] alphabet-size barrier (ABF26 §T3.10). This file
proves the pigeonhole core `restriction_image_card_le` (the number of distinct restrictions of a
finite set of words to a coordinate subset `I` is at most `|F|^|I|`) and the analytic descent
step `descent` (from `2^(c·n) ≤ q^(η·n)` conclude the alphabet lower bound `2^(c/η) ≤ q`), with a
connector to the [ABF26 T3.10] statement shape.
-/

open Real
open ListDecodable

namespace AGL23

/-- **AGL23 pigeonhole core.** The number of distinct restrictions of a finite set of
words `ι → F` to a coordinate subset `I` is at most `|F|^|I|`. -/
theorem restriction_image_card_le {ι : Type*} {F : Type*} [Fintype F] [DecidableEq F]
    (S : Finset (ι → F)) (I : Finset ι) :
    (S.image (fun w => fun i : I => w i)).card ≤ Fintype.card F ^ I.card := by
  classical
  have hsub : S.image (fun w => fun i : I => w i) ⊆ (Finset.univ : Finset (I → F)) :=
    fun x _ => Finset.mem_univ x
  calc (S.image (fun w => fun i : I => w i)).card
      ≤ (Finset.univ : Finset (I → F)).card := Finset.card_le_card hsub
    _ = Fintype.card (I → F) := by rw [Finset.card_univ]
    _ = Fintype.card F ^ I.card := by rw [Fintype.card_fun, Fintype.card_coe]

/-- **AGL23 descent step.** From the counting inequality `2^(c·n) ≤ q^(η·n)` (`n,η > 0`)
conclude the alphabet lower bound `2^(c/η) ≤ q`: the final `(η·n)`-th-root step of
[AGL23] Theorem 1.1. -/
theorem descent (q : ℝ) (n η c : ℝ)
    (hq : 0 ≤ q) (hn : 0 < n) (hη : 0 < η)
    (hineq : (2 : ℝ) ^ (c * n) ≤ q ^ (η * n)) :
    (2 : ℝ) ^ (c / η) ≤ q := by
  have hηn : 0 < η * n := mul_pos hη hn
  have h2pos : (0:ℝ) < 2 ^ (c * n) := Real.rpow_pos_of_pos (by norm_num) _
  have hmono := Real.rpow_le_rpow h2pos.le hineq (le_of_lt (inv_pos.mpr hηn))
  rw [← Real.rpow_mul hq, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)] at hmono
  rw [mul_inv_cancel₀ (ne_of_gt hηn), Real.rpow_one] at hmono
  have hexp : c * n * (η * n)⁻¹ = c / η := by rw [mul_inv]; field_simp
  rwa [hexp] at hmono

/-- **AGL23 alphabet-barrier reduction (arithmetic spine).** The load-bearing
arithmetic+pigeonhole core of [AGL23 Thm 1.1] / [ABF26 T3.10], isolated from the two
genuinely-external combinatorial constructions ([AGL23] Lemma 4.1 subcode-with-distance
and Lemma 4.2 large set family with bounded `W`-wise unions). Given their conclusions —
a pigeonhole window `I₀` with `|I₀| ≤ 4·ε·n`, a finite codeword set `S`, a family `ℱ`
with `2^(c·n) ≤ |ℱ|`, and an injective realization of `ℱ` as `I₀`-restrictions of `S` —
we derive the alphabet lower bound `q ≥ 2^((c/4)/ε)` (so [ABF26 T3.10]'s constant is
`α = c/4`). -/
theorem alphabet_barrier_reduction
    {ι : Type*} {F : Type*} [Fintype F] [DecidableEq F]
    (S : Finset (ι → F)) (I₀ : Finset ι) (Fam : Finset (I₀ → F))
    (n ε c : ℝ) (hn : 0 < n) (hε : 0 < ε)
    (hI₀ : (I₀.card : ℝ) ≤ 4 * ε * n)
    (hq1 : (1 : ℝ) ≤ Fintype.card F)
    (hFam_lower : (2 : ℝ) ^ (c * n) ≤ (Fam.card : ℝ))
    (hrealize : Fam ⊆ S.image (fun w => fun i : I₀ => w i)) :
    (2 : ℝ) ^ ((c / 4) / ε) ≤ (Fintype.card F : ℝ) := by
  classical
  have hpigeon_nat : Fam.card ≤ Fintype.card F ^ I₀.card :=
    le_trans (Finset.card_le_card hrealize) (restriction_image_card_le S I₀)
  have hpigeon : (Fam.card : ℝ) ≤ (Fintype.card F : ℝ) ^ (I₀.card : ℝ) := by
    have h : (Fam.card : ℝ) ≤ ((Fintype.card F ^ I₀.card : ℕ) : ℝ) := by exact_mod_cast hpigeon_nat
    rwa [Nat.cast_pow, ← Real.rpow_natCast (Fintype.card F : ℝ) I₀.card] at h
  have hexp_mono : (Fintype.card F : ℝ) ^ (I₀.card : ℝ)
      ≤ (Fintype.card F : ℝ) ^ (4 * ε * n) :=
    Real.rpow_le_rpow_of_exponent_le hq1 hI₀
  have hchain : (2 : ℝ) ^ (c * n) ≤ (Fintype.card F : ℝ) ^ (4 * ε * n) :=
    le_trans hFam_lower (le_trans hpigeon hexp_mono)
  have hq0 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := le_trans (by norm_num) hq1
  have h4ε : (0 : ℝ) < 4 * ε := by positivity
  have hform : (4 * ε) * n = 4 * ε * n := by ring
  have hdesc := descent (Fintype.card F : ℝ) n (4 * ε) c hq0 hn h4ε (by rw [hform]; exact hchain)
  have hceq : c / (4 * ε) = (c / 4) / ε := (div_div c 4 ε).symm
  rwa [hceq] at hdesc

/-! ### Connector to the [ABF26 T3.10] statement shape.

The remaining gap — the entire [AGL23] §4 combinatorial extraction (Lemma 4.1 + Lemma 4.2
+ the §3.3 pigeonhole search that manufactures `(S, I₀, Fam)` from the list-decodability
hypothesis) — is captured EXACTLY by `AGL23CountingExtraction` below. It asserts the
single AGL23 counting inequality `2^(c·n) ≤ q^(4·η·n)` for codes satisfying the
list-decodability hypothesis at the near-optimal radius. Everything *after* the counting
inequality (the descent to `|F| ≥ 2^(α/η)`, including the `∃α>0 ∀η ∃n₀` packaging) is
proved here. This pins the gap to precisely the unformalized AGL23 counting bound. -/

/-- The AGL23 counting inequality, as a hypothesis bundle for fixed `(ℓ, ρ)`. For some
constant `c > 0` and for every slack `η > 0` there is a threshold `n₀` so that every
code over `F`, of length `≥ n₀`, rate `≥ ρ`, list-`ℓ`-decodable at the radius
`ℓ/(ℓ+1)·(1-ρ-η)`, satisfies `2^(c·|ι|) ≤ |F|^(4·η·|ι|)`. This is exactly [AGL23]'s
output after Lemma 4.1, Lemma 4.2 and the §3.3 pigeonhole — the part not yet formalized. -/
def AGL23CountingExtraction (ℓ : ℕ) (ρ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ,
      ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
        {F : Type} [Field F] [Fintype F] [DecidableEq F]
        (C : Submodule F (ι → F)),
        n₀ ≤ Fintype.card ι →
        (Module.finrank F C : ℝ) ≥ ρ * Fintype.card ι →
        Lambda ((C : Set (ι → F))) ((ℓ : ℝ) / (ℓ + 1) * (1 - ρ - η)) ≤ (ℓ : ℕ∞) →
        (2 : ℝ) ^ (c * Fintype.card ι) ≤
          (Fintype.card F : ℝ) ^ (4 * η * Fintype.card ι)

/-- **[ABF26 T3.10] modulo the AGL23 counting extraction.** Given the precisely-isolated
remaining gap `AGL23CountingExtraction ℓ ρ`, the full large-alphabet barrier statement
(the exact conclusion of `large_alphabet_barrier_bdg24_agl23`) follows, with the explicit
constant `α = c/4`. The proof is the `descent` root-extraction applied uniformly. -/
theorem large_alphabet_barrier_of_counting
    (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ) (ρ : ℝ) (_hρ_pos : 0 < ρ) (_hρ_lt : ρ < 1)
    (hext : AGL23CountingExtraction ℓ ρ) :
    ∃ α : ℝ, 0 < α ∧
      ∀ (η : ℝ), 0 < η →
        ∃ n₀ : ℕ,
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F]
            (C : Submodule F (ι → F)),
            n₀ ≤ Fintype.card ι →
            (Module.finrank F C : ℝ) ≥ ρ * Fintype.card ι →
            Lambda ((C : Set (ι → F))) ((ℓ : ℝ) / (ℓ + 1) * (1 - ρ - η)) ≤ (ℓ : ℕ∞) →
            (Fintype.card F : ℝ) ≥ (2 : ℝ) ^ (α / η) := by
  obtain ⟨c, hc_pos, hcount⟩ := hext
  refine ⟨c / 4, by positivity, ?_⟩
  intro η hη
  obtain ⟨n₀, hn₀⟩ := hcount η hη
  refine ⟨max n₀ 1, ?_⟩
  intro ι _ _ _ F _ _ _ C hn hrate hΛ
  have hn0 : n₀ ≤ Fintype.card ι := le_trans (le_max_left _ _) hn
  have hcard_pos : 0 < Fintype.card ι := by
    have : 1 ≤ Fintype.card ι := le_trans (le_max_right _ _) hn
    omega
  have hnR : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hcard_pos
  have hcnt := hn₀ C hn0 hrate hΛ
  have hq1 : (1:ℝ) ≤ (Fintype.card F : ℝ) := by
    have : 1 ≤ Fintype.card F := Fintype.card_pos
    exact_mod_cast this
  have hq0 : (0:ℝ) ≤ (Fintype.card F : ℝ) := le_trans (by norm_num) hq1
  have h4η : (0:ℝ) < 4 * η := by positivity
  have hform : (4 * η) * (Fintype.card ι : ℝ) = 4 * η * Fintype.card ι := by ring
  have hdesc := descent (Fintype.card F : ℝ) (Fintype.card ι : ℝ) (4 * η) c hq0 hnR h4η
    (by rw [hform]; exact hcnt)
  have hceq : c / (4 * η) = (c / 4) / η := (div_div c 4 η).symm
  rw [hceq] at hdesc
  exact hdesc

/-- **Non-vacuity of the reduction.** The hypothesis bundle of
`alphabet_barrier_reduction` is simultaneously satisfiable while forcing a STRICT
alphabet lower bound `q > 1` (not the trivial `q ≥ 1`), so the reduction is not a
vacuous/degenerate statement that any alphabet satisfies. Model: `ι = Fin 1`,
`F = Fin 2`, the two constant words, `c = ε = n = 1`; the family of the two
`I₀`-restrictions has size `2 = 2^(c·n)`, so the conclusion gives `q ≥ 2^(1/4) > 1`. -/
theorem reduction_nonvacuous :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (F : Type) (_ : Fintype F) (_ : DecidableEq F)
      (S : Finset (ι → F)) (I₀ : Finset ι) (Fam : Finset (I₀ → F))
      (n ε c : ℝ) (_hn : 0 < n) (_hε : 0 < ε)
      (_hI₀ : (I₀.card : ℝ) ≤ 4 * ε * n)
      (_hq1 : (1 : ℝ) ≤ Fintype.card F)
      (_hFam : (2 : ℝ) ^ (c * n) ≤ (Fam.card : ℝ))
      (_hrealize : Fam ⊆ S.image (fun w => fun i : I₀ => w i)),
      (1 : ℝ) < (2 : ℝ) ^ ((c / 4) / ε) := by
  classical
  refine ⟨Fin 1, inferInstance, inferInstance, Fin 2, inferInstance, inferInstance,
    {fun _ => 0, fun _ => 1},
    Finset.univ,
    ({fun _ => 0, fun _ => 1} : Finset (Fin 1 → Fin 2)).image
      (fun w => fun i : (Finset.univ : Finset (Fin 1)) => w i),
    1, 1, 1, one_pos, one_pos, ?_, ?_, ?_, Finset.Subset.refl _, ?_⟩
  · have h1 : (Finset.univ : Finset (Fin 1)).card = 1 := by simp
    rw [h1]; norm_num
  · rw [Fintype.card_fin]; norm_num
  · have hcard : (({fun _ => 0, fun _ => 1} : Finset (Fin 1 → Fin 2)).image
        (fun w => fun i : (Finset.univ : Finset (Fin 1)) => w i)).card = 2 := by
      rw [Finset.card_image_of_injOn, Finset.card_pair]
      · intro h
        have := congrFun h 0
        simp at this
      · intro a ha b hb hab
        funext i
        have := congrFun hab ⟨i, Finset.mem_univ i⟩
        simpa using this
    rw [hcard]; norm_num
  · rw [show (((1:ℝ)/4)/1) = (1:ℝ)/4 by norm_num]
    refine (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr (Or.inl ⟨by norm_num, by norm_num⟩)

end AGL23

#print axioms AGL23.restriction_image_card_le
#print axioms AGL23.descent
#print axioms AGL23.alphabet_barrier_reduction
#print axioms AGL23.large_alphabet_barrier_of_counting
#print axioms AGL23.reduction_nonvacuous
