/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.ToMathlib.BKR06EndToEnd
import ArkLib.Data.CodingTheory.ListDecoding.Bounds

/-!
# ABF26 T3.12 [BKR06 Cor 2.2]: the bare front door, proven

This file discharges `CodingTheory.rs_lambda_superpoly_extension_bkr06` — previously an
external `Prop` ("genuinely external — LOWER bound") — as an in-tree theorem
`rs_lambda_superpoly_extension_bkr06_proven`, assembling the ingredient chain from
`ArkLib.ToMathlib.BKR06EndToEnd`:

* **witness sequence** `qs i := 2^{i+N+1}` (strictly monotone prime powers, shifted past
  the band threshold `N` obtained from the Archimedean property);
* **base-field glue** — `charP_of_card_eq_prime_pow` + `ZMod.algebra` view the abstract
  per-instance field `F` (`#F = 2^m`) as a `ZMod 2`-extension of degree `m`
  (`finrank_eq_of_card_eq_pow`);
* **band choice** — `bkr06_band_choice_exponent` at `L = log 2` produces cutoffs `u`, `v`
  meeting all tight-chain side conditions, the window condition, and the count comparison
  `(α−β²)·log 2·m² ≤ m·u − v²`;
* **tight count** — `bkr06_close_codewords_card_ge_tight` delivers `≥ 2^{m·u−v²}` close
  codewords in `RS[F, refl, 2^u+1]` at radius `δ = 1 − (#F)^{β−1}`;
* **window transport** — `rs_window_le_floor` + `rs_closeCodewords_ncard_mono_window`
  move the count into the bare statement's window `k = ⌊(#F)^α⌋`;
* **index transport** — `rs_closeCodewords_ncard_transport` along
  `Fintype.equivOfCardEq : ι ≃ F` relabels to the abstract index type;
* **exponent algebra** — `(#F)^{(α−β²)·log(#F)} = 2^{(α−β²)·log 2·m²} ≤ 2^{m·u−v²}`;
* **trivial regime** — for `α ≤ β²` the target is `≤ 1` and
  `rs_close_codewords_card_ge_trivial_regime` suffices at every index (no threshold).

All declarations compile `sorry`/`axiom`-free and are axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

open Polynomial ListDecodable

namespace BKR06

/-- Cast bridge: `((2^m : ℕ) : ℝ) = (2 : ℝ)^m`. -/
private lemma cast_two_pow (m : ℕ) : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by
  push_cast
  ring

/-- **Exponent algebra.**  The bare statement's count target at `q = 2^m` equals the
`rpow`-base-2 form: `(2^m : ℝ)^{(α−β²)·log (2^m)} = 2^{(α−β²)·log 2·m²}`. -/
private lemma target_exponent_eq (α β : ℝ) (m : ℕ) :
    ((2 ^ m : ℕ) : ℝ) ^ ((α - β ^ 2) * Real.log ((2 ^ m : ℕ) : ℝ)) =
      (2 : ℝ) ^ ((α - β ^ 2) * Real.log 2 * (m : ℝ) ^ 2) := by
  rw [cast_two_pow]
  rw [← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    Real.log_rpow (by norm_num : (0:ℝ) < 2)]
  ring_nf

/-- **ABF26 Theorem 3.12 [BKR06 Cor 2.2] — proven.**

The bare external front door `CodingTheory.rs_lambda_superpoly_extension_bkr06` holds:
for all `0 < α < β < 1` there is a strictly increasing sequence of prime powers
`qs i = 2^{i+N+1}` such that every field `F` of cardinality `qs i` (with any index type
`ι` of the same cardinality) admits a Reed-Solomon code `RS[F, domain, ⌊(#F)^α⌋]` and a
received word `w` whose `δ = 1 − (#F)^{β−1}`-close-codeword set has at least
`(#F)^{(α−β²)·log (#F)}` elements. -/
theorem rs_lambda_superpoly_extension_bkr06_proven
    (α β : ℝ) (hα_pos : 0 < α) (hα_lt : α < β) (hβ_lt : β < 1) :
    CodingTheory.rs_lambda_superpoly_extension_bkr06 α β hα_pos hα_lt hβ_lt := by
  unfold CodingTheory.rs_lambda_superpoly_extension_bkr06
  have hβ_pos : 0 < β := lt_trans hα_pos hα_lt
  have hα1 : α ≤ 1 := le_of_lt (lt_trans hα_lt hβ_lt)
  by_cases hreg : α ≤ β ^ 2
  · -- ## Trivial regime `α ≤ β²`: target `≤ 1`, one close codeword suffices.
    refine ⟨fun i => 2 ^ (i + 1), ?_, ?_, ?_⟩
    · intro i j hij
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · intro i
      exact Nat.prime_two.isPrimePow.pow (by omega)
    · intro i ι _ _ _ F _ _ _ hF hι
      have hcards : Fintype.card ι = Fintype.card F := by rw [hF, hι]
      set e : ι ≃ F := Fintype.equivOfCardEq hcards with he
      set kk : ℕ := Nat.floor (((2 ^ (i + 1) : ℕ) : ℝ) ^ α) with hkk
      obtain ⟨pivot, hcount⟩ :=
        rs_close_codewords_card_ge_trivial_regime (K := F) α β hreg (le_of_lt hβ_lt)
          (Function.Embedding.refl F) kk
      refine ⟨e.toEmbedding,
        (ReedSolomon.evalOnPoints (Function.Embedding.refl F) pivot) ∘ e, ?_⟩
      dsimp only
      rw [ge_iff_le]
      -- chain: target ≤ count over F (trivial regime) ≤ count over ι (transport);
      -- align the lemma instances to the goal's raw `2^(i+1)` via `hF`.
      have htrans :=
        rs_closeCodewords_ncard_transport (K := F) e kk
          (ReedSolomon.evalOnPoints (Function.Embedding.refl F) pivot)
          (1 - (Fintype.card F : ℝ) ^ (β - 1))
      rw [hF] at hcount htrans
      calc ((2 ^ (i + 1) : ℕ) : ℝ) ^ ((α - β ^ 2) * Real.log ((2 ^ (i + 1) : ℕ) : ℝ))
          ≤ _ := hcount
        _ ≤ _ := by exact_mod_cast htrans
  · -- ## Band regime `β² < α`: the tight chain at the shifted witness sequence.
    push Not at hreg
    have hL2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hL2lt1 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    -- band coefficients and Archimedean thresholds
    set c₁ : ℝ := β - β ^ 2 - (α - β ^ 2) * Real.log 2 with hc₁
    set c₂ : ℝ := (α - β ^ 2) * (1 - Real.log 2) with hc₂
    have hc₁_pos : 0 < c₁ := by
      rw [hc₁]
      nlinarith [mul_pos (sub_pos.mpr hreg) hL2pos]
    have hc₂_pos : 0 < c₂ := by
      rw [hc₂]
      exact mul_pos (sub_pos.mpr hreg) (by linarith)
    obtain ⟨N₁, hN₁⟩ := exists_nat_ge ((2 * β + 2) / c₁)
    obtain ⟨N₂, hN₂⟩ := exists_nat_ge ((2 * β + 3) / c₂)
    set N : ℕ := max N₁ N₂ with hN
    refine ⟨fun i => 2 ^ (i + N + 1), ?_, ?_, ?_⟩
    · intro i j hij
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · intro i
      exact Nat.prime_two.isPrimePow.pow (by omega)
    · intro i ι _ _ _ F _ _ _ hF hι
      set m : ℕ := i + N + 1 with hm
      -- the band's two largeness conditions hold at this m
      have hmN₁ : (N₁ : ℝ) ≤ (m : ℝ) := by
        have : N₁ ≤ m := by omega
        exact_mod_cast this
      have hmN₂ : (N₂ : ℝ) ≤ (m : ℝ) := by
        have : N₂ ≤ m := by omega
        exact_mod_cast this
      have hmc₁ : 2 * β + 2 ≤ (m : ℝ) * c₁ := by
        have h1 : 2 * β + 2 ≤ (N₁ : ℝ) * c₁ := (div_le_iff₀ hc₁_pos).mp hN₁
        have h2 : (N₁ : ℝ) * c₁ ≤ (m : ℝ) * c₁ :=
          mul_le_mul_of_nonneg_right hmN₁ hc₁_pos.le
        linarith
      have hmc₂ : 2 * β + 3 ≤ (m : ℝ) * c₂ := by
        have h1 : 2 * β + 3 ≤ (N₂ : ℝ) * c₂ := (div_le_iff₀ hc₂_pos).mp hN₂
        have h2 : (N₂ : ℝ) * c₂ ≤ (m : ℝ) * c₂ :=
          mul_le_mul_of_nonneg_right hmN₂ hc₂_pos.le
        linarith
      have hL1 : β ^ 2 * m + (α - β ^ 2) * Real.log 2 * m + 2 * β + 2 ≤ β * m := by
        have hexpand : (m : ℝ) * c₁
            = β * m - β ^ 2 * m - (α - β ^ 2) * Real.log 2 * m := by
          rw [hc₁]; ring
        linarith
      have hL2 : β ^ 2 * m + (α - β ^ 2) * Real.log 2 * m + 2 * β + 3 ≤ α * m := by
        have hexpand : (m : ℝ) * c₂
            = α * m - β ^ 2 * m - (α - β ^ 2) * Real.log 2 * m := by
          rw [hc₂]; ring
        linarith
      -- the band cutoffs
      obtain ⟨u, v, hvm, huv, hv2, hum, hβv, hwindow, hexp⟩ :=
        bkr06_band_choice_exponent m α β (Real.log 2)
          hβ_pos.le (le_of_lt hβ_lt) hα1 hreg.le hL2pos.le hL1 hL2
      -- view F as a ZMod 2 extension of degree m
      haveI hchar : CharP F 2 := charP_of_card_eq_prime_pow Nat.prime_two hF
      letI : Algebra (ZMod 2) F := ZMod.algebra F 2
      have hfinrank : Module.finrank (ZMod 2) F = m :=
        finrank_eq_of_card_eq_pow (le_refl 2) (ZMod.card 2) hF
      -- the tight close-codeword count at window 2^u + 1
      obtain ⟨pivot, hcount⟩ :=
        bkr06_close_codewords_card_ge_tight (K := F) (F := ZMod 2) 2 (le_refl 2)
          (ZMod.card 2) v u
          (by rw [hfinrank]; exact hvm) huv
          (by rw [hfinrank]; exact hv2)
          (by rw [hfinrank]; exact hum)
          β (by rw [hfinrank]; exact hβv)
      rw [hfinrank] at hcount
      -- the abstract-index equivalence and the bare statement's window
      have hcards : Fintype.card ι = Fintype.card F := by rw [hF, hι]
      set e : ι ≃ F := Fintype.equivOfCardEq hcards with he
      set kk : ℕ := Nat.floor (((2 ^ m : ℕ) : ℝ) ^ α) with hkk
      have hk_window : 2 ^ u + 1 ≤ kk := by
        rw [hkk, cast_two_pow]
        exact rs_window_le_floor 2 m u α (le_refl 2) hwindow
      set w₀ : F → F := ReedSolomon.evalOnPoints (Function.Embedding.refl F) pivot
        with hw₀
      set δ : ℝ := 1 - (Fintype.card F : ℝ) ^ (β - 1) with hδ
      refine ⟨e.toEmbedding, w₀ ∘ e, ?_⟩
      dsimp only
      rw [ge_iff_le]
      -- count chain: window monotonicity then index transport; align the lemma
      -- instances to the goal's raw `2^m` via `hF`.
      have hmono := rs_closeCodewords_ncard_mono_window (K := F)
        (Function.Embedding.refl F) w₀ δ hk_window
      have htrans := rs_closeCodewords_ncard_transport (K := F) e kk w₀ δ
      rw [hδ] at hcount hmono htrans
      rw [hF] at hcount hmono htrans
      -- exponent chain: target = 2^{(α−β²)·log2·m²} ≤ 2^{m·u − v²} ≤ tight count
      have htarget : ((2 ^ m : ℕ) : ℝ) ^ ((α - β ^ 2) * Real.log ((2 ^ m : ℕ) : ℝ))
          ≤ (2 : ℝ) ^ ((m : ℝ) * u - (v : ℝ) ^ 2) := by
        rw [target_exponent_eq α β m]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      -- the tight count with the ℕ-cast `(2 : ℕ) : ℝ = 2` bridge
      have hcount' : (2 : ℝ) ^ ((m : ℝ) * u - (v : ℝ) ^ 2) ≤
          ((ListDecodable.closeCodewordsRel
              ((ReedSolomon.code (Function.Embedding.refl F) (2 ^ u + 1) : Set (F → F)))
              w₀ (1 - ((2 ^ m : ℕ) : ℝ) ^ (β - 1))).ncard : ℝ) := by
        exact_mod_cast hcount
      -- assemble
      calc ((2 ^ m : ℕ) : ℝ) ^ ((α - β ^ 2) * Real.log ((2 ^ m : ℕ) : ℝ))
          ≤ (2 : ℝ) ^ ((m : ℝ) * u - (v : ℝ) ^ 2) := htarget
        _ ≤ _ := hcount'
        _ ≤ _ := by exact_mod_cast le_trans hmono htrans

#print axioms BKR06.rs_lambda_superpoly_extension_bkr06_proven

end BKR06
