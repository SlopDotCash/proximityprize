/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Collapse
import ArkLib.Data.CodingTheory.ProximityLeaves

/-!
# Closed form for the §1 Grand List Decoding Challenge (Finding F6, list side)

This file completes the *list-decoding* half of the F6 program by giving the closed-form
decision of the `grandListDecodingChallenge` predicate for Reed-Solomon codes — the exact
analogue of the MCA-side `grandMCAChallenge_iff_choose_le`
(`GrandChallengeRadiusOneExact.lean`).

The MCA side already had its closed form; the list side had only the radius-one collapse
(`grandListDecodingChallenge_iff_Lambda_one` + `Lambda_one_eq_ncard`,
`GrandChallengeCollapse.lean`) but **no closed form for the underlying `ncard`**. The two
missing cardinalities are supplied here:

* `ncard_interleavedCodeSet_eq_pow` — the `m`-fold interleaving of a finite code `C` has
  exactly `|C|^m` codewords. The interleaving `interleavedCodeSet C = {V | ∀ j, Vᵀ j ∈ C}`
  is the `m`-fold product of `C`; the explicit **column bijection**
  `V ↦ (fun j => Vᵀ j)` carries it onto `Set.pi univ (fun _ : Fin m => C)`, and
  `Set.encard_pi_eq_prod_encard` finishes.
* `ncard_reedSolomonCode` — for `k ≤ n` the Reed-Solomon code `RS[F, domain, k]` has
  exactly `q^k` codewords (re-exported from `ReedSolomon.ncard_code_eq_pow_card`, itself
  `dim_eq_deg_of_le'` + `Module.card_eq_pow_finrank`).

Combining these with the radius-one collapse yields:

* `grandListDecodingChallenge_iff_pow_le` — for `RS[F, domain, k]` with `k ≤ n`:

    `grandListDecodingChallenge (RS) m ε* ↔ (q^(k·m) : ENNReal) ≤ ε* · q`

  the complete list-side analogue of `grandMCAChallenge_iff_choose_le`. (`Λ(C^⋈m, 1)` is the
  whole interleaved code `= q^(k·m)`, so the challenge collapses to a single inequality.)

* `not_listDecodingPrize_of_closedForm` — a re-proof of `not_listDecodingPrize` from the
  closed form: `q^(k·m) ≤ 2⁻¹²⁸·q` is false whenever `k·m ≥ 1` (the left side is at least
  `q²`, the right side strictly below `q`).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal

namespace ProximityGap

open Code InterleavedCode ListDecodable

section Interleaving

variable {ι : Type} [Fintype ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The column map `V ↦ (fun j => Vᵀ j)` from interleaved words to column tuples is
injective on `interleavedCodeSet C`: a matrix is determined by its columns. It carries the
interleaved code bijectively onto the `m`-fold product `Set.pi univ (fun _ => C)`. -/
lemma columnMap_image_interleavedCodeSet {m : ℕ} (C : Set (ι → F)) :
    (fun V : Matrix ι (Fin m) F => fun k : Fin m => V.transpose k) ''
        (interleavedCodeSet (κ := Fin m) C)
      = Set.pi Set.univ (fun _ : Fin m => C) := by
  ext g
  simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies, interleavedCodeSet,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨V, hV, rfl⟩ k
    exact hV k
  · intro hg
    refine ⟨Matrix.of fun i k => g k i, ?_, ?_⟩
    · intro k
      have : (Matrix.of fun i k => g k i : Matrix ι (Fin m) F).transpose k = g k := by
        funext i; rfl
      rw [this]; exact hg k
    · funext k i; rfl

/-- **Cardinality of an interleaved code.** For a finite code `C : Set (ι → F)`, the `m`-fold
interleaving `C^⋈ (Fin m) = interleavedCodeSet C` has exactly `|C|^m` codewords — it is the
`m`-fold product of `C`, witnessed by the explicit column bijection `V ↦ (fun j => Vᵀ j)`. -/
theorem ncard_interleavedCodeSet_eq_pow {m : ℕ} (C : Set (ι → F)) (hC : C.Finite) :
    ((C^⋈ (Fin m)) : Set (Matrix ι (Fin m) F)).ncard = C.ncard ^ m := by
  classical
  -- The interleaved code is finite (subset of a finite type).
  have hIfin : (interleavedCodeSet (κ := Fin m) C).Finite := Set.toFinite _
  -- The column map.
  set Φ : Matrix ι (Fin m) F → (Fin m → (ι → F)) := fun V k => V.transpose k with hΦ
  have hinj : Set.InjOn Φ (interleavedCodeSet (κ := Fin m) C) := by
    intro V _ W _ heq
    ext i k
    exact congrFun (congrFun heq k) i
  -- Compute via `encard` and the product-cardinality lemma.
  have hencard : (interleavedCodeSet (κ := Fin m) C).encard = C.encard ^ m := by
    calc (interleavedCodeSet (κ := Fin m) C).encard
        = (Φ '' (interleavedCodeSet (κ := Fin m) C)).encard := (hinj.encard_image).symm
      _ = (Set.pi Set.univ (fun _ : Fin m => C)).encard := by
            rw [columnMap_image_interleavedCodeSet]
      _ = ∏ _k : Fin m, C.encard := by rw [Set.encard_pi_eq_prod_encard]
      _ = C.encard ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Transport back to `ncard`.
  rw [← hIfin.cast_ncard_eq, ← hC.cast_ncard_eq] at hencard
  have hgoal : ((interleavedCodeSet (κ := Fin m) C).ncard : ℕ∞) = ((C.ncard ^ m : ℕ) : ℕ∞) := by
    rw [hencard]; push_cast; ring
  exact_mod_cast hgoal

end Interleaving

section ReedSolomonCard

variable {ι : Type} [Fintype ι] {F : Type} [Field F] [Fintype F]

/-- **Cardinality of a Reed-Solomon code.** For an injective evaluation domain and degree
bound `k ≤ |ι|`, the Reed-Solomon code `RS[F, domain, k]` has exactly `q^k` codewords.
Re-export of `ReedSolomon.ncard_code_eq_pow_card`. -/
theorem ncard_reedSolomonCode (domain : ι ↪ F) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    (ReedSolomon.code domain k : Set (ι → F)).ncard = Fintype.card F ^ k :=
  ReedSolomon.ncard_code_eq_pow_card domain k hk

end ReedSolomonCard

section ClosedForm

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The `m`-fold interleaving of a Reed-Solomon code with `k ≤ n` has exactly `q^(k·m)`
codewords. -/
theorem ncard_interleavedReedSolomonCode (domain : ι ↪ F) {k : ℕ}
    (hk : k ≤ Fintype.card ι) (m : ℕ) :
    (((ReedSolomon.code domain k : Set (ι → F))^⋈ (Fin m)) :
        Set (Matrix ι (Fin m) F)).ncard = Fintype.card F ^ (k * m) := by
  rw [ncard_interleavedCodeSet_eq_pow _ (Set.toFinite _),
    ncard_reedSolomonCode domain hk, ← pow_mul]

/-- The radius-one maximised list size of the `m`-fold interleaved Reed-Solomon code with
`k ≤ n` equals `q^(k·m)`: at radius one the list is the whole interleaved code
(`Lambda_one_eq_ncard`), of cardinality `q^(k·m)`
(`ncard_interleavedReedSolomonCode`). -/
theorem Lambda_interleavedReedSolomon_one_eq (domain : ι ↪ F) {k : ℕ}
    (hk : k ≤ Fintype.card ι) (m : ℕ) :
    ListDecodable.Lambda ((ReedSolomon.code domain k : Set (ι → F))^⋈ (Fin m))
        ((1 : ℝ≥0) : ℝ) = ((Fintype.card F ^ (k * m) : ℕ) : ℕ∞) := by
  rw [show ((1 : ℝ≥0) : ℝ) = (1 : ℝ) by norm_num,
    Lambda_one_eq_ncard (α := Fin m → F)]
  exact_mod_cast congrArg (Nat.cast : ℕ → ℕ∞)
    (ncard_interleavedReedSolomonCode domain hk m)

/-- **Closed form of the §1 Grand List Decoding Challenge for Reed-Solomon** (Finding F6,
list side). The complete analogue of `grandMCAChallenge_iff_choose_le`: for `RS[F, domain, k]`
with `k ≤ n`, the existence-of-a-maximal-real-threshold predicate is equivalent to the single
inequality `q^(k·m) ≤ ε* · q`.

The predicate collapses (`grandListDecodingChallenge_iff_Lambda_one`) to the radius-one list
size `Λ(C^⋈m, 1)`, which is the **whole interleaved code** (`Lambda_one_eq_ncard`), of size
`q^(k·m)` (`ncard_interleavedReedSolomonCode`). -/
theorem grandListDecodingChallenge_iff_pow_le (domain : ι ↪ F) {k : ℕ}
    (hk : k ≤ Fintype.card ι) (m : ℕ) (ε_star : ℝ≥0) :
    grandListDecodingChallenge (ReedSolomon.code domain k : Set (ι → F)) m ε_star ↔
      ((Fintype.card F : ENNReal) ^ (k * m)) ≤
        ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) := by
  rw [grandListDecodingChallenge_iff_Lambda_one,
    Lambda_interleavedReedSolomon_one_eq domain hk m]
  push_cast
  rfl

/-- The rate-addressed Reed-Solomon list-decoding challenge in closed form. -/
theorem grandListDecodingChallengeRS_iff_pow_le (domain : ι ↪ F) {k : ℕ}
    (hk : k ≤ Fintype.card ι) (m : ℕ) (ε_star : ℝ≥0) :
    GrandChallenges.grandListDecodingChallengeRS domain k m ε_star ↔
      ((Fintype.card F : ENNReal) ^ (k * m)) ≤
        ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) :=
  grandListDecodingChallenge_iff_pow_le domain hk m ε_star

end ClosedForm

section Sharpening

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The RS list-decoding challenge is false in the prize regime, via the closed form.**
For `0 < k`, `0 < m`, `k ≤ n`, `ε* < 1`: by `grandListDecodingChallenge_iff_pow_le` the
challenge is `q^(k·m) ≤ ε*·q`. Since `1 ≤ k·m` this forces `q ≤ q^(k·m) ≤ ε*·q < q`. -/
theorem not_grandListDecodingChallengeRS_of_pos_closedForm (domain : ι ↪ F) {k m : ℕ}
    (hk0 : 0 < k) (hkn : k ≤ Fintype.card ι) (hm : 0 < m) {ε_star : ℝ≥0} (hε : ε_star < 1) :
    ¬ GrandChallenges.grandListDecodingChallengeRS domain k m ε_star := by
  rw [grandListDecodingChallengeRS_iff_pow_le domain hkn m]
  intro hbound
  have hq_pos : (0 : ENNReal) < (Fintype.card F : ENNReal) := by
    exact_mod_cast Fintype.card_pos
  have hq_ne_top : (Fintype.card F : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  -- `1 ≤ k·m`, so `q = q^1 ≤ q^(k·m)`.
  have hkm : 1 ≤ k * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hq_one_le : (1 : ENNReal) ≤ (Fintype.card F : ENNReal) := by
    exact_mod_cast Fintype.card_pos
  have hq_le_pow : (Fintype.card F : ENNReal) ≤ (Fintype.card F : ENNReal) ^ (k * m) := by
    calc (Fintype.card F : ENNReal) = (Fintype.card F : ENNReal) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ (Fintype.card F : ENNReal) ^ (k * m) := pow_le_pow_right₀ hq_one_le hkm
  -- The strict bound `ε*·q < q`.
  have hε' : (ε_star : ENNReal) < 1 := by exact_mod_cast hε
  have hlt : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      (Fintype.card F : ENNReal) := by
    calc (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        = (Fintype.card F : ENNReal) * (ε_star : ENNReal) := mul_comm _ _
      _ < (Fintype.card F : ENNReal) * 1 :=
          ENNReal.mul_lt_mul_right hq_pos.ne' hq_ne_top hε'
      _ = (Fintype.card F : ENNReal) := mul_one _
  exact absurd (le_trans hq_le_pow hbound) (not_le.mpr hlt)

/-- **Re-proof of `not_listDecodingPrize` from the closed form.** The formal §1 list-decoding
prize predicate is false for every domain with `2 ≤ |ι|` and every `0 < m`: at the rate
`ρ = 1/2` the degree `k = ⌊|ι|/2⌋` satisfies `1 ≤ k` and `k ≤ n`, and
`not_grandListDecodingChallengeRS_of_pos_closedForm` applies with `ε* = 2⁻¹²⁸ < 1` (where
the closed form gives the sharp contradiction `q^(k·m) ≤ 2⁻¹²⁸·q < q ≤ q^(k·m)`). -/
theorem not_listDecodingPrize_of_closedForm (domain : ι ↪ F) {m : ℕ} (hm : 0 < m)
    (hι : 2 ≤ Fintype.card ι) :
    ¬ GrandChallenges.listDecodingPrize domain m := by
  intro hprize
  have h0 := hprize 0
  have hrate : prizeRates 0 = 1 / 2 := by unfold prizeRates; norm_num
  set k := ⌊prizeRates 0 * (Fintype.card ι : ℝ≥0)⌋₊ with hk_def
  -- `1 ≤ k`.
  have hk0 : 0 < k := by
    rw [hk_def]
    refine lt_of_lt_of_le Nat.zero_lt_one (Nat.le_floor ?_)
    rw [hrate, Nat.cast_one]
    calc (1 : ℝ≥0) = (1 / 2) * 2 := by norm_num
      _ ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) := by gcongr; exact_mod_cast hι
  -- `k ≤ n`.
  have hkn : k ≤ Fintype.card ι := by
    rw [hk_def]
    refine Nat.floor_le_of_le ?_
    rw [hrate]
    calc (1 / 2) * (Fintype.card ι : ℝ≥0) ≤ 1 * (Fintype.card ι : ℝ≥0) := by gcongr; norm_num
      _ = (Fintype.card ι : ℝ≥0) := one_mul _
  -- `ε* < 1`.
  have hε : epsStar < 1 := by
    unfold epsStar
    rw [div_lt_one (by positivity)]
    exact one_lt_pow₀ one_lt_two (by norm_num)
  exact not_grandListDecodingChallengeRS_of_pos_closedForm domain hk0 hkn hm hε h0

end Sharpening

end ProximityGap
