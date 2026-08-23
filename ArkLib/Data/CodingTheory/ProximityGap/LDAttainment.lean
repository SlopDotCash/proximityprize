/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# Attainment resolution of the formalized Grand List Decoding Challenge (ABF26 §1)

This file **completely resolves the formalized statement** `grandListDecodingChallenge`
(and with it `listDecodingPrize`), in the *negative* direction sanctioned by its own
docstring ("or proving no such `δ*_C` exists for some parameter regime").

## The resolution

`Lambda C δ` is built from the *closed*-ball list `closeCodewordsRel` (membership is
`relHammingDist ≤ δ`).  Over a finite index set `ι` with `n := |ι|`, the relative Hamming
distance only takes values in the grid `{j/n : j ≤ n}` (`Code.relHammingDistRange`), so
`δ ↦ Lambda C δ` is a *right-continuous step function*: it is constant on every interval
`[δ, (⌊δ·n⌋+1)/n)`.  Consequently the "good set" `{δ : Λ(C^⋈m, δ) ≤ ε*·|F|}` is half-open
on the right wherever it is bounded, and its supremum is **never attained** below `1`:

* for any candidate `δ* < 1`, real density provides `δ ∈ (δ*, (⌊δ*·n⌋+1)/n)` with
  `Λ(δ) = Λ(δ*) ≤ ε*·|F|`, contradicting the strict-failure-above-`δ*` clause;
* the only remaining candidate is `δ* = 1`, whose failure clause is vacuous, so the
  challenge *degenerates* to the radius-1 question `Λ(C^⋈m, 1) ≤ ε*·|F|` — i.e. "is the
  whole interleaved code smaller than `ε*·|F|`?".

This is `grandListDecodingChallenge_iff_Lambda_one_le` below.  For every Reed–Solomon
instance with `k ≥ 1` and `m ≥ 1` the radius-1 question is false (the constant codewords
already give `Λ(C^⋈m, 1) ≥ |F| > ε*·|F|` for `ε* < 1`), whence

* `not_grandListDecodingChallengeRS` : the formalized challenge is **false** for every
  RS code with `k ≥ 1`, `m ≥ 1`, `ε* < 1`;
* `not_listDecodingPrize_of_two_le_card` : the formalized prize statement is **false** for every
  domain (named to coexist with the convergent `GrandChallengeCollapse.not_listDecodingPrize`)
  with at least 2 points and every interleaving `m ≥ 1`.

## What this does and does not mean

This is a *statement-level* resolution: the `∃ δ*`-with-strict-maximality Prop does not
capture the paper's challenge.  ABF26 asks to *determine the value* of the threshold
`δ*_C = sup {δ : |Λ(C^≡m, δ)| ≤ ε*·|F|}` (in particular whether it is near the Johnson
radius `1 - √ρ` or near capacity `1 - ρ`); that supremum exists but — by the present
file — is not a maximum, so an attained-maximum formalization is refutable for reasons
orthogonal to the deep open question.  The faithful quantitative reformulation (the
`sSup`-based threshold, with the Johnson-side lower bound and the capacity-side upper
bound) is the subject of `GrandChallengeLDThreshold.lean`.

The analogous resolution for the Grand MCA Challenge (whose `ε_mca` is a step function
of `δ` for the same reason) is in `GrandChallengeCollapse.lean`
(`grandMCAChallenge_iff_epsMCA_one`, `mcaPrize_iff_forall_epsMCA_one`); the resulting
radius-one question is analyzed further in `GrandChallengeRadiusOne.lean`,
`GrandChallengeRadiusOneExact.lean`, and `GrandChallengeDecision.lean`, with the
faithful-witness framework in `GrandChallengeResolutionWitness.lean`.
-/

namespace ProximityGap

open scoped NNReal
open ListDecodable

section Grid

variable {ι : Type*} [Fintype ι] [Nonempty ι] {A : Type*}

/-- **Grid constancy of relative-Hamming balls.**  If `r ≤ r'` and `r'·n` is still below
the next grid point `⌊r·n⌋ + 1`, the relative-Hamming balls of radii `r` and `r'`
coincide: the relative distance only takes values `d/n` with `d : ℕ`. -/
lemma relHammingBall_eq_of_grid (y : ι → A) {r r' : ℝ}
    (h0 : 0 ≤ r) (hle : r ≤ r')
    (hlt : r' * (Fintype.card ι : ℝ) < ⌊r * (Fintype.card ι : ℝ)⌋₊ + 1) :
    relHammingBall y r' = relHammingBall y r := by
  classical
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  ext x
  simp only [relHammingBall, Set.mem_setOf_eq]
  constructor
  · intro h
    obtain ⟨d, _hdn, hdeq⟩ :=
      Code.relHammingDist_mem_relHammingDistRange (F := A) (u := y) (v := x)
    have hcast : ((Code.relHammingDist y x : ℚ≥0) : ℝ)
        = (d : ℝ) / (Fintype.card ι : ℝ) := by
      rw [hdeq]; push_cast; ring
    rw [hcast] at h ⊢
    rw [div_le_iff₀ hn] at h ⊢
    have h1 : (d : ℝ) < (⌊r * (Fintype.card ι : ℝ)⌋₊ : ℝ) + 1 := lt_of_le_of_lt h hlt
    have h2 : d ≤ ⌊r * (Fintype.card ι : ℝ)⌋₊ := by
      have := Nat.lt_succ_iff.mp (by exact_mod_cast h1)
      exact this
    calc (d : ℝ) ≤ (⌊r * (Fintype.card ι : ℝ)⌋₊ : ℝ) := by exact_mod_cast h2
      _ ≤ r * (Fintype.card ι : ℝ) := Nat.floor_le (mul_nonneg h0 hn.le)
  · intro h
    exact le_trans h hle

/-- Grid constancy for the close-codewords list. -/
lemma closeCodewordsRel_eq_of_grid (C : Code ι A) (y : ι → A) {r r' : ℝ}
    (h0 : 0 ≤ r) (hle : r ≤ r')
    (hlt : r' * (Fintype.card ι : ℝ) < ⌊r * (Fintype.card ι : ℝ)⌋₊ + 1) :
    closeCodewordsRel C y r' = closeCodewordsRel C y r := by
  unfold closeCodewordsRel
  rw [relHammingBall_eq_of_grid y h0 hle hlt]

/-- Grid constancy for the maximised list size `Λ`. -/
lemma Lambda_eq_of_grid (C : Code ι A) {r r' : ℝ}
    (h0 : 0 ≤ r) (hle : r ≤ r')
    (hlt : r' * (Fintype.card ι : ℝ) < ⌊r * (Fintype.card ι : ℝ)⌋₊ + 1) :
    Lambda C r' = Lambda C r := by
  unfold Lambda
  exact iSup_congr fun f => by rw [closeCodewordsRel_eq_of_grid C f h0 hle hlt]

/-- **Density step.**  Below radius `1` the maximised list size cannot strictly increase
immediately: every `δ* < 1` admits `δ ∈ (δ*, 1]` with `Λ(C, δ) = Λ(C, δ*)` for *every*
code `C` on `ι` (any alphabet).  This is the obstruction to the attained-maximum shape of
the formalized grand challenges. -/
lemma exists_gt_Lambda_eq (δstar : ℝ≥0) (hδ : δstar < 1) :
    ∃ δ : ℝ≥0, δstar < δ ∧ δ ≤ 1 ∧
      ∀ {A : Type*} (C : Code ι A), Lambda C (δ : ℝ) = Lambda C (δstar : ℝ) := by
  classical
  set n : ℕ := Fintype.card ι with hn
  have hnpos : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  set fl : ℕ := ⌊(δstar : ℝ) * (n : ℝ)⌋₊ with hfl
  -- next grid point
  set g : ℝ≥0 := ((fl : ℝ≥0) + 1) / (n : ℝ≥0) with hg
  have hgR : (g : ℝ) = ((fl : ℝ) + 1) / (n : ℝ) := by
    rw [hg]; push_cast; ring
  -- δ* < g
  have hlt_g : δstar < g := by
    rw [← NNReal.coe_lt_coe, hgR]
    rw [lt_div_iff₀ hnR]
    exact Nat.lt_floor_add_one ((δstar : ℝ) * (n : ℝ))
  -- g ≤ 1
  have hg1 : g ≤ 1 := by
    rw [← NNReal.coe_le_coe, hgR]
    have hfl_lt : fl < n := by
      rw [hfl]
      rw [Nat.floor_lt (mul_nonneg δstar.coe_nonneg hnR.le)]
      have : (δstar : ℝ) < 1 := by exact_mod_cast hδ
      calc (δstar : ℝ) * (n : ℝ) < 1 * (n : ℝ) := by
            exact mul_lt_mul_of_pos_right this hnR
        _ = (n : ℝ) := one_mul _
    rw [div_le_iff₀ hnR]
    have : (fl : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hfl_lt
    simpa using this
  -- midpoint witness
  refine ⟨(δstar + g) / 2, ?_, ?_, ?_⟩
  · -- δ* < midpoint
    rw [← NNReal.coe_lt_coe]
    push_cast
    have : (δstar : ℝ) < (g : ℝ) := by exact_mod_cast hlt_g
    linarith
  · -- midpoint ≤ 1
    have hmid_lt : (δstar + g) / 2 < g := by
      rw [← NNReal.coe_lt_coe]
      push_cast
      have : (δstar : ℝ) < (g : ℝ) := by exact_mod_cast hlt_g
      linarith
    exact le_trans hmid_lt.le hg1
  · -- Λ-constancy on [δ*, midpoint]
    intro A C
    have hgcoe : (δstar : ℝ) < (g : ℝ) := by exact_mod_cast hlt_g
    refine Lambda_eq_of_grid C δstar.coe_nonneg ?_ ?_
    · -- δ* ≤ midpoint
      change (δstar : ℝ) ≤ (((δstar + g) / 2 : ℝ≥0) : ℝ)
      push_cast
      linarith
    · -- midpoint · n < ⌊δ* · n⌋ + 1
      have hmidg : (((δstar + g) / 2 : ℝ≥0) : ℝ) < (g : ℝ) := by
        push_cast
        linarith
      have : (((δstar + g) / 2 : ℝ≥0) : ℝ) * (n : ℝ) < (g : ℝ) * (n : ℝ) :=
        mul_lt_mul_of_pos_right hmidg hnR
      calc (((δstar + g) / 2 : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)
          < (g : ℝ) * (n : ℝ) := by rw [← hn] at *; exact this
        _ = (fl : ℝ) + 1 := by
            rw [hgR, div_mul_cancel₀]
            exact hnR.ne'
        _ = (⌊(δstar : ℝ) * (Fintype.card ι : ℝ)⌋₊ : ℝ) + 1 := by simp [hfl, hn]

end Grid

section Characterization

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **The formalized Grand List Decoding Challenge degenerates to the radius-1 question.**

`grandListDecodingChallenge C m ε*` holds *iff* the whole interleaved code is small:
`Λ(C^⋈m, 1) ≤ ε*·|F|`.  In particular the `∃ δ*`-with-strict-maximality shape carries no
information about list-decoding thresholds: for any `δ* < 1` the maximality clause fails
on the grid plateau just above `δ*` (`exists_gt_Lambda_eq`), leaving only the degenerate
witness `δ* = 1`. -/
theorem grandListDecodingChallenge_iff_Lambda_one_le
    (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) :
    grandListDecodingChallenge C m ε_star ↔
      (ListDecodable.Lambda (C^⋈ (Fin m)) ((1 : ℝ≥0) : ℝ) : ENNReal) ≤
        (ε_star : ENNReal) * (Fintype.card F : ENNReal) := by
  constructor
  · rintro ⟨δs, hδs1, hΛ, hmax⟩
    rcases lt_or_eq_of_le hδs1 with hlt | heq
    · obtain ⟨δ, hgt, hle1, hEq⟩ := exists_gt_Lambda_eq (ι := ι) δs hlt
      have hcontra := hmax δ hgt hle1
      rw [hEq (C^⋈ (Fin m))] at hcontra
      exact absurd hΛ (not_le.mpr hcontra)
    · rw [heq] at hΛ
      exact hΛ
  · intro h
    exact ⟨1, le_refl 1, h, fun δ h1 h2 => absurd h2 (not_le.mpr h1)⟩

end Characterization

section ReedSolomon

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [DecidableEq F] [DecidableEq ι] in
/-- Any code containing all constant words has interleaved radius-1 list size at least
`|F|`: the constant interleaved stacks are pairwise distinct and all lie in the radius-1
ball around any fixed word. -/
lemma card_le_Lambda_interleaved_one
    (C : Set (ι → F)) (hconst : ∀ x : F, (fun _ : ι => x) ∈ C)
    {m : ℕ} (hm : m ≠ 0) :
    (Fintype.card F : ℕ∞) ≤ ListDecodable.Lambda (C^⋈ (Fin m)) ((1 : ℝ≥0) : ℝ) := by
  classical
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
  -- the constant-stack embedding
  set e : F → (ι → (Fin m → F)) := fun x => fun _ _ => x with he
  have hinj : Function.Injective e := by
    intro a b hab
    exact congrFun (congrFun hab (Classical.arbitrary ι)) (Classical.arbitrary (Fin m))
  have hsub : Set.range e ⊆
      ListDecodable.closeCodewordsRel (C^⋈ (Fin m)) (fun _ _ => (0 : F))
        ((1 : ℝ≥0) : ℝ) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨?_, ?_⟩
    · -- membership in the interleaved code
      show ∀ k : Fin m, (Matrix.transpose (e x)) k ∈ C
      intro k
      have : Matrix.transpose (e x) k = fun _ : ι => x := rfl
      rw [this]
      exact hconst x
    · -- within relative distance 1
      simp [relHammingBall]
  have hcard : (Set.range e).ncard = Fintype.card F := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
  calc (Fintype.card F : ℕ∞)
      = ((Set.range e).ncard : ℕ∞) := by rw [hcard]
    _ ≤ ((ListDecodable.closeCodewordsRel (C^⋈ (Fin m)) (fun _ _ => (0 : F))
          ((1 : ℝ≥0) : ℝ)).ncard : ℕ∞) := by
        exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ListDecodable.Lambda (C^⋈ (Fin m)) ((1 : ℝ≥0) : ℝ) :=
        le_iSup (fun f => ((ListDecodable.closeCodewordsRel (C^⋈ (Fin m)) f
          ((1 : ℝ≥0) : ℝ)).ncard : ℕ∞)) (fun _ _ => (0 : F))

/-- **The formalized Grand List Decoding Challenge is false for every Reed–Solomon
instance** with `k ≥ 1`, `m ≥ 1` and `ε* < 1`.  (The constant codewords force
`Λ(C^⋈m, 1) ≥ |F| > ε*·|F|`, so the degenerate radius-1 witness also fails.) -/
theorem not_grandListDecodingChallengeRS
    (domain : ι ↪ F) {k m : ℕ} (hk : k ≠ 0) (hm : m ≠ 0)
    {ε_star : ℝ≥0} (hε : ε_star < 1) :
    ¬ GrandChallenges.grandListDecodingChallengeRS domain k m ε_star := by
  rw [GrandChallenges.grandListDecodingChallengeRS,
    grandListDecodingChallenge_iff_Lambda_one_le]
  intro h
  -- constants are RS codewords for k ≥ 1
  have : NeZero k := ⟨hk⟩
  have hconst : ∀ x : F, (fun _ : ι => x) ∈ (ReedSolomon.code domain k : Set (ι → F)) :=
    fun x => by
      change ReedSolomon.constantCode x ι ∈ ReedSolomon.code domain k
      exact ReedSolomon.constantCode_mem_code
  have h1 : (Fintype.card F : ℕ∞) ≤
      ListDecodable.Lambda ((ReedSolomon.code domain k : Set (ι → F))^⋈ (Fin m))
        ((1 : ℝ≥0) : ℝ) :=
    card_le_Lambda_interleaved_one _ hconst hm
  -- ε*·|F| < |F| ≤ Λ(1)
  have hq0 : (Fintype.card F : ENNReal) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hqt : (Fintype.card F : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h2 : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      (Fintype.card F : ENNReal) := by
    calc (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < 1 * (Fintype.card F : ENNReal) := by
          rw [mul_comm (ε_star : ENNReal), mul_comm (1 : ENNReal)]
          exact ENNReal.mul_lt_mul_right hq0 hqt (by exact_mod_cast hε)
      _ = (Fintype.card F : ENNReal) := one_mul _
  have h1' : (Fintype.card F : ENNReal) ≤
      (ListDecodable.Lambda ((ReedSolomon.code domain k : Set (ι → F))^⋈ (Fin m))
        ((1 : ℝ≥0) : ℝ) : ENNReal) := by
    calc (Fintype.card F : ENNReal)
        = ((Fintype.card F : ℕ∞) : ENNReal) := by simp
      _ ≤ _ := by exact_mod_cast h1
  exact absurd h (not_le.mpr (lt_of_lt_of_le h2 h1'))

/-- **The formalized list-decoding prize statement is false for every domain** (with at
least two evaluation points) and every interleaving parameter `m ≥ 1`: already the rate
`1/2` instance of the challenge fails. -/
theorem not_listDecodingPrize_of_two_le_card
    (domain : ι ↪ F) {m : ℕ} (hm : m ≠ 0) (hι : 2 ≤ Fintype.card ι) :
    ¬ GrandChallenges.listDecodingPrize domain m := by
  intro h
  have h0 := h 0
  refine not_grandListDecodingChallengeRS domain ?_ hm ?_ h0
  · -- ⌊(1/2)·n⌋ ≥ 1
    have hrate : prizeRates 0 = 1 / 2 := by
      simp [prizeRates]
    have h1 : (1 : ℝ≥0) ≤ prizeRates 0 * (Fintype.card ι : ℝ≥0) := by
      rw [hrate]
      have h2' : (2 : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by exact_mod_cast hι
      calc (1 : ℝ≥0) = 1 / 2 * 2 := by norm_num
        _ ≤ 1 / 2 * (Fintype.card ι : ℝ≥0) := by
            exact mul_le_mul_of_nonneg_left h2' (by positivity)
    have : 1 ≤ ⌊prizeRates 0 * (Fintype.card ι : ℝ≥0)⌋₊ := by
      rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]
      exact Nat.floor_pos.mpr h1
    omega
  · -- ε* = 2⁻¹²⁸ < 1
    rw [epsStar]
    rw [div_lt_one]
    · exact_mod_cast (Nat.one_lt_pow (n := 128) (a := 2) (by norm_num) (by norm_num))
    · positivity

end ReedSolomon

end ProximityGap
