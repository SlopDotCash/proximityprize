/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.JohnsonBound.Family

/-!
# `johnson_bound_lambda_le_ell` is *false* as stated (Finding-26 style refutation)

`ArkLib/Data/CodingTheory/JohnsonBound/Family.lean` exposes `johnson_bound_lambda_le_ell`
(ABF26 Theorem 3.2) as a `Prop`-valued predicate (NOT a `theorem`, NOT a `sorry`):

  for any code `C ⊆ Σ^n` with `|Σ| = q` and `ℓ ≥ 2`,
  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`,  where  `δ_min(C) = minDist(C)/n`.

This file proves the statement is **not a theorem as stated** by exhibiting a concrete
instance whose conclusion fails (`johnson_bound_lambda_le_ell_false`). The predicate
therefore cannot be honestly upgraded to a theorem — it needs a hypothesis repair
(a proximity bound keeping the square-root argument of `Jqℓ` nonnegative). The usable
Johnson outputs that carry that constraint are `mds_johnson_lambda_le` (proved sorry-free
in `Family.lean`) and the squared form in
`ProximityGap/GrandChallengeLDThresholdJohnsonSq.lean`. See disposition
`docs/kb/audits/proximity-prize/dispositions/issue-49-johnson-family.md`.

## Why it is false

`Jqℓ q ℓ δ = (1 - 1/q) · (1 - √(1 - (q/(q-1))·(ℓ/(ℓ-1))·δ))`.  The standard q-ary
ℓ-Johnson bound is valid only in the regime where the radicand
`1 - (q/(q-1))·(ℓ/(ℓ-1))·δ` is **nonnegative**; the Lean statement carries no such
hypothesis.  Mathlib's `Real.sqrt` returns `0` on negative inputs, so once
`(q/(q-1))·(ℓ/(ℓ-1))·δ > 1` the radius collapses to the meaninglessly large value
`(1 - 1/q)`, and a ball of that radius can contain far more than `ℓ` codewords.

## The witness

Take `ι = Fin 2` (so `n = |ι| = 2`), `α = Fin 2` (so `q = 2`), `ℓ = 2`, and the explicit
three-word code

  `C = { ![0,0], ![0,1], ![1,0] } ⊆ (Fin 2 → Fin 2)`.

* `minDist(C) = 1` (the closest distinct pair `![0,0], ![0,1]` differs in one coordinate),
  so `δ_min = 1/2`.
* `(q/(q-1))·(ℓ/(ℓ-1))·δ_min = 2·2·(1/2) = 2 > 1`, hence the radicand is `1 - 2 = -1 < 0`,
  `√(-1) = 0`, and `Jqℓ 2 2 (1/2) = (1 - 1/2)·(1 - 0) = 1/2`.
* Centring at `f = ![0,0]`, all three codewords lie within relative distance `1/2`
  (distances `0, 1/2, 1/2`), so `closeCodewordsRel C f (1/2) = C` has `ncard = 3` and
  `Λ(C, 1/2) ≥ 3 > 2 = ℓ`.

Hence `|Λ(C, J_{q,ℓ}(δ_min(C)))| = 3 > 2 = ℓ`, refuting the statement.

The one subtlety is that `relHammingBall` is defined with `open Classical`, so the ball
membership uses `Classical.propDecidable` whereas the `Fin 2` codeword facts compute with
`instDecidableEqFin`.  These give *equal* relative distances (`relHammingDist`'s value is
instance-independent); the helper `mem_ball_of_mem_C` is therefore stated for an *arbitrary*
`DecidableEq α` instance so it applies to whichever instance the ball carries.
-/

set_option linter.unusedSectionVars false

namespace JohnsonBound.JqlRefutation

open ListDecodable JohnsonBound Code

/-- The refuting alphabet/index types: `ι = α = Fin 2` (so `n = 2`, `q = 2`). -/
abbrev ι : Type := Fin 2
abbrev α : Type := Fin 2

/-- The three codewords. -/
def c0 : ι → α := ![0, 0]
def c1 : ι → α := ![0, 1]
def c2 : ι → α := ![1, 0]

/-- The explicit refuting code `C = { ![0,0], ![0,1], ![1,0] }`. -/
def C : Set (ι → α) := {c0, c1, c2}

/-- The three codewords are pairwise distinct. -/
theorem c0_ne_c1 : c0 ≠ c1 := by decide
theorem c0_ne_c2 : c0 ≠ c2 := by decide
theorem c1_ne_c2 : c1 ≠ c2 := by decide

/-- Pairwise Hamming distances. -/
theorem ham_c0_c1 : hammingDist c0 c1 = 1 := by decide
theorem ham_c0_c2 : hammingDist c0 c2 = 1 := by decide
theorem ham_c1_c2 : hammingDist c1 c2 = 2 := by decide

/-- Membership in `C` is membership in the explicit three-element set. -/
theorem mem_C_iff (x : ι → α) : x ∈ C ↔ x = c0 ∨ x = c1 ∨ x = c2 := by
  simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- `card ι = 2`. -/
theorem card_ι : Fintype.card ι = 2 := by decide

/-- **`Code.minDist C = 1`.**  The defining set of distinct-pair distances is `{1, 2}`
(`d(c0,c1) = d(c0,c2) = 1`, `d(c1,c2) = 2`), and every distinct pair has distance `≥ 1`. -/
theorem minDist_C : Code.minDist C = 1 := by
  apply le_antisymm
  · -- `minDist C ≤ 1`: `1` is in the defining set, witnessed by the pair `(c0, c1)`.
    refine Nat.sInf_le ⟨c0, (mem_C_iff c0).mpr (Or.inl rfl), c1,
      (mem_C_iff c1).mpr (Or.inr (Or.inl rfl)), c0_ne_c1, ham_c0_c1⟩
  · -- `1 ≤ minDist C`: every distinct pair `(u, v)` has `hammingDist u v ≥ 1`.
    refine le_csInf ⟨1, ⟨c0, (mem_C_iff c0).mpr (Or.inl rfl), c1,
      (mem_C_iff c1).mpr (Or.inr (Or.inl rfl)), c0_ne_c1, ham_c0_c1⟩⟩ ?_
    rintro d ⟨u, _, v, _, huv, rfl⟩
    exact Nat.one_le_iff_ne_zero.mpr (by simpa [hammingDist_eq_zero] using huv)

/-- **The Johnson radius collapses to `1/2` at `q = ℓ = 2`, `δ = 1/2`.**
The radicand `1 - (2/1)·(2/1)·(1/2) = -1 < 0`, so `√(-1) = 0` and
`Jqℓ 2 2 (1/2) = (1 - 1/2)·(1 - 0) = 1/2`. -/
theorem Jqℓ_eq_half : Jqℓ (2 : ℚ) (2 : ℚ) ((1 : ℚ) / 2) = (1 / 2 : ℝ) := by
  norm_num [Jqℓ, Real.sqrt_eq_zero_of_nonpos]

/-- **Ball membership (canonical instance).**  Every codeword lies within relative distance
`1/2` of `c0` (distances `0, 1/2, 1/2`).  Stated with the ambient (canonical `Fin 2`)
`DecidableEq` instance, under which the `Fin 2` Hamming-distance facts compute. -/
theorem relDist_le_half (c : ι → α) (hc : c = c0 ∨ c = c1 ∨ c = c2) :
    ((Code.relHammingDist c0 c : ℚ≥0) : ℝ) ≤ (1 / 2 : ℝ) := by
  rcases hc with rfl | rfl | rfl
  · -- distance `0`
    have h0 : Code.relHammingDist c0 c0 = 0 := by
      rw [Code.relHammingDist, hammingDist_self]; simp
    rw [h0]; norm_num
  · -- distance `1/2`
    have h1 : Code.relHammingDist c0 c1 = 1 / 2 := by
      rw [Code.relHammingDist, ham_c0_c1, card_ι]; norm_num
    rw [h1]; push_cast; norm_num
  · -- distance `1/2`
    have h2 : Code.relHammingDist c0 c2 = 1 / 2 := by
      rw [Code.relHammingDist, ham_c0_c2, card_ι]; norm_num
    rw [h2]; push_cast; norm_num

/-- **The ball of radius `1/2` about `c0` is the whole code:** `closeCodewordsRel C c0 (1/2) = C`.

`relHammingBall` is defined with `open Classical`, so the membership predicate carries the
`Classical.propDecidable` instance; `DecidableEq (Fin 2)` is a subsingleton, so we transport
to the canonical instance (under which `relDist_le_half` is stated) by `Subsingleton.elim`. -/
theorem closeCodewordsRel_eq_C :
    closeCodewordsRel C c0 (1 / 2 : ℝ) = C := by
  ext c
  simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcC, _⟩; exact hcC
  · intro hcC
    refine ⟨hcC, ?_⟩
    -- the ball's (classical) `relHammingDist` instance is a subsingleton-equal to the
    -- canonical one used by `relDist_le_half`; bridge with `Subsingleton.elim`.
    have hkey := relDist_le_half c ((mem_C_iff c).mp hcC)
    convert hkey using 3

/-- The refuting code has exactly three codewords. -/
theorem ncard_C : C.ncard = 3 := by
  rw [C, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_singleton]
  · simp only [Set.mem_singleton_iff]; exact c1_ne_c2
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨c0_ne_c1, c0_ne_c2⟩

/-- **`Λ(C, 1/2) ≥ 3`.**  The point-list at the centre `c0` is all of `C` (`ncard = 3`), and
`Lambda` is the supremum over centres. -/
theorem three_le_Lambda : (3 : ℕ∞) ≤ Lambda C (1 / 2 : ℝ) := by
  have hpt : ((closeCodewordsRel C c0 (1 / 2 : ℝ)).ncard : ℕ∞) ≤ Lambda C (1 / 2 : ℝ) :=
    le_iSup (fun f : ι → α => ((closeCodewordsRel C f (1 / 2 : ℝ)).ncard : ℕ∞)) c0
  rwa [closeCodewordsRel_eq_C, ncard_C] at hpt

/-- **ABF26 Theorem 3.2 (`johnson_bound_lambda_le_ell`) is FALSE as stated.**

For the concrete code `C = { ![0,0], ![0,1], ![1,0] } ⊆ (Fin 2 → Fin 2)` and `ℓ = 2`, the
conclusion `Lambda C (Jqℓ q ℓ δ_min) ≤ ℓ` FAILS: the left side is `≥ 3` while the right side
is `2`.  The failure is intrinsic to the unconditioned statement — `δ_min = 1/2` drives the
square-root argument of `Jqℓ` negative, `Real.sqrt` clamps it to `0`, and the Johnson
"radius" collapses to `1/2`, a ball that swallows the entire code.  The theorem needs a
proximity hypothesis (`(q/(q-1))·(ℓ/(ℓ-1))·δ_min ≤ 1`) that the present statement lacks. -/
theorem johnson_bound_lambda_le_ell_false :
    ¬ (let q : ℚ := Fintype.card α
       let δ_min : ℚ := Code.minDist C / Fintype.card ι
       Lambda C (Jqℓ q 2 δ_min) ≤ (2 : ℕ∞)) := by
  -- the radius at this instance is exactly `1/2`: `q = 2`, `minDist C = 1`, `card ι = 2`.
  have hradius :
      Jqℓ (Fintype.card α : ℚ) 2 ((Code.minDist C : ℚ) / Fintype.card ι) = (1 / 2 : ℝ) := by
    have hq : (Fintype.card α : ℚ) = 2 := by rw [show Fintype.card α = 2 from by decide]; rfl
    have hmd : Code.minDist C = 1 := minDist_C
    rw [hq, hmd]
    -- goal: `Jqℓ 2 2 (↑1 / 2) = 1/2`; same radicand collapse as `Jqℓ_eq_half`.
    norm_num [Jqℓ, Real.sqrt_eq_zero_of_nonpos]
  simp only [hradius]
  intro hle
  exact absurd (le_trans three_le_Lambda hle) (by decide)

/-- **Direct contradiction with the named statement.**  If `johnson_bound_lambda_le_ell` (ABF26
T3.2, the refuted `Prop`-valued predicate in `Family.lean`) were a theorem, instantiating it at
the witness `C`, `ℓ = 2`, `(le_refl 2 : 2 ≤ 2)` would prove exactly the proposition refuted by
`johnson_bound_lambda_le_ell_false`.  This is packaged as an implication so the file does not
itself assume the (false) upstream statement: any honest proof of the hypothesis yields `False`. -/
theorem upstream_theorem_is_inconsistent
    (johnson_bound_lambda_le_ell :
      ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
        {α : Type} [Fintype α] [DecidableEq α]
        (C : Set (ι → α)) (ℓ : ℕ), 2 ≤ ℓ →
        (let q : ℚ := Fintype.card α
         let δ_min : ℚ := Code.minDist C / Fintype.card ι
         Lambda C (Jqℓ q ℓ δ_min) ≤ (ℓ : ℕ∞))) :
    False :=
  johnson_bound_lambda_le_ell_false (johnson_bound_lambda_le_ell C 2 (le_refl 2))

-- Axiom audit (must be exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`).
#print axioms upstream_theorem_is_inconsistent
#print axioms johnson_bound_lambda_le_ell_false
#print axioms three_le_Lambda
#print axioms minDist_C
#print axioms Jqℓ_eq_half

end JohnsonBound.JqlRefutation
