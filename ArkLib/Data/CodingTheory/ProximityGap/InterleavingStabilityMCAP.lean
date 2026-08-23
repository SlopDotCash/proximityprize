/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA
import ArkLib.Data.CodingTheory.ProximityGap.ProximityGapP

/-!
# Interleaving stability for the general power-generator MCA error

This file extends the Jo26 small-seed interleaving-stability argument from the affine-line
surface `ProximityGap.epsMCA` to the general power-generator surface
`ProximityGapP.epsMCAP`.

The seed set is still the field `F`, so the same covering lemma from
`InterleavingStabilityMCA.lean` applies: for every bad seed `γ`, the row-combination vectors
that would destroy the bad witness form a proper subspace of `F^t`, and at most `|F|` such
proper subspaces cannot cover `F^t`.  A single nonzero row-combination therefore preserves all
bad seeds at once.

Main results:

* `jointTupleSubmoduleP` / `jointTupleSubmoduleP_ne_top` — the `parℓ`-tuple bad-seed
  subspace and its properness.
* `epsMCAP_le_epsMCAP_interleaved` — zero-row embedding.
* `epsMCAP_interleaved_le_epsMCAP` — one row-combination preserves every bad seed.
* `epsMCAP_interleaved_eq` — exact interleaving invariance for `epsMCAP`.

This is the `epsMCAP` version of [Jo26] Corollary 4.5 for the in-tree power-generator API.
-/

namespace ProximityGapP

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- The `parℓ`-tuple bad-seed subspace: row-combination vectors `λ : F^t` whose
`λ`-combined base stack admits a joint `parℓ`-tuple of codewords on `S`. -/
def jointTupleSubmoduleP (C : Submodule F (ι → A)) (S : Finset ι) {parℓ t : ℕ}
    (U : WordStack (Fin t → A) (Fin parℓ) ι) : Submodule F (Fin t → F) where
  carrier := {lam | pairJointAgreesOnP (C : Set (ι → A)) S
    (fun j i => ∑ k, lam k • U j i k)}
  zero_mem' := by
    refine ⟨0, fun j => C.zero_mem, fun i hi j => ?_⟩
    simp
  add_mem' := by
    rintro lam lam' ⟨v, hv, hag⟩ ⟨w, hw, hag'⟩
    refine ⟨fun j => v j + w j, fun j => C.add_mem (hv j) (hw j), fun i hi j => ?_⟩
    calc
      (v j + w j) i = (∑ k, lam k • U j i k) + ∑ k, lam' k • U j i k := by
        rw [Pi.add_apply, hag i hi j, hag' i hi j]
      _ = ∑ k, (lam + lam') k • U j i k := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [Pi.add_apply, add_smul]
  smul_mem' := by
    rintro c lam ⟨v, hv, hag⟩
    refine ⟨fun j => c • v j, fun j => C.smul_mem c (hv j), fun i hi j => ?_⟩
    calc
      (c • v j) i = c • ∑ k, lam k • U j i k := by rw [Pi.smul_apply, hag i hi j]
      _ = ∑ k, (c • lam) k • U j i k := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ => by
          rw [Pi.smul_apply, smul_smul, smul_eq_mul]

open Classical in
/-- Properness of the `parℓ`-tuple bad-seed subspace.  If every row-combination admitted a
base-code joint tuple, then applying this to the standard basis vectors would give every
interleaving row a joint tuple, which assembles into a joint tuple for the interleaved code. -/
theorem jointTupleSubmoduleP_ne_top (C : Submodule F (ι → A)) {S : Finset ι} {parℓ t : ℕ}
    (U : WordStack (Fin t → A) (Fin parℓ) ι)
    (hnopair : ¬ pairJointAgreesOnP ((C : Set (ι → A))^⋈ (Fin t)) S U) :
    jointTupleSubmoduleP C S U ≠ ⊤ := by
  intro htop
  apply hnopair
  have hrow : ∀ k : Fin t, pairJointAgreesOnP (C : Set (ι → A)) S
      (fun j i => U j i k) := by
    intro k
    have hmem : (Pi.single k (1 : F)) ∈ jointTupleSubmoduleP C S U := by
      rw [htop]
      trivial
    obtain ⟨v, hv, hag⟩ := hmem
    have hsum : ∀ (j : Fin parℓ) (i : ι),
        (∑ k', (Pi.single k (1 : F) : Fin t → F) k' • U j i k') = U j i k := by
      intro j i
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, zero_smul]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    refine ⟨v, hv, fun i hi j => ?_⟩
    have h := hag i hi j
    dsimp only at h ⊢
    rw [hsum j i] at h
    exact h
  choose V hV hagree using hrow
  refine ⟨fun j i k => V k j i, ?_, ?_⟩
  · intro j k
    exact hV k j
  · intro i hi j
    funext k
    exact hagree k i hi j

/-! ## Easy direction: zero-row embedding -/

open Classical in
/-- Zero-row embedding: a base `epsMCAP` bad stack embeds into the interleaved code by placing
the whole stack in row `0` and zeros in every other row. -/
theorem epsMCAP_le_epsMCAP_interleaved (C : Submodule F (ι → A)) {parℓ : ℕ}
    (exp : Fin parℓ → ℕ) (t : ℕ) [NeZero t] (δ : ℝ≥0) :
    epsMCAP (F := F) (A := A) (C : Set (ι → A)) exp δ
      ≤ epsMCAP (F := F) (A := Fin t → A) ((C : Set (ι → A))^⋈ (Fin t)) exp δ := by
  classical
  unfold epsMCAP
  apply iSup_le
  intro v
  set u : WordStack (Fin t → A) (Fin parℓ) ι :=
    fun j i k => if k = (0 : Fin t) then v j i else 0 with hu
  have h_imp : ∀ γ : F, mcaEventP (C : Set (ι → A)) exp δ v γ →
      mcaEventP ((C : Set (ι → A))^⋈ (Fin t)) exp δ u γ := by
    rintro γ ⟨S, hcard, ⟨w, hw, hagree⟩, hnopair⟩
    refine ⟨S, hcard, ?_, ?_⟩
    · refine ⟨fun i k => if k = (0 : Fin t) then w i else 0, ?_, ?_⟩
      · intro k
        show (fun i => if k = (0 : Fin t) then w i else 0) ∈ (C : Set (ι → A))
        by_cases hk : k = 0
        · subst hk
          simpa using hw
        · simp only [if_neg hk]
          exact C.zero_mem
      · intro i hi
        funext k
        by_cases hk : k = 0
        · subst hk
          simp [curveComb, hu, hagree i hi]
        · simp [curveComb, hu, hk]
    · rintro ⟨V, hV, hpair⟩
      apply hnopair
      refine ⟨fun j i => V j i 0, ?_, ?_⟩
      · intro j
        exact hV j 0
      · intro i hi j
        have h := congrArg (fun f : Fin t → A => f 0) (hpair i hi j)
        simpa [hu] using h
  refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
  exact le_iSup
    (fun w : WordStack (Fin t → A) (Fin parℓ) ι =>
      Pr_{let γ ← $ᵖ F}[mcaEventP ((C : Set (ι → A))^⋈ (Fin t)) exp δ w γ])
    u

/-! ## Hard direction: one row-combination preserves every bad seed -/

open Classical in
/-- The Jo26 small-seed direction for `epsMCAP`: because the bad-seed subspaces are indexed
by the seed set `F`, one nonzero row-combination vector avoids all of them simultaneously. -/
theorem epsMCAP_interleaved_le_epsMCAP (C : Submodule F (ι → A)) {parℓ : ℕ}
    (exp : Fin parℓ → ℕ) (t : ℕ) [NeZero t] (δ : ℝ≥0) :
    epsMCAP (F := F) (A := Fin t → A) ((C : Set (ι → A))^⋈ (Fin t)) exp δ
      ≤ epsMCAP (F := F) (A := A) (C : Set (ι → A)) exp δ := by
  classical
  unfold epsMCAP
  apply iSup_le
  intro u
  obtain ⟨lam, _hlam0, hlamK⟩ := ProximityGap.exists_nonzero_notMem_of_proper_family
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne t))
    (fun γ => if h : mcaEventP ((C : Set (ι → A))^⋈ (Fin t)) exp δ u γ
      then jointTupleSubmoduleP C h.choose u else ⊥)
    (fun γ => by
      dsimp only
      split_ifs with h
      · exact jointTupleSubmoduleP_ne_top C u h.choose_spec.2.2
      · exact bot_ne_top)
  set v : WordStack A (Fin parℓ) ι := fun j i => ∑ k, lam k • u j i k with hv
  have h_imp : ∀ γ : F,
      mcaEventP ((C : Set (ι → A))^⋈ (Fin t)) exp δ u γ →
      mcaEventP (C : Set (ι → A)) exp δ v γ := by
    intro γ h
    obtain ⟨hcard, ⟨w, hwmem, hwagree⟩, _hnopair⟩ := h.choose_spec
    refine ⟨h.choose, hcard, ?_, ?_⟩
    · refine ⟨fun i => ∑ k, lam k • w i k, ?_, ?_⟩
      · have hrows : ∀ k : Fin t, (fun i => w i k) ∈ (C : Set (ι → A)) := hwmem
        have heq : (fun i => ∑ k, lam k • w i k)
            = ∑ k, lam k • (fun i => w i k) := by
          funext i
          rw [Finset.sum_apply]
          exact Finset.sum_congr rfl fun k _ => rfl
        rw [heq]
        exact Submodule.sum_mem _ fun k _ => C.smul_mem _ (hrows k)
      · intro i hi
        have hpt : ∀ k : Fin t, w i k = ∑ j, (γ ^ exp j) • u j i k := by
          intro k
          have h := congrArg (fun f : Fin t → A => f k) (hwagree i hi)
          simpa [curveComb, Pi.smul_apply] using h
        calc
          (fun i => ∑ k, lam k • w i k) i = ∑ k, lam k • w i k := rfl
          _ = ∑ k, lam k • (∑ j, (γ ^ exp j) • u j i k) := by
            exact Finset.sum_congr rfl fun k _ => by rw [hpt k]
          _ = ∑ k, ∑ j, lam k • ((γ ^ exp j) • u j i k) := by
            exact Finset.sum_congr rfl fun k _ => by rw [Finset.smul_sum]
          _ = ∑ j, ∑ k, lam k • ((γ ^ exp j) • u j i k) := by
            rw [Finset.sum_comm]
          _ = ∑ j, (γ ^ exp j) • ∑ k, lam k • u j i k := by
            exact Finset.sum_congr rfl fun j _ => by
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun k _ => by
                rw [smul_smul, smul_smul, mul_comm]
          _ = curveComb exp v γ i := rfl
    · intro hpair
      have hmem := hlamK γ
      rw [dif_pos h] at hmem
      exact hmem hpair
  refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
  exact le_iSup
    (fun w : WordStack A (Fin parℓ) ι =>
      Pr_{let γ ← $ᵖ F}[mcaEventP (C : Set (ι → A)) exp δ w γ])
    v

/-! ## Exact invariance -/

/-- **Jo26 exact interleaving invariance for `epsMCAP`.**  The general power-generator MCA
error is unchanged by row-wise interleaving when the generator seed set is the field itself. -/
theorem epsMCAP_interleaved_eq (C : Submodule F (ι → A)) {parℓ : ℕ}
    (exp : Fin parℓ → ℕ) (t : ℕ) [NeZero t] (δ : ℝ≥0) :
    epsMCAP (F := F) (A := Fin t → A) ((C : Set (ι → A))^⋈ (Fin t)) exp δ
      = epsMCAP (F := F) (A := A) (C : Set (ι → A)) exp δ :=
  le_antisymm (epsMCAP_interleaved_le_epsMCAP C exp t δ)
    (epsMCAP_le_epsMCAP_interleaved C exp t δ)

end

end ProximityGapP

/-! ## Axiom audit -/
#print axioms ProximityGapP.jointTupleSubmoduleP_ne_top
#print axioms ProximityGapP.epsMCAP_le_epsMCAP_interleaved
#print axioms ProximityGapP.epsMCAP_interleaved_le_epsMCAP
#print axioms ProximityGapP.epsMCAP_interleaved_eq
