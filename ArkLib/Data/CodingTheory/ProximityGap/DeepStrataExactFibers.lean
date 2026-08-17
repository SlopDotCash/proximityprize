/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSecondMomentSharp

/-!
# Exact deep-strata fibers: stratifying the sharp second moment by overlap level (#389)

GOAL: the HEADLINE residual (deep_pair_rank_eq) is already landed + wired. The
suggested follow-up is to use the EXACT fiber per overlap level rather than the
coarse floor q^(M-(m+1)) that sum_N2_le_sharp lumps all deep pairs at.

`sum_N2_le_sharp` (DeepBandSecondMomentSharp.lean) counts EVERY deep pair at the
floor q^(M-(m+1)), which equals the exact fiber ONLY at the shallowest deep
overlap j = k+1. For overlap j = k+d with d ≥ 2 the exact fiber deep_fiber_eq
gives q^(M-(2m+1-d)) — a factor q^(d-1) SMALLER. So the genuinely-sharp second
moment stratifies the deep sum by overlap level.

This file proves the FULLY OVERLAP-STRATIFIED sharp deep-stratum sum:

  Σ_{deep pairs p} #{c : pred p c}
     ≤ Σ_{d=1}^{m}  (#pairs at overlap k+d) · q^(M-(2m+1-d))

an EQUALITY in the fiber per pair (deep_fiber_eq), strictly sharper than the
uniform floor whenever any deep pair has overlap ≥ k+2.
-/

open Finset Polynomial
open scoped NNReal ENNReal

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ProximityGap.PairRank.DeepStrataFibers

open ProximityGap ProximityGap.Ownership ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The pair-coherence predicate, as in `sum_N2_le_sharp`. -/
def pred (dom : Fin n ↪ F) (k m : ℕ) {M : ℕ}
    (p : Finset (Fin n) × Finset (Fin n)) (c : Fin M → F) : Prop :=
  IsCoherent dom k m p.1 (genPoly c)
    ∧ IsCoherent dom k m p.2 (genPoly c)
    ∧ (coreInterp dom p.1 (genPoly c)).coeff k
      = (coreInterp dom p.2 (genPoly c)).coeff k

open Classical in
/-- **The exact deep fiber, per pair, indexed by overlap level.**  For a deep
pair `(T,T')` with overlap EXACTLY `k+d` (`1 ≤ d`, `T ≠ T'`), the pair-coherence
fiber is exactly `q^(M-(2m+1-d))`.  (Restatement of `deep_fiber_eq` with the
overlap pinned to a level, which is what stratification consumes.) -/
theorem deep_fiber_at_level (dom : Fin n ↪ F) {k m : ℕ} {T T' : Finset (Fin n)}
    (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1) (hne : T ≠ T')
    {d : ℕ} (hd : 1 ≤ d) (hlev : (T ∩ T').card = k + d) {M : ℕ}
    (hM : 2 * (k + m + 1) ≤ M) :
    (Finset.univ.filter (fun c : Fin M → F => pred dom k m (T, T') c)).card
      = (Fintype.card F) ^ (M - (2 * m + 1 - d)) := by
  classical
  have hdeep : k < (T ∩ T').card := by omega
  have h := deep_fiber_eq dom hT hT' hne hdeep hM
  -- rewrite the overlap (T∩T').card - k = d
  have hsub : (T ∩ T').card - k = d := by omega
  rw [hsub] at h
  -- pred is definitionally the filter body of deep_fiber_eq
  convert h using 3

/-- The deep stratum at a fixed overlap level `k+d`. -/
noncomputable def deepLevel (dom : Fin n ↪ F) (k m d : ℕ) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
    (fun p => p.1 ≠ p.2 ∧ (p.1 ∩ p.2).card = k + d)

open Classical in
/-- **The exact level-d deep sum.**  Over the overlap-`k+d` stratum, the
pair-coherence sum is EXACTLY `(#level-d pairs) · q^(M-(2m+1-d))` — the exact
fiber, no slack. -/
theorem sum_deepLevel_eq (dom : Fin n ↪ F) (k m : ℕ) {d : ℕ} (hd : 1 ≤ d)
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) :
    (∑ p ∈ deepLevel dom k m d,
        (Finset.univ.filter (fun c : Fin M → F => pred dom k m p c)).card)
      = (deepLevel dom k m d).card * (Fintype.card F) ^ (M - (2 * m + 1 - d)) := by
  classical
  rw [Finset.sum_congr rfl (fun p hp => ?_), Finset.sum_const, smul_eq_mul]
  obtain ⟨hpmem, hne, hlev⟩ := Finset.mem_filter.mp hp
  rcases Finset.mem_product.mp hpmem with ⟨hp1, hp2⟩
  have := deep_fiber_at_level dom
    ((Finset.mem_powersetCard.mp hp1).2) ((Finset.mem_powersetCard.mp hp2).2)
    hne hd hlev hM
  -- p = (p.1, p.2)
  have hpeq : p = (p.1, p.2) := rfl
  rw [show (Finset.univ.filter (fun c : Fin M → F => pred dom k m p c)).card
        = (Finset.univ.filter (fun c : Fin M → F => pred dom k m (p.1, p.2) c)).card
      from by rw [← hpeq]]
  exact this

open Classical in
/-- **The deep stratum is the disjoint union of its overlap levels.**  The full
deep set `deepS = {p : T ≠ T' ∧ k < (T∩T').card}` partitions over
`d ∈ {1, …, m}` (distinct equal-size cores have `k < |T∩T'| ≤ k+m`). -/
theorem deepS_eq_biUnion_levels (dom : Fin n ↪ F) (k m : ℕ) :
    ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
        (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
        (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card))
      = (Finset.Icc 1 m).biUnion (fun d => deepLevel dom k m d) := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
    Finset.mem_Icc, deepLevel]
  constructor
  · rintro ⟨⟨hp1, hp2⟩, hne, hover⟩
    -- distinct equal-size cores: overlap ≤ k+m
    have hT : p.1.card = k + m + 1 := (Finset.mem_powersetCard.mp hp1).2
    have hT' : p.2.card = k + m + 1 := (Finset.mem_powersetCard.mp hp2).2
    have hov_le : (p.1 ∩ p.2).card ≤ k + m := by
      by_contra h
      push_neg at h
      have hinter : p.1 ∩ p.2 = p.1 :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      have hsub : p.1 ⊆ p.2 := by
        intro x hx
        have : x ∈ p.1 ∩ p.2 := hinter.symm ▸ hx
        exact (Finset.mem_inter.mp this).2
      exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))
    refine ⟨(p.1 ∩ p.2).card - k, ⟨by omega, by omega⟩, ⟨hp1, hp2⟩, hne, by omega⟩
  · rintro ⟨d, ⟨hd1, hdm⟩, ⟨hp1, hp2⟩, hne, hlev⟩
    exact ⟨⟨hp1, hp2⟩, hne, by omega⟩

open Classical in
/-- The overlap levels are pairwise disjoint (an overlap card determines `d`). -/
theorem deepLevels_pairwiseDisjoint (dom : Fin n ↪ F) (k m : ℕ) :
    (Finset.Icc 1 m : Finset ℕ).toSet.PairwiseDisjoint
      (fun d => deepLevel dom k m d) := by
  intro d₁ _ d₂ _ hne
  simp only [Function.onFun, Finset.disjoint_left, deepLevel, Finset.mem_filter]
  rintro p ⟨-, -, h1⟩ ⟨-, -, h2⟩
  exact hne (by omega : d₁ = d₂)

open Classical in
/-- **THE FULLY OVERLAP-STRATIFIED SHARP DEEP SUM.**  The deep-stratum
pair-coherence sum equals the sum over overlap levels `d ∈ {1, …, m}` of
`(#level-d pairs) · q^(M-(2m+1-d))` — EXACT fiber at every level, strictly
sharper than `sum_N2_le_sharp`'s uniform floor `q^(M-(m+1))` whenever some deep
pair has overlap `≥ k+2` (where the level fiber is `q^(d-1)` times smaller). -/
theorem sum_deep_stratified_eq (dom : Fin n ↪ F) (k m : ℕ) {M : ℕ}
    (hM : 2 * (k + m + 1) ≤ M) :
    (∑ p ∈ (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
          (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card))),
        (Finset.univ.filter (fun c : Fin M → F => pred dom k m p c)).card)
      = ∑ d ∈ Finset.Icc 1 m,
          (deepLevel dom k m d).card * (Fintype.card F) ^ (M - (2 * m + 1 - d)) := by
  classical
  rw [deepS_eq_biUnion_levels dom k m]
  rw [Finset.sum_biUnion (deepLevels_pairwiseDisjoint dom k m)]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  exact sum_deepLevel_eq dom k m hd.1 hM

open Classical in
/-- **CONSISTENCY with the coarse floor.**  The stratified sum is `≤` the floor
`(#deep pairs)·q^(M-(m+1))` used by `sum_N2_le_sharp` — i.e. the new exact form
is genuinely no worse, and strictly better at every level `d ≥ 2`.  (Sanity check
that the sharp stratification dominates the existing sharp bound.) -/
theorem sum_deep_stratified_le_floor (dom : Fin n ↪ F) (k m : ℕ) {M : ℕ}
    (hM : 2 * (k + m + 1) ≤ M) :
    (∑ d ∈ Finset.Icc 1 m,
        (deepLevel dom k m d).card * (Fintype.card F) ^ (M - (2 * m + 1 - d)))
      ≤ ((((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
          (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card))).card)
        * (Fintype.card F) ^ (M - (m + 1)) := by
  classical
  -- the LHS is the stratified sum = the deep sum, bounded fiber-wise by the floor
  have hkey : (∑ d ∈ Finset.Icc 1 m,
        (deepLevel dom k m d).card * (Fintype.card F) ^ (M - (2 * m + 1 - d)))
      = ∑ p ∈ (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
          (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card))),
        (Finset.univ.filter (fun c : Fin M → F => pred dom k m p c)).card :=
    (sum_deep_stratified_eq dom k m hM).symm
  rw [hkey]
  -- now each deep-pair fiber ≤ q^(M-(m+1)) by deep_fiber_le, exactly the floor bound
  set deepS := (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
      (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card))) with hdeepS
  have hfloor : ∀ p ∈ deepS,
      (Finset.univ.filter (fun c : Fin M → F => pred dom k m p c)).card
        ≤ (Fintype.card F) ^ (M - (m + 1)) := by
    intro p hp
    obtain ⟨hpmem, hne, hover⟩ := Finset.mem_filter.mp hp
    rcases Finset.mem_product.mp hpmem with ⟨hp1, hp2⟩
    have h := deep_fiber_le dom
      ((Finset.mem_powersetCard.mp hp1).2) ((Finset.mem_powersetCard.mp hp2).2)
      hne hover hM
    -- pred unfolds to the filter body of deep_fiber_le (up to the decidability
    -- instance on the filter predicate)
    rw [show (Finset.univ.filter (fun c : Fin M → F => pred dom k m p c)).card
          = (Finset.univ.filter (fun c : Fin M → F =>
              IsCoherent dom k m p.1 (genPoly c) ∧ IsCoherent dom k m p.2 (genPoly c)
                ∧ (coreInterp dom p.1 (genPoly c)).coeff k
                  = (coreInterp dom p.2 (genPoly c)).coeff k)).card
        from by
          unfold pred
          congr 1
          exact Finset.filter_congr_decidable _ _ _]
    exact h
  calc ∑ p ∈ deepS,
        (Finset.univ.filter (fun c : Fin M → F => pred dom k m p c)).card
      ≤ ∑ p ∈ deepS, (Fintype.card F) ^ (M - (m + 1)) := Finset.sum_le_sum hfloor
    _ = deepS.card * (Fintype.card F) ^ (M - (m + 1)) := by
        rw [Finset.sum_const, smul_eq_mul]

end ProximityGap.PairRank.DeepStrataFibers

