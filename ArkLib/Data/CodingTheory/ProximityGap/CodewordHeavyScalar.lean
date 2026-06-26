/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ExplainableCoreExactCount

/-!
# The codeword heavy-scalar bound: the dual of the line-core partition

Issue #389. `LineCorePartition.lean` showed each `(k+m+1)`-core is explainable for at most one
scalar on the bad-scalar line `w_γ = u₀ + γ·u₁` (when `u₁` is far). This file proves the
**dual** incidence bound, from the side of a fixed codeword:

> **`codeword_heavy_scalar_card_le`** — for a fixed codeword `c` and a **nonvanishing**
> direction `u₁` (every `u₁ i ≠ 0` — true for `u₁ = xᵏ` on a smooth domain), the scalars `γ`
> for which `c` agrees with `w_γ` on at least `a` points number at most `⌊n/a⌋`.

The mechanism is that each domain point `i` agrees with `w_γ` at the **unique** scalar
`γᵢ = (c i − u₀ i)/u₁ i`; so the agreement sets of `c` across the line are the fibers of
`i ↦ γᵢ`, which **partition** the `n` domain points. A scalar can receive a heavy
(`≥ a`) fiber from `c` only `≤ n/a` times.

Together with `line_core_unique_scalar` this pins the full **bipartite incidence** between
codewords and scalars along the line: each core belongs to one scalar, and each codeword
feeds `≤ ⌊n/(k+m+1)⌋` scalars. This is the exact combinatorial skeleton on which any
per-scalar supply bound must rest — the structural content the extremal refutation
(`ExplainableCoreExactCount.lean`) showed combinatorics alone cannot supply, now made
precise from both sides.

## References

* Issue #389; `LineCorePartition.lean` (the core side), `ExplainableCoreExactCount.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Coordinates where the line direction is zero.  These coordinates contribute to every scalar
only when the fixed codeword already agrees with the offset. -/
noncomputable def directionZeroSet (u₁ : Fin n → F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => u₁ i = 0)

open Classical in
/-- Coordinates where the line direction is nonzero.  On this support, a fixed codeword chooses a
unique scalar at each coordinate. -/
noncomputable def directionSupportSet (u₁ : Fin n → F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => u₁ i ≠ 0)

open Classical in
/-- Zero-direction coordinates where the fixed codeword already agrees with the line offset.
These coordinates agree with every scalar on the affine line. -/
noncomputable def directionZeroAgreementSet (c u₀ u₁ : Fin n → F) : Finset (Fin n) :=
  (directionZeroSet u₁).filter (fun i => c i = u₀ i)

/-- Zero-direction agreements are contained in every scalar agreement set along the line. -/
theorem directionZeroAgreementSet_subset_agreeSet_line
    (c u₀ u₁ : Fin n → F) (γ : F) :
    directionZeroAgreementSet c u₀ u₁ ⊆
      agreeSet c (fun i => u₀ i + γ • u₁ i) := by
  classical
  intro i hi
  rw [directionZeroAgreementSet, Finset.mem_filter] at hi
  have hzero : u₁ i = 0 := by
    simpa [directionZeroSet] using hi.1
  have hbase : c i = u₀ i := hi.2
  rw [agreeSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [hbase, hzero]
  simp

/-- Cardinal form of `directionZeroAgreementSet_subset_agreeSet_line`. -/
theorem directionZeroAgreementSet_card_le_agreeSet_line
    (c u₀ u₁ : Fin n → F) (γ : F) :
    (directionZeroAgreementSet c u₀ u₁).card
      ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card :=
  Finset.card_le_card (directionZeroAgreementSet_subset_agreeSet_line c u₀ u₁ γ)

open Classical in
/-- If the zero-direction agreements already meet the threshold, then the fixed codeword is heavy
for every scalar.  This is the sharp excluded branch for support-aware scalar counting. -/
theorem heavyScalarSet_eq_univ_of_directionZeroAgreement_ge (a : ℕ)
    (c u₀ u₁ : Fin n → F)
    (hzero : a ≤ (directionZeroAgreementSet c u₀ u₁).card) :
    ((Finset.univ : Finset F).filter
        (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card))
      = Finset.univ := by
  ext γ
  constructor
  · intro _; exact Finset.mem_univ γ
  · intro _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ γ,
        le_trans hzero (directionZeroAgreementSet_card_le_agreeSet_line c u₀ u₁ γ)⟩

open Classical in
/-- Cardinal form: the zero-direction threshold branch saturates the whole scalar field. -/
theorem heavyScalarSet_card_eq_field_card_of_directionZeroAgreement_ge (a : ℕ)
    (c u₀ u₁ : Fin n → F)
    (hzero : a ≤ (directionZeroAgreementSet c u₀ u₁).card) :
    ((Finset.univ : Finset F).filter
        (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)).card
      = Fintype.card F := by
  rw [heavyScalarSet_eq_univ_of_directionZeroAgreement_ge a c u₀ u₁ hzero,
    Finset.card_univ]

/-- The agreement set of a fixed `c` with the line word `w_γ` is the `γ`-fiber of the
pointwise slope `i ↦ (c i − u₀ i)/u₁ i` (when `u₁` is nonvanishing). -/
theorem agreeSet_line_eq_fiber (c u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) (γ : F) :
    agreeSet c (fun i => u₀ i + γ • u₁ i)
      = (Finset.univ : Finset (Fin n)).filter (fun i => (c i - u₀ i) / u₁ i = γ) := by
  ext i
  rw [agreeSet, Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨-, hi⟩
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [div_eq_iff (hu₁ i), smul_eq_mul] at *
    rw [show c i - u₀ i = γ * u₁ i from by rw [hi]; ring]
  · rintro ⟨-, hi⟩
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [div_eq_iff (hu₁ i)] at hi
    rw [smul_eq_mul, ← hi]; ring

open Classical in
/-- **The codeword heavy-scalar bound.** For a fixed codeword (indeed any word) `c` and a
nonvanishing direction `u₁`, the scalars `γ` whose line word `w_γ = u₀ + γ·u₁` agrees with
`c` on at least `a` points number at most `⌊n/a⌋`. -/
theorem codeword_heavy_scalar_card_le (a : ℕ) (ha : 1 ≤ a)
    (c u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) :
    ((Finset.univ : Finset F).filter
        (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)).card ≤ n / a := by
  classical
  set f : Fin n → F := fun i => (c i - u₀ i) / u₁ i with hf
  set H : Finset F := (Finset.univ : Finset F).filter
    (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card) with hH
  -- rewrite the heavy condition in terms of fibers of f
  have hHfib : H = (Finset.univ : Finset F).filter
      (fun γ => a ≤ ((Finset.univ : Finset (Fin n)).filter (fun i => f i = γ)).card) := by
    rw [hH]
    refine Finset.filter_congr fun γ _ => ?_
    rw [agreeSet_line_eq_fiber c u₀ u₁ hu₁ γ]
  -- the fibers of f partition the n domain points
  have hpart : (Finset.univ : Finset (Fin n)).card
      = ∑ γ ∈ (Finset.univ : Finset F),
          ((Finset.univ : Finset (Fin n)).filter (fun i => f i = γ)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (f i))
  have hn : ∑ γ ∈ (Finset.univ : Finset F),
      ((Finset.univ : Finset (Fin n)).filter (fun i => f i = γ)).card = n := by
    rw [← hpart, Finset.card_univ, Fintype.card_fin]
  -- every γ ∈ H has a heavy fiber
  have hmem : ∀ γ ∈ H, a ≤ ((Finset.univ : Finset (Fin n)).filter
      (fun i => f i = γ)).card := by
    intro γ hγ
    rw [hHfib] at hγ
    exact (Finset.mem_filter.mp hγ).2
  -- |H|·a ≤ Σ_{γ∈H} fiber ≤ Σ_all fiber = n
  have hlb : H.card * a ≤ ∑ γ ∈ H,
      ((Finset.univ : Finset (Fin n)).filter (fun i => f i = γ)).card := by
    calc H.card * a = ∑ _γ ∈ H, a := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ γ ∈ H, ((Finset.univ : Finset (Fin n)).filter (fun i => f i = γ)).card :=
          Finset.sum_le_sum hmem
  have hub : ∑ γ ∈ H,
      ((Finset.univ : Finset (Fin n)).filter (fun i => f i = γ)).card ≤ n :=
    le_trans (Finset.sum_le_sum_of_subset
      (hHfib ▸ Finset.filter_subset _ _)) (le_of_eq hn)
  have hfin : H.card * a ≤ n := le_trans hlb hub
  exact (Nat.le_div_iff_mul_le ha).mpr hfin

/-- Agreement with a fixed codeword is bounded by the zero-direction coordinates plus one moving
fiber of the pointwise scalar map on the nonzero support.  This is the support-aware replacement
for the everywhere-nonzero direction hypothesis. -/
theorem agreeSet_line_card_le_zero_add_movingFiber
    (c u₀ u₁ : Fin n → F) (γ : F) :
    (agreeSet c (fun i => u₀ i + γ • u₁ i)).card
      ≤ (directionZeroSet u₁).card +
        ((directionSupportSet u₁).filter
          (fun i => (c i - u₀ i) / u₁ i = γ)).card := by
  classical
  have hsub :
      agreeSet c (fun i => u₀ i + γ • u₁ i) ⊆
        directionZeroSet u₁ ∪
          ((directionSupportSet u₁).filter
            (fun i => (c i - u₀ i) / u₁ i = γ)) := by
    intro i hi
    rw [agreeSet, Finset.mem_filter] at hi
    by_cases hzero : u₁ i = 0
    · exact Finset.mem_union.mpr <| Or.inl <| by
        simp [directionZeroSet, hzero]
    · exact Finset.mem_union.mpr <| Or.inr <| by
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · simp [directionSupportSet, hzero]
        · rw [div_eq_iff hzero]
          rw [show c i - u₀ i = γ * u₁ i from by rw [hi.2]; ring]
  calc
    (agreeSet c (fun i => u₀ i + γ • u₁ i)).card
        ≤ (directionZeroSet u₁ ∪
            ((directionSupportSet u₁).filter
              (fun i => (c i - u₀ i) / u₁ i = γ))).card :=
          Finset.card_le_card hsub
    _ ≤ (directionZeroSet u₁).card +
        ((directionSupportSet u₁).filter
          (fun i => (c i - u₀ i) / u₁ i = γ)).card :=
          Finset.card_union_le _ _

open Classical in
/-- **Support-aware heavy-scalar bound.**  Let `z` be the number of zero coordinates of the
direction `u₁`.  If the agreement threshold `a` is larger than `z`, then a fixed codeword can be
heavy for at most `support(u₁) / (a - z)` scalars.  The old nowhere-zero bound is the special case
`z = 0`. -/
theorem codeword_heavy_scalar_card_le_support_div_sub_zero (a : ℕ)
    (c u₀ u₁ : Fin n → F) (hz : (directionZeroSet u₁).card < a) :
    ((Finset.univ : Finset F).filter
        (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)).card
      ≤ (directionSupportSet u₁).card / (a - (directionZeroSet u₁).card) := by
  classical
  set z : ℕ := (directionZeroSet u₁).card with hzdef
  set b : ℕ := a - z with hbdef
  have hbpos : 0 < b := by
    rw [hbdef, hzdef]
    exact Nat.sub_pos_of_lt hz
  have hb : 1 ≤ b := Nat.succ_le_iff.mpr hbpos
  set H : Finset F := (Finset.univ : Finset F).filter
    (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card) with hH
  let fiber : F → Finset (Fin n) := fun γ =>
    (directionSupportSet u₁).filter (fun i => (c i - u₀ i) / u₁ i = γ)
  have hpart : (directionSupportSet u₁).card =
      ∑ γ ∈ (Finset.univ : Finset F), (fiber γ).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (f := fun i => (c i - u₀ i) / u₁ i)
      (s := directionSupportSet u₁) (t := (Finset.univ : Finset F))
      (fun i _ => Finset.mem_univ _)
  have hmem : ∀ γ ∈ H, b ≤ (fiber γ).card := by
    intro γ hγ
    rw [hH] at hγ
    have hheavy : a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card :=
      (Finset.mem_filter.mp hγ).2
    have hcard := agreeSet_line_card_le_zero_add_movingFiber c u₀ u₁ γ
    have hle : a ≤ z + (fiber γ).card := by
      rw [hzdef]
      exact le_trans hheavy hcard
    rw [hbdef]
    exact (Nat.sub_le_iff_le_add).mpr (by simpa [add_comm] using hle)
  have hlb : H.card * b ≤ ∑ γ ∈ H, (fiber γ).card := by
    calc H.card * b = ∑ _γ ∈ H, b := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ γ ∈ H, (fiber γ).card := Finset.sum_le_sum hmem
  have hub : ∑ γ ∈ H, (fiber γ).card ≤ (directionSupportSet u₁).card :=
    le_trans (Finset.sum_le_sum_of_subset (hH ▸ Finset.filter_subset _ _)) (le_of_eq hpart.symm)
  have hfin : H.card * b ≤ (directionSupportSet u₁).card := le_trans hlb hub
  exact (Nat.le_div_iff_mul_le hb).mpr hfin

/-! ## Source audit -/

#print axioms directionZeroSet
#print axioms directionSupportSet
#print axioms directionZeroAgreementSet
#print axioms directionZeroAgreementSet_subset_agreeSet_line
#print axioms directionZeroAgreementSet_card_le_agreeSet_line
#print axioms heavyScalarSet_eq_univ_of_directionZeroAgreement_ge
#print axioms heavyScalarSet_card_eq_field_card_of_directionZeroAgreement_ge
#print axioms agreeSet_line_eq_fiber
#print axioms codeword_heavy_scalar_card_le
#print axioms agreeSet_line_card_le_zero_add_movingFiber
#print axioms codeword_heavy_scalar_card_le_support_div_sub_zero

end ProximityGap.Ownership
