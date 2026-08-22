/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# The exact-computation kit: `mcaEvent` decidability and the bad-count normal form

Support brick for the #357 exact-`δ*` programme (the R1 pin, the registered
monomial-orbit-extremality conjecture, and the n = 8 rung named as its falsifier (i)).

The exact-point campaign keeps re-proving the same three reductions by hand at each
instance (the R1 file does all three ad hoc at `RS[F₅, F₅*, 2]`):

1. the `ℝ≥0` cardinality clause of `mcaEvent` is an integer threshold (`t ≤ S.card`);
2. with that bridge, `mcaEvent` is **decidable** for any concrete code (membership
   decidable, everything else finite);
3. the per-stack bad-scalar probability is `(#bad γ)/|F|`, so
   `ε_mca = (worst-case bad-scalar count)/|F|` — the **bad-count normal form**, the shape in
   which every probe verdict (the flat-numerator law, the O137 extremality census, the exact
   ladder) is actually stated.

This file proves all three once, generically:

* `mcaEventNat` — the integer-threshold form of the bad event, with `Decidable` instances
  for it and for `pairJointAgreesOn` (given `DecidablePred (· ∈ C)`).
* `mcaEvent_iff_mcaEventNat` / `mcaEvent_iff_mcaEventNat_ceil` — the bridge, in hypothesis
  form (any `t` satisfying the clause-equivalence) and closed form (`t = ⌈(1−δ)·n⌉₊`);
  `card_clause_bridge_of_eq` discharges the hypothesis when `(1−δ)·n` is exactly integral
  (the `δ = j/n` grid every exact rung lives on).
* `badScalarCount` — the **computable** bad-scalar census of a stack.
* `prob_mcaEvent_eq_badScalarCount_div` — `Pr[mcaEvent] = badScalarCount / |F|`.
* `epsMCA_eq_sup_badScalarCount` — **the bad-count normal form**:
  `ε_mca(C, δ) = (max over stacks of badScalarCount) / |F|`.

Composed with the syndrome factorization (`epsMCA_eq_iSup_syndromeProb`) and the S3 orbit
engine (`epsMCA_eq_iSup_subtype_of_reps`), the sup can then be restricted to syndrome-class
or orbit representatives — together these make exact `ε_mca` values at the next rungs a
finite, kernel-checkable computation rather than a bespoke proof.

## References
- [ABF26] ePrint 2026/680, Definition 4.3. Issue #357 (the exact-point programme).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCAExactKit

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## Decidability of the joint-explanation clause -/

/-- `pairJointAgreesOn` is decidable once code membership is: the explanation pair ranges
over the finite type `ι → A`. -/
instance instDecidablePairJointAgreesOn (C : Set (ι → A)) [DecidablePred (· ∈ C)]
    (S : Finset ι) (u₀ u₁ : ι → A) : Decidable (pairJointAgreesOn C S u₀ u₁) :=
  decidable_of_iff (∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ S, v₀ i = u₀ i ∧ v₁ i = u₁ i) Iff.rfl

/-! ## The integer-threshold form of the bad event -/

/-- `mcaEvent` with the `ℝ≥0` cardinality clause replaced by an integer threshold
`t ≤ S.card`. For `t = ⌈(1−δ)·n⌉₊` this is *equivalent* to `mcaEvent C δ`
(`mcaEvent_iff_mcaEventNat_ceil`) — and, unlike `mcaEvent`, it is decidable. -/
def mcaEventNat (C : Set (ι → A)) (t : ℕ) (u₀ u₁ : ι → A) (γ : F) : Prop :=
  ∃ S : Finset ι, t ≤ S.card ∧
    (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
    ¬ pairJointAgreesOn C S u₀ u₁

instance instDecidableMcaEventNat (C : Set (ι → A)) [DecidablePred (· ∈ C)]
    (t : ℕ) (u₀ u₁ : ι → A) (γ : F) : Decidable (mcaEventNat C t u₀ u₁ γ) :=
  decidable_of_iff (∃ S : Finset ι, t ≤ S.card ∧
    (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
    ¬ pairJointAgreesOn C S u₀ u₁) Iff.rfl

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- **The bridge, hypothesis form.** Any integer threshold `t` equivalent to the `ℝ≥0`
cardinality clause turns `mcaEvent` into `mcaEventNat`. -/
theorem mcaEvent_iff_mcaEventNat (C : Set (ι → A)) {δ : ℝ≥0} {t : ℕ}
    (ht : ∀ S : Finset ι,
      ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0)) ↔ t ≤ S.card)
    (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) C δ u₀ u₁ γ ↔ mcaEventNat C t u₀ u₁ γ :=
  exists_congr fun S => and_congr_left' (ht S)

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- The cardinality clause at threshold `⌈(1−δ)·n⌉₊`, via `Nat.ceil_le`. -/
theorem card_clause_iff_ceil {δ : ℝ≥0} (S : Finset ι) :
    ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0)) ↔
      ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ ≤ S.card :=
  ge_iff_le.trans Nat.ceil_le.symm

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- **The bridge, closed form:** `mcaEvent C δ` is `mcaEventNat` at threshold
`⌈(1−δ)·n⌉₊`. -/
theorem mcaEvent_iff_mcaEventNat_ceil (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) C δ u₀ u₁ γ ↔
      mcaEventNat C ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ u₀ u₁ γ :=
  mcaEvent_iff_mcaEventNat C (fun S => card_clause_iff_ceil S) u₀ u₁ γ

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- **Bridge discharge on the grid.** When `(1−δ)·n` is exactly the integer `t` (the
`δ = j/n` grid where every exact rung lives), the hypothesis of
`mcaEvent_iff_mcaEventNat` holds at `t`. -/
theorem card_clause_bridge_of_eq {δ : ℝ≥0} {t : ℕ}
    (h : (1 - δ) * (Fintype.card ι : ℝ≥0) = t) :
    ∀ S : Finset ι,
      ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0)) ↔ t ≤ S.card := by
  intro S
  rw [h, ge_iff_le, Nat.cast_le]

/-! ## The computable bad-scalar census -/

/-- The bad-scalar count of a stack at integer threshold `t` — a **computable** `ℕ`. -/
def badScalarCount (C : Set (ι → A)) [DecidablePred (· ∈ C)] (t : ℕ)
    (u₀ u₁ : ι → A) : ℕ :=
  (Finset.univ.filter (fun γ : F => mcaEventNat C t u₀ u₁ γ)).card

open Classical in
/-- **The per-stack probability is the census over the field size.** -/
theorem prob_mcaEvent_eq_badScalarCount_div (C : Set (ι → A)) [DecidablePred (· ∈ C)]
    {δ : ℝ≥0} {t : ℕ}
    (ht : ∀ S : Finset ι,
      ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0)) ↔ t ≤ S.card)
    (u₀ u₁ : ι → A) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) C δ u₀ u₁ γ]
      = (badScalarCount (F := F) C t u₀ u₁ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [prob_uniform_eq_card_filter_div_card]
  have hcard : (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ u₀ u₁ γ)).card
      = badScalarCount (F := F) C t u₀ u₁ :=
    congrArg Finset.card
      (Finset.filter_congr fun γ _ => mcaEvent_iff_mcaEventNat C ht u₀ u₁ γ)
  rw [hcard]
  simp only [ENNReal.coe_natCast]

/-! ## The bad-count normal form of `ε_mca` -/

omit [DecidableEq ι] in
open Classical in
/-- A finite supremum of `ℕ`-casts in `ℝ≥0∞` is the cast of the `Finset.sup`. -/
theorem iSup_natCast_eq_sup_cast {α : Type} [Fintype α] [Nonempty α] (c : α → ℕ) :
    (⨆ a : α, ((c a : ℕ) : ℝ≥0∞)) = ((Finset.univ.sup c : ℕ) : ℝ≥0∞) := by
  apply le_antisymm
  · exact iSup_le fun a => Nat.cast_le.mpr (Finset.le_sup (Finset.mem_univ a))
  · obtain ⟨a₀, _, ha₀⟩ :=
      Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty c
    rw [ha₀]
    exact le_iSup (fun a : α => ((c a : ℕ) : ℝ≥0∞)) a₀

open Classical in
/-- **The bad-count normal form.** `ε_mca(C, δ)` equals the worst-case bad-scalar census
over all stacks, divided by `|F|` — the exact shape of every probe-lab verdict (the
flat-numerator law, the extremality censuses, the exact ladder), now available as the
generic target for kernel computation at concrete instances. -/
theorem epsMCA_eq_sup_badScalarCount (C : Set (ι → A)) [DecidablePred (· ∈ C)]
    {δ : ℝ≥0} {t : ℕ}
    (ht : ∀ S : Finset ι,
      ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0)) ↔ t ≤ S.card) :
    epsMCA (F := F) (A := A) C δ
      = ((Finset.univ.sup (fun u : WordStack A (Fin 2) ι =>
            badScalarCount (F := F) C t (u 0) (u 1)) : ℕ) : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) := by
  have h1 : (⨆ u : WordStack A (Fin 2) ι,
        Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) C δ (u 0) (u 1) γ])
      = ⨆ u : WordStack A (Fin 2) ι,
          (badScalarCount (F := F) C t (u 0) (u 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
    iSup_congr fun u => prob_mcaEvent_eq_badScalarCount_div C ht (u 0) (u 1)
  have h2 : (⨆ u : WordStack A (Fin 2) ι,
        (badScalarCount (F := F) C t (u 0) (u 1) : ℝ≥0∞)) / (Fintype.card F : ℝ≥0∞)
      = ⨆ u : WordStack A (Fin 2) ι,
          (badScalarCount (F := F) C t (u 0) (u 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
    ENNReal.iSup_div _ _
  have h3 : (⨆ u : WordStack A (Fin 2) ι,
        (badScalarCount (F := F) C t (u 0) (u 1) : ℝ≥0∞))
      = ((Finset.univ.sup (fun u : WordStack A (Fin 2) ι =>
            badScalarCount (F := F) C t (u 0) (u 1)) : ℕ) : ℝ≥0∞) :=
    iSup_natCast_eq_sup_cast (fun u : WordStack A (Fin 2) ι =>
      badScalarCount (F := F) C t (u 0) (u 1))
  unfold epsMCA
  rw [h1, ← h2, h3]

/-! ## Source audit -/

#print axioms mcaEvent_iff_mcaEventNat_ceil
#print axioms card_clause_bridge_of_eq
#print axioms prob_mcaEvent_eq_badScalarCount_div
#print axioms iSup_natCast_eq_sup_cast
#print axioms epsMCA_eq_sup_badScalarCount

end ProximityGap.MCAExactKit
