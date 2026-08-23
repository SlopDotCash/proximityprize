/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.AgreementSetPacking

/-!
# Multiplicity-aware agreement-set packing: `#pinned · C(a,k+1) ≤ C(n,k+1)` (issue #444,
under-det / agreement-sharing face)

`AgreementSetPacking.pinnedScalars_card_le_choose` packs the distinct-`γ` count by mapping each
pinned `γ` to ONE non-degenerate `(k+1)`-tuple it owns, giving the LOOSE bound
`#pinnedScalars ≤ C(n, k+1)`.  That bound has multiplicity `1`: it throws away all but one of the
many `(k+1)`-subtuples a pinned scalar's aligned `a`-set carries.

`PinnedScalarMultDivision` noted the missing ingredient for the tighter distinct-`γ` bound is a
**uniform multiplicity floor `M`**, and that it does NOT supply `M`.  This file supplies that floor
*via the packing (overlap) lever*, not the incidence-division lever:

> **Multiplicity-aware packing.** An aligned `a`-set `S_γ` has EVERY `(k+1)`-subset `γ`-aligned
> (alignment is subset-monotone, `Aligned.mono`), so it carries `C(a, k+1)` distinct `γ`-aligned
> `(k+1)`-subsets.  By the overlap law (`gamma_eq_of_shared_nondeg_tuple`), a `(k+1)`-subset that is
> **non-degenerate** is aligned for at most ONE scalar.  Hence, in the regime where each pinned
> scalar owns an `a`-set whose `(k+1)`-subtuples are ALL non-degenerate (the general-position band
> the under-det probe operates in), the per-scalar `(k+1)`-subset classes of size `C(a,k+1)` are
> pairwise DISJOINT, packing into the `C(n,k+1)` `(k+1)`-subsets of the domain:
>
>   **`#pinnedScalars · C(a, k+1) ≤ C(n, k+1)`     ⟹     `#pinnedScalars ≤ C(n,k+1) / C(a,k+1)`.**

This is the multiplicity floor `M = C(a, k+1)` the division route lacked, derived purely from the
overlap law.

## Probe: `scripts/probes/probe_underdet_aset_tuple_packing.py`
Exact `F_p`, PROPER thin `μ_n = ⟨g^{(p−1)/n}⟩`, prize band `p ≈ n⁴`, `n | p−1`, NEVER `n = q−1`.
Planting deep aligned `a`-sets and measuring per-`γ` non-degenerate `(k+1)`-tuple counts confirms:
* each pinned `γ` owns **exactly `C(a,k+1)`** non-degenerate `(k+1)`-subtuples of its `a`-set
  (`[15,15,15,15] = C(6,2)`, `[35] = C(7,3)`, `[28] = C(8,2)`, `[84] = C(9,3)`, `[66] = C(12,2)`);
* the tuple-classes are DISJOINT across distinct `γ` (overlap law);
* the deflated bound `C(n,k+1)/C(a,k+1)` is **substantial** (deflation ×15, ×28, ×84, …) and at the
  prize band `a ≈ n/2` reaches the budget `~ n` (n=16, a=8: bound 4 ≤ 16; n=32, a=12: 7 ≤ 32).
A companion probe (`probe_underdet_nondeg_tuple_packing.py`) shows that WITHOUT the `a`-set
requirement (raw single tuples, generic words) the per-`γ` multiplicity is `1`, so the deflation is
genuinely supplied by the `a`-set / general-position structure, not by the bare overlap law.

## Scope (rules 3, 6: honesty contract)
* NOT a CORE closure, NOT thinness-essential: this is field-universal combinatorics about the
  alignment census, sharpening the under-det / agreement-sharing face.
* **Honest conditionality.** The `C(a,k+1)` floor is proved under the explicit hypothesis that each
  pinned scalar owns an aligned `a`-set whose `(k+1)`-subtuples are all non-degenerate (the
  `AllSubtuplesNondeg` predicate).  The probe verifies this holds for planted general-position
  `a`-sets; it can FAIL for `a`-sets sitting on a lower-degree subvariety (where many subtuples
  jointly vanish).  Without the hypothesis the bound degrades to the unconditional
  `pinnedScalars_card_le_choose` (`M = 1`).  This mirrors the κ₆-rung pattern: an exact structural
  identity gated on a probe-verified general-position hypothesis.
* Consistent with the growth-law resolution: at the prize band `a ≈ n/2` the deflated bound lands at
  the budget `~ n` (Johnson), NOT below it; so this packing does NOT itself open a window-interior
  gap.  Any beyond-Johnson lift lives in the per-`γ` char-sum (BGK) wall, which this does not touch.
  CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

/-- **General-position predicate.** Every injective `(k+1)`-tuple inside `S` is non-degenerate
(the residual pencil does not jointly vanish).  This is the regime the under-det probe operates in;
it is what upgrades the bare overlap law to the `C(a,k+1)` multiplicity floor. -/
def AllSubtuplesNondeg (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) : Prop :=
  ∀ t : Fin (k + 1) → Fin n, Function.Injective t → (∀ b, t b ∈ S) →
    ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)

/-- **The `(k+1)`-subset class of a pinned scalar's `a`-set.**  All `(k+1)`-subsets of `S`
(there are `C(a, k+1)` of them when `|S| = a`).  Under general position these are non-degenerate,
`γ`-aligned `(k+1)`-subsets owned by `γ`. -/
noncomputable def tupleClass (S : Finset (Fin n)) (k : ℕ) : Finset (Finset (Fin n)) :=
  S.powersetCard (k + 1)

theorem mem_tupleClass {S : Finset (Fin n)} {k : ℕ} {T : Finset (Fin n)} :
    T ∈ tupleClass S k ↔ T ⊆ S ∧ T.card = k + 1 := by
  unfold tupleClass; rw [Finset.mem_powersetCard]

/-- `tupleClass` of an `a`-set has card `C(a, k+1)`. -/
theorem card_tupleClass {S : Finset (Fin n)} {k a : ℕ} (hS : S.card = a) :
    (tupleClass S k).card = a.choose (k + 1) := by
  unfold tupleClass; rw [Finset.card_powersetCard, hS]

omit [Fintype F] [DecidableEq F] in
/-- **Enumerate a `(k+1)`-card finset as an injective `(k+1)`-tuple** (via `orderEmbOfFin`). -/
theorem exists_tuple_of_card {S : Finset (Fin n)} {k : ℕ} (hcard : S.card = k + 1) :
    ∃ t : Fin (k + 1) → Fin n, Function.Injective t ∧ ∀ b, t b ∈ S := by
  let e := S.orderEmbOfFin hcard
  exact ⟨fun i => e i, e.injective, fun i => S.orderEmbOfFin_mem hcard i⟩

omit [Fintype F] [DecidableEq F] in
/-- **DISJOINTNESS of tuple-classes across distinct pinned scalars** (general-position form).
If `S` is a general-position `γ`-aligned `a`-set and `S'` a `γ'`-aligned set with `γ ≠ γ'`, then
their `(k+1)`-subset classes are DISJOINT: a shared `(k+1)`-subset `T ⊆ S ∩ S'` would be a
non-degenerate `(k+1)`-tuple aligned for both, forcing `γ = γ'` by the overlap law. -/
theorem tupleClass_disjoint {dom : Fin n ↪ F} {k : ℕ} {u₀ u₁ : Fin n → F} {γ γ' : F} (hne : γ ≠ γ')
    {S S' : Finset (Fin n)}
    (hSal : Aligned dom k u₀ u₁ γ S) (hSnd : AllSubtuplesNondeg dom k u₀ u₁ S)
    (hS'al : Aligned dom k u₀ u₁ γ' S') :
    Disjoint (tupleClass S k) (tupleClass S' k) := by
  classical
  rw [Finset.disjoint_left]
  intro T hT hT'
  rw [mem_tupleClass] at hT hT'
  obtain ⟨hTS, hTcard⟩ := hT
  obtain ⟨hTS', -⟩ := hT'
  obtain ⟨t, htinj, htmemT⟩ := exists_tuple_of_card hTcard
  have htmemS : ∀ b, t b ∈ S := fun b => hTS (htmemT b)
  have htmemS' : ∀ b, t b ∈ S' := fun b => hTS' (htmemT b)
  have hnd := hSnd t htinj htmemS
  have hmemInter : ∀ b, t b ∈ S ∩ S' := fun b => Finset.mem_inter.mpr ⟨htmemS b, htmemS' b⟩
  exact hne (gamma_eq_of_shared_nondeg_tuple hSal hS'al htinj hmemInter hnd)

/-- A `tupleClass S k` for `S ⊆ univ` lands inside the `(k+1)`-subsets of `univ`. -/
theorem tupleClass_subset_univ_powerset (S : Finset (Fin n)) (k : ℕ) :
    tupleClass S k ⊆ (Finset.univ : Finset (Fin n)).powersetCard (k + 1) := by
  intro T hT
  rw [mem_tupleClass] at hT
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ _, hT.2⟩

open Classical in
/-- **THE MULTIPLICITY-AWARE PACKING BOUND.**  Suppose every pinned scalar `γ` owns a
general-position aligned `a`-set `S_γ` (all of its `(k+1)`-subtuples non-degenerate).  Then the
distinct-`γ` count packs with multiplicity `C(a, k+1)`:

> **`#pinnedScalars · C(a, k+1) ≤ C(n, k+1)`.**

This is the floor `M = C(a, k+1)` the division route lacked, from the overlap law alone. -/
theorem pinnedScalars_card_mul_choose_le
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hown : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      ∃ S : Finset (Fin n), S.card = a ∧ Aligned dom k u₀ u₁ γ S ∧
        AllSubtuplesNondeg dom k u₀ u₁ S) :
    (pinnedScalars dom k a u₀ u₁).card * a.choose (k + 1) ≤ n.choose (k + 1) := by
  classical
  -- Choose a general-position aligned a-set for each pinned scalar.
  choose Sγ hcardγ halignγ hndγ using hown
  -- The per-scalar (k+1)-subset class, packaged as a dependent function of the membership proof.
  let cls : ∀ γ, γ ∈ pinnedScalars dom k a u₀ u₁ → Finset (Finset (Fin n)) :=
    fun γ hγ => tupleClass (Sγ γ hγ) k
  -- The disjoint union of their tuple-classes lands in the (k+1)-subsets of univ.
  have hdisj : ∀ γ ∈ pinnedScalars dom k a u₀ u₁, ∀ γ' ∈ pinnedScalars dom k a u₀ u₁, γ ≠ γ' →
      ∀ hγ hγ', Disjoint (cls γ hγ) (cls γ' hγ') := by
    intro γ hγ₀ γ' hγ'₀ hne hγ hγ'
    exact tupleClass_disjoint hne (halignγ γ hγ) (hndγ γ hγ) (halignγ γ' hγ')
  -- Sum over attach so each summand can use the membership proof.
  have hbsub : (pinnedScalars dom k a u₀ u₁).attach.biUnion (fun p => cls p.1 p.2)
      ⊆ (Finset.univ : Finset (Fin n)).powersetCard (k + 1) := by
    intro T hT
    rw [Finset.mem_biUnion] at hT
    obtain ⟨p, -, hTmem⟩ := hT
    exact tupleClass_subset_univ_powerset _ _ hTmem
  have hcard_bUnion : ((pinnedScalars dom k a u₀ u₁).attach.biUnion (fun p => cls p.1 p.2)).card
      = ∑ p ∈ (pinnedScalars dom k a u₀ u₁).attach, (cls p.1 p.2).card := by
    apply Finset.card_biUnion
    rintro ⟨γ, hγ⟩ - ⟨γ', hγ'⟩ - hpne
    have hne : γ ≠ γ' := fun h => hpne (Subtype.ext h)
    exact hdisj γ hγ γ' hγ' hne hγ hγ'
  -- Each class has card C(a,k+1); sum = |P| * C(a,k+1).
  have hsum : ∑ p ∈ (pinnedScalars dom k a u₀ u₁).attach, (cls p.1 p.2).card
      = (pinnedScalars dom k a u₀ u₁).card * a.choose (k + 1) := by
    rw [Finset.sum_congr rfl (fun p _ => card_tupleClass (hcardγ p.1 p.2))]
    rw [Finset.sum_const, Finset.card_attach, smul_eq_mul]
  calc (pinnedScalars dom k a u₀ u₁).card * a.choose (k + 1)
      = ∑ p ∈ (pinnedScalars dom k a u₀ u₁).attach, (cls p.1 p.2).card := hsum.symm
    _ = ((pinnedScalars dom k a u₀ u₁).attach.biUnion (fun p => cls p.1 p.2)).card :=
        hcard_bUnion.symm
    _ ≤ ((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).card :=
        Finset.card_le_card hbsub
    _ = n.choose (k + 1) := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **The deflated distinct-`γ` bound** (division form): when each pinned scalar owns a
general-position aligned `a`-set and `C(a,k+1) > 0`,
> **`#pinnedScalars ≤ C(n,k+1) / C(a,k+1)`.** -/
theorem pinnedScalars_card_le_choose_div
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hpos : 0 < a.choose (k + 1))
    (hown : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      ∃ S : Finset (Fin n), S.card = a ∧ Aligned dom k u₀ u₁ γ S ∧
        AllSubtuplesNondeg dom k u₀ u₁ S) :
    (pinnedScalars dom k a u₀ u₁).card ≤ n.choose (k + 1) / a.choose (k + 1) := by
  rw [Nat.le_div_iff_mul_le hpos]
  exact pinnedScalars_card_mul_choose_le dom k a u₀ u₁ hown

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.tupleClass_disjoint
#print axioms ProximityGap.Ownership.pinnedScalars_card_mul_choose_le
#print axioms ProximityGap.Ownership.pinnedScalars_card_le_choose_div
