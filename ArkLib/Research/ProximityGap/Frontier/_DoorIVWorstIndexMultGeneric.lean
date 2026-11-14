/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

/-!
# Door IV worst-index multiplicative genericity: no power-coset restriction

This file records the axiom-clean obstruction behind the probe
`scripts/probes/probe_dooriv_worstb_subfield2.py`.

## Probe context (door-(iv) Lane 1)

The worst frequency `b` for `CORE` (the `argmax_b |S(b)|`) is determined, up to the `μ_n`-coset
`b·μ_n`, by its **coset index** `I ∈ Z_m`, `m = (p−1)/n`.  An earlier probe
(`probe_dooriv_worstb_class_structure`, push `a2ad4130b`) established that this index is
**additively** generic: no `2`-adic, AP, or `mod d` residue structure.  The companion probe here
tests the remaining, **multiplicative** half.

Over `~200–300` structured primes per `n = 16, 32, 64` (proper `μ_n`, `p ≫ n³`), the fraction of
worst-`b` coset indices that are *quadratic residues* (mod the largest prime factor of `m`) is

`0.5051 (z=+0.17),  0.4595 (z=−1.39),  0.4949 (z=−0.14)`,

all within `~2` standard errors of `0.5`.  So the worst-index set is **multiplicatively generic**:
it contains both residues and non-residues, hence is *not* confined to any single coset of the
subgroup of `d`-th powers.  Together with the additive result this closes the worst-index
class-restriction map: **no class-restriction lever — additive or multiplicative — can thin the
door-(iv) worst-`b` search.**

## The brick

The enabling obstruction (multiplicative analogue of `a2ad4130b`'s `no_proper_progression`): we
model a left coset of a subgroup `H ≤ G` by the predicate `inCoset g x := g⁻¹ * x ∈ H`.  Any two
elements of the same coset have a ratio in `H` (`ratio_mem_of_inCoset`).  Consequently, if a set `s`
contains two elements `a, b` with `b⁻¹ · a ∉ H`, then `s` is **not contained in any single coset**
of `H` (`not_subset_coset_of_ratio_not_mem`).  Specialized to the squares subgroup this is exactly
"an index set with both a QR and a non-QR is not power-coset restricted", turning the probe's flat
QR-rate into a genuine no-restriction statement.  This is a constraint lemma, not `CORE`, and uses
no moment or completion.
-/

namespace ProximityGap.Frontier.DoorIVWorstIndexMultGeneric

variable {G : Type*} [Group G]

/-- Coset-membership predicate: `x` is in the left coset `g · H` iff `g⁻¹ * x ∈ H`. -/
def inCoset (H : Subgroup G) (g x : G) : Prop := g⁻¹ * x ∈ H

/-- Two elements of the same left coset `g · H` have a ratio `b⁻¹ * a ∈ H`.  (For a *left* coset the
left-invariant ratio is `b⁻¹ * a`; in the abelian specialization this is the usual `a * b⁻¹`.) -/
theorem ratio_mem_of_inCoset {H : Subgroup G} {g a b : G}
    (ha : inCoset H g a) (hb : inCoset H g b) : b⁻¹ * a ∈ H := by
  unfold inCoset at ha hb
  -- b⁻¹ * a = (g⁻¹ * b)⁻¹ * (g⁻¹ * a)
  have hkey : b⁻¹ * a = (g⁻¹ * b)⁻¹ * (g⁻¹ * a) := by group
  rw [hkey]
  exact H.mul_mem (H.inv_mem hb) ha

/-- **No-coset-restriction obstruction.**  If a set `s` contains two elements whose ratio lies
*outside* a subgroup `H`, then `s` is not contained in any single left coset of `H`.  This is the
multiplicative analogue of "two elements with distinct residues ⟹ no AP". -/
theorem not_subset_coset_of_ratio_not_mem {H : Subgroup G} {s : Set G} {a b : G}
    (ha : a ∈ s) (hb : b ∈ s) (hne : b⁻¹ * a ∉ H) :
    ∀ g : G, ¬ (∀ x ∈ s, inCoset H g x) := by
  intro g hsub
  exact hne (ratio_mem_of_inCoset (hsub a ha) (hsub b hb))

/-- Finite-index-set interface for `not_subset_coset_of_ratio_not_mem`.  This is the shape used by
worst-`b` probes, which return a finite candidate set of observed coset indices: one escaping pair
ratio already certifies that the whole finite set is not contained in any single subgroup coset. -/
theorem not_finset_subset_coset_of_ratio_not_mem
    {H : Subgroup G} {s : Finset G} {a b : G}
    (ha : a ∈ s) (hb : b ∈ s) (hne : b⁻¹ * a ∉ H) :
    ∀ g : G, ¬ (∀ x ∈ s, inCoset H g x) := by
  intro g hsub
  exact (not_subset_coset_of_ratio_not_mem (H := H) (s := (s : Set G))
    (a := a) (b := b) (by simpa using ha) (by simpa using hb) hne) g (by
      intro x hx
      exact hsub x (by simpa using hx))

end ProximityGap.Frontier.DoorIVWorstIndexMultGeneric

namespace ProximityGap.Frontier.DoorIVWorstIndexMultGeneric

/-!
### Specialization to the squares subgroup

The worst-index probe finds both a QR and a non-QR in the worst-index set, i.e. two elements whose
ratio is a non-square; the general lemma above then forbids any single power-coset restriction.  We
package the squares subgroup (in an abelian group) and the specialized obstruction. -/

/-- The subgroup of squares in an abelian group (range of the squaring endomorphism). -/
def squares (A : Type*) [CommGroup A] : Subgroup A where
  carrier := {x | ∃ y, y * y = x}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro x z ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, by rw [mul_mul_mul_comm]⟩
  inv_mem' := by
    rintro x ⟨a, rfl⟩
    exact ⟨a⁻¹, by rw [mul_inv]⟩

theorem mem_squares_iff {A : Type*} [CommGroup A] {x : A} :
    x ∈ squares A ↔ ∃ y, y * y = x := Iff.rfl

/-- Necessary pair-ratio condition for a quadratic-power-coset restriction.  If a set is contained
in one coset of the squares subgroup, then every ratio of two selected elements is a square.  This is
the positive certificate whose contrapositive is exactly the QR/non-QR obstruction below. -/
theorem ratio_mem_squares_of_subset_coset {A : Type*} [CommGroup A] {s : Set A}
    {g a b : A} (hsub : ∀ x ∈ s, inCoset (squares A) g x)
    (ha : a ∈ s) (hb : b ∈ s) :
    b⁻¹ * a ∈ squares A :=
  ratio_mem_of_inCoset (hsub a ha) (hsub b hb)

/-- **Worst-index multiplicative genericity ⟹ no power-coset restriction.**  If the worst-index
set `s` (inside an abelian group `A`) contains elements `a, b` such that `b⁻¹ · a` is *not* a square
(the QR/non-QR coexistence the probe finds), then `s` is contained in no single coset of the squares
subgroup — the multiplicative class-restriction lever is unavailable. -/
theorem not_power_coset_restricted {A : Type*} [CommGroup A] {s : Set A} {a b : A}
    (ha : a ∈ s) (hb : b ∈ s) (hns : b⁻¹ * a ∉ squares A) :
    ∀ g : A, ¬ (∀ x ∈ s, inCoset (squares A) g x) :=
  not_subset_coset_of_ratio_not_mem ha hb hns

/-- Finset-facing squares version.  This is the literal shape of the QR/non-QR probe certificate:
a finite observed worst-index set containing one pair with non-square ratio is not confined to one
quadratic-residue coset. -/
theorem not_finset_power_coset_restricted {A : Type*} [CommGroup A]
    {s : Finset A} {a b : A}
    (ha : a ∈ s) (hb : b ∈ s) (hns : b⁻¹ * a ∉ squares A) :
    ∀ g : A, ¬ (∀ x ∈ s, inCoset (squares A) g x) := by
  intro g hsub
  exact (not_power_coset_restricted (s := (s : Set A)) (a := a) (b := b)
    (by simpa using ha) (by simpa using hb) hns) g (by
      intro x hx
      exact hsub x (by simpa using hx))

/-!
### General `k`-th power cosets

The same obstruction is not special to quadratic residues.  If a proposed worst-index selector is
confined to one coset of `k`-th powers, every pairwise ratio must be a `k`-th power.  Thus one
observed ratio outside the `k`-th-power subgroup is a kernel-checkable certificate that the selector
is not a single power-coset restriction.
-/

/-- The subgroup of `k`-th powers in an abelian group. -/
def kthPowers (A : Type*) [CommGroup A] (k : ℕ) : Subgroup A where
  carrier := {x | ∃ y, y ^ k = x}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro x z ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, by rw [mul_pow]⟩
  inv_mem' := by
    rintro x ⟨a, rfl⟩
    exact ⟨a⁻¹, by simp⟩

theorem mem_kthPowers_iff {A : Type*} [CommGroup A] {k : ℕ} {x : A} :
    x ∈ kthPowers A k ↔ ∃ y, y ^ k = x := Iff.rfl

/-- Necessary pair-ratio condition for a `k`-th-power coset restriction.  If a set `s` is contained
in one coset of `kthPowers A k`, then every ratio `b⁻¹ * a` of two elements of `s` is itself a
`k`-th power.  This is the positive certificate whose contrapositive is the no-restriction lemma. -/
theorem ratio_mem_kthPowers_of_subset_coset {A : Type*} [CommGroup A] {k : ℕ} {s : Set A}
    {g a b : A} (hsub : ∀ x ∈ s, inCoset (kthPowers A k) g x)
    (ha : a ∈ s) (hb : b ∈ s) :
    b⁻¹ * a ∈ kthPowers A k :=
  ratio_mem_of_inCoset (hsub a ha) (hsub b hb)

/-- **General power-coset obstruction.**  If `s` contains two elements whose ratio is not a `k`-th
power, then `s` is contained in no single coset of the `k`-th-power subgroup.  This packages the
Lane-1 worst-index verdict for any multiplicative power-class restriction, not only QR/non-QR. -/
theorem not_kth_power_coset_restricted {A : Type*} [CommGroup A] {k : ℕ} {s : Set A} {a b : A}
    (ha : a ∈ s) (hb : b ∈ s) (hnp : b⁻¹ * a ∉ kthPowers A k) :
    ∀ g : A, ¬ (∀ x ∈ s, inCoset (kthPowers A k) g x) :=
  not_subset_coset_of_ratio_not_mem ha hb hnp

/-- Finset-facing `k`-th-power version: if a finite observed worst-index set contains one pair whose
ratio is not a `k`-th power, then it is not confined to a single `k`-th-power coset. -/
theorem not_finset_kth_power_coset_restricted {A : Type*} [CommGroup A]
    {k : ℕ} {s : Finset A} {a b : A}
    (ha : a ∈ s) (hb : b ∈ s) (hnp : b⁻¹ * a ∉ kthPowers A k) :
    ∀ g : A, ¬ (∀ x ∈ s, inCoset (kthPowers A k) g x) := by
  intro g hsub
  exact (not_kth_power_coset_restricted (s := (s : Set A)) (a := a) (b := b)
    (by simpa using ha) (by simpa using hb) hnp) g (by
      intro x hx
      exact hsub x (by simpa using hx))

end ProximityGap.Frontier.DoorIVWorstIndexMultGeneric

#print axioms ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.ratio_mem_of_inCoset
#print axioms ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.not_subset_coset_of_ratio_not_mem
#print axioms ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.not_finset_subset_coset_of_ratio_not_mem
#print axioms ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.ratio_mem_squares_of_subset_coset
#print axioms ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.not_power_coset_restricted
#print axioms ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.not_finset_power_coset_restricted
#print axioms ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.ratio_mem_kthPowers_of_subset_coset
#print axioms ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.not_kth_power_coset_restricted
#print axioms ProximityGap.Frontier.DoorIVWorstIndexMultGeneric.not_finset_kth_power_coset_restricted
