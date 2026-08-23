/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.Quarantine.DisproofLoop6
import Mathlib.Algebra.Order.Field.Basic

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-!
# Loop 7 — conditional Frobenius disproofs and their first self-refutation

Loop 6 isolated a real obstruction: if a Frobenius-stable bad-scalar set is bounded by a
field-independent constant `C`, then every bad scalar has bounded Frobenius degree. A high-degree
bad scalar would therefore be a promising disproof mechanism.

Loop 7 keeps three reusable pieces:

* a conditional contradiction: a constant bad-count bound plus a bad scalar whose Frobenius degree
  exceeds that constant is impossible;
* an abstract filter form: any Frobenius-invariant bad-event predicate inherits the same orbit
  lower bound, so the obstruction is not specific to one presentation of the event;
* the first disproof of the disproof: the toy Frobenius constructions found so far sit extremely
  close to capacity, with `η ≲ A / d`. In that regime a linear orbit lower bound `#bad = O(d)` is
  only `O(1 / η)`, and the prize RHS is explicitly allowed to contain an `η^{-c₃}` factor.

Thus near-capacity linear-orbit growth cannot refute the field-universal prize by itself; to beat
the conjecture one needs either a high-degree orbit at fixed gap, or bad-count growth faster than
every permitted polynomial in `1/η` and the interleaving width.
-/

namespace ArkLib.ProximityGap.DisproofLoop7

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Conditional Frobenius disproof.** If a Frobenius-closed bad set has the conjectural
constant-cardinality bound `#S ≤ C`, but contains a scalar whose first `d` Frobenius iterates are
distinct with `C < d`, then the assumptions are inconsistent.

This packages Loop 6's orbit lower bound in the exact "realizing a high-degree bad scalar would
disprove the constant bad-count claim" form. -/
theorem realizing_high_degree_bad_scalar_disproves
    {p : ℕ} {S : Finset F} {C : ℝ} {y : F} {d : ℕ}
    (hclosed : ∀ x ∈ S, x ^ p ∈ S)
    (hbound : (S.card : ℝ) ≤ C)
    (hy : y ∈ S)
    (hinj : Set.InjOn (fun k => y ^ (p ^ k)) (Finset.range d))
    (hgt : C < (d : ℝ)) :
    False := by
  have hle : (d : ℝ) ≤ C :=
    ArkLib.ProximityGap.DisproofLoop6.const_badcount_forbids_high_degree
      hclosed hbound hy d hinj
  exact not_lt_of_ge hle hgt

section InvariantPredicate

variable [Fintype F]

/-- If a predicate is Frobenius-invariant, then the finite set of elements satisfying it is closed
under Frobenius. -/
theorem frobenius_invariant_filter_closed
    (p : ℕ) (P : F → Prop) [DecidablePred P]
    (hP : ∀ x : F, P x → P (x ^ p)) :
    ∀ x ∈ (Finset.univ.filter P), x ^ p ∈ (Finset.univ.filter P) := by
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨Finset.mem_univ _, hP x hx.2⟩

/-- **Predicate form of the Frobenius orbit lower bound.** For any Frobenius-invariant bad-event
predicate `P`, a satisfying scalar with `d` distinct Frobenius iterates forces at least `d`
satisfying scalars. -/
theorem frobenius_invariant_card_ge
    {p : ℕ} (P : F → Prop) [DecidablePred P]
    (hP : ∀ x : F, P x → P (x ^ p))
    {y : F} (hy : P y) (d : ℕ)
    (hinj : Set.InjOn (fun k => y ^ (p ^ k)) (Finset.range d)) :
    d ≤ (Finset.univ.filter P).card := by
  refine ArkLib.ProximityGap.DisproofLoop6.frobenius_orbit_card_le
    (S := Finset.univ.filter P) ?_ ?_ d hinj
  · exact frobenius_invariant_filter_closed p P hP
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hy⟩

end InvariantPredicate

/-- If a degree parameter `d` only appears when the prize gap is at most `A / d`, then the degree
is bounded by the inverse gap: `d ≤ A / η`.

This is the core self-refutation for the near-capacity Frobenius-orbit attack: a growing orbit
whose growth is paid for by a shrinking gap is polynomial in `1/η`, exactly the kind of growth the
prize bound allows. -/
theorem degree_le_const_div_gap_of_gap_le_const_div_degree
    {d : ℕ} {η A : ℝ}
    (hd : 0 < (d : ℝ)) (hη : 0 < η)
    (hgap : η ≤ A / (d : ℝ)) :
    (d : ℝ) ≤ A / η := by
  have hmul : η * (d : ℝ) ≤ A := by
    calc
      η * (d : ℝ) ≤ (A / (d : ℝ)) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right hgap (le_of_lt hd)
      _ = A := by field_simp [ne_of_gt hd]
  rw [le_div_iff₀ hη]
  simpa [mul_comm] using hmul

/-- Linear bad-count growth in such a near-capacity family is absorbed by one inverse-gap factor.

If `#bad ≤ B d` and the construction only works with `η ≤ A/d`, then `#bad ≤ (B A)/η`. So a
merely linear Frobenius-orbit family cannot beat a prize RHS with even a first power of `1/η`.
-/
theorem linear_badcount_le_const_div_gap_of_gap_le_const_div_degree
    {bad d : ℕ} {η A B : ℝ}
    (hd : 0 < (d : ℝ)) (hη : 0 < η) (hB : 0 ≤ B)
    (hbad : (bad : ℝ) ≤ B * (d : ℝ))
    (hgap : η ≤ A / (d : ℝ)) :
    (bad : ℝ) ≤ (B * A) / η := by
  have hdle : (d : ℝ) ≤ A / η :=
    degree_le_const_div_gap_of_gap_le_const_div_degree hd hη hgap
  calc
    (bad : ℝ) ≤ B * (d : ℝ) := hbad
    _ ≤ B * (A / η) := mul_le_mul_of_nonneg_left hdle hB
    _ = (B * A) / η := by ring

end ArkLib.ProximityGap.DisproofLoop7
