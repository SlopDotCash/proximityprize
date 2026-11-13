/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Bad-scalar root certificates

This Frontier file records the q-independent counting gate behind the
resultant-scalar probes for issue #407.

The mathematical content is deliberately small and closed: if every bad scalar
is a root of a nonzero one-variable certificate polynomial, then the bad-scalar
count is at most the certificate degree.  This is the reusable terminal step for
resultant, discriminant, and subresultant lanes; all prize difficulty is in
constructing a low-degree nonzero certificate that really covers the worst-case
bad set.
-/

namespace ProximityGap.Frontier.BadScalarCertificate

open Finset Polynomial

variable {F ι : Type*} [Field F] [DecidableEq F]

/--
A bad-scalar set is certified by `P` when `P` is nonzero and vanishes on every
bad scalar.
-/
def CertifiedBadScalars (Bad : Finset F) (P : F[X]) : Prop :=
  P ≠ 0 ∧ ∀ γ ∈ Bad, Polynomial.IsRoot P γ

/--
The terminal resultant-counting gate: a nonzero certificate polynomial of degree
`D` certifies at most `D` bad scalars.
-/
theorem card_le_natDegree_of_certified {Bad : Finset F} {P : F[X]}
    (hcert : CertifiedBadScalars Bad P) :
    Bad.card ≤ P.natDegree := by
  have hsub : Bad ⊆ P.roots.toFinset := by
    intro γ hγ
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hcert.1]
    exact hcert.2 γ hγ
  calc
    Bad.card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := P.card_roots'

/-- Degree-budget form of `card_le_natDegree_of_certified`. -/
theorem card_le_of_certified_degree_le {Bad : Finset F} {P : F[X]} {D : ℕ}
    (hcert : CertifiedBadScalars Bad P) (hdeg : P.natDegree ≤ D) :
    Bad.card ≤ D :=
  le_trans (card_le_natDegree_of_certified hcert) hdeg

/--
Refutation hook: a proposed degree-`< #Bad` root certificate cannot cover all
bad scalars.
-/
theorem not_certified_of_natDegree_lt_card {Bad : Finset F} {P : F[X]}
    (hdeg : P.natDegree < Bad.card) :
    ¬ CertifiedBadScalars Bad P := by
  intro hcert
  exact Nat.not_lt_of_ge (card_le_natDegree_of_certified hcert) hdeg

/--
Union-certificate form.  If the bad scalars are covered by roots of finitely many certificate
polynomials, the count is bounded by the sum of the degrees.
-/
theorem card_le_sum_natDegree_of_root_cover [Fintype ι] [DecidableEq ι]
    (Bad : Finset F) (P : ι → F[X])
    (hcover : Bad ⊆ (Finset.univ.biUnion fun i => (P i).roots.toFinset)) :
    Bad.card ≤ ∑ i, (P i).natDegree := by
  calc
    Bad.card ≤ (Finset.univ.biUnion fun i => (P i).roots.toFinset).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ i, ((P i).roots.toFinset.card) := Finset.card_biUnion_le
    _ ≤ ∑ i, (P i).natDegree := by
      exact Finset.sum_le_sum fun i _ => by
        calc
          (P i).roots.toFinset.card ≤ (P i).roots.card := Multiset.toFinset_card_le _
          _ ≤ (P i).natDegree := (P i).card_roots'

/--
Existential-certificate form.  If every bad scalar is a root of at least one
nonzero certificate in a finite family, the count is bounded by the sum of the
certificate degrees.
-/
theorem card_le_sum_natDegree_of_exists_root [Fintype ι] [DecidableEq ι]
    (Bad : Finset F) (P : ι → F[X]) (hnz : ∀ i, P i ≠ 0)
    (hroot : ∀ γ ∈ Bad, ∃ i, Polynomial.IsRoot (P i) γ) :
    Bad.card ≤ ∑ i, (P i).natDegree := by
  refine card_le_sum_natDegree_of_root_cover Bad P ?_
  intro γ hγ
  rcases hroot γ hγ with ⟨i, hi⟩
  rw [Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hnz i)]
    exact hi⟩

/--
Degree-budget form for finite unions of root certificates.
-/
theorem card_le_of_root_cover_sum_degree_le [Fintype ι] [DecidableEq ι]
    (Bad : Finset F) (P : ι → F[X]) {D : ℕ}
    (hcover : Bad ⊆ (Finset.univ.biUnion fun i => (P i).roots.toFinset))
    (hdeg : (∑ i, (P i).natDegree) ≤ D) :
    Bad.card ≤ D :=
  le_trans (card_le_sum_natDegree_of_root_cover Bad P hcover) hdeg

/-- Degree-budget form for existential finite certificate families. -/
theorem card_le_of_exists_root_sum_degree_le [Fintype ι] [DecidableEq ι]
    (Bad : Finset F) (P : ι → F[X]) {D : ℕ} (hnz : ∀ i, P i ≠ 0)
    (hroot : ∀ γ ∈ Bad, ∃ i, Polynomial.IsRoot (P i) γ)
    (hdeg : (∑ i, (P i).natDegree) ≤ D) :
    Bad.card ≤ D :=
  le_trans (card_le_sum_natDegree_of_exists_root Bad P hnz hroot) hdeg

/--
Uniform-degree finite-family form.  If every bad scalar is covered by one
certificate from an indexed family and every certificate has degree `≤ D`, then
the bad-scalar count is bounded by `#ι * D`.
-/
theorem card_le_card_mul_degree_of_exists_root [Fintype ι] [DecidableEq ι]
    (Bad : Finset F) (P : ι → F[X]) {D : ℕ} (hnz : ∀ i, P i ≠ 0)
    (hroot : ∀ γ ∈ Bad, ∃ i, Polynomial.IsRoot (P i) γ)
    (hdeg : ∀ i, (P i).natDegree ≤ D) :
    Bad.card ≤ Fintype.card ι * D := by
  refine card_le_of_exists_root_sum_degree_le Bad P hnz hroot ?_
  calc
    ∑ i, (P i).natDegree ≤ ∑ _i : ι, D := Finset.sum_le_sum fun i _ => hdeg i
    _ = Fintype.card ι * D := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/--
Finite-cover form with a uniform degree bound and an explicit index-card budget.
-/
theorem card_le_of_exists_root_uniform_degree_budget [Fintype ι] [DecidableEq ι]
    (Bad : Finset F) (P : ι → F[X]) {D B : ℕ} (hnz : ∀ i, P i ≠ 0)
    (hroot : ∀ γ ∈ Bad, ∃ i, Polynomial.IsRoot (P i) γ)
    (hdeg : ∀ i, (P i).natDegree ≤ D) (hbudget : Fintype.card ι * D ≤ B) :
    Bad.card ≤ B :=
  le_trans (card_le_card_mul_degree_of_exists_root Bad P hnz hroot hdeg) hbudget

end ProximityGap.Frontier.BadScalarCertificate

#print axioms ProximityGap.Frontier.BadScalarCertificate.card_le_natDegree_of_certified
#print axioms ProximityGap.Frontier.BadScalarCertificate.card_le_of_certified_degree_le
#print axioms ProximityGap.Frontier.BadScalarCertificate.not_certified_of_natDegree_lt_card
#print axioms ProximityGap.Frontier.BadScalarCertificate.card_le_sum_natDegree_of_root_cover
#print axioms ProximityGap.Frontier.BadScalarCertificate.card_le_sum_natDegree_of_exists_root
#print axioms ProximityGap.Frontier.BadScalarCertificate.card_le_of_root_cover_sum_degree_le
#print axioms ProximityGap.Frontier.BadScalarCertificate.card_le_of_exists_root_sum_degree_le
#print axioms ProximityGap.Frontier.BadScalarCertificate.card_le_card_mul_degree_of_exists_root
#print axioms
  ProximityGap.Frontier.BadScalarCertificate.card_le_of_exists_root_uniform_degree_budget
