/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Deployment-local certificates do not prove uniform deployment bounds

The Chai--Fan/action-orbit lane contains genuinely useful finite or deployment-local evidence:
checked base panels, checked fields, or a fixed deployment subgroup can be certified directly.  The
prize-facing consumer is stronger.  It needs a statement that holds uniformly over the target
instance family, or a theorem transferring every target instance to one of the checked instances.

This file records that contract in an abstract form.

* `CertifiedOn S Good` is finite/local verification on a set of instances `S`.
* `UniformGood Good` is the all-instance statement consumed by the deployment/prize theorem.
* `CoveredByCertified S Good` is the missing substitution/propagation theorem: every target
  instance is reduced to a checked instance in a way preserving `Good`.

The negative theorem `finite_nat_certificates_not_force_uniform` says that finite checks over an
unbounded scale parameter cannot imply the uniform statement by logic alone.  The positive theorem
`uniformGood_of_certifiedOn_and_cover` says exactly what extra theorem would be sufficient.

This is intentionally not a new delta-star proof.  It is a guardrail for routing deployment-local
or finite-check evidence: without the cover/propagation input, the evidence remains local.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DeploymentLocalCertificateUniformityGate

/-- `Good` has been certified on the finite/local set of instances `S`. -/
def CertifiedOn {ι : Type} (S : Finset ι) (Good : ι -> Prop) : Prop :=
  ∀ i : ι, i ∈ S -> Good i

/-- The uniform all-instance statement required by a deployment-scale theorem. -/
def UniformGood {ι : Type} (Good : ι -> Prop) : Prop :=
  ∀ i : ι, Good i

/-- A checked-set cover/propagation theorem: every target instance reduces to some checked
instance, preserving `Good`.  This is where an action-orbit substitution principle, a base-panel
descent theorem, or a genuine all-scale propagation theorem must enter. -/
def CoveredByCertified {ι : Type} (S : Finset ι) (Good : ι -> Prop) : Prop :=
  ∀ i : ι, ∃ j ∈ S, Good j -> Good i

/-- The local countermodel: `Good` holds exactly on the checked set. -/
def LocalModel {ι : Type} (S : Finset ι) : ι -> Prop :=
  fun i => i ∈ S

/-- The local countermodel passes every check in `S`. -/
theorem certifiedOn_localModel {ι : Type} (S : Finset ι) :
    CertifiedOn S (LocalModel S) := by
  intro i hi
  exact hi

/-- If there is an unchecked target instance, finite/local certification cannot force the uniform
statement. -/
theorem certifiedOn_not_force_uniform {ι : Type}
    (S : Finset ι) {i0 : ι} (hi0 : i0 ∉ S) :
    ¬ (∀ Good : ι -> Prop, CertifiedOn S Good -> UniformGood Good) := by
  intro h
  have huniform : UniformGood (LocalModel S) :=
    h (LocalModel S) (certifiedOn_localModel S)
  exact hi0 (huniform i0)

/-- A finite set of natural-numbered deployment scales always misses some future scale. -/
theorem exists_nat_not_mem_finset (S : Finset ℕ) : ∃ n : ℕ, n ∉ S := by
  classical
  by_cases hS : S.Nonempty
  · refine ⟨S.max' hS + 1, ?_⟩
    intro hmem
    have hle : S.max' hS + 1 ≤ S.max' hS := Finset.le_max' S (S.max' hS + 1) hmem
    omega
  · refine ⟨0, ?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp hS]

/-- Finite certification over an unbounded scale parameter cannot imply the all-scale deployment
statement.  This is the abstract form of the "checked deployment instances are not uniformity"
guardrail. -/
theorem finite_nat_certificates_not_force_uniform (S : Finset ℕ) :
    ¬ (∀ Good : ℕ -> Prop, CertifiedOn S Good -> UniformGood Good) := by
  rcases exists_nat_not_mem_finset S with ⟨n, hn⟩
  exact certifiedOn_not_force_uniform S hn

/-- Positive replacement: finite/local certification becomes uniform only after a cover or
propagation theorem that reduces every target instance to a checked one. -/
theorem uniformGood_of_certifiedOn_and_cover {ι : Type} {S : Finset ι} {Good : ι -> Prop}
    (hcert : CertifiedOn S Good)
    (hcover : CoveredByCertified S Good) :
    UniformGood Good := by
  intro i
  rcases hcover i with ⟨j, hjS, hji⟩
  exact hji (hcert j hjS)

/-- Equivalence form: a finite/local certificate plus the cover theorem is exactly a sufficient
route to the uniform statement. -/
theorem covered_certificate_suffices {ι : Type} {S : Finset ι} {Good : ι -> Prop} :
    CertifiedOn S Good ∧ CoveredByCertified S Good -> UniformGood Good := by
  rintro ⟨hcert, hcover⟩
  exact uniformGood_of_certifiedOn_and_cover hcert hcover

/-! ## Axiom audit -/
#print axioms certifiedOn_localModel
#print axioms certifiedOn_not_force_uniform
#print axioms exists_nat_not_mem_finset
#print axioms finite_nat_certificates_not_force_uniform
#print axioms uniformGood_of_certifiedOn_and_cover
#print axioms covered_certificate_suffices

end ArkLib.ProximityGap.Frontier.DeploymentLocalCertificateUniformityGate
