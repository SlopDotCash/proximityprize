/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction

/-!
# WF407 T16-pgl2 — the PGL₂ torus-normalizer does NOT transfer a DOF-cut to the char-sum face

**Target (thread 407-T16).** The MCA bad event is invariant under the rotation `x↦c·x`
(`c` in the domain subgroup) and the inversion `x↦−1/x` (both formalized:
`MCAEquivariance.mcaEvent_rs_rotate`, `MCAMobius.mcaEvent_rs_inversion`). These generate the
**dihedral torus-normalizer** action that preserves the evaluation domain `μ_n`; they do **not**
generate all of PGL₂, and a general Möbius map need not preserve `μ_n`, so no full PGL₂
invariance is claimed or proved. On the MCA face the inversion is the **degree-weighted twist**
`(T u)(i) = (dom i)^{k−1}·u(σ i)`, an isometry of the bad event; together with the reflection it
cuts the Gauss-phase DOF by `×4` to the "Katz floor" `n/4` (the integer-pinned exact-relation set,
EXHAUSTED — see census 407-T16, DISPROOF_LOG O133/A5).

**The real question (3).** Does this torus-normalizer action transfer to the **char-sum face** — the
Gauss periods `η_b = Σ_{x∈μ_n} ψ(b·x)` (= eigenvalues of the Paley graph `Cay(F_q, μ_n)`), where the worst
case `B = max_{b≠0}‖η_b‖` lives — and give a NON-relation **concentration** input?

**Verdict: NO. Exact numerics (`scripts/probes/wf407_T16-pgl2_*.py`, exhaustive, no sampling) show:**

1. **Inversion on the DOMAIN is a trivial reindex.** `μ_n` is inversion-closed (`x∈μ_n ⟹ x⁻¹∈μ_n`),
   so `x ↦ −1/x` maps `μ_n` onto `μ_n` *as a set*; the char sum over the inverted index set is the
   **same** `η_b`. The MCA twist's degree weight `x^{k−1}` vanishes at `k = 1` (the linear/char-sum
   face), so the twist degenerates to this trivial domain reindex — **no new relation, no DOF cut.**
   This is the formalized content of this file (`eta_inv_reindex`, generalizing
   `GaussPeriodCosetReduction.eta_mul_of_image_eq`): if inversion permutes `G` (`G.image(·⁻¹) = G`)
   then `η` over the inverted domain equals `η` over `G`. (No `0 ∉ G` hypothesis is needed: field
   inversion is injective on all of `F` under the convention `0⁻¹ = 0`. The older names
   `eta_image_inv_invariant`, `image_inv_self_of_invClosed`, `eta_dominv_eq` keep their redundant
   `0 ∉ G` argument as compatibility wrappers.)

2. **Inversion on the FREQUENCY is NOT a relation (and not a concentration).** `b ↦ η_b` factors
   through `F_q^×/μ_n ≅ ℤ/m` (`m = (q−1)/n` periods; `eta_image_card_mul_le`). On `ℤ/m`: negation
   `b↦−b` is the IDENTITY, because `−1 ∈ μ_n` (n even) puts `b` and `−b` in the **same** coset.
   Consequently `η_{−b} = η_b`, and since also `η_{−b} = conj(η_b)`, every period is **real**; the
   conjugation supplies **no** further halving after the subgroup quotient, so there are `m`
   distinct-coset periods, not `m/2`. Inversion `b↦b⁻¹` acts as the group inversion `x↦−x` on
   `ℤ/m`, the ONLY nontrivial coset symmetry the normalizer adds. But `‖η_{b⁻¹}‖ ≠ ‖η_b‖` in the
   probed instances (measured gap 1.6–8.8, not 0): **inversion is NOT a modulus relation**, so the
   `x↦−x` coset fold does NOT reduce `max_b‖η_b‖`. Geometric-mean-with-inverse
   `√(‖η_b‖·‖η_{b⁻¹}‖) < B` at the spike in the probed instances: the inverse of the worst coset was
   not worst there, so inversion gives no averaged bound in those instances. This is finite
   evidence about inversion data, not a general no-concentration theorem.

**Conclusion.** The `×4 → n/4` Katz floor is a degree-weighted (k ≥ 2) MCA-face / relation
phenomenon; on the linear char-sum face the torus normalizer gives no modulus-preserving fold
beyond the subgroup quotient itself (`B` is a max over the `m` coset periods). In this sense the
avenue is **walled onto W4** — the residual is the Gauss-period HOUSE over the `m = (q−1)/n`
coset periods, i.e. the Paley Graph / BGK wall, **unchanged** by the torus-normalizer action.

**Honesty.** This file proves only the elementary positive fact (1) — domain-inversion invariance of
`η`, which is exactly *why* inversion adds nothing on the char-sum face. Facts (2)/the verdict are
the exact-numerics record on probed instances; no closure and no method-wide impossibility is
claimed. All theorems are axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

namespace ArkLib.ProximityGap.WF407_T16PGL2CharFace

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Domain-inversion invariance of the period (the L2 fact).** If the involutive reindexing
`y ↦ y⁻¹` permutes the index set `G` (`G.image(·⁻¹) = G`, e.g. `G` an inversion-closed multiplicative
subgroup), then the subgroup Gauss sum computed over the *inverted* domain equals the original:
`Σ_{y∈G} ψ(b·y⁻¹) = η_b`. This is the formal reason the inversion generator `x↦−1/x` of the torus
normalizer contributes NOTHING new on the char-sum face: at `k = 1` the MCA twist's degree weight
`x^{k−1}` vanishes and the twist degenerates to this trivial reindex. Pure `Finset.sum_image` over
the inversion bijection (field inversion is injective on all of `F`, so `0 ∉ G` is not needed). -/
theorem eta_inv_reindex (ψ : AddChar F ℂ) (G : Finset F) (b : F)
    (hinv : G.image (fun y => y⁻¹) = G) :
    ∑ y ∈ G, ψ (b * y⁻¹) = eta ψ G b := by
  unfold eta
  conv_rhs => rw [← hinv]
  rw [Finset.sum_image]
  intro a _ c _ h
  exact inv_injective.eq_iff.mp h

/-- **Inversion-closed sets satisfy the hypothesis.** A finite set `G ⊆ F` that is inversion-closed
(`x⁻¹ ∈ G` for `x ∈ G`) has `G.image(·⁻¹) = G`. Subgroups of `F^×` are always inversion-closed, so
this is automatic for `μ_n`. -/
theorem image_inv_eq_self_of_inv_mem (G : Finset F) (hinv : ∀ x ∈ G, x⁻¹ ∈ G) :
    G.image (fun y => y⁻¹) = G := by
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact hinv y hy
  · -- |G.image(·⁻¹)| = |G| since field inversion is injective
    refine le_of_eq (Finset.card_image_of_injOn ?_).symm
    intro a _ c _ h
    exact inv_injective.eq_iff.mp h

/-- **The combined L2 statement for inversion-closed sets (the headline).** For a finite
inversion-closed `G` (e.g. a multiplicative subgroup), the period over the inverted domain is the
original period: `Σ_{y∈G} ψ(b·y⁻¹) = η_b`. Hence the inversion `x↦−1/x` on the *domain* is a
trivial reindex on the char-sum face — it does not perturb `η` and supplies no DOF cut. The `×4`
Katz floor `n/4` is confined to the degree-weighted MCA/relation face and does not transfer here. -/
theorem eta_dominv_eq_of_inv_mem (ψ : AddChar F ℂ) (G : Finset F) (b : F)
    (hinv : ∀ x ∈ G, x⁻¹ ∈ G) :
    ∑ y ∈ G, ψ (b * y⁻¹) = eta ψ G b :=
  eta_inv_reindex ψ G b (image_inv_eq_self_of_inv_mem G hinv)

/-- Compatibility wrapper for `eta_inv_reindex` (the `0 ∉ G` argument is redundant). -/
theorem eta_image_inv_invariant (ψ : AddChar F ℂ) (G : Finset F) (b : F)
    (_h0 : (0 : F) ∉ G) (hinv : G.image (fun y => y⁻¹) = G) :
    ∑ y ∈ G, ψ (b * y⁻¹) = eta ψ G b :=
  eta_inv_reindex ψ G b hinv

/-- Compatibility wrapper for `image_inv_eq_self_of_inv_mem` (the `0 ∉ G` argument is
redundant). -/
theorem image_inv_self_of_invClosed (G : Finset F) (_h0 : (0 : F) ∉ G)
    (hinv : ∀ x ∈ G, x⁻¹ ∈ G) :
    G.image (fun y => y⁻¹) = G :=
  image_inv_eq_self_of_inv_mem G hinv

/-- Compatibility wrapper for `eta_dominv_eq_of_inv_mem` (the `0 ∉ G` argument is redundant). -/
theorem eta_dominv_eq (ψ : AddChar F ℂ) (G : Finset F) (b : F)
    (_h0 : (0 : F) ∉ G) (hinv : ∀ x ∈ G, x⁻¹ ∈ G) :
    ∑ y ∈ G, ψ (b * y⁻¹) = eta ψ G b :=
  eta_dominv_eq_of_inv_mem ψ G b hinv

end ArkLib.ProximityGap.WF407_T16PGL2CharFace

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.WF407_T16PGL2CharFace.eta_inv_reindex
#print axioms ArkLib.ProximityGap.WF407_T16PGL2CharFace.image_inv_eq_self_of_inv_mem
#print axioms ArkLib.ProximityGap.WF407_T16PGL2CharFace.eta_dominv_eq_of_inv_mem
#print axioms ArkLib.ProximityGap.WF407_T16PGL2CharFace.eta_image_inv_invariant
#print axioms ArkLib.ProximityGap.WF407_T16PGL2CharFace.image_inv_self_of_invClosed
#print axioms ArkLib.ProximityGap.WF407_T16PGL2CharFace.eta_dominv_eq
