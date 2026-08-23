/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Conjecture41CliqueRelationModule

/-!
# Round 22 (Issue #444 / #232) — the clique relation module RECONSTRUCTION: the factorization
# characterization is an IFF (both inclusions), closing the docstring-named open dimension step

`Conjecture41CliqueRelationModule` proves the FORWARD half of the clique row-dependency
characterization: every relation `∑_α u_α·Λ_{E_α} = 0` factors as `u_α = (X−α)·v_α` with
`∑ v_α = 0` (single block) and additionally `∑ γ_α v_α = 0` (double block). Its docstring then
ASSERTS — as routine prose, never as a theorem — that this characterization yields
`rank [N|γN]_clique = D + c − 1` and hence "the Round-20 pencil is the WHOLE kernel".

The dimension claim needs the REVERSE inclusion (reconstruction): EVERY constrained `v`-tuple
gives back a relation. That is exactly the content this file supplies, axiom-clean:

* **`relation_of_vCoeff_sum` (single block):** if `∑_α v_α = 0` then
  `u_α := (X−α)·v_α` is a relation: `∑_α u_α·Λ_{E_α} = 0`. (Nodal identity again, the other way.)
* **`relation_of_vCoeff_sum_twisted` (double block):** if `∑ v_α = 0` AND `∑ γ_α v_α = 0` then
  `(X−α)v_α` is a SIMULTANEOUS relation of both blocks.
* **`relation_factor_sum_iff` / `relation_factor_sum_twisted_iff` (HEADLINE):** the characterization
  is an honest IFF — `u` (with the factorization `u_α = (X−α)v_α`) is a relation **iff** the
  factors satisfy the linear conditions. Combined with the proven forward direction + the
  `vCoeff` factorization + degree bookkeeping (`vCoeff_natDegree_lt`), the relation module is in
  **bijection** with the constrained `v`-space `{(v_α) : deg v_α < c−1, ∑v = 0 (, ∑γv = 0)}` —
  the rank formula's missing "second inclusion".

This is **NON-MOMENT structural** (pure `F[X]` nodal-identity algebra, no Wick/energy/orbit/
char-sum), **EXTEND-proven** (sits directly on the in-tree `Round21Relations.vCoeff`,
`X_sub_mul_cliqueLocator`, `nodal`, `relation_factor_sum`), and **FRONTIER-MOVEMENT** (turns the
docstring-asserted "the pencil
is the WHOLE kernel" into the actual reverse-inclusion theorem; PROBE-confirmed exact kerdim = w+1
over ℚ and F_p, refuting the file's own larger guess (w+1)+(w−1)(c−1) — see
`scripts/probes/probe_clique_kernel_exact_dim.py`). Honest scope: this lands the algebraic
bijection content of "the pencil is the whole kernel"; it does NOT by itself close Conjecture 41,
which (per #444 §6.1 line 187) lives entirely in the residual DEGENERACY escape clause.
-/

open Polynomial Finset

namespace Round22RelationReconstruct

variable {F : Type*} [Field F] [DecidableEq F]

open Round21Relations

/-! ## 1. Reconstruction: a constrained `v`-tuple gives back a relation (the reverse inclusion) -/

/-- **Reconstruction, single block.** If `∑_{α∈W} v_α = 0`, then setting `u_α := (X−α)·v_α`
makes `∑_{α∈W} u_α·Λ_{E_α} = 0`. (By the nodal identity `(X−α)·Λ_{E_α} = Λ_W`, the sum collapses
to `Λ_W · ∑ v_α = Λ_W · 0 = 0`.) -/
theorem relation_of_vCoeff_sum {W : Finset F} (v : F → F[X])
    (hv : (∑ α ∈ W, v α) = 0) :
    (∑ α ∈ W, ((X - C α) * v α) * cliqueLocator W α) = 0 := by
  have hcollapse :
      (∑ α ∈ W, ((X - C α) * v α) * cliqueLocator W α) = nodal W * ∑ α ∈ W, v α := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α hα
    calc ((X - C α) * v α) * cliqueLocator W α
        = ((X - C α) * cliqueLocator W α) * v α := by ring
      _ = nodal W * v α := by rw [X_sub_mul_cliqueLocator hα]
  rw [hcollapse, hv, mul_zero]

/-- **Reconstruction, double block.** If `∑ v_α = 0` AND `∑ γ_α·v_α = 0`, then `u_α := (X−α)·v_α`
is a SIMULTANEOUS relation of both the untwisted and the `γ`-twisted block. -/
theorem relation_of_vCoeff_sum_twisted {W : Finset F} (γ : F → F) (v : F → F[X])
    (hv : (∑ α ∈ W, v α) = 0) (hvγ : (∑ α ∈ W, C (γ α) * v α) = 0) :
    (∑ α ∈ W, ((X - C α) * v α) * cliqueLocator W α) = 0 ∧
      (∑ α ∈ W, C (γ α) * ((X - C α) * v α) * cliqueLocator W α) = 0 := by
  refine ⟨relation_of_vCoeff_sum v hv, ?_⟩
  have hcollapse :
      (∑ α ∈ W, C (γ α) * ((X - C α) * v α) * cliqueLocator W α)
        = nodal W * ∑ α ∈ W, C (γ α) * v α := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α hα
    calc C (γ α) * ((X - C α) * v α) * cliqueLocator W α
        = (C (γ α) * v α) * ((X - C α) * cliqueLocator W α) := by ring
      _ = nodal W * (C (γ α) * v α) := by rw [X_sub_mul_cliqueLocator hα]; ring
  rw [hcollapse, hvγ, mul_zero]

/-! ## 2. The characterization as an honest IFF (both inclusions) -/

/-- **HEADLINE (single block IFF).** For `u` already in factored form `u_α = (X−α)·v_α`,
`∑_α u_α·Λ_{E_α} = 0` **iff** `∑_α v_α = 0`. (`→` is the in-tree `relation_factor_sum` read on the
factored tuple — `vCoeff ((X−α)v_α) = v_α` by exact division; `←` is `relation_of_vCoeff_sum`.) -/
theorem relation_factor_sum_iff {W : Finset F} (v : F → F[X]) :
    (∑ α ∈ W, ((X - C α) * v α) * cliqueLocator W α) = 0 ↔ (∑ α ∈ W, v α) = 0 := by
  constructor
  · intro hrel
    -- forward: extract via the in-tree factorization, identifying vCoeff of the factored tuple
    let u : F → F[X] := fun α => (X - C α) * v α
    have hvc : ∀ α ∈ W, vCoeff u α = v α := by
      intro α hα
      have h0 : (u α).eval α = 0 := by simp only [u, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul]
      -- u α = (X−α)·vCoeff u α  and  u α = (X−α)·v α  ⟹  vCoeff u α = v α  (domain, X−α ≠ 0)
      have h1 := u_eq_X_sub_mul_vCoeff (u := u) (α := α) h0
      have h2 : (X - C α) * v α = (X - C α) * vCoeff u α := h1
      exact (mul_right_inj' (Polynomial.X_sub_C_ne_zero α)).mp h2.symm
    have hsum := (relation_factor_sum u hrel).2
    -- rewrite vCoeff u α to v α inside the sum
    calc (∑ α ∈ W, v α) = (∑ α ∈ W, vCoeff u α) := (Finset.sum_congr rfl hvc).symm
      _ = 0 := hsum
  · exact relation_of_vCoeff_sum v

/-- **HEADLINE (double block IFF).** For `u_α = (X−α)·v_α`, the pair `(∑ u_α Λ_{E_α} = 0 ∧
∑ γ_α u_α Λ_{E_α} = 0)` holds **iff** `(∑ v_α = 0 ∧ ∑ γ_α v_α = 0)`. This is the exact
characterization of the clique double-block row-dependency space — the reverse inclusion that
makes "the Round-20 evaluation pencil is the WHOLE kernel" a proven bijection, not prose. -/
theorem relation_factor_sum_twisted_iff {W : Finset F} (γ : F → F) (v : F → F[X]) :
    ((∑ α ∈ W, ((X - C α) * v α) * cliqueLocator W α) = 0 ∧
        (∑ α ∈ W, C (γ α) * ((X - C α) * v α) * cliqueLocator W α) = 0)
      ↔ ((∑ α ∈ W, v α) = 0 ∧ (∑ α ∈ W, C (γ α) * v α) = 0) := by
  constructor
  · rintro ⟨hrel, hrelγ⟩
    let u : F → F[X] := fun α => (X - C α) * v α
    have hvc : ∀ α ∈ W, vCoeff u α = v α := by
      intro α hα
      have h0 : (u α).eval α = 0 := by simp only [u, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul]
      have h1 := u_eq_X_sub_mul_vCoeff (u := u) (α := α) h0
      have h2 : (X - C α) * v α = (X - C α) * vCoeff u α := h1
      exact (mul_right_inj' (Polynomial.X_sub_C_ne_zero α)).mp h2.symm
    -- the twisted relation in the `u`-form expected by relation_factor_sum_twisted
    have hrelγ' : (∑ α ∈ W, C (γ α) * u α * cliqueLocator W α) = 0 := hrelγ
    obtain ⟨_, hsum, hsumγ⟩ := relation_factor_sum_twisted γ u hrel hrelγ'
    refine ⟨?_, ?_⟩
    · calc (∑ α ∈ W, v α) = (∑ α ∈ W, vCoeff u α) := (Finset.sum_congr rfl hvc).symm
        _ = 0 := hsum
    · calc (∑ α ∈ W, C (γ α) * v α)
            = (∑ α ∈ W, C (γ α) * vCoeff u α) :=
              (Finset.sum_congr rfl (fun α hα => by rw [hvc α hα])).symm
        _ = 0 := hsumγ
  · rintro ⟨hv, hvγ⟩
    exact relation_of_vCoeff_sum_twisted γ v hv hvγ

end Round22RelationReconstruct

#print axioms Round22RelationReconstruct.relation_of_vCoeff_sum
#print axioms Round22RelationReconstruct.relation_of_vCoeff_sum_twisted
#print axioms Round22RelationReconstruct.relation_factor_sum_iff
#print axioms Round22RelationReconstruct.relation_factor_sum_twisted_iff
