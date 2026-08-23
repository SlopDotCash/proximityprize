/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# N2 brick 1 (#357): the syndrome factorization — `ε_mca` lives on the quotient module

The dual-syndrome attack (campaign hypothesis N2) starts from one unconditional statement:
**the MCA bad-scalar probability of a stack depends on the stack only through its pair of
syndrome classes** — i.e. through the cosets `(u₀ + C, u₁ + C)` in the quotient module
`(ι → A) ⧸ C`. (For any parity-check presentation `H` of `C`, the coset of `u` *is* its
syndrome `H·u`; the coset formulation is presentation-free.) This file proves it, from the
translation law of the equivariance engine:

* `stackProb` — the per-stack bad-scalar probability `Pr_γ[mcaEvent C δ u₀ u₁ γ]`.
* `stackProb_eq_of_sub_mem` — well-definedness on cosets: if `u₀ − u₀' ∈ C` and
  `u₁ − u₁' ∈ C` then `stackProb u₀ u₁ = stackProb u₀' u₁'` (Law 1 of `MCAEquivariance`).
* `syndromeProb` — the descended function on `((ι → A) ⧸ C)²`, via `Quotient.lift₂`.
* `epsMCA_eq_iSup_syndromeProb` — **the factorization theorem**:
  `ε_mca(C, δ) = ⨆ (q₀ q₁ : (ι → A) ⧸ C), syndromeProb q₀ q₁`.

Consequences for the campaign:

1. **The probe lab is certified.** Every exact `ε_mca` computation in
   `scripts/probes/probe_exact_epsmca_ladder.py` enumerates syndrome classes rather than
   stacks; this theorem is precisely the missing soundness statement for that reduction
   (the engine that produced the R1 ground truth and all exact-rung data).
2. **The state space collapses.** The supremum ranges over `|A|^{2(n−k)}`-many syndrome
   pairs instead of `|A|^{2n}`-many stacks (`q^8` vs `q^{16}` already at the n = 8 rung) —
   the feasibility theorem for every future exact δ* point.
3. **The N2 program opens.** With `ε_mca` formally a function on the syndrome space, the
   dual-code geometry (for smooth-domain RS the dual is generalized RS; syndromes are
   character sums over the subgroup) is now *the* native coordinate system for the sup —
   wall 2 (average → worst case) restated as a finite geometric question about an explicit
   GRS syndrome space.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (the δ* campaign; hypothesis N2); [ABF26] ePrint 2026/680; Yuan–Zhu
  arXiv:2605.07595 (syndrome-space proximity gaps for random linear codes).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCASyndromeFactorization

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- The per-stack bad-scalar probability: the quantity whose supremum over stacks is
`ε_mca`. -/
noncomputable def stackProb (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℝ≥0∞ :=
  Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ]

open Classical in
/-- **Coset well-definedness**: stacks in the same coset pair have equal bad-scalar
probability. The translation law (`MCAEquivariance` Law 1) in subtraction form. -/
theorem stackProb_eq_of_sub_mem (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ u₀' u₁' : ι → A} (h₀ : u₀ - u₀' ∈ C) (h₁ : u₁ - u₁' ∈ C) :
    stackProb (F := F) C δ u₀ u₁ = stackProb (F := F) C δ u₀' u₁' := by
  have hrw₀ : u₀ = u₀' + (u₀ - u₀') := by abel
  have hrw₁ : u₁ = u₁' + (u₁ - u₁') := by abel
  unfold stackProb
  conv_lhs => rw [hrw₀, hrw₁]
  exact MCAEquivariance.prob_mcaEvent_translate C h₀ h₁

open Classical in
/-- The bad-scalar probability descended to the syndrome space `((ι → A) ⧸ C)²`. -/
noncomputable def syndromeProb (C : Submodule F (ι → A)) (δ : ℝ≥0) :
    (ι → A) ⧸ C → (ι → A) ⧸ C → ℝ≥0∞ :=
  Quotient.lift₂ (stackProb (F := F) C δ) (fun u₀ u₁ u₀' u₁' h₀ h₁ => by
    have hm₀ : u₀ - u₀' ∈ C := (Submodule.quotientRel_def C).mp h₀
    have hm₁ : u₁ - u₁' ∈ C := (Submodule.quotientRel_def C).mp h₁
    exact stackProb_eq_of_sub_mem C δ hm₀ hm₁)

open Classical in
@[simp] theorem syndromeProb_mk (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    syndromeProb (F := F) C δ (Submodule.Quotient.mk u₀) (Submodule.Quotient.mk u₁)
      = stackProb (F := F) C δ u₀ u₁ := rfl

open Classical in
/-- **The syndrome factorization theorem**: `ε_mca` is the supremum of the descended
probability over the syndrome space — the MCA worst case is a function of `q^{2(n−k)}`
syndrome pairs, not `q^{2n}` stacks. -/
theorem epsMCA_eq_iSup_syndromeProb (C : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      = ⨆ (q₀ : (ι → A) ⧸ C) (q₁ : (ι → A) ⧸ C), syndromeProb (F := F) C δ q₀ q₁ := by
  unfold epsMCA
  refine le_antisymm (iSup_le fun u => ?_) (iSup_le fun q₀ => iSup_le fun q₁ => ?_)
  · -- each stack's term is a syndrome term
    have : Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ]
        = syndromeProb (F := F) C δ
            (Submodule.Quotient.mk (u 0)) (Submodule.Quotient.mk (u 1)) := rfl
    rw [this]
    exact le_trans (le_iSup _ (Submodule.Quotient.mk (u 1)))
      (le_iSup (fun q₀ => ⨆ q₁, syndromeProb (F := F) C δ q₀ q₁)
        (Submodule.Quotient.mk (u 0)))
  · -- each syndrome term is a stack's term
    obtain ⟨u₀, rfl⟩ := Submodule.Quotient.mk_surjective C q₀
    obtain ⟨u₁, rfl⟩ := Submodule.Quotient.mk_surjective C q₁
    rw [syndromeProb_mk]
    have : stackProb (F := F) C δ u₀ u₁
        = Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ
            ((![u₀, u₁] : WordStack A (Fin 2) ι) 0)
            ((![u₀, u₁] : WordStack A (Fin 2) ι) 1) γ] := rfl
    rw [this]
    exact le_iSup (fun u : WordStack A (Fin 2) ι =>
      Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ]) ![u₀, u₁]

/-! ## Source audit -/

#print axioms stackProb_eq_of_sub_mem
#print axioms syndromeProb_mk
#print axioms epsMCA_eq_iSup_syndromeProb

end ProximityGap.MCASyndromeFactorization
