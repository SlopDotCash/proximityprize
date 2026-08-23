/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# The syndrome factorization of `ε_mca` (#357 N2, brick 1)

The probe laboratory computes exact values of `ε_mca` at all only because of one structural
fact: **the MCA event depends on the stack `(u₀, u₁) ` only through its pair of syndrome
classes** — the cosets `(u₀ + C, u₁ + C)`. (For a linear code `C = ker H`, the coset of `u`
is precisely the data of the syndrome `H u`; the quotient `(ι → A) ⧸ C` *is* the syndrome
space.) This file promotes that change of coordinates from probe folklore to a theorem:

* `mcaEvent_congr_quotient` — two stacks with the same syndrome-class pair have the same
  MCA event at every `γ` (direct consumer of `MCAEquivariance.mcaEvent_translate`);
* **`epsMCA_eq_iSup_syndromePairs`** — `ε_mca(C, δ)` *is* the supremum over the
  `|A/C|²`-element syndrome-pair space of the per-class bad-scalar probability, for any
  section `σ` of the quotient map.

Consequences. (i) The exact-`ε_mca` probe engine (`probe_exact_epsmca_ladder.py`) is
retroactively certified: enumerating syndrome pairs is lossless. (ii) The index of the sup
drops from `|A|^{2n}` to `|A|^{2(n−k)}` — the speedup that makes exact rungs feasible.
(iii) This is the unconditional half of the N2 dual-syndrome programme (#357): the open half
(the bad-γ census as a joint-weight statement about the dual GRS code) now has its left-hand
side in formal form.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- [ABF26] ePrint 2026/680; Yuan–Zhu arXiv:2605.07595 (syndrome-space lens for random linear
  codes). Issue #357 (N2 in the campaign dossier).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCASyndromeSup

open ProximityGap.MCAEquivariance

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The MCA event factors through syndrome classes**: stacks in the same coset pair of `C`
have the same event at every scalar. -/
theorem mcaEvent_congr_quotient (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {u₀ u₁ v₀ v₁ : ι → A}
    (h₀ : Submodule.Quotient.mk (p := C) u₀ = Submodule.Quotient.mk (p := C) v₀)
    (h₁ : Submodule.Quotient.mk (p := C) u₁ = Submodule.Quotient.mk (p := C) v₁)
    (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ v₀ v₁ γ := by
  have hc₀ : u₀ - v₀ ∈ C := (Submodule.Quotient.eq C).mp h₀
  have hc₁ : u₁ - v₁ ∈ C := (Submodule.Quotient.eq C).mp h₁
  have hu₀ : u₀ = v₀ + (u₀ - v₀) := by abel
  have hu₁ : u₁ = v₁ + (u₁ - v₁) := by abel
  rw [hu₀, hu₁]
  exact mcaEvent_translate C hc₀ hc₁ γ

open Classical in
/-- The per-stack bad-scalar probability factors through syndrome classes. -/
theorem prob_mcaEvent_congr_quotient (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {u₀ u₁ v₀ v₁ : ι → A}
    (h₀ : Submodule.Quotient.mk (p := C) u₀ = Submodule.Quotient.mk (p := C) v₀)
    (h₁ : Submodule.Quotient.mk (p := C) u₁ = Submodule.Quotient.mk (p := C) v₁) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ]
      = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ v₀ v₁ γ] :=
  Pr_congr_iff _ fun γ => mcaEvent_congr_quotient C h₀ h₁ γ

open Classical in
/-- **The syndrome factorization of `ε_mca`.** For any section `σ` of the quotient map
`(ι → A) → (ι → A) ⧸ C` (any choice of coset representatives — equivalently, any decoder of
syndromes to words), the MCA error is the supremum over the **syndrome-pair space**:

  `ε_mca(C, δ) = ⨆_{(q₀, q₁) ∈ (A^ι/C)²}  Pr_γ[mcaEvent C δ (σ q₀) (σ q₁) γ]`.

The sup index has `|A/C|² = |A|^{2(n−k)}` elements instead of `|A|^{2n}` — the change of
coordinates that makes exact `ε_mca` computation feasible, now a theorem. -/
theorem epsMCA_eq_iSup_syndromePairs (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (σ : ((ι → A) ⧸ C) → (ι → A))
    (hσ : ∀ q, Submodule.Quotient.mk (p := C) (σ q) = q) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      = ⨆ q : ((ι → A) ⧸ C) × ((ι → A) ⧸ C),
          Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ (σ q.1) (σ q.2) γ] := by
  unfold epsMCA
  apply le_antisymm
  · refine iSup_le fun u => ?_
    set q : ((ι → A) ⧸ C) × ((ι → A) ⧸ C) :=
      (Submodule.Quotient.mk (p := C) (u 0), Submodule.Quotient.mk (p := C) (u 1)) with hq
    have h₀ : Submodule.Quotient.mk (p := C) (u 0)
        = Submodule.Quotient.mk (p := C) (σ q.1) := by rw [hσ]
    have h₁ : Submodule.Quotient.mk (p := C) (u 1)
        = Submodule.Quotient.mk (p := C) (σ q.2) := by rw [hσ]
    rw [prob_mcaEvent_congr_quotient C h₀ h₁]
    exact le_iSup (fun q : ((ι → A) ⧸ C) × ((ι → A) ⧸ C) =>
      Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ (σ q.1) (σ q.2) γ]) q
  · refine iSup_le fun q => ?_
    have hb := le_iSup (fun u : WordStack A (Fin 2) ι =>
      Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ])
      (fun k => if k = 0 then σ q.1 else σ q.2)
    have h0 : (fun k : Fin 2 => if k = 0 then σ q.1 else σ q.2) 0 = σ q.1 := rfl
    have h1 : (fun k : Fin 2 => if k = 0 then σ q.1 else σ q.2) 1 = σ q.2 := by
      norm_num
    rw [h0, h1] at hb
    exact hb

/-! ## Source audit -/

#print axioms mcaEvent_congr_quotient
#print axioms prob_mcaEvent_congr_quotient
#print axioms epsMCA_eq_iSup_syndromePairs

end ProximityGap.MCASyndromeSup
