/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCASyndromeFactorization
import ArkLib.Data.CodingTheory.ProximityGap.MCAExactComputationKit

/-!
# The explicit transversal: `ε_mca` as a finite sup over an information-set complement

Support brick for the #357 exact-`δ*` programme, composing the two descent layers:

* the **syndrome factorization** (`epsMCA_eq_iSup_syndromeProb`) says `ε_mca` only sees the
  stack modulo `C` — but its quotient indexing is abstract (`Quotient.out` is
  noncomputable), so it cannot feed a kernel computation directly;
* the **exact-computation kit** (`epsMCA_eq_sup_badScalarCount`) makes the per-stack value
  computable — but its sup still ranges over all `|A|^{2n}` stacks.

This file supplies the missing piece: an **explicit, computable transversal** of the
translation action. If `R : Finset (ι → A)` covers every coset of `C` (`∀ u, ∃ r ∈ R,
u - r ∈ C`), then

  `ε_mca(C, δ) = ⨆ (r₀ ∈ R) (r₁ ∈ R), Pr[mcaEvent C δ r₀ r₁]`  (`epsMCA_eq_sup_cover`),

and composed with the kit (`epsMCA_eq_sup_badScalarCount_cover`):

  `ε_mca(C, δ) = (max over R × R of badScalarCount) / |F|` — a fully finite, decidable
  expression over `|R|²` pairs.

The canonical `R` comes from **interpolation**: if every assignment on an information set
`I ⊆ ι` extends to a codeword (`cover_vanishing_of_interpolation` — for `RS[F, L, k]`, any
`k` points, by Lagrange), then the words **vanishing on `I`** form such a cover of size
`|A|^{n−|I|}` — the explicit syndrome transversal. At the R1 instance this is the probes'
`625`-class reduction (vs `390,625` stacks), now formal *and* computable; at the n = 8 rung
(the registered monomial-orbit-extremality conjecture's falsifier (i)) it is the difference
between feasible and not.

## References
- [ABF26] ePrint 2026/680, Definition 4.3. Issue #357 (the exact-point programme, N2).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCAExplicitTransversal

open ProximityGap.MCASyndromeFactorization ProximityGap.MCAExactKit

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The cover reduction -/

/-- A finite set of words covering every translation coset of the code. -/
def IsCosetCover (C : Submodule F (ι → A)) (R : Finset (ι → A)) : Prop :=
  ∀ u : ι → A, ∃ r ∈ R, u - r ∈ C

open Classical in
/-- **The cover reduction:** `ε_mca` is the sup of the per-stack probability over pairs
from any coset cover. -/
theorem epsMCA_eq_sup_cover (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {R : Finset (ι → A)} (hR : IsCosetCover C R) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      = ⨆ r₀ ∈ R, ⨆ r₁ ∈ R,
          Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ r₀ r₁ γ] := by
  unfold epsMCA
  apply le_antisymm
  · refine iSup_le fun u => ?_
    obtain ⟨r₀, hr₀R, hr₀⟩ := hR (u 0)
    obtain ⟨r₁, hr₁R, hr₁⟩ := hR (u 1)
    have heq : Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ]
        = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ r₀ r₁ γ] :=
      stackProb_eq_of_sub_mem (F := F) C δ hr₀ hr₁
    rw [heq]
    exact le_iSup₂_of_le r₀ hr₀R (le_iSup₂_of_le r₁ hr₁R le_rfl)
  · refine iSup₂_le fun r₀ _ => iSup₂_le fun r₁ _ => ?_
    exact le_iSup_of_le (![r₀, r₁] : WordStack A (Fin 2) ι) le_rfl

open Classical in
/-- **The fully finite normal form.** Over a coset cover `R`, with the integer-threshold
bridge in force, `ε_mca` is the maximum bad-scalar census over `R × R`, divided by `|F|`:
a decidable expression over `|R|²` pairs. -/
theorem epsMCA_eq_sup_badScalarCount_cover (C : Submodule F (ι → A))
    [DecidablePred (· ∈ (C : Set (ι → A)))] {δ : ℝ≥0} {t : ℕ}
    (ht : ∀ S : Finset ι,
      ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0)) ↔ t ≤ S.card)
    {R : Finset (ι → A)} (hR : IsCosetCover C R) (hRne : R.Nonempty) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      = ((R.sup (fun r₀ => R.sup (fun r₁ =>
            badScalarCount (F := F) (C : Set (ι → A)) t r₀ r₁)) : ℕ) : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA_eq_sup_cover (F := F) C δ hR]
  -- both directions at leaf level: the per-stack probability is the census over `q`
  apply le_antisymm
  · refine iSup₂_le fun r₀ hr₀ => iSup₂_le fun r₁ hr₁ => ?_
    rw [prob_mcaEvent_eq_badScalarCount_div (C : Set (ι → A)) ht r₀ r₁]
    gcongr
    exact_mod_cast le_trans
      (Finset.le_sup (f := fun r₁ =>
        badScalarCount (F := F) (C : Set (ι → A)) t r₀ r₁) hr₁)
      (Finset.le_sup (f := fun r₀ => R.sup (fun r₁ =>
        badScalarCount (F := F) (C : Set (ι → A)) t r₀ r₁)) hr₀)
  · obtain ⟨r₀, hr₀, h₀⟩ := Finset.exists_mem_eq_sup R hRne
      (fun r₀ => R.sup (fun r₁ =>
        badScalarCount (F := F) (C : Set (ι → A)) t r₀ r₁))
    obtain ⟨r₁, hr₁, h₁⟩ := Finset.exists_mem_eq_sup R hRne
      (fun r₁ => badScalarCount (F := F) (C : Set (ι → A)) t r₀ r₁)
    rw [h₀, h₁, ← prob_mcaEvent_eq_badScalarCount_div (C : Set (ι → A)) ht r₀ r₁]
    exact le_iSup₂_of_le r₀ hr₀ (le_iSup₂_of_le r₁ hr₁ le_rfl)

/-! ## The interpolation transversal -/

/-- The words vanishing on `I` — the explicit candidate transversal of size
`|A|^{n−|I|}`. -/
def vanishingOn (I : Finset ι) : Finset (ι → A) :=
  Finset.univ.filter (fun u => ∀ i ∈ I, u i = 0)

theorem mem_vanishingOn {I : Finset ι} {u : ι → A} :
    u ∈ (vanishingOn I : Finset (ι → A)) ↔ ∀ i ∈ I, u i = 0 := by
  simp [vanishingOn]

/-- `vanishingOn I` is nonempty (it contains `0`). -/
theorem vanishingOn_nonempty (I : Finset ι) :
    (vanishingOn I : Finset (ι → A)).Nonempty :=
  ⟨0, mem_vanishingOn.mpr fun _ _ => rfl⟩

omit [Fintype F] [DecidableEq F] in
/-- **Interpolation gives a cover:** if every word can be matched on `I` by a codeword
(for `RS[F, L, k]` with `|I| ≤ k`: Lagrange interpolation), then the words vanishing on
`I` cover every coset of `C`. -/
theorem cover_vanishingOn_of_interpolation (C : Submodule F (ι → A)) (I : Finset ι)
    (hI : ∀ v : ι → A, ∃ c ∈ C, ∀ i ∈ I, c i = v i) :
    IsCosetCover C (vanishingOn I) := by
  intro u
  obtain ⟨c, hcC, hc⟩ := hI u
  refine ⟨u - c, mem_vanishingOn.mpr ?_, ?_⟩
  · intro i hi
    simp [hc i hi]
  · have : u - (u - c) = c := by abel
    rw [this]
    exact hcC

open Classical in
/-- **The interpolation normal form** — the composition the exact rungs consume:
for any code with interpolation on `I` and any on-grid radius, `ε_mca` is the maximum
bad-scalar census over pairs of words vanishing on `I`, divided by `|F|`. The sup ranges
over `|A|^{2(n−|I|)}` pairs — the probes' syndrome reduction, formal and computable. -/
theorem epsMCA_eq_sup_badScalarCount_vanishingOn (C : Submodule F (ι → A))
    [DecidablePred (· ∈ (C : Set (ι → A)))] {δ : ℝ≥0} {t : ℕ}
    (ht : ∀ S : Finset ι,
      ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0)) ↔ t ≤ S.card)
    (I : Finset ι) (hI : ∀ v : ι → A, ∃ c ∈ C, ∀ i ∈ I, c i = v i) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      = (((vanishingOn I).sup (fun r₀ => (vanishingOn I).sup (fun r₁ =>
            badScalarCount (F := F) (C : Set (ι → A)) t r₀ r₁)) : ℕ) : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_eq_sup_badScalarCount_cover C ht
    (cover_vanishingOn_of_interpolation C I hI) (vanishingOn_nonempty I)

/-! ## Source audit -/

#print axioms epsMCA_eq_sup_cover
#print axioms epsMCA_eq_sup_badScalarCount_cover
#print axioms cover_vanishingOn_of_interpolation
#print axioms epsMCA_eq_sup_badScalarCount_vanishingOn

end ProximityGap.MCAExplicitTransversal
