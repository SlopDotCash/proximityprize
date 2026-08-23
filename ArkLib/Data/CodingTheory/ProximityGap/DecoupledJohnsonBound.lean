/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole

/-!
# The decoupled-Johnson bound on MCA bad scalars (#389)

A **fourth, structurally distinct** upper bound on the number of MCA-bad scalars, complementing
the three already in tree (per-witness subset ownership, high-distance `BandCollapse`, and the
failure-side second moment).  Where the ownership census counts the subsets each bad scalar
*owns* and `BandCollapse` exploits low-weight rigidity, this bound is a **Johnson-type packing on
the witness sets themselves**, controlled by the self-agreement of the *direction word* `u₁`.

## The mechanism

For two bad scalars `γ ≠ γ'` with witness sets `S_γ, S_{γ'}` and witness codewords `w_γ, w_{γ'}`
(`w_γ = u₀ + γ • u₁` on `S_γ`), on the overlap `S_γ ∩ S_{γ'}` we have

    w_γ − w_{γ'} = (u₀ + γ•u₁) − (u₀ + γ'•u₁) = (γ − γ') • u₁ ,

so `u₁ = (γ − γ')⁻¹ • (w_γ − w_{γ'})` there — and the right-hand side is a **codeword** (`C` is a
submodule).  Hence `S_γ ∩ S_{γ'}` is contained in the agreement set of `u₁` with a single
codeword, so

    |S_γ ∩ S_{γ'}| ≤ A₁ := max over `c ∈ C` of the agreement of `u₁` with `c`.

The Cauchy–Schwarz set-packing lemma `card_mul_sub_le_of_agreement` (already in tree) then yields,
for witness size `≥ a` and gap `n·A₁ ≤ a²`,

    **#{bad γ} · (a² − n·A₁) ≤ n²,**   i.e.   `#bad ≤ n²/(a² − n·A₁)`.

This is the natural "second moment" of the **floor** (the `BallIntersection`/`AgreementMomentTwo`
files compute second moments of the failure/ceiling side).  Probe `_wf_decoupled_johnson.py`:
exhaustive, 0 violations of both the pairwise bound and the packing bound across `k = 1,2`.

## Honest scope

`A₁` is `u₁`'s own proximity to the code.  The bound is **non-vacuous exactly when `u₁` is far from
the code** (`A₁ < a²/n`); the structured adversary `u₁ = codeword + sparse spike` makes `A₁ ≈ n`,
killing the gap (probe: the structured family is immune).  So this bound is Johnson-*side* — it
does not break the beyond-Johnson wall — but it **localizes the open core precisely**: the entire
beyond-Johnson difficulty lives in the regime where the *direction word itself is near the code*.
When `u₁` is far, this packing alone gives a strong floor with no per-witness counting at all.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal
open Classical

namespace ArkLib.ProximityGap.DecoupledJohnson

open ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The pairwise witness-overlap bound** (the novel step).  If `γ ≠ γ'` are both bad with
witness sets `Sγ, Sγ'` and witness codewords `wγ, wγ'` (`wγ = u₀ + γ•u₁` on `Sγ`, etc.), then on
the overlap `u₁` coincides with the single codeword `(γ−γ')⁻¹ • (wγ − wγ')`, so the overlap is
contained in an agreement set of `u₁` and has size `≤ A₁`. -/
theorem witness_overlap_le_of_codeword_agreement
    (C : Submodule F (ι → A)) (u₀ u₁ : ι → A) (A₁ : ℕ)
    (hA1 : ∀ c ∈ C, (Finset.univ.filter (fun i => c i = u₁ i)).card ≤ A₁)
    {γ γ' : F} (hγ : γ ≠ γ') {Sγ Sγ' : Finset ι} {wγ wγ' : ι → A}
    (hwγC : wγ ∈ C) (hwγ'C : wγ' ∈ C)
    (hwγ : ∀ i ∈ Sγ, wγ i = u₀ i + γ • u₁ i)
    (hwγ' : ∀ i ∈ Sγ', wγ' i = u₀ i + γ' • u₁ i) :
    (Sγ ∩ Sγ').card ≤ A₁ := by
  classical
  set c : ι → A := (γ - γ')⁻¹ • (wγ - wγ') with hc
  have hcC : c ∈ C := C.smul_mem _ (C.sub_mem hwγC hwγ'C)
  have hsub : Sγ ∩ Sγ' ⊆ Finset.univ.filter (fun i => c i = u₁ i) := by
    intro i hi
    rw [Finset.mem_inter] at hi
    obtain ⟨hiγ, hiγ'⟩ := hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    -- c i = (γ−γ')⁻¹ • (wγ i − wγ' i) = (γ−γ')⁻¹ • ((γ−γ')•u₁ i) = u₁ i
    have hwi : wγ i - wγ' i = (γ - γ') • u₁ i := by
      rw [hwγ i hiγ, hwγ' i hiγ']
      rw [sub_smul]
      abel
    have hci : c i = (γ - γ')⁻¹ • (wγ i - wγ' i) := by
      simp [hc, Pi.smul_apply, Pi.sub_apply]
    rw [hci, hwi, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hγ), one_smul]
  exact le_trans (Finset.card_le_card hsub) (hA1 c hcC)

/-- **The decoupled-Johnson bound on MCA bad scalars.**  Let `C` be a (linear) code, `(u₀, u₁)` a
word stack, `a` an integer agreement floor with `(a : ℝ≥0) ≤ (1−δ)·n`, and `A₁` a uniform bound on
the agreement of the direction word `u₁` with any single codeword.  Then, under the Johnson gap
`n·A₁ ≤ a²`, the number of MCA-bad scalars satisfies

    `#bad · (a² − n·A₁) ≤ n²`,   i.e.   `#bad ≤ n² / (a² − n·A₁)`.

The bound is controlled entirely by `u₁`'s own proximity `A₁` — decoupled from `u₀`. -/
theorem mca_badScalars_card_mul_sub_le
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (a A₁ : ℕ)
    (ha : (a : ℝ≥0) ≤ (1 - δ) * Fintype.card ι)
    (hA1 : ∀ c ∈ C, (Finset.univ.filter (fun i => c i = u₁ i)).card ≤ A₁)
    (hgap : Fintype.card ι * A₁ ≤ a ^ 2) :
    (Finset.univ.filter
        (fun γ : F => _root_.ProximityGap.mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ)).card
      * (a ^ 2 - Fintype.card ι * A₁) ≤ (Fintype.card ι) ^ 2 := by
  classical
  set B := Finset.univ.filter
      (fun γ : F => _root_.ProximityGap.mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ) with hBdef
  rcases B.eq_empty_or_nonempty with hB | hB
  · simp [hB]
  · haveI : Nonempty ↥B := hB.to_subtype
    -- extract for each bad scalar a witness set + witness codeword
    have hev : ∀ γ : ↥B, _root_.ProximityGap.mcaEvent (C : Set (ι → A)) δ u₀ u₁ (γ : F) :=
      fun γ => (Finset.mem_filter.mp γ.2).2
    choose Sf hScard hrest using hev
    choose wf hwfC hwfagree using fun γ => (hrest γ).1
    -- (1) every witness set has size ≥ a
    have hlo : ∀ γ : ↥B, a ≤ (Sf γ).card := by
      intro γ
      have h1 : (a : ℝ≥0) ≤ ((Sf γ).card : ℝ≥0) := le_trans ha (hScard γ)
      exact_mod_cast h1
    -- (2) pairwise overlaps ≤ A₁ — the novel step
    have hpair : ∀ γ γ' : ↥B, γ ≠ γ' → (Sf γ ∩ Sf γ').card ≤ A₁ := by
      intro γ γ' hne
      refine witness_overlap_le_of_codeword_agreement C u₀ u₁ A₁ hA1
        (fun h => hne (Subtype.ext h)) (hwfC γ) (hwfC γ') (hwfagree γ) (hwfagree γ')
    -- (3) apply the Cauchy–Schwarz set-packing lemma
    have key := ArkLib.Coverage.card_mul_sub_le_of_agreement Sf a A₁ hlo hpair hgap
    rwa [Fintype.card_coe] at key

/-- **Divided form.**  Under the strict Johnson gap `n·A₁ < a²`, the bad-scalar count is capped by
`#bad ≤ n² / (a² − n·A₁)` — directly consumable by the `ε_mca` ledger. -/
theorem mca_badScalars_card_le_div
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (a A₁ : ℕ)
    (ha : (a : ℝ≥0) ≤ (1 - δ) * Fintype.card ι)
    (hA1 : ∀ c ∈ C, (Finset.univ.filter (fun i => c i = u₁ i)).card ≤ A₁)
    (hgap : Fintype.card ι * A₁ < a ^ 2) :
    (Finset.univ.filter
        (fun γ : F => _root_.ProximityGap.mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ)).card
      ≤ (Fintype.card ι) ^ 2 / (a ^ 2 - Fintype.card ι * A₁) := by
  have hmul := mca_badScalars_card_mul_sub_le C δ u₀ u₁ a A₁ ha hA1 (le_of_lt hgap)
  exact (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hgap)).2 hmul

end ArkLib.ProximityGap.DecoupledJohnson

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.DecoupledJohnson.witness_overlap_le_of_codeword_agreement
#print axioms ArkLib.ProximityGap.DecoupledJohnson.mca_badScalars_card_mul_sub_le
#print axioms ArkLib.ProximityGap.DecoupledJohnson.mca_badScalars_card_le_div
