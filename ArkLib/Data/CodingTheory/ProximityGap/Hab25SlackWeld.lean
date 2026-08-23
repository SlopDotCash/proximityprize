/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CoordinateUpgradeWeld

/-!
# The slack weld: global branch from a witnessed subcell (#302, R-K3)

The assigned-factor-rich weld (`global_branch_of_assigned_factor_rich`) demands its factor
data `(Hf, assign, S)` at **every** cell scalar — but the global-branch conclusion
`(Y − C pHat) ∣ R` is a statement about `R`, not about the cell `E`.  This file proves the
**slack form**: the factor data is required only at scalars *witnessed* at the relevant
coordinate (an abstract per-coordinate predicate `W` with defect bound
`|E.filter (¬ W t ·)| ≤ M`), and the count leg absorbs the loss:

* **`global_branch_of_witnessed_subcell`** — with `|E| > B_R + deg_Y R·(L−1) + k·M`, the
  witnessed-everywhere subcell `E' := E.filter (fun γ => ∀ t ∈ T, W t γ)` still beats the
  defect budget (`|E'| ≥ |E| − k·M` by a union bound over the `k` coordinates), and running
  the assigned-factor weld on `E'` produces the global branch outright.  The unwitnessed
  scalars never need an assigned factor: they are *counted away*, not pinned.
* `global_branch_of_fully_witnessed` — the `M = 0` specialization (every cell scalar
  witnessed at every chosen coordinate): the count leg degrades to the original
  `|E| > B_R + deg_Y R·(L−1)` — the R-K1 fully-witnessed corollary.

## Honest regime statement

The witness data remains load-bearing — the algebra-only strawman is FALSE (`Y² − Z`; see
the honesty note in `Hab25CandidateProduction`).  Moreover, BCIKS20 itself does **not** take
this route: the paper never forms a witnessed-everywhere intersection and never pays an
additive `k·M`; its Claim 5.10 concludes the identity `γ(x) = w(x,Z)` *in the extension
field `L`* from per-coordinate agreement counts alone, pinning disagreeing scalars
retroactively, and interpolates the branch in `L` scalar-free (eprint 2020/654, pp. 24–27).
Quantitatively the per-coordinate defect at the top coordinates is *multiplicative*
(`|S′_x| ≥ (1−ρ−δ)/(1−ρ)·|S′|`, Claim 5.11), i.e. `M ≈ δ/(1−ρ)·|E|`, so the intersection
subcell here is useful when `k·δ/(1−ρ) < 1` — genuine content below that radius, NOT the
Johnson-regime closure.  The Johnson-regime route is the per-coordinate-independent one
(global capture + the `𝒪`-level kill of `CoordinateKillBudget` Part 1); this file is the
counting-side complement, not its replacement.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 Claims 5.9–5.11.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open _root_.ProximityGap Code

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The slack weld: the global branch from witness-rich factor assignments on the
witnessed subcell only.**  The factor data (`hroot`/`hrich`/`hwit`) is demanded only at
pairs `(t, γ)` with `γ` witnessed at `t`; the per-coordinate defect (`≤ M` unwitnessed
scalars at each of the `k` chosen coordinates) is absorbed by the count leg
`|E| > B_R + deg_Y R·(L−1) + k·M`.  The unwitnessed scalars are counted away — the branch
conclusion is about `R`, so they never need pinning. -/
theorem global_branch_of_witnessed_subcell {n L k : ℕ} (hk : 0 < k) (hL : 0 < L)
    {domain : Fin n ↪ F₀} {u : WordStack F₀ (Fin L) (Fin n)}
    (R : (F₀[X])[X][Y]) {BR : ℕ}
    (hRB : ∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ BR)
    (E : Finset F₀) (P : F₀ → F₀[X]) (T : Finset (Fin n)) (hT : T.card = k)
    (W : Fin n → F₀ → Prop) (M : ℕ)
    (hdefect : ∀ t ∈ T, (E.filter (fun γ => ¬ W t γ)).card ≤ M)
    (hdeg : ∀ γ ∈ E, (P γ).degree < (k : ℕ))
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    {ι : Type} (Hf : Fin n → ι → F₀[X][Y]) {B : ℕ}
    (hirr : ∀ t ∈ T, ∀ i : ι, Irreducible (Hf t i))
    (hB : ∀ t ∈ T, ∀ (i : ι) (k' : ℕ), ((Hf t i).coeff k').natDegree ≤ B)
    (assign : Fin n → F₀ → ι) (S : Fin n → ι → Finset F₀)
    (hroot : ∀ t ∈ T, ∀ γ ∈ E, W t γ →
      ((Hf t (assign t γ)).map (Polynomial.evalRingHom γ)).eval
        ((P γ).eval (domain t)) = 0)
    (hrich : ∀ t ∈ T, ∀ γ ∈ E, W t γ →
      B + (Hf t (assign t γ)).natDegree * (L - 1) < (S t (assign t γ)).card)
    (hwit : ∀ t ∈ T, ∀ γ ∈ E, W t γ → ∀ ζ ∈ S t (assign t γ),
      ((Hf t (assign t γ)).map (Polynomial.evalRingHom ζ)).eval
        ((foldSectionAt u t).eval ζ) = 0)
    (hbig : BR + R.natDegree * (L - 1) + k * M < E.card) :
    (Polynomial.X - Polynomial.C
        (branchOfCurveTuple (fun j => lagrangeCurveTuple domain u T j))) ∣ R := by
  classical
  set E' : Finset F₀ := E.filter (fun γ => ∀ t ∈ T, W t γ) with hE'def
  have hE'sub : E' ⊆ E := Finset.filter_subset _ _
  -- every scalar dropped from `E'` fails the witness at some chosen coordinate
  have hsdiff : E \ E' ⊆ T.biUnion (fun t => E.filter (fun γ => ¬ W t γ)) := by
    intro γ hγ
    rw [Finset.mem_sdiff] at hγ
    obtain ⟨hγE, hγnot⟩ := hγ
    have hnotall : ¬ ∀ t ∈ T, W t γ := by
      intro hall
      exact hγnot (Finset.mem_filter.mpr ⟨hγE, hall⟩)
    push Not at hnotall
    obtain ⟨t, ht, hnW⟩ := hnotall
    exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_filter.mpr ⟨hγE, hnW⟩⟩
  -- the union bound: at most `k·M` scalars are dropped
  have hdrop : (E \ E').card ≤ k * M := by
    calc (E \ E').card
        ≤ (T.biUnion (fun t => E.filter (fun γ => ¬ W t γ))).card :=
          Finset.card_le_card hsdiff
      _ ≤ ∑ t ∈ T, (E.filter (fun γ => ¬ W t γ)).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ T, M := Finset.sum_le_sum (fun t ht => hdefect t ht)
      _ = T.card * M := by rw [Finset.sum_const, smul_eq_mul]
      _ = k * M := by rw [hT]
  have hEcard : E.card ≤ E'.card + k * M := by
    have hsplit : (E \ E').card + E'.card = E.card :=
      Finset.card_sdiff_add_card_eq_card hE'sub
    omega
  -- the witnessed subcell still beats the budget
  have hbig' : BR + R.natDegree * (L - 1) < E'.card := by omega
  -- membership in `E'` carries the witness at every chosen coordinate
  have hmem : ∀ γ ∈ E', γ ∈ E ∧ ∀ t ∈ T, W t γ := by
    intro γ hγ
    exact Finset.mem_filter.mp hγ
  exact global_branch_of_assigned_factor_rich hk hL R hRB E' P T hT
    (fun γ hγ => hdeg γ (hmem γ hγ).1)
    (fun γ hγ => hdvdP γ (hmem γ hγ).1)
    Hf hirr hB assign S
    (fun t ht γ hγ => hroot t ht γ (hmem γ hγ).1 ((hmem γ hγ).2 t ht))
    (fun t ht γ hγ => hrich t ht γ (hmem γ hγ).1 ((hmem γ hγ).2 t ht))
    (fun t ht γ hγ => hwit t ht γ (hmem γ hγ).1 ((hmem γ hγ).2 t ht))
    hbig'

/-- **The fully-witnessed corollary (R-K1, `M = 0`)**: when every cell scalar is witnessed
at every chosen coordinate, the count leg degrades to the original
`|E| > B_R + deg_Y R·(L−1)`. -/
theorem global_branch_of_fully_witnessed {n L k : ℕ} (hk : 0 < k) (hL : 0 < L)
    {domain : Fin n ↪ F₀} {u : WordStack F₀ (Fin L) (Fin n)}
    (R : (F₀[X])[X][Y]) {BR : ℕ}
    (hRB : ∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ BR)
    (E : Finset F₀) (P : F₀ → F₀[X]) (T : Finset (Fin n)) (hT : T.card = k)
    (W : Fin n → F₀ → Prop)
    (hall : ∀ t ∈ T, ∀ γ ∈ E, W t γ)
    (hdeg : ∀ γ ∈ E, (P γ).degree < (k : ℕ))
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    {ι : Type} (Hf : Fin n → ι → F₀[X][Y]) {B : ℕ}
    (hirr : ∀ t ∈ T, ∀ i : ι, Irreducible (Hf t i))
    (hB : ∀ t ∈ T, ∀ (i : ι) (k' : ℕ), ((Hf t i).coeff k').natDegree ≤ B)
    (assign : Fin n → F₀ → ι) (S : Fin n → ι → Finset F₀)
    (hroot : ∀ t ∈ T, ∀ γ ∈ E, W t γ →
      ((Hf t (assign t γ)).map (Polynomial.evalRingHom γ)).eval
        ((P γ).eval (domain t)) = 0)
    (hrich : ∀ t ∈ T, ∀ γ ∈ E, W t γ →
      B + (Hf t (assign t γ)).natDegree * (L - 1) < (S t (assign t γ)).card)
    (hwit : ∀ t ∈ T, ∀ γ ∈ E, W t γ → ∀ ζ ∈ S t (assign t γ),
      ((Hf t (assign t γ)).map (Polynomial.evalRingHom ζ)).eval
        ((foldSectionAt u t).eval ζ) = 0)
    (hbig : BR + R.natDegree * (L - 1) < E.card) :
    (Polynomial.X - Polynomial.C
        (branchOfCurveTuple (fun j => lagrangeCurveTuple domain u T j))) ∣ R := by
  classical
  refine global_branch_of_witnessed_subcell hk hL R hRB E P T hT W 0
    (fun t ht => ?_) hdeg hdvdP Hf hirr hB assign S hroot hrich hwit (by omega)
  have hempty : E.filter (fun γ => ¬ W t γ) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun γ hγ => not_not_intro (hall t ht γ hγ))
  simp [hempty]

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms global_branch_of_witnessed_subcell
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms global_branch_of_fully_witnessed
