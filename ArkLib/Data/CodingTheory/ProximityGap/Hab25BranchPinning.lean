/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.HenselBranchRigidity
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCapture

/-!
# Branch pinning: the per-`γ` rigidity half of the capture (BCIKS20 Claim 5.8)

The per-component capture asks: many planar points `(γ, P γ(x₀))` on one irreducible
fiber component force the decode family onto a polynomial curve. This file proves its
**per-`γ` rigidity half** from the in-tree Hensel machinery: once a **global integral
branch** `pHat ∈ F[Z][X]` through the section exists, the decode family *is* its
specialization family, and the curve-pinning input of the Claim-1 dichotomy follows:

* `decode_eq_specialized_branch` — at one scalar: a decode polynomial and a specialized
  global branch through the **same fiber value** coincide
  (`ProximityPrize.HenselBranchRigidity.branch_eq_of_fiber_eq_of_separable`: the
  specialized interpolant's fiber at `x₀` is separable, so the branch through a point is
  unique);
* `specializedBranchCurve` / `map_eval_eq_curve_sum` — a global branch with `Z`-degree
  `< L` *is* a polynomial curve: its specializations are `∑_j γʲ·a_j` for the
  coefficient-transpose tuple `a`;
* **`pinning_of_global_branch`** — the literal `hpin` input of
  `cell_card_le_of_curve_decode_family_pinning`: a global branch through the cell's
  section (divisibility + fiber match + S5 separability, all per-`γ`) pins the decode
  family to the curve tuple of its transpose.

What this leaves of BCIKS20 C5.8/C5.9 is exactly the **existence half**: the global
branch `pHat` over the function field, with its `Z`-degree budget (`< 2` for the pair's
affine case) — the Λ-weight/βHensel coefficient bounds of the #138/#139 stream. All the
specialization, rigidity, and pinning logic around it is now proven.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open _root_.ProximityGap Code
open scoped NNReal

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀]

/-- **Per-`γ` branch rigidity (the uniqueness half of BCIKS20 Claim 5.8).** A decode
polynomial and a specialized global branch dividing the same specialized interpolant
through the same fiber value coincide — the fiber separability (the S5 good-point
output) makes the branch through a point unique. -/
theorem decode_eq_specialized_branch {R : (F₀[X])[X][Y]} {γ x₀ : F₀} {p q : F₀[X]}
    (hsep : ((R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))).map
      (Polynomial.evalRingHom x₀)).Separable)
    (hp : (Polynomial.X - Polynomial.C p) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (hq : (Polynomial.X - Polynomial.C q) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (hfib : p.eval x₀ = q.eval x₀) :
    p = q :=
  ProximityPrize.HenselBranchRigidity.branch_eq_of_fiber_eq_of_separable
    hsep hp hq hfib

/-- The coefficient transpose of a global branch `pHat ∈ F[Z][X]`: the `X`-polynomial of
its `Zʲ`-slices, `a_j = ∑_i C((pHat.coeff i).coeff j)·Xⁱ`. -/
noncomputable def specializedBranchCurve (pHat : (F₀[X])[X]) (j : ℕ) : F₀[X] :=
  ∑ i ∈ Finset.range (pHat.natDegree + 1),
    Polynomial.C ((pHat.coeff i).coeff j) * Polynomial.X ^ i

lemma specializedBranchCurve_coeff (pHat : (F₀[X])[X]) (j i : ℕ) :
    (specializedBranchCurve pHat j).coeff i =
      if i ∈ Finset.range (pHat.natDegree + 1) then (pHat.coeff i).coeff j else 0 := by
  unfold specializedBranchCurve
  rw [Polynomial.finset_sum_coeff]
  by_cases hmem : i ∈ Finset.range (pHat.natDegree + 1)
  · rw [if_pos hmem, Finset.sum_eq_single i]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (fun hc => hne hc.symm), mul_zero]
    · intro habs
      exact absurd hmem habs
  · rw [if_neg hmem, Finset.sum_eq_zero]
    intro b hb
    have hbi : b ≠ i := fun hbi => hmem (hbi ▸ hb)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun hc => hbi hc.symm), mul_zero]

/-- The transpose tuple inherits the branch's `X`-degree bound. -/
lemma specializedBranchCurve_natDegree_lt {pHat : (F₀[X])[X]} {k : ℕ} (hk : 0 < k)
    (hdeg : pHat.natDegree < k) (j : ℕ) :
    (specializedBranchCurve pHat j).natDegree < k := by
  have hle : (specializedBranchCurve pHat j).natDegree ≤ k - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans (Polynomial.natDegree_X_pow_le _) ?_
    have := Finset.mem_range.mp hi
    omega
  omega

/-- **A global branch with `Z`-degree `< L` is a polynomial curve**: its specialization
at every `γ` is `∑_j C(γʲ)·a_j` for the transpose tuple. -/
lemma map_eval_eq_curve_sum {L : ℕ} (pHat : (F₀[X])[X])
    (hZ : ∀ i : ℕ, (pHat.coeff i).natDegree < L) (γ : F₀) :
    pHat.map (Polynomial.evalRingHom γ) =
      ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * specializedBranchCurve pHat (j : ℕ) := by
  ext i
  rw [Polynomial.coeff_map, Polynomial.coe_evalRingHom, Polynomial.finset_sum_coeff]
  have hRHS : ∀ j : Fin L,
      (Polynomial.C (γ ^ (j : ℕ)) * specializedBranchCurve pHat (j : ℕ)).coeff i =
      γ ^ (j : ℕ) * (specializedBranchCurve pHat (j : ℕ)).coeff i := fun j =>
    Polynomial.coeff_C_mul _
  rw [Finset.sum_congr rfl fun j _ => hRHS j]
  by_cases hi : i ∈ Finset.range (pHat.natDegree + 1)
  · -- in range: the slice identity is the evaluation as a coefficient sum
    have hslice : ∀ j : Fin L, (specializedBranchCurve pHat (j : ℕ)).coeff i =
        (pHat.coeff i).coeff (j : ℕ) := fun j => by
      rw [specializedBranchCurve_coeff, if_pos hi]
    rw [Finset.sum_congr rfl fun j _ => by rw [hslice j]]
    rw [Polynomial.eval_eq_sum_range' (hZ i) γ]
    rw [← Fin.sum_univ_eq_sum_range (fun j => (pHat.coeff i).coeff j * γ ^ j) L]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · -- out of range: both sides vanish
    have hpz : pHat.coeff i = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      have := Finset.mem_range.not.mp hi
      omega
    rw [hpz, Polynomial.eval_zero, Finset.sum_eq_zero]
    intro j _
    rw [specializedBranchCurve_coeff, if_neg hi, mul_zero]

variable [Fintype F₀] [DecidableEq F₀]

/-- **The pinning from a global branch (BCIKS20 C5.8, rigidity half — the literal
`hpin` of the K4 seam).** If a global integral branch `pHat ∈ F[Z][X]` exists with
* `X`-degree `< k` and `Z`-degree `< L` (the C5.8/C5.9 budgets),
* per-`γ` divisibility into the specialized interpolant, and
* the fiber match with the decode family at a separable good point `x₀`,

then the decode family is pinned to the polynomial curve of the branch's transpose —
the exact hypothesis shape of `cell_card_le_of_curve_decode_family_pinning` and (at
`L = 2`) of the pair K4. What remains of C5.8/C5.9 is the existence of `pHat` with these
budgets — the Λ-weight/βHensel kernel. -/
theorem pinning_of_global_branch {n k L : ℕ} [NeZero n] {domain : Fin n ↪ F₀}
    {δ : ℝ≥0} {u : WordStack F₀ (Fin L) (Fin n)}
    {R : (F₀[X])[X][Y]} {x₀ : F₀} (E : Finset F₀) (P : F₀ → F₀[X])
    (pHat : (F₀[X])[X]) (hk : 0 < k)
    (hdegX : pHat.natDegree < k)
    (hdegZ : ∀ i : ℕ, (pHat.coeff i).natDegree < L)
    (hdec : ∀ γ ∈ E, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (hdvdpHat : ∀ γ ∈ E, (Polynomial.X - Polynomial.C
        (pHat.map (Polynomial.evalRingHom γ))) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (hsep : ∀ γ ∈ E, ((R.map (Polynomial.mapRingHom
        (Polynomial.evalRingHom γ))).map (Polynomial.evalRingHom x₀)).Separable)
    (hfib : ∀ γ ∈ E, (P γ).eval x₀ = (pHat.map (Polynomial.evalRingHom γ)).eval x₀) :
    ∃ a : Fin L → F₀[X], (∀ j, (a j).natDegree < k) ∧
      ∀ γ ∈ E, P γ = ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * a j := by
  refine ⟨fun j => specializedBranchCurve pHat (j : ℕ),
    fun j => specializedBranchCurve_natDegree_lt hk hdegX (j : ℕ), ?_⟩
  intro γ hγ
  have hpin : P γ = pHat.map (Polynomial.evalRingHom γ) :=
    decode_eq_specialized_branch (hsep γ hγ) (hdvdP γ hγ) (hdvdpHat γ hγ) (hfib γ hγ)
  rw [hpin]
  exact map_eval_eq_curve_sum pHat hdegZ γ

/-- **The cell bound from a global branch**: composing the pinning with the `L`-ary
Claim-1 dichotomy — a cell carrying a global branch through its section obeys
`|Ecell| ≤ T` for any `T ≥ n·(L−1)`. The capture obligation is now *only* the branch
existence. -/
theorem cell_card_le_of_global_branch {n k L : ℕ} [NeZero n] {domain : Fin n ↪ F₀}
    {δ : ℝ≥0} {u : WordStack F₀ (Fin L) (Fin n)}
    {R : (F₀[X])[X][Y]} {x₀ : F₀} (E : Finset F₀) (P : F₀ → F₀[X])
    (pHat : (F₀[X])[X]) (T : ℕ) (hk : 0 < k)
    (hn : Fintype.card (Fin n) * (L - 1) ≤ T)
    (hdegX : pHat.natDegree < k)
    (hdegZ : ∀ i : ℕ, (pHat.coeff i).natDegree < L)
    (hdec : ∀ γ ∈ E, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (hdvdpHat : ∀ γ ∈ E, (Polynomial.X - Polynomial.C
        (pHat.map (Polynomial.evalRingHom γ))) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (hsep : ∀ γ ∈ E, ((R.map (Polynomial.mapRingHom
        (Polynomial.evalRingHom γ))).map (Polynomial.evalRingHom x₀)).Separable)
    (hfib : ∀ γ ∈ E, (P γ).eval x₀ = (pHat.map (Polynomial.evalRingHom γ)).eval x₀) :
    E.card ≤ T :=
  cell_card_le_of_curve_decode_family_pinning E T P hn hdec
    (fun _ => pinning_of_global_branch E P pHat hk hdegX hdegZ hdec hdvdP hdvdpHat
      hsep hfib)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms decode_eq_specialized_branch
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms map_eval_eq_curve_sum
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms pinning_of_global_branch
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms cell_card_le_of_global_branch
