/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# Bridge B21 — the over-determined agreement condition is AFFINE in `γ` (target E4)

**Spec B21 / target E4.** Along a window's affine path `u₀ + γ·u₁`, the over-determination
("agreement") condition that pins `δ*` is *linear (affine) in `γ` per window*:

> `DD_k(u₀ + γ·u₁) = DD_k(u₀) + γ·DD_k(u₁) = 0`.

Here `DD_k` is the divided-difference / over-determination operator — the linear functional
whose vanishing expresses "the word along the line agrees with `RS[μ_n, k]` on this window".
The point of E4 is purely structural: this operator is `F`-**linear** in its word argument,
so when the word itself runs along an affine line `γ ↦ u₀ + γ • u₁`, the condition
`DD_k(word γ) = 0` is an **affine** equation in `γ` (a single linear-in-`γ` constraint per
window), not a higher-degree one. That is what makes the bad-`γ` set a *union of affine
loci* (one per over-determination row), which is the combinatorial skeleton behind the
orbit / partial-orbit picture of E3–E4 and the geometric decay `D*(1) ≈ n³`.

## What is proven here (axiom-clean)

Working over an arbitrary base field `F` (so this specializes to the prize field), with the
word space an arbitrary `F`-module `W` and the residual space an arbitrary `F`-module `U`:

* **`dd_affine`** — for any `F`-linear `DD : W →ₗ[F] U` and any affine path
  `γ ↦ u₀ + γ • u₁`, `DD (u₀ + γ • u₁) = DD u₀ + γ • DD u₁`.  This is the literal
  `DD_k(u₀+γ u₁)=DD_k(u₀)+γ DD_k(u₁)` of the spec.
* **`agreement_affine_iff`** — the single-row agreement condition is affine:
  `DD (u₀ + γ • u₁) = 0 ↔ DD u₀ + γ • DD u₁ = 0`.
* **`overdet_agreement_affine_iff`** — the *over-determined* (multi-row) agreement system
  `∀ i, DD i (u₀ + γ • u₁) = 0` is equivalent, row by row, to the affine system
  `∀ i, DD i u₀ + γ • DD i u₁ = 0`.  (`i` ranges over the over-determination rows of the
  window; the system is over-determined when there are more rows than the line has freedom.)
* **`overdet_badSet_eq`** — consequently the *bad-`γ` set* of a window (the `γ` for which the
  whole over-determination system vanishes) equals the set cut out by the affine system; each
  row contributes an **affine** locus in `γ`.
* **`dd_eval_isLinear`** — the concrete divided-difference shape `w ↦ ∑ⱼ cⱼ • (eval w at node
  j)` (a finite `F`-linear combination of coordinate evaluations) really is such a linear map,
  so the abstract `DD` above is faithful to `DD_k`.

## Bridge to the substrate (`IncidencePeriodBridge`)

The substrate `IncidencePeriodBridge.lineIncidence G s₀ s₁` counts the `γ` on the affine line
`γ ↦ s₀ + γ·s₁` that land in the ball `G`.  The lemma **`lineIncidence_affine_locus`** below
records that this is exactly the count of `γ` satisfying the affine membership condition
`affineLine s₀ s₁ γ ∈ G`, i.e. the bad/agreement set the substrate already brackets is the
`γ`-locus of one such affine path.  So B21 supplies the *per-window linearity* that the
substrate's incidence count tacitly ranges over: each over-determination row is an affine
equation in `γ`, and `lineIncidence` is the membership count along one affine line.

Axiom-clean; pure linearity, no field-size or regime hypotheses.  Issue #444 (target E4).
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB21

/-! ### The affine path `γ ↦ u₀ + γ • u₁` -/

variable {F : Type*} [Field F]
variable {W U : Type*} [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]

/-- The affine path through `u₀` with direction `u₁`, parametrized by `γ : F`. -/
def affinePath (u₀ u₁ : W) (γ : F) : W := u₀ + γ • u₁

@[simp] theorem affinePath_apply (u₀ u₁ : W) (γ : F) :
    affinePath u₀ u₁ γ = u₀ + γ • u₁ := rfl

/-! ### E4 core: a linear operator is affine along the path -/

/-- **The divided-difference is affine along the line (E4, literal form).**
For any `F`-linear over-determination operator `DD : W →ₗ[F] U`,
`DD (u₀ + γ • u₁) = DD u₀ + γ • DD u₁`.  This is exactly
`DD_k(u₀ + γ·u₁) = DD_k(u₀) + γ·DD_k(u₁)`. -/
theorem dd_affine (DD : W →ₗ[F] U) (u₀ u₁ : W) (γ : F) :
    DD (affinePath u₀ u₁ γ) = DD u₀ + γ • DD u₁ := by
  simp [affinePath, map_add, map_smul]

/-- **The single-row agreement condition is affine in `γ`.**
`DD (u₀ + γ • u₁) = 0 ↔ DD u₀ + γ • DD u₁ = 0`. -/
theorem agreement_affine_iff (DD : W →ₗ[F] U) (u₀ u₁ : W) (γ : F) :
    DD (affinePath u₀ u₁ γ) = 0 ↔ DD u₀ + γ • DD u₁ = 0 := by
  rw [dd_affine]

/-! ### Over-determined (multi-row) system -/

variable {ι : Type*}

/-- **The over-determined agreement system is row-by-row affine.**
For a family of over-determination rows `DD : ι → (W →ₗ[F] U)`, the system
`∀ i, DD i (u₀ + γ • u₁) = 0` is equivalent to the affine system
`∀ i, DD i u₀ + γ • DD i u₁ = 0`.  Over-determination = `|ι|` larger than the line's freedom;
the equivalence is purely the linearity of each row. -/
theorem overdet_agreement_affine_iff (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W) (γ : F) :
    (∀ i, DD i (affinePath u₀ u₁ γ) = 0) ↔ (∀ i, DD i u₀ + γ • DD i u₁ = 0) := by
  constructor
  · intro h i; rw [← dd_affine]; exact h i
  · intro h i; rw [dd_affine]; exact h i

/-- The bad-`γ` set of a window: the `γ` for which the whole over-determination system
vanishes. -/
def badGammaSet (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W) : Set F :=
  {γ : F | ∀ i, DD i (affinePath u₀ u₁ γ) = 0}

/-- **The bad-`γ` set is cut out by the affine system (E4 consequence).**
Each over-determination row contributes an affine-in-`γ` equation. -/
theorem overdet_badSet_eq (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W) :
    badGammaSet DD u₀ u₁ = {γ : F | ∀ i, DD i u₀ + γ • DD i u₁ = 0} := by
  ext γ
  simp only [badGammaSet, Set.mem_setOf_eq]
  exact overdet_agreement_affine_iff DD u₀ u₁ γ

/-- A single over-determination row, as a γ-locus, is genuinely affine: it is the solution set
of `DD u₀ + γ • DD u₁ = 0`, a linear equation in `γ` (degree ≤ 1, the `γ` coefficient `DD u₁`,
constant term `DD u₀`). -/
theorem row_locus_affine (DD : W →ₗ[F] U) (u₀ u₁ : W) :
    {γ : F | DD (affinePath u₀ u₁ γ) = 0} = {γ : F | DD u₀ + γ • DD u₁ = 0} := by
  ext γ
  simp only [Set.mem_setOf_eq]
  exact agreement_affine_iff DD u₀ u₁ γ

/-! ### The concrete divided-difference shape is such a linear map -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The concrete divided-difference / over-determination functional on word space `n → F`:
`w ↦ ∑ⱼ c j • w j`, a finite `F`-linear combination of coordinate evaluations (this is the
shape of `DD_k(w) = ∑ⱼ (∏_{l≠j}(x_j−x_l))⁻¹ · w_j`, a divided difference / complete-homogeneous
read-out — the coefficients `c` are the divided-difference weights). -/
def ddEval (c : n → F) : (n → F) →ₗ[F] F where
  toFun w := ∑ j, c j * w j
  map_add' w w' := by
    simp only [Pi.add_apply, mul_add]
    rw [← Finset.sum_add_distrib]
  map_smul' a w := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring

@[simp] theorem ddEval_apply (c : n → F) (w : n → F) :
    ddEval c w = ∑ j, c j * w j := rfl

/-- The concrete divided-difference operator IS a linear map (witnessing that the abstract
`DD : W →ₗ[F] U` above faithfully models `DD_k`), so the affine-in-`γ` conclusions apply to it.
In particular its value along the line is affine: -/
theorem ddEval_affine (c : n → F) (u₀ u₁ : n → F) (γ : F) :
    ddEval c (affinePath u₀ u₁ γ) = ddEval c u₀ + γ • ddEval c u₁ :=
  dd_affine (ddEval c) u₀ u₁ γ

/-! ### Bridge to the substrate incidence count -/

variable {Fld : Type*} [Field Fld] [Fintype Fld] [DecidableEq Fld]

/-- **Bridge to `IncidencePeriodBridge.lineIncidence`.** The substrate's far-line incidence
counts the `γ` on the affine line `γ ↦ s₀ + γ·s₁` landing in the ball `G`.  Read in the
language of B21, this is exactly the membership count along the affine path
`affinePath s₀ s₁` (with `W = U = Fld` the one-dimensional word space): the agreement/bad set
the substrate brackets is the `γ`-locus of one affine path.  (Here membership `· ∈ G` plays the
role of the per-row vanishing condition; B21 supplies that each such row is affine in `γ`.) -/
theorem lineIncidence_affine_locus (G : Finset Fld) (s₀ s₁ : Fld) :
    ArkLib.ProximityGap.IncidencePeriodBridge.lineIncidence G s₀ s₁
      = (Finset.univ.filter (fun γ : Fld => affinePath s₀ s₁ γ ∈ G)).card := by
  unfold ArkLib.ProximityGap.IncidencePeriodBridge.lineIncidence
  rfl

end ArkLib.ProximityGap.BridgeB21

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.BridgeB21.dd_affine
#print axioms ArkLib.ProximityGap.BridgeB21.overdet_agreement_affine_iff
#print axioms ArkLib.ProximityGap.BridgeB21.overdet_badSet_eq
#print axioms ArkLib.ProximityGap.BridgeB21.ddEval_affine
#print axioms ArkLib.ProximityGap.BridgeB21.lineIncidence_affine_locus
