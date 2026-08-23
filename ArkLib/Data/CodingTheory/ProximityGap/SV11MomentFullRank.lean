/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BinomialMatrixDet
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# The SV11 moment system is full rank — the DB² sharp-auxiliary route provably collapses (#389)

A machine-checked **refutation** (project tier-b: a dead end gets a countermodel, then stays
documented-refuted) of the tempting "DB² family" route to a sharp split-case Stepanov bound
`|R ∩ (R+c)| ≤ 4|R|^{2/3}`.

The route proposes an auxiliary `Ψ = ∑_{a<D, b<B} coef(a,b)·g_{a,b}` whose order-`M` vanishing at
the rep set is supposed to reduce (per a claimed "the `t`-power skeleton is inert under Hasse
derivatives") to few `r`-independent conditions, leaving a nonzero `coef` when `D·B² > 2D²`.
That is **false**: per `x`-layer the order-`M` moment conditions are governed by the matrix
`[C(t·b, k)]_{k,b<B}`, which is **nonsingular** (it is the transpose of the binomial matrix of
`det_choose_ne_zero` with `mᵦ = t·b`). Hence whenever `M ≥ B` the moment system has only the zero
solution — and the route needs `M ≈ ½t^{2/3} ≫ B ≈ t^{1/3}`, so the auxiliary collapses to `Ψ = 0`
and the Stepanov contradiction never fires.

`sv11_moment_forces_zero` records exactly this: the in-tree moment hypothesis `hmom`
(`∀ k < M, ∑_{b<B} coef(a,b)·C(t·b,k) = 0`) of `SV11RepMultiplicity.sv11_combination_rootMultiplicity_ge`
is unsatisfiable with a nonzero `coef` on any `x`-layer once `M ≥ B` and the `t·b` are distinct in
`F`. This strengthens `StepanovGenericInsufficiency.generic_stepanov_degree_ge` (the generic
dimension count cannot beat `r ≤ t`) from "generic fails" to "this specific moment route provably
fails". The genuine sharp bound (`GVRepBound`) stays an explicit open Prop — it needs a real
*joint-relation* rank deficiency (from `x^t = 1` **and** `(x−c)^t = 1` simultaneously) or the
`t`-power Wronskian degree-reduction, neither of which this route supplies.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Finset Matrix

namespace ProximityGap

variable {F : Type*} [Field F]

/-- **The per-layer moment matrix `[C(t·b, k)]_{k,b<B}` is nonsingular ⇒ the moment route forces
`coef = 0` when `M ≥ B`.** On any single `x`-layer `a`, the in-tree order-`M` moment conditions
`∀ k < M, ∑_{b<B} coef(a,b)·C(t·b,k) = 0` (with the `t·b` distinct in `F`) admit only the trivial
solution once `B ≤ M`. So the "DB² family" auxiliary `Ψ = ∑ coef·g_{a,b}` collapses to `Ψ = 0` at
its own parameters (`M ≈ ½t^{2/3} ≫ B ≈ t^{1/3}`); no Stepanov contradiction is produced. -/
theorem sv11_moment_forces_zero {B M : ℕ} (t a : ℕ) (coef : ℕ → ℕ → F)
    (hBM : B ≤ M)
    (hinj : Function.Injective (fun b : Fin B => ((t * (b : ℕ) : ℕ) : F)))
    (hmom : ∀ k, k < M → ∑ b ∈ Finset.range B, coef a b * (((t * b).choose k : ℕ) : F) = 0) :
    ∀ b, b < B → coef a b = 0 := by
  classical
  -- the kernel vector and the moment matrix
  set v : Fin B → F := fun b => coef a (b : ℕ) with hv
  set Mw : Matrix (Fin B) (Fin B) F :=
    Matrix.of (fun k b => ((Nat.choose (t * (b : ℕ)) (k : ℕ)) : F)) with hMw
  -- nonsingular: transpose of `det_choose_ne_zero`'s binomial matrix with `mᵦ = t·b`
  have hdet : Mw.det ≠ 0 := by
    have htr : Mw
        = (Matrix.of (fun b k : Fin B => ((Nat.choose (t * (b : ℕ)) (k : ℕ)) : F)))ᵀ := by
      ext k b; simp [hMw, Matrix.transpose_apply, Matrix.of_apply]
    rw [htr, Matrix.det_transpose]
    exact ProximityGap.BinomialDet.det_choose_ne_zero (fun b : Fin B => t * (b : ℕ)) hinj
  -- `v` is in the kernel: the first `B ≤ M` moment conditions say `Mw *ᵥ v = 0`
  have hker : Mw *ᵥ v = 0 := by
    funext k
    have hk : (k : ℕ) < M := lt_of_lt_of_le k.isLt hBM
    simp only [Matrix.mulVec, dotProduct, hMw, hv, Matrix.of_apply, Pi.zero_apply]
    rw [Fin.sum_univ_eq_sum_range
        (fun b => ((Nat.choose (t * b) (k : ℕ)) : F) * coef a b) B]
    rw [Finset.sum_congr rfl (fun b _ => mul_comm _ _)]
    exact hmom (k : ℕ) hk
  -- nonsingular ⇒ `v = 0` ⇒ `coef a b = 0` for every layer index `b < B`
  have hv0 : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hker
  intro b hb
  have hvb := congrFun hv0 ⟨b, hb⟩
  simpa [hv] using hvb

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.sv11_moment_forces_zero
