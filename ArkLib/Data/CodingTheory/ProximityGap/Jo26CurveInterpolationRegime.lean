/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GG25MarkedCurve
import Mathlib.LinearAlgebra.Lagrange

/-!
# [Jo26] Lemma 5.2 — the interpolation (small-witness) regime (issue #334, K5, brick T2a)

For `b ≤ ℓ + 1`, marked curve decodability is **free**, independent of the distance
parameter: given any specified seed set `A₀` of size `a ≥ b`, choose `b` of its seeds and run
Lagrange interpolation through the codeword values there.  The interpolating curve has degree
`≤ b − 1 ≤ ℓ`, and its vector coefficients are `F`-linear combinations of the codeword values
`f α`, hence lie in the code whenever the code is `F`-linear (a submodule).

* `lagrangeCurve` — the coefficient stack `cⱼ := ∑_{α ∈ B} coeff j (basisₐ) • f α`;
* `lagrangeCurve_mem` — the coefficients lie in the submodule;
* `lagrangeCurve_eval` — the curve passes through `f β` for every `β ∈ B` (sum exchange +
  `Polynomial.eval_eq_sum_range'` at `natDegree = #B − 1 < ℓ + 1` +
  `Lagrange.eval_basis_self`/`eval_basis_of_ne`);
* `markedCurveDecodable_interpolation` — **[Jo26] Lemma 5.2**: every `F`-submodule code is
  marked `(ℓ, δ, a, b)`-curve-decodable whenever `b ≤ ℓ + 1` and `b ≤ a`, for every `δ`;
* `curveDecodable_interpolation` — the unmarked corollary via `CurveDecodable.of_marked`.

[Jo26] Remark 5.3: the nontrivial regime for applications is `b > ℓ + 1`; this brick pins the
boundary.  The remaining T2 legs (Lemma 5.4 non-covering + the Theorem 5.5 converse) and the
T3 covering transfer (Theorem 5.7) are follow-ups; nothing here claims them.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset Code Polynomial
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The Lagrange coefficient stack through the values of `f` on `B`: the `j`-th curve
coefficient is `∑_{α ∈ B} (coeff j of the Lagrange basis polynomial at α) • f α`. -/
noncomputable def lagrangeCurve (B : Finset F) (f : F → ι → A) (j : ℕ) : ι → A :=
  fun i => ∑ α ∈ B, (Lagrange.basis B id α).coeff j • f α i

/-- The Lagrange curve coefficients lie in any `F`-submodule containing the values. -/
theorem lagrangeCurve_mem (M : Submodule F (ι → A)) {B : Finset F} {f : F → ι → A}
    (hf : ∀ α, f α ∈ M) (j : ℕ) :
    lagrangeCurve B f j ∈ M := by
  have h : lagrangeCurve B f j = ∑ α ∈ B, (Lagrange.basis B id α).coeff j • f α := by
    funext i
    rw [Finset.sum_apply]
    rfl
  rw [h]
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (hf α)

/-- **The interpolation identity.** For `β ∈ B` with `#B ≤ ℓ + 1`, the degree-`≤ ℓ` curve
with the Lagrange coefficient stack passes through `f β`. -/
theorem lagrangeCurve_eval {B : Finset F} {f : F → ι → A} {ℓ : ℕ}
    (hBl : B.card ≤ ℓ + 1) {β : F} (hβ : β ∈ B) (i : ι) :
    (∑ j : Fin (ℓ + 1), β ^ (j : ℕ) • lagrangeCurve B f (j : ℕ) i) = f β i := by
  classical
  have hinj : Set.InjOn (id : F → F) B := fun _ _ _ _ h => h
  calc (∑ j : Fin (ℓ + 1), β ^ (j : ℕ) • lagrangeCurve B f (j : ℕ) i)
      = ∑ j : Fin (ℓ + 1), ∑ α ∈ B,
          ((Lagrange.basis B id α).coeff (j : ℕ) * β ^ (j : ℕ)) • f α i := by
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold lagrangeCurve
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [smul_smul, mul_comm]
    _ = ∑ α ∈ B, ∑ j : Fin (ℓ + 1),
          ((Lagrange.basis B id α).coeff (j : ℕ) * β ^ (j : ℕ)) • f α i :=
        Finset.sum_comm
    _ = ∑ α ∈ B, ((Lagrange.basis B id α).eval β) • f α i := by
        refine Finset.sum_congr rfl fun α hα => ?_
        rw [← Finset.sum_smul]
        congr 1
        have hpos : 0 < B.card := Finset.card_pos.mpr ⟨α, hα⟩
        have hdeg : (Lagrange.basis B id α).natDegree < ℓ + 1 := by
          rw [Lagrange.natDegree_basis hinj hα]
          omega
        rw [eval_eq_sum_range' hdeg β]
        exact (Fin.sum_univ_eq_sum_range
          (fun k => (Lagrange.basis B id α).coeff k * β ^ k) (ℓ + 1))
    _ = f β i := by
        rw [Finset.sum_eq_single β
          (fun α hα hne => by
            rw [show ((Lagrange.basis B id α).eval β)
                = ((Lagrange.basis B id α).eval (id β)) from rfl,
              Lagrange.eval_basis_of_ne hne hβ, zero_smul])
          (fun h => absurd hβ h)]
        rw [show ((Lagrange.basis B id β).eval β)
            = ((Lagrange.basis B id β).eval (id β)) from rfl,
          Lagrange.eval_basis_self hinj hβ, one_smul]

/-- **[Jo26] Lemma 5.2 (the small-witness regime).** Every `F`-submodule code is marked
`(ℓ, δ, a, b)`-curve-decodable whenever `b ≤ ℓ + 1` and `b ≤ a`, for every `δ`: Lagrange
interpolation through any `b` of the specified seeds produces the witness curve, with
coefficients in the code by linearity.  The distance hypothesis is not used. -/
theorem markedCurveDecodable_interpolation (M : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℝ≥0)
    {a b : ℕ} (hbl : b ≤ ℓ + 1) (hab : b ≤ a) :
    MarkedCurveDecodable (F := F) (M : Set (ι → A)) ℓ δ a b := by
  intro u f hf A₀ hcard _hdist
  obtain ⟨B, hBsub, hBcard⟩ :=
    Finset.exists_subset_card_eq (le_trans hab (le_of_eq hcard.symm))
  refine ⟨fun j => lagrangeCurve B f (j : ℕ), fun j => lagrangeCurve_mem M hf _, ?_⟩
  calc b = B.card := hBcard.symm
    _ ≤ _ := Finset.card_le_card fun β hβ => Finset.mem_filter.mpr
        ⟨hBsub hβ,
         _root_.funext fun i => (lagrangeCurve_eval (hBcard ▸ hbl) hβ i).symm⟩

/-- The unmarked corollary of [Jo26] Lemma 5.2, via the easy direction of Theorem 5.5. -/
theorem curveDecodable_interpolation (M : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℝ≥0)
    {a b : ℕ} (hbl : b ≤ ℓ + 1) (hab : b ≤ a) :
    CurveDecodable (F := F) (M : Set (ι → A)) ℓ δ a b :=
  curveDecodable_of_marked (markedCurveDecodable_interpolation M ℓ δ hbl hab)

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.lagrangeCurve_mem
#print axioms ProximityGap.lagrangeCurve_eval
#print axioms ProximityGap.markedCurveDecodable_interpolation
#print axioms ProximityGap.curveDecodable_interpolation
