/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettUnion
import ArkLib.Data.CodingTheory.GMMDS.LovettReduction
import ArkLib.Data.CodingTheory.GMMDS.LovettVStarReduce
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Lovett's GM-MDS proof: Lemma 2.2 assembled (#389, layer 8)

With a **shared coordinate** `j` (every `vᵢ(j) ≥ 1`), independence of the *reduced* union
`P(k−1,V')` implies independence of `P(k,V)` (arXiv:1803.02523, Lemma 2.2): `vAbs_update_pred`
matches the index `Σᵢ Fin(k−|vᵢ|)` with `Σᵢ Fin((k−1)−|vᵢ'|)`, and
`pFam_family_indep_of_reduced` lifts by `(x−aⱼ)`.

`vAbs`, `pFam`, `pVanish` are kept locally opaque (via `single_le_vAbs` proved first) so the
dependent-`Σ` index defeq stays structural and does not diverge.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {m n : ℕ}

/-- A single coordinate is at most the weight (proved while `vAbs` is still reducible). -/
theorem single_le_vAbs (f : Fin n → ℕ) (j : Fin n) : f j ≤ vAbs f := by
  rw [vAbs]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

attribute [local irreducible] vAbs pFam pVanish

set_option maxHeartbeats 800000 in
/-- **Lemma 2.2 (assembled).**  Shared coordinate `j` + reduced-union independence at `k−1`
⟹ `P(k,V)` independence. -/
theorem pFamUnion_indep_of_reduced {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k)
    {j : Fin n} (hj : ∀ i, 1 ≤ V i j)
    (IH : LinearIndependent (MvPolynomial (Fin n) F)
      (pFamUnion (F := F) (fun i => Function.update (V i) j (V i j - 1)) (k - 1))) :
    LinearIndependent (MvPolynomial (Fin n) F) (pFamUnion (F := F) V k) := by
  classical
  have hcard : ∀ i, k - vAbs (V i)
      = (k - 1) - vAbs (Function.update (V i) j (V i j - 1)) := by
    intro i
    have hge : 1 ≤ vAbs (V i) := le_trans (hj i) (single_le_vAbs (V i) j)
    rw [vAbs_update_pred (V i) j (hj i)]; omega
  let e : (Σ i : Fin m, Fin (k - vAbs (V i)))
      ≃ (Σ i : Fin m, Fin ((k - 1) - vAbs (Function.update (V i) j (V i j - 1)))) :=
    Equiv.sigmaCongrRight (fun i => finCongr (hcard i))
  have hIH' := IH.comp e e.injective
  have heq : (pFamUnion (F := F) (fun i => Function.update (V i) j (V i j - 1)) (k - 1)) ∘ e
      = (fun p : Σ i : Fin m, Fin (k - vAbs (V i)) =>
          pFam (F := F) (Function.update (V p.1) j (V p.1 j - 1)) ((p.2 : ℕ))) := by
    funext p
    show pFamUnion (F := F) (fun i => Function.update (V i) j (V i j - 1)) (k - 1) (e p)
        = pFam (F := F) (Function.update (V p.1) j (V p.1 j - 1)) ((p.2 : ℕ))
    rw [pFamUnion]
    congr 1
  rw [heq] at hIH'
  -- inline `pFam_family_indep_of_reduced` to avoid a divergent cross-lemma unification:
  -- factor each `pFam (vᵢ) eᵢ = (x − aⱼ) · pFam (vᵢ − eⱼ) eᵢ` and lift the reduced family.
  have hgoaleq : pFamUnion (F := F) V k
      = (LinearMap.mulLeft (MvPolynomial (Fin n) F) (xSubA j))
        ∘ (fun p : Σ i : Fin m, Fin (k - vAbs (V i)) =>
            pFam (F := F) (Function.update (V p.1) j (V p.1 j - 1)) ((p.2 : ℕ))) := by
    funext p
    rw [pFamUnion, Function.comp_apply, LinearMap.mulLeft_apply, ← pFam_factor (hj p.1)]
  rw [hgoaleq]
  refine hIH'.map' _ (LinearMap.ker_eq_bot.mpr (fun x y h => ?_))
  simp only [LinearMap.mulLeft_apply] at h
  exact mul_left_cancel₀ (xSubA_monic (F := F) j).ne_zero h

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.pFamUnion_indep_of_reduced
