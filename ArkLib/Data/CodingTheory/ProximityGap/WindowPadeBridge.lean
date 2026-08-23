/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowCrossWitness

/-!
# The Padé bridge: every bad scalar yields a factored witness identity (#371)

The consumer-side bridge from `mcaEvent` to the cross-witness/Padé interface:
for a genuinely rational coprime stack, every bad scalar `γ` produces a factored
identity

  `Z_S · h = ℓ₁R₀ + γ·ℓ₀R₁ − P·ℓ₀ℓ₁`,   `|S| ≥ n − w`,  `deg P < k`,
  `deg h + |S| ≤ 2w + k − 1`,

(`Z_S` the witness-set vanishing polynomial, `h` the kernel cofactor).  Feeding two
such identities to `cross_witness_dvd`/`witness_fraction_unique` runs the entire
Padé machinery on actual MCA events: per scalar the reduced fraction `h/Z_T` is
canonical, and badness is the D-splitness of the canonical reconstruction
denominator (`probe_pade_reconstruction.py`, validated exactly).
-/

open Finset Polynomial
open scoped NNReal

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section Bridge

variable (dom : Fin n ↪ F) {k w : ℕ}
variable {ℓ₀ ℓ₁ R₀ R₁ : F[X]}

open Classical in
/-- **The Padé bridge**: every `mcaEvent`-bad scalar of a genuine coprime stack
factors through a witness identity ready for the cross-witness laws. -/
theorem mcaEvent_factored (hk : 1 ≤ k)
    (hℓ₀d : ℓ₀.natDegree ≤ w) (hℓ₁d : ℓ₁.natDegree ≤ w)
    (hR₀d : R₀.natDegree ≤ w + k - 1) (hR₁d : R₁.natDegree ≤ w + k - 1)
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0)
    (hcop : IsCoprime ℓ₀ ℓ₁) (hgen₀ : ¬ ℓ₀ ∣ R₀)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) {γ : F}
    (hbad : mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => R₀.eval (dom i) / ℓ₀.eval (dom i))
      (fun i => R₁.eval (dom i) / ℓ₁.eval (dom i)) γ) :
    ∃ (S : Finset (Fin n)) (h P : F[X]),
      n - w ≤ S.card ∧ P.natDegree ≤ k - 1 ∧
      h.natDegree + S.card ≤ 2 * w + k - 1 ∧
      (S.prod fun i => X - C (dom i)) * h
        = ℓ₁ * R₀ + C γ * (ℓ₀ * R₁) - P * (ℓ₀ * ℓ₁) := by
  obtain ⟨P, hPd, hge, hle⟩ := window_explainer dom hk hℓ₀d hℓ₁d hR₀d hR₁d
    hℓ₀v hℓ₁v hcop hgen₀ hδn hbad
  set S : Finset (Fin n) := w2Agr dom ℓ₀ ℓ₁ R₀ R₁ P γ with hS
  set M : F[X] := w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ with hM
  have hM0 : M ≠ 0 := w2Residual_ne_zero hcop hgen₀
  have hvan : ∀ i ∈ S, M.eval (dom i) = 0 := by
    intro i hi
    rw [hS, w2Agr, Finset.mem_filter] at hi
    exact hi.2
  have hdvd : (S.prod fun i => X - C (dom i)) ∣ M :=
    vanishing_prod_dvd dom hM0 hvan
  set ZS : F[X] := S.prod fun i => X - C (dom i) with hZS
  have hmonic : ZS.Monic := by
    rw [hZS]
    exact monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (dom i))
  have hfact : ZS * (M /ₘ ZS) = M := by
    have hmod : M %ₘ ZS = 0 := (modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd
    have hsum := modByMonic_add_div M ZS
    rw [hmod, zero_add] at hsum
    exact hsum
  refine ⟨S, M /ₘ ZS, P, hge, hPd, ?_, ?_⟩
  · -- degree bookkeeping: deg h + |S| = deg M ≤ 2w + k − 1
    have hZSdeg : ZS.natDegree = S.card := by
      rw [hZS]
      rw [natDegree_prod _ _ (fun i _ => X_sub_C_ne_zero (dom i))]
      simp [natDegree_X_sub_C]
    have hhne : M /ₘ ZS ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hfact
      exact hM0 hfact.symm
    have hZSne : ZS ≠ 0 := hmonic.ne_zero
    have hdeg : ZS.natDegree + (M /ₘ ZS).natDegree = M.natDegree := by
      rw [← natDegree_mul hZSne hhne, hfact]
    have hMdeg : M.natDegree ≤ 2 * w + k - 1 :=
      w2Residual_natDegree_le_general hk hℓ₀d hℓ₁d hR₀d hR₁d hPd
    omega
  · rw [hfact, hM, w2Residual]

end Bridge

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.mcaEvent_factored
