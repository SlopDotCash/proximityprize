/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSPerScalarCapture
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# The mcaEvent → GS bridge — bad scalars decode into the specialized interpolant (#302)

The first half of the `PerPairFactorData.hcover` production: every `mcaEvent`-bad scalar
`γ` of a word pair carries a decoded codeword polynomial that (i) roots the specialized
generic GS interpolant `Q₀(γ)` (via `scalar_close_codeword_isRoot`) and (ii) retains the
event's witness data in exactly the per-scalar **capture shape** consumed downstream
(`Claim510Capture.affineCaptured_of_pencil_proximity`): a large set `S` on which the
decoded polynomial's evaluations equal the fold, with no joint agreement.

The second half (factor assignment with the content-term junk index) layers
`exists_specialized_factor_assignment` on this bridge.

## Main results

* `mcaEvent_decoded_data` — **the bridge**: a bad scalar yields a decoded codeword rooting
  `Q₀(γ)` together with the capture-shaped witness data.

## References

* [BCIKS20] ePrint 2020/654 — §5.2.5 (Step 2); [Hab25] ePrint 2025/2110.
-/

open Polynomial Polynomial.Bivariate
open _root_.ProximityGap
open scoped NNReal

set_option linter.unusedSectionVars false

namespace GuruswamiSudan.OverRatFunc

variable {F : Type} [Field F]

attribute [local instance] Classical.propDecidable

/-- **The `mcaEvent` → GS bridge.**  Every `mcaEvent`-bad scalar `γ` (at proximity `δ`
below the GS Johnson radius) carries a decoded Reed–Solomon codeword that roots the
specialized interpolant `Q₀(γ)`, together with the event's witness set in the per-scalar
capture shape: `S` large, the decoded polynomial equals the fold on `S`, and no pair of
codewords jointly agrees on `S`. -/
theorem mcaEvent_decoded_data {n k m : ℕ}
    (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain ωs) (genericFold f₀ f₁) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (γ : F)
    (hγQ : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0)
    (hk : k + 1 ≤ n) (hm : 1 ≤ m) (hn : 0 < n)
    (δ : ℝ≥0) (hδ1 : δ < 1) (hδj : (δ : ℝ) < gs_johnson k n m)
    (hev : mcaEvent (ReedSolomon.code ωs k : Set (Fin n → F)) δ f₀ f₁ γ) :
    ∃ p : ReedSolomon.code ωs k,
      (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))).IsRoot
        (ReedSolomon.codewordToPoly p) ∧
      ∃ S : Finset (Fin n), ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card (Fin n)) ∧
        (∀ i ∈ S, (ReedSolomon.codewordToPoly p).eval (ωs i) = f₀ i + γ * f₁ i) ∧
        ¬ pairJointAgreesOn (ReedSolomon.code ωs k : Set (Fin n → F)) S f₀ f₁ := by
  classical
  obtain ⟨S, hScard, ⟨w, hwC, hwS⟩, hnj⟩ := hev
  set p : ReedSolomon.code ωs k := ⟨w, hwC⟩ with hp
  -- node evaluations of the interpolant recover the codeword
  have hxinj : Set.InjOn ωs.toFun (Finset.univ : Finset (Fin n)) :=
    fun a _ b _ h => ωs.injective h
  have heval : ∀ i : Fin n, (ReedSolomon.codewordToPoly p).eval (ωs i) = w i := by
    intro i
    rw [ReedSolomon.codewordToPoly]
    exact Lagrange.eval_interpolate_at_node _ hxinj (Finset.mem_univ i)
  -- the fold agreement on `S`, in eval form
  have hSagree : ∀ i ∈ S, (ReedSolomon.codewordToPoly p).eval (ωs i)
      = f₀ i + γ * f₁ i := by
    intro i hi
    rw [heval i, hwS i hi, smul_eq_mul]
  -- the Hamming-distance bound from the witness set
  have hdisagree : Finset.univ.filter
      (fun i => (fun j => f₀ j + γ * f₁ j) i
        ≠ (fun j => (ReedSolomon.codewordToPoly p).eval (ωs j)) i) ⊆ Sᶜ := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_compl]
    intro hiS
    exact hi.2 (by simp only []; rw [hSagree i hiS])
  have hdist_nat : hammingDist (fun j => f₀ j + γ * f₁ j)
      (fun j => (ReedSolomon.codewordToPoly p).eval (ωs j)) ≤ n - S.card := by
    calc hammingDist _ _
        ≤ Sᶜ.card := Finset.card_le_card hdisagree
      _ = n - S.card := by rw [Finset.card_compl, Fintype.card_fin]
  -- the real-arithmetic Johnson-radius bound
  have hScard_real : ((1 : ℝ) - (δ : ℝ)) * n ≤ (S.card : ℝ) := by
    have h := hScard
    rw [Fintype.card_fin] at h
    have h2 : ((1 - δ : ℝ≥0) : ℝ) * (n : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast h
    rwa [NNReal.coe_sub (le_of_lt hδ1), NNReal.coe_one] at h2
  have hdist_real : (hammingDist (fun j => f₀ j + γ * f₁ j)
      (fun j => (ReedSolomon.codewordToPoly p).eval (ωs j)) : ℝ) / n
      < gs_johnson k n m := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : (hammingDist (fun j => f₀ j + γ * f₁ j)
        (fun j => (ReedSolomon.codewordToPoly p).eval (ωs j)) : ℝ) ≤ (n : ℝ) - S.card := by
      have := hdist_nat
      have hSn : S.card ≤ n := by
        calc S.card ≤ Fintype.card (Fin n) := S.card_le_univ.trans (by simp)
          _ = n := Fintype.card_fin n
      calc (hammingDist _ _ : ℝ) ≤ ((n - S.card : ℕ) : ℝ) := by exact_mod_cast this
        _ = (n : ℝ) - S.card := by
            rw [Nat.cast_sub hSn]
    have h2 : (n : ℝ) - S.card ≤ (δ : ℝ) * n := by
      have := hScard_real
      nlinarith
    calc (hammingDist _ _ : ℝ) / n ≤ ((δ : ℝ) * n) / n := by
          exact div_le_div_of_nonneg_right (le_trans h1 h2) hnR.le
      _ = (δ : ℝ) := by field_simp
      _ < gs_johnson k n m := hδj
  -- the GS root via per-scalar capture
  refine ⟨p, scalar_close_codeword_isRoot ωs f₀ f₁ hQ hrep γ hγQ hk hm p hdist_real,
    S, by rw [Fintype.card_fin]; exact (by rwa [Fintype.card_fin] at hScard),
    hSagree, hnj⟩

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit -/
#print axioms GuruswamiSudan.OverRatFunc.mcaEvent_decoded_data
