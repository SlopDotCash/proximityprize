/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._W14JacobiWindowMomentEquivalence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZW14MomentsDetermineWindowDischarge

/-!
# W14 integration bridge — the named open input is discharged IN W14'S OWN VOCABULARY (#466)

`Frontier/_W14JacobiWindowMomentEquivalence.lean` (lane file) named
`W14WindowMoment.MomentsDetermineWindow` as its open classical input and consumed it
explicitly (`hconv`).  `Frontier/_ZW14MomentsDetermineWindowDischarge.lean` proved the
identical statement (definitions copied verbatim) by walk-counting induction.  This bridge
machine-checks the definitional identity and **fires W14's own consumers with zero named
input left**:

> **`w14_momentsDetermineWindow_holds`** — `W14WindowMoment.MomentsDetermineWindow N K`
> holds for every `N`, `K` (the lane's named open input, discharged in its own vocabulary).
>
> **`w14_cornerAgree_iff_moments_agree_unconditional`** — W14's exact information-content
> identity (depth-`K` window ⟺ moments to order `2K+1`), now an unconditional theorem.
>
> **`w14_truncation_invariant_is_lowMoment_functional_unconditional`** — W14's SEAM-COLLAPSE
> verdict (every depth-`K` truncation invariant is a functional of the low moments alone),
> now an unconditional theorem.

Axiom-clean; no `sorry`, no `native_decide`, no new axioms.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.ZW14IntegrationBridge

open ArkLib.ProximityGap.Frontier

/-- **The W14 named open input, discharged in W14's own vocabulary.**  The two copies of the
definition are syntactically identical, so the discharge transfers by definitional equality. -/
theorem w14_momentsDetermineWindow_holds (N K : ℕ) :
    W14WindowMoment.MomentsDetermineWindow N K := by
  intro A A' htri htri' hsym hsym' hpos hpos' i0 h0 hmom
  exact ZW14MomentsDischarge.momentsDetermineWindow_holds N K A A'
    htri htri' hsym hsym' hpos hpos' i0 h0 hmom

/-- W14's exact information-content identity, unconditional: the depth-`K` Jacobi window and
the moment vector to order `2K+1` are mutually determined. -/
theorem w14_cornerAgree_iff_moments_agree_unconditional
    {N K : ℕ}
    {A A' : Matrix (Fin N) (Fin N) ℝ}
    (htri : W14WindowMoment.IsTridiagonal A) (htri' : W14WindowMoment.IsTridiagonal A')
    (hsym : A.IsSymm) (hsym' : A'.IsSymm)
    (hpos : W14WindowMoment.PosSubdiag A) (hpos' : W14WindowMoment.PosSubdiag A')
    {i0 : Fin N} (h0 : (i0 : ℕ) = 0) :
    W14WindowMoment.CornerAgree A A' K ↔
      (∀ r : ℕ, r ≤ 2 * K + 1 → (A ^ r) i0 i0 = (A' ^ r) i0 i0) :=
  W14WindowMoment.cornerAgree_iff_moments_agree
    (w14_momentsDetermineWindow_holds N K) htri htri' hsym hsym' hpos hpos' h0

/-- W14's seam-collapse verdict, unconditional: every corner-block functional of the Jacobi
data at depth `K` is a functional of the moments `m_0, …, m_{2K+1}` alone. -/
theorem w14_truncation_invariant_is_lowMoment_functional_unconditional
    {N K : ℕ}
    {X : Type} (Φ : Matrix (Fin N) (Fin N) ℝ → X)
    (hΦ : ∀ A A' : Matrix (Fin N) (Fin N) ℝ, W14WindowMoment.CornerAgree A A' K → Φ A = Φ A')
    {A A' : Matrix (Fin N) (Fin N) ℝ}
    (htri : W14WindowMoment.IsTridiagonal A) (htri' : W14WindowMoment.IsTridiagonal A')
    (hsym : A.IsSymm) (hsym' : A'.IsSymm)
    (hpos : W14WindowMoment.PosSubdiag A) (hpos' : W14WindowMoment.PosSubdiag A')
    {i0 : Fin N} (h0 : (i0 : ℕ) = 0)
    (hmom : ∀ r : ℕ, r ≤ 2 * K + 1 → (A ^ r) i0 i0 = (A' ^ r) i0 i0) :
    Φ A = Φ A' :=
  W14WindowMoment.truncation_invariant_is_lowMoment_functional
    (w14_momentsDetermineWindow_holds N K) Φ hΦ htri htri' hsym hsym' hpos hpos' h0 hmom

end ArkLib.ProximityGap.Frontier.ZW14IntegrationBridge

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.ZW14IntegrationBridge.w14_momentsDetermineWindow_holds
#print axioms ArkLib.ProximityGap.Frontier.ZW14IntegrationBridge.w14_cornerAgree_iff_moments_agree_unconditional
#print axioms ArkLib.ProximityGap.Frontier.ZW14IntegrationBridge.w14_truncation_invariant_is_lowMoment_functional_unconditional
