/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.MpFinSupply

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries

namespace ArkLib.MpFinSupply

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable {x₀ : F} {R : F[X][X][Y]} {hHyp : Hypotheses x₀ R H}
variable {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H}

/-- **`BridgeData` from the denominator-free (multiplied-out) `α_t`-identity reading.** The
supplier-friendly form: instead of the division identity
`coeff t aβ = π_z(betaRec t)/(w^a·x^e)`, accept the equivalent product identity
`coeff t aβ · (w^a·x^e) = π_z(betaRec t)` (no field division on the supplier side; the two are
equivalent since `w, x ≠ 0`). -/
noncomputable def bridgeData_of_mul_form {t : ℕ} {z : F} {root : rationalRoot (H_tilde' H) z}
    {aβ aP : PowerSeries F} (w x : F) (a e : ℕ)
    (hαβ' : PowerSeries.coeff t aβ * (w ^ a * x ^ e)
      = (π_z z root) (betaRec x₀ R H hHyp Bcoeff t))
    (hw : w ≠ 0) (hx : x ≠ 0)
    (haP_coeff : PowerSeries.coeff t aP = 0) :
    BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
      t z root aβ aP where
  w := w
  x := x
  a := a
  e := e
  hαβ := by
    have hwx : w ^ a * x ^ e ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hw) (pow_ne_zero _ hx)
    exact (eq_div_iff hwx).mpr hαβ'
  hw := hw
  hx := hx
  haP_coeff := haP_coeff

end ArkLib.MpFinSupply

#print axioms ArkLib.MpFinSupply.bridgeData_of_mul_form
