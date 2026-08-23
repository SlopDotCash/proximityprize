/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BCIKS20PigeonholeSupply
import ArkLib.ToMathlib.GSFactorData
import ArkLib.ToMathlib.BivariateDegreeToolkit

/-!
# Concrete §5 assembly — the Johnson side (Claim 5.7 residuals from the GS interpolant)

This is the last assembly layer on the **Claim-5.7 / graph-extraction** branch of the BCIKS20 §5
list-decoding agreement chain.  The upstream supply lemma `ProximityGap.claim57Residuals_of_johnson`
(`Claim57Supply.lean`) already reduces the `Claim57Residuals` bundle to genuine geometric /
Johnson-regime hypotheses, in particular the **Johnson counting inequality**

```
hcount : ∀ z, natWeightedDegree (eval_on_Z Q z) 1 k < m·#matchingCoords
```

(and its `⌈δ·n⌉`-nonmatching variant `m·(n − ⌈δ·n⌉)`).  This file closes **Step 4** of the
mission — the *Johnson arithmetic* — by deriving that per-`z` counting inequality from a **single,
`z`-independent** Johnson-budget hypothesis on the GS interpolant `Q`, namely

```
hJohnson : natWeightedDegree Q 1 k < m·(n − ⌈δ·n⌉).
```

The reduction is the genuine, kernel-clean algebra:

* `BivariateDegreeToolkit.natWeightedDegree_one_k_eval_on_Z_le` (PROVEN): specialising `Z ↦ z`
  never raises the `(1, k)`-weighted degree, i.e.
  `natWeightedDegree (eval_on_Z Q z) 1 k ≤ natWeightedDegree Q 1 k`.

So the `z`-independent budget transfers verbatim to every `z`.  `hJohnson` is exactly the BCIKS
Johnson-radius parameter inequality (Lemma 5.3: the weighted degree of the GS interpolant is below
the agreement budget `m·(#agreeing coordinates)`, and `δ`-closeness forces `#agreeing ≥ n − ⌈δn⌉`);
the `ModifiedGuruswami.Q_deg` field already bounds `natWeightedDegree Q 1 k` strictly below the real
`D_X`, and the Johnson regime is exactly `D_X ≤ m·(n − ⌈δn⌉)`, so `hJohnson` is the honest integer
form of that regime statement.  We keep `hJohnson` as the named §5 residual rather than re-deriving
the `D_X`-to-integer bridge (which lives in the uneditable `ModifiedGuruswami` field block).

Then `claim57Residuals_of_gsInterpolant` assembles the full `Claim57Residuals` bundle from the GS
interpolant `h_gs` together with the remaining genuine §5 inputs (`hx0`/`hsep`/`hlarge`/`hfactor`),
by feeding the derived per-`z` `hcount` into `claim57Residuals_of_natCeil_johnson`.

No `sorry`/`axiom`/`native_decide`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Claims 5.6–5.7, list-decoding agreement), Lemma 5.3 (Johnson-radius GS parameter bound).
-/

-- Documentation-heavy file (BCIKS §5 prose in the docstrings); the long-line style linter is
-- disabled locally, matching the sibling supply files.
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace ProximityGap

open Polynomial Polynomial.Bivariate NNReal Finset Function ProbabilityTheory Code Trivariate
open scoped BigOperators LinearCode

variable {F : Type} [Field F] [DecidableEq F] [Finite F]
variable {n : ℕ}
variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}

/-! ## Step 4 — the Johnson counting inequality from a single budget on the interpolant

The per-`z` counting inequality of `claim57Residuals_of_natCeil_johnson` is
`natWeightedDegree (eval_on_Z Q z) 1 k < m·(n − ⌈δn⌉)`.  Because `Z ↦ z` only shrinks the
`(1, k)`-weighted degree (`natWeightedDegree_one_k_eval_on_Z_le`, proven), a *single*
`z`-independent budget `natWeightedDegree Q 1 k < m·(n − ⌈δn⌉)` transfers to every `z`. -/

/-- **The Johnson counting inequality, derived (per `z`).**  From the `z`-independent Johnson budget
`natWeightedDegree Q 1 k < m·(n − ⌈δ·n⌉)` on the GS interpolant, the per-`z` counting inequality
`natWeightedDegree (eval_on_Z Q z) 1 k < m·(n − ⌈δ·n⌉)` follows, since `Z ↦ z` never raises the
`(1, k)`-weighted degree (`BivariateDegreeToolkit.natWeightedDegree_one_k_eval_on_Z_le`). -/
theorem hcount_natCeil_of_johnson_budget
    (hJohnson : Bivariate.natWeightedDegree Q 1 k < m * (n - ⌈δ * (n : ℚ)⌉₊))
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
    Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k <
      m * (n - ⌈δ * (n : ℚ)⌉₊) :=
  lt_of_le_of_lt
    (ArkLib.BivariateDegreeToolkit.natWeightedDegree_one_k_eval_on_Z_le Q z.1 k)
    hJohnson

/-! ## Step 2/5 (Johnson branch) — the Claim-5.7 residual bundle from the GS interpolant

Feeding the derived `hcount` into `claim57Residuals_of_natCeil_johnson` produces the full
`Claim57Residuals` bundle from the GS interpolant `h_gs` and the remaining genuine §5 inputs.  This
is the Johnson-branch counterpart of `GSFactorData.of_section5Inputs` (which produces the R/H
factorization bundle from the same interpolant on the keystone branch). -/

/-- **The Claim-5.7 residual bundle from the GS interpolant (Johnson regime).**

Produces `ProximityGap.Claim57Residuals k δ x₀ h_gs` from genuine §5 / Johnson-regime data:

* `h_gs` — the GS interpolant `ModifiedGuruswami` (Prop 5.5, satisfiable in regime via
  `modified_guruswami_has_a_solution`);
* `hx0`/`hsep` — the Claim-5.6 specialization side conditions;
* `hJohnson` — the **single Johnson-budget inequality** `natWeightedDegree Q 1 k < m·(n − ⌈δ·n⌉)`
  (the genuine Johnson-radius parameter condition; transferred to the per-`z` `hcount` via
  `hcount_natCeil_of_johnson_budget`);
* `hlarge` — the close-set largeness / degree-budget condition;
* `hfactor` — the legacy `pg_Rset ⟹ Eq-5.12 factorization list` bridge.

Every other field of `Claim57Residuals` is discharged by the in-tree bricks (the canonical matching
set makes `A`/`hA` automatic, `hS_nonempty` follows from `hlarge`). -/
@[reducible]
noncomputable def claim57Residuals_of_gsInterpolant
    [NeZero n] [DecidableEq (Polynomial F)] [DecidableEq (RatFunc F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hJohnson : Bivariate.natWeightedDegree Q 1 k < m * (n - ⌈δ * (n : ℚ)⌉₊))
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hfactor : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose) :
    Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs :=
  claim57Residuals_of_natCeil_johnson (F := F) (m := m) (n := n) (k := k)
    (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hx0 hsep
    (fun z => hcount_natCeil_of_johnson_budget (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) (δ := δ) hJohnson z)
    hlarge hfactor

/-! ## The matching `GSFactorData.Bundle` from the same interpolant (keystone branch head)

For the keystone branch the same GS interpolant produces the R/H factorization `Bundle`.  We
re-expose `GSFactorData.of_section5Inputs` here under a name that pairs with the Johnson
assembler above, so the top-level §5 concrete assembler can produce both branch heads from
one `h_gs`.  (This is a thin
re-export — `of_section5Inputs` is already PROVEN in `GSFactorData.lean`.) -/

noncomputable def gsFactorBundle_of_gsInterpolant
    [DecidableEq (RatFunc F)] [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q) :
    ArkLib.GSFactorData.Bundle (F := F) x₀ :=
  ArkLib.GSFactorData.of_section5Inputs (F := F) (n := n) (m := m) k x₀
    h_gs hx0 hsep hS_nonempty A hA hcount hlarge

/-! ## Paired §5 heads from one GS interpolant

The Johnson branch (`Claim57Residuals`) and keystone branch (`GSFactorData.Bundle`) are
produced from the same GS interpolant and specialization side conditions.  This paired
wrapper keeps the two heads
together for later top-level §5 assemblers. -/

/-- **Both concrete §5 heads from the same GS interpolant.**

Returns the Johnson graph-extraction residual bundle and the keystone `R/H` factorization bundle
from one `ModifiedGuruswami` witness.  The Johnson head uses the single `hJohnson` budget; the
keystone head keeps the explicit matching-set data required by `GSFactorData.of_section5Inputs`. -/
noncomputable def section5JohnsonHeads_of_gsInterpolant
    [NeZero n] [DecidableEq (RatFunc F)] [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hJohnson : Bivariate.natWeightedDegree Q 1 k < m * (n - ⌈δ * (n : ℚ)⌉₊))
    (hS_nonempty : (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).Nonempty)
    (A : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Finset (Fin n))
    (hA : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      ∀ i ∈ A z, (u₀ + z.1 • u₁) i =
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2).eval (ωs i))
    (hcount : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z.1) 1 k < m * (A z).card)
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hfactor : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose) :
    Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
        (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs ×
      ArkLib.GSFactorData.Bundle (F := F) x₀ :=
  ⟨claim57Residuals_of_gsInterpolant (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hx0 hsep hJohnson
      hlarge hfactor,
    gsFactorBundle_of_gsInterpolant (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hx0 hsep hS_nonempty A
      hA hcount hlarge⟩

end ProximityGap
