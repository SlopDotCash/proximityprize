/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.Bridge2BGKS20

/-!
# BGKS20 T5.4 — "all but one scalar" producer for `NearCertainBadLine`

The BGKS20 characteristic-2 construction (Lemma 3.3) is, by its own docstring, a stack
`u = (u₀, u₁)` that is **not** jointly `δ_int`-close to the code `C`, yet whose affine line
`u₀ + γ·u₁` is `δ_fld`-close to `C` for **all but one** scalar `γ ∈ F`. The existing bridge API
(`ArkLib/ToMathlib/Bridge2BGKS20.lean`, `ArkLib/ToMathlib/NearCertainBadLineProof.lean`) only
exposes the *already-counted* `|F| - 1 ≤ |Γ|` form, or the special case where the whole line lands
inside `C` with `Γ = univ`. Neither matches the literal "close for all but one scalar" shape that
the external construction outputs.

This file adds that missing producer:

* `nearCertainBadLine_of_allButOne` — from a stack `u` not jointly `δ_int`-close, plus a single bad
  scalar `γ_bad : F` such that **every** `γ ≠ γ_bad` makes the line `u₀ + γ·u₁` be `δ_fld`-close to
  `C`, assemble a `Bridge.NearCertainBadLine`. The good set is taken to be `Finset.univ.erase γ_bad`,
  whose cardinality is exactly `|F| - 1`, discharging the `(|F| : ℝ) - 1 ≤ |Γ|` count with no slack.
* `epsCA_ge_one_sub_inv_of_allButOne` — the T5.4 endpoint, composing the producer with the proven
  separation bridge `epsCA_separation_bridge_of_residual` to land
  `ε_ca(C, δ_fld, δ_int) ≥ 1 - 1/|F|`.

## What this does *not* close

This is pure `Finset`-cardinality + good-set glue around the already-proven separation bridge. It
does **not** manufacture the BGKS20 characteristic-2 *bad stack* itself — exhibiting a concrete `u`
whose line is genuinely `δ_fld`-close for all but one scalar while being not jointly close is the
external geometric content of BGKS20 Lemma 3.3, and remains the open #22 residual. This file reduces
the residual to *exactly* that single-bad-scalar witness, with the counting fully discharged.

## References
* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*, 2026.
  Theorem 5.4.
* [BGKS20] Ben-Sasson, Goldreich, Kopparty, Saraf. *Bounds on the List Decodability of Reed-Solomon
  Codes*, 2020. Lemma 3.3.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory.Bridge

open scoped NNReal BigOperators
open ProximityGap Code

-- `AllButOne` is a *namespace* (not a plain section) so these declarations land at
-- `CodingTheory.Bridge.AllButOne.*`. This avoids a fully-qualified-name collision with the
-- specialized (alphabet `A := F`) `nearCertainBadLine_of_allButOne` /
-- `epsCA_ge_one_sub_inv_of_allButOne` in `NearCertainBadLineProof.lean`; both files are pulled
-- into the `ArkLib.lean` umbrella, where duplicate FQNs are a hard error. This file's versions are
-- the more general arbitrary-alphabet `A` form.
namespace AllButOne

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Cardinality of the "all but one scalar" good set.**
Erasing a single scalar `γ_bad` from `Finset.univ` over a finite field `F` leaves exactly
`|F| - 1` scalars, so the real-valued count `(|F| : ℝ) - 1 ≤ (univ.erase γ_bad).card` holds with no
slack. (`Fintype.card F ≥ 1` makes the `ℕ`-subtraction agree with the `ℝ`-subtraction.) -/
theorem card_univ_erase_ge (γ_bad : F) :
    (Fintype.card F : ℝ) - 1 ≤ ((Finset.univ.erase γ_bad).card : ℝ) := by
  classical
  have hmem : γ_bad ∈ (Finset.univ : Finset F) := Finset.mem_univ γ_bad
  have hcard : (Finset.univ.erase γ_bad).card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_univ]
  rw [hcard]
  have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
  -- `((|F| - 1 : ℕ) : ℝ) = (|F| : ℝ) - 1` since `1 ≤ |F|`.
  rw [Nat.cast_sub hpos, Nat.cast_one]

/-- **"All but one scalar" producer (BGKS20 line-witness shape).**
Given a stack `u` that is **not** jointly `δ_int`-close to `C`, together with a single bad scalar
`γ_bad : F` such that **every** other scalar `γ ≠ γ_bad` makes the line `u 0 + γ • u 1` be
`δ_fld`-close to `C`, the code `C` admits a `NearCertainBadLine`. The good set is
`Finset.univ.erase γ_bad`, whose cardinality `|F| - 1` exactly meets the required count. -/
theorem nearCertainBadLine_of_allButOne
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (hjp : ¬ jointProximity (C := C) (u := u) δ_int)
    (γ_bad : F)
    (hgood : ∀ γ : F, γ ≠ γ_bad → δᵣ(u 0 + γ • u 1, C) ≤ δ_fld) :
    NearCertainBadLine (F := F) C δ_fld δ_int := by
  classical
  refine ⟨u, hjp, Finset.univ.erase γ_bad, ?_, card_univ_erase_ge (F := F) γ_bad⟩
  intro γ hγ
  -- Membership in `univ.erase γ_bad` says exactly `γ ≠ γ_bad`.
  exact hgood γ (Finset.ne_of_mem_erase hγ)

/-- **T5.4 endpoint from the "all but one scalar" producer.**
Under the hypotheses of `nearCertainBadLine_of_allButOne`, the correlated-agreement error of `C`
satisfies the BGKS20 separation lower bound
`ε_ca(C, δ_fld, δ_int) ≥ 1 - 1/|F|`. -/
theorem epsCA_ge_one_sub_inv_of_allButOne
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (hjp : ¬ jointProximity (C := C) (u := u) δ_int)
    (γ_bad : F)
    (hgood : ∀ γ : F, γ ≠ γ_bad → δᵣ(u 0 + γ • u 1, C) ≤ δ_fld) :
    ENNReal.ofReal (1 - 1 / Fintype.card F) ≤ epsCA (F := F) C δ_fld δ_int :=
  epsCA_separation_bridge_of_residual (F := F) C δ_fld δ_int
    (nearCertainBadLine_of_allButOne C δ_fld δ_int u hjp γ_bad hgood)

end AllButOne

end CodingTheory.Bridge

/-! ### Axiom audit (issue #22 BGKS20 all-but-one producer surface) -/

#print axioms CodingTheory.Bridge.AllButOne.card_univ_erase_ge
#print axioms CodingTheory.Bridge.AllButOne.nearCertainBadLine_of_allButOne
#print axioms CodingTheory.Bridge.AllButOne.epsCA_ge_one_sub_inv_of_allButOne
