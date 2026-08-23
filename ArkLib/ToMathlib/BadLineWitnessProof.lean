/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.Bridge2BCHKS25

/-!
# BCHKS25 T5.2: assembling `BadLineWitness` from the affine-shift interpolation output

This file is the *constructor* layer above `ArkLib.ToMathlib.Bridge2BCHKS25`. The bridge file
proves the **consumer** direction (a `Bridge.BadLineWitness` discharges the `hBadLine` residual
`ε_ca ≥ 1/(2n)`); the missing direction for ABF26 Theorem 5.2 [BCHKS25 Theorem 1.9] is the
**producer**: building such a witness from the data BCHKS25's affine-shift interpolation outputs.

## What the BCHKS25 interpolation produces (its genuinely-external geometric core)

From `|F|`-many close RS codewords, BCHKS25's counting argument exhibits, for the bad combining
stack `(u₀, u₁)`:

* `hjp` — the stack is *not* jointly `δ_int`-close;
* a finite set `Γ` of "good" combiners `γ` with line `u₀ + γ • u₁` being `δ_fld`-close to `C`;
* a *count* on `Γ`: a `≥ 1/(2n)` fraction of all scalars are good.

The count is the substantive output. It is naturally phrased two ways, both handled here:

* a **rational/real** lower bound `(|F| : ℝ) / (2n) ≤ Γ.card` (the affine-shift fraction), or
* the integral form `|F| ≤ 2n · Γ.card` already used inside `BadLineWitness`.

## What is proven here (structural, `sorry`-free, axiom-clean)

* `badLineCount_real_iff_nat` — the count-arithmetic glue: `(|F| : ℝ) ≤ 2n · Γ.card`
  is exactly the `BadLineWitness` card hypothesis, with the `1/(2n)`-fraction phrasing
  `(|F| : ℝ)/(2n) ≤ Γ.card` as a convenient equivalent.
* `badLineWitness_of_interpolationData` — **the producer**: from the three explicit outputs of
  BCHKS25's interpolation (stack `u`, non-joint-proximity `hjp`, good-combiner set `Γ` with the
  fraction count) assemble a `Bridge.BadLineWitness`. This is the assembly the consumer side of
  the bridge has been waiting for; the only remaining obligation is BCHKS25's interpolation
  *count* itself.
* `badLineWitness_of_smallField` — a **fully in-tree** corollary requiring *no* external count:
  when the field is small relative to the block size (`|F| ≤ 2n`), a *single* good combiner
  already meets the `BadLineWitness` cardinality bound, so any non-jointly-close stack with one
  `δ_fld`-close line is a witness. (BCHKS25's interpolation count is the hard part precisely
  because it must beat the *large*-field regime.)
* `provBadLine_of_interpolation` — packages the producer as the `P → BadLineWitness` shape
  consumed by `Bridge.hBadLine_of_provBadLine`, so a BCHKS25 interpolation count for RS plugs
  straight into `rs_epsCA_small_implies_lambda_lt_F_bchks25_of_badLineWitness`.

## What this file still does *not* close

It does **not** manufacture the interpolation count `(|F| : ℝ)/(2n) ≤ Γ.card` from `|F|` close
RS codewords — that is BCHKS25's RS-specific affine-shift counting (Theorem 1.9), which is not
derivable from the in-tree `epsCA`/`Lambda`/`ReedSolomon` API. This file reduces the residual to
*exactly* that one count, with all surrounding assembly and arithmetic discharged.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Theorem 5.2.
* [BCHKS25] Theorem 1.9.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory.Bridge

open scoped NNReal BigOperators
open ProximityGap Code

section BadLineConstruction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Count-arithmetic glue.** The `BadLineWitness` cardinality hypothesis
`(|F| : ℝ) ≤ 2n · Γ.card` is equivalent to the affine-shift *fraction* phrasing
`(|F| : ℝ) / (2n) ≤ Γ.card`. This lets a BCHKS25 interpolation count, naturally stated as a
fraction of good scalars, feed `BadLineWitness` directly. -/
theorem badLineCount_real_iff_nat (m : ℕ) :
    (Fintype.card F : ℝ) / (2 * Fintype.card ι) ≤ (m : ℝ)
      ↔ (Fintype.card F : ℝ) ≤ (2 * Fintype.card ι) * m := by
  have hn : (0 : ℝ) < 2 * Fintype.card ι := by
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    linarith
  rw [div_le_iff₀ hn, mul_comm]

/-- **The BCHKS25 producer (assembly).** Given the explicit output of BCHKS25's affine-shift
interpolation — a combining stack `u` that is not jointly `δ_int`-close, a finite set `Γ` of
good combiners (each making the line `u 0 + γ • u 1` be `δ_fld`-close to `C`), and the
interpolation *fraction* count `(|F| : ℝ)/(2n) ≤ Γ.card` — produce a `Bridge.BadLineWitness`.

Composing with `epsCA_badLine_bridge_of_residual` (already in `Bridge2BCHKS25`) discharges the
`hBadLine` residual `ε_ca ≥ 1/(2n)`. The only remaining obligation is the interpolation count
itself, which is BCHKS25's RS-specific external content. -/
theorem badLineWitness_of_interpolationData
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0)
    (u : WordStack A (Fin 2) ι)
    (hjp : ¬ jointProximity (C := C) (u := u) δ_int)
    (Γ : Finset F)
    (hΓ : ∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1, C) ≤ δ_fld)
    (hcount : (Fintype.card F : ℝ) / (2 * Fintype.card ι) ≤ (Γ.card : ℝ)) :
    BadLineWitness (F := F) C δ_fld δ_int :=
  ⟨u, hjp, Γ, hΓ, (badLineCount_real_iff_nat (F := F) (ι := ι) Γ.card).mp hcount⟩

/-- Variant of the producer taking the integral count `|F| ≤ 2n · Γ.card` directly. -/
theorem badLineWitness_of_interpolationData_nat
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0)
    (u : WordStack A (Fin 2) ι)
    (hjp : ¬ jointProximity (C := C) (u := u) δ_int)
    (Γ : Finset F)
    (hΓ : ∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1, C) ≤ δ_fld)
    (hcount : (Fintype.card F : ℝ) ≤ (2 * Fintype.card ι) * Γ.card) :
    BadLineWitness (F := F) C δ_fld δ_int :=
  ⟨u, hjp, Γ, hΓ, hcount⟩

/-- **Small-field corollary (fully in-tree, no external count).** When `|F| ≤ 2n`, a *single*
good combiner already satisfies the `BadLineWitness` cardinality bound `|F| ≤ 2n · |Γ|`
(with `|Γ| = 1`). Hence any non-jointly-close stack possessing one `δ_fld`-close combining line
is a witness — no interpolation count is required.

This isolates exactly why BCHKS25's interpolation is needed only in the *large*-field regime:
for `|F| ≤ 2n` the witness is unconditional given one bad line. -/
theorem badLineWitness_of_smallField
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0)
    (u : WordStack A (Fin 2) ι)
    (hjp : ¬ jointProximity (C := C) (u := u) δ_int)
    (γ₀ : F) (hγ₀ : δᵣ(u 0 + γ₀ • u 1, C) ≤ δ_fld)
    (hsmall : (Fintype.card F : ℝ) ≤ 2 * Fintype.card ι) :
    BadLineWitness (F := F) C δ_fld δ_int := by
  refine ⟨u, hjp, {γ₀}, ?_, ?_⟩
  · intro γ hγ
    rw [Finset.mem_singleton] at hγ
    subst hγ
    exact hγ₀
  · -- `|F| ≤ 2n · |{γ₀}| = 2n · 1 = 2n`
    have hcard : ({γ₀} : Finset F).card = 1 := Finset.card_singleton γ₀
    rw [hcard]
    simpa using hsmall

/-- **Producer in `P → BadLineWitness` form.** This is exactly the hypothesis shape consumed by
`Bridge.hBadLine_of_provBadLine` (and through it
`rs_epsCA_small_implies_lambda_lt_F_bchks25_of_badLineWitness`). A BCHKS25 interpolation count
`P → (stack, non-joint-proximity, good set, fraction count)` for RS therefore closes ABF26
Theorem 5.2 via the existing bridge — the single remaining external input is the count. -/
theorem provBadLine_of_interpolation
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) {P : Prop}
    (interp : P →
      Σ' u : WordStack A (Fin 2) ι,
        PLift (¬ jointProximity (C := C) (u := u) δ_int) ×'
        Σ' Γ : Finset F,
          PLift (∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1, C) ≤ δ_fld) ×'
          PLift ((Fintype.card F : ℝ) / (2 * Fintype.card ι) ≤ (Γ.card : ℝ))) :
    P → BadLineWitness (F := F) C δ_fld δ_int := by
  intro hp
  obtain ⟨u, ⟨hjp⟩, Γ, ⟨hΓ⟩, ⟨hcount⟩⟩ := interp hp
  exact badLineWitness_of_interpolationData C δ_fld δ_int u hjp Γ hΓ hcount

end BadLineConstruction

end CodingTheory.Bridge

/-! ### Axiom audit (issue #103 producer surface) -/

#print axioms CodingTheory.Bridge.badLineCount_real_iff_nat
#print axioms CodingTheory.Bridge.badLineWitness_of_interpolationData
#print axioms CodingTheory.Bridge.badLineWitness_of_interpolationData_nat
#print axioms CodingTheory.Bridge.badLineWitness_of_smallField
#print axioms CodingTheory.Bridge.provBadLine_of_interpolation
