/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettThm17Reduction
import ArkLib.Data.CodingTheory.AGL24GMMDSInterface

/-!
# The Lovett ⟶ AGL24 GM-MDS bridge (#389)

This file wires Lovett's algebraic GM-MDS theorem (arXiv:1803.02523, Theorem 1.7) to the
import boundary that the AGL24 Appendix A assembly consumes
(`AGL24.GMMDSDualZeroPatternTheorem`).

## The two endpoints

* **Source** — `ArkLib.GMMDS.LovettThm17 F n` (file `LovettUnion.lean`): for every `V*(k)`
  system `V : Fin m → Fin n → ℕ` the polynomial family `pFamUnion V k` is linearly
  independent over `F[a]` (the formal evaluation points `a₁,…,aₙ`).  This is Lovett's
  Theorem 1.7; `lovettThm17_of_steps` reduces it to the primitive case.

* **Target** — `AGL24.GMMDSDualZeroPatternTheorem k` (file `AGL24GMMDSInterface.lean`): for
  every generic zero pattern `(e, δ)` satisfying `GZPCondition e δ k` there are field
  evaluation points `φ : ι ↪ F` and dual rows `h`, supported on the prescribed edge sets,
  whose span is `dotForm.orthogonal (ReedSolomon.code φ k)`.

## The mathematics of the bridge (paper trace)

Lovett's Theorem 1.7 ⟹ Conjecture 1.3 (paper p.5: "Conjecture 1.3 follows directly from
Theorem 1.7"): the polynomial families being independent means the corresponding zero-pattern
generator matrix has full *symbolic* rank over `F[a]`.  The GM-MDS *matrix* construction
(paper p.3) then applies **Schwartz–Zippel** to replace the formal variables `a₁,…,aₙ` by
distinct field elements of `F` (possible when `|F| ≥ n + k − 1`) while keeping every `k × k`
minor nonsingular; the resulting MDS matrix realizes the prescribed zero pattern.  The
*dual* form `GMMDSDualZeroPatternTheorem` is the dual-space repackaging that AGL24
Theorem A.2 consumes: the rows of the zero-pattern parity-check matrix span the Reed–Solomon
dual.

## What is proven here, and the exact remaining gap

The translation from a `GZPCondition` to a `V*(k)` system, the Schwartz–Zippel
specialization, and the dual-space repackaging are a *single* faithful import step from the
GM-MDS literature, not yet formalized in-tree.  Following the project's modularity
convention, that step is isolated as **one** named `Prop`, `LovettToGZPDualBridge`, which is
stated to consume *exactly* `LovettThm17`'s conclusion (polynomial-family independence) and
produce the field-level dual span.  The assembly

> `lovettToGZPDualBridge` ⟹ (`LovettThm17 F n` ⟹ `GMMDSDualZeroPatternTheorem k`)

and the further forwarding to the older `GMMDSResidual` are proven here, axiom-clean.  This
closes the **wiring** gap: once Lovett's Theorem 1.7 is discharged (via
`lovettThm17_of_steps`) and the single named import step is supplied, the AGL24 floor is
met.  The remaining mathematical content is concentrated in the one named residual
`LovettToGZPDualBridge` — the GM-MDS matrix construction (GZP→`V*`, Schwartz–Zippel,
dual repackaging).

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : Type*} [Field F]

/-- **The single named import step of the Lovett ⟶ AGL24 GM-MDS bridge** (the GM-MDS matrix
construction: translate a generic zero pattern to a `V*(k)` system, apply Schwartz–Zippel to
specialize the formal evaluation points to distinct field elements, and repackage the
resulting zero-pattern parity-check rows as a span of the Reed–Solomon dual).

It is stated to consume *precisely* the conclusion of Lovett's Theorem 1.7
(`LovettThm17 (F := F) n`, the linear independence of every `V*(k)` polynomial family over
`F[a]`) as a hypothesis, and to produce the field-level dual-span existence of
`GMMDSDualZeroPatternTheorem`.  Holding it separate is the project's modularity convention:
it isolates the entire remaining mathematics of the bridge into one named `Prop`. -/
def LovettToGZPDualBridge (F : Type*) [Field F]
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n k : ℕ) : Prop :=
  (∀ m : ℕ, LovettThm17 (F := F) m) →
    AGL24.GMMDSDualZeroPatternTheorem (ι := ι) (F := F) k

/-- **The bridge assembly.**  Given the single named GM-MDS import step
(`LovettToGZPDualBridge`) and Lovett's Theorem 1.7 (in every coordinate dimension `m`), the
AGL24 dual-zero-pattern boundary `GMMDSDualZeroPatternTheorem` holds.  Axiom-clean. -/
theorem gmmDsDualZeroPatternTheorem_of_lovett {n k : ℕ}
    (hbridge : LovettToGZPDualBridge F ι n k)
    (hlovett : ∀ m : ℕ, LovettThm17 (F := F) m) :
    AGL24.GMMDSDualZeroPatternTheorem (ι := ι) (F := F) k :=
  hbridge hlovett

/-- **End-to-end wiring**: the named import step plus Lovett's Theorem 1.7 discharge the
older existential `GMMDSResidual` interface consumed by
`AGL24.symbolicFullRank_of_classical_imports`.  Axiom-clean. -/
theorem gmmDsResidual_of_lovett {n k : ℕ}
    (hbridge : LovettToGZPDualBridge F ι n k)
    (hlovett : ∀ m : ℕ, LovettThm17 (F := F) m) :
    AGL24.GMMDSResidual ι F k :=
  AGL24.gmmDsResidual_of_dualZeroPatternTheorem
    (gmmDsDualZeroPatternTheorem_of_lovett hbridge hlovett)

/-- **The bridge, fully reduced to Lovett's two named induction pieces.**  Composing the
master induction `lovettThm17_of_steps` (which reduces Theorem 1.7 to the reducible step and
the primitive case in each dimension) with the GM-MDS import step yields the AGL24
dual-zero-pattern boundary.  Axiom-clean.  This is the form that makes explicit that
*discharging Lovett's primitive case (and the Lean-technical reducible step) plus supplying
the single GM-MDS matrix import step closes the AGL24 floor*. -/
theorem gmmDsDualZeroPatternTheorem_of_lovett_steps {n k : ℕ}
    (hbridge : LovettToGZPDualBridge F ι n k)
    (hstep : ∀ m : ℕ, LovettReducibleStep F m)
    (hprim : ∀ m : ℕ, LovettPrimitiveCase F m) :
    AGL24.GMMDSDualZeroPatternTheorem (ι := ι) (F := F) k :=
  gmmDsDualZeroPatternTheorem_of_lovett hbridge
    (fun m => lovettThm17_of_steps (hstep m) (hprim m))

/-- **End-to-end, fully reduced**: the GM-MDS import step plus Lovett's two named induction
pieces discharge the older `GMMDSResidual` interface.  Axiom-clean. -/
theorem gmmDsResidual_of_lovett_steps {n k : ℕ}
    (hbridge : LovettToGZPDualBridge F ι n k)
    (hstep : ∀ m : ℕ, LovettReducibleStep F m)
    (hprim : ∀ m : ℕ, LovettPrimitiveCase F m) :
    AGL24.GMMDSResidual ι F k :=
  AGL24.gmmDsResidual_of_dualZeroPatternTheorem
    (gmmDsDualZeroPatternTheorem_of_lovett_steps hbridge hstep hprim)

end ArkLib.GMMDS

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.GMMDS.gmmDsDualZeroPatternTheorem_of_lovett
#print axioms ArkLib.GMMDS.gmmDsResidual_of_lovett
#print axioms ArkLib.GMMDS.gmmDsDualZeroPatternTheorem_of_lovett_steps
#print axioms ArkLib.GMMDS.gmmDsResidual_of_lovett_steps
