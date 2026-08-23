/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.ToMathlib.GGR11Interleaved

/-!
# Reconnecting `InterleavedCode.lambda_le_ggr11` to the refined GGR11 residual

`ArkLib.Data.CodingTheory.InterleavedCode` states the GGR11 / ABF26-L2.10
interleaved list-size bound as the bare `Prop`-valued definition
`InterleavedCode.lambda_le_ggr11`, with the GGR11 Blue/Red budgets `b = ⌈δ/η⌉`,
`r = ⌈log₂(δ_min/η)⌉` (`η = δ_min − δ`).  `ArkLib.ToMathlib.GGR11Interleaved`
then carries the *refined* development:

* the closed-form leaf-counting recursion `ggr11_tree_count_le` (GGR11 Theorem 3.6),
  proved fully (`sorry`/`axiom`-free);
* the refined residual `GGR11TreeStructure` (the Erase-Decode tree existence,
  GGR11 Algorithm 1 / Lemmas 3.3–3.5) and the chain
  `GGR11TreeStructure → GGR11PerWordBound → (bound)` for *arbitrary* budgets `b r`;
* unconditional discharges in the elementary `m ≤ r` regime
  (`ggr11_treeStructure_of_le_exp`) and the infinite-list regime
  (`ggr11_perWordBound_of_Lambda_top`).

Those two files were never wired together at the *specific* GGR11 budgets used by
`lambda_le_ggr11`.  This file closes that gap (ABF26 issue #50, acceptance item 2):
it names the GGR11 budgets (`ggr11Eta`, `ggr11BlueBudget`, `ggr11RedBudget`),
proves `lambda_le_ggr11` from each refined entry point, and re-exposes the two
already-proven regimes against the bare definition.  Acceptance item 3 (regression
coverage for the `Λ(C^{≡m}, δ) → Λ(C, δ)` reduction API) is the `Regression`
section at the end.

## The remaining residual (acceptance item 1)

The genuine Erase-Decode tree *construction* in the complementary `m > r` regime —
GGR11 Algorithm 1 with the Blue/Red erasure-decoding budgets of Lemmas 3.3–3.5 —
has no in-tree analogue and is **not** closed here.  It remains the precisely-named
external residual `InterleavedCode.GGR11.GGR11TreeStructure`.  Every theorem below
either consumes that residual explicitly or lives in a regime where it is already
discharged; none silently weakens it.

## References

- [GGR11] Gopalan, Guruswami, Raghavendra. *List Decoding Tensor Products and
  Interleaved Codes.* SIAM J. Comput. 40(5), 2011.
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated
  Agreement.* 2026 (Lemma 2.10).
-/

open ListDecodable Code InterleavedCode

namespace InterleavedCode.GGR11Reconnect

variable {ι F : Type} [Fintype ι] [Field F] [DecidableEq F]

/-- The GGR11 proximity slack `η = δ_min(C) − δ` used by `lambda_le_ggr11`. -/
noncomputable def ggr11Eta (C : Set (ι → F)) (δ : ℝ) : ℝ :=
  (Code.minDist C : ℝ) / Fintype.card ι - δ

/-- The GGR11 Blue budget `b = ⌈δ / η⌉` used by `lambda_le_ggr11`. -/
noncomputable def ggr11BlueBudget (C : Set (ι → F)) (δ : ℝ) : ℕ :=
  ⌈δ / ggr11Eta C δ⌉₊

/-- The GGR11 Red budget `r = ⌈log₂(δ_min(C) / η)⌉` used by `lambda_le_ggr11`. -/
noncomputable def ggr11RedBudget (C : Set (ι → F)) (δ : ℝ) : ℕ :=
  ⌈Real.log ((Code.minDist C : ℝ) / Fintype.card ι / ggr11Eta C δ) / Real.log 2⌉₊

/-- `lambda_le_ggr11`, unfolded to the explicit bound at the GGR11 budgets.

This exposes the definitional content of `InterleavedCode.lambda_le_ggr11` to the
reconnect theorems below: it is exactly the GGR11-budget instance of the
`GGR11Interleaved` bound shape, confirming the budget abbreviations track the
`let`-bindings inside the bare definition. -/
theorem lambda_le_ggr11_iff
    (C : Set (ι → F)) (δ : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hδ_lb : 0 ≤ δ) (hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι) :
    InterleavedCode.lambda_le_ggr11 C δ m hm hδ_lb hδ_ub ↔
      Lambda (interleavedCodeSet (κ := Fin m) C) δ ≤
        ((ggr11BlueBudget C δ + ggr11RedBudget C δ).choose (ggr11RedBudget C δ) : ℕ∞)
          * (Lambda C δ) ^ ggr11RedBudget C δ :=
  Iff.rfl

/-- **Reconnect (tree-existence form).** The bare `InterleavedCode.lambda_le_ggr11`
bound follows from the refined Erase-Decode tree residual `GGR11TreeStructure` at
the GGR11 Blue/Red budgets. This is the wiring acceptance item 2 of issue #50 asks
for: the tree-existence residual now *directly* discharges the headline bound. -/
theorem lambda_le_ggr11_of_treeStructure
    (C : Set (ι → F)) (δ : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hδ_lb : 0 ≤ δ) (hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι)
    (h : GGR11.GGR11TreeStructure C δ m (ggr11BlueBudget C δ) (ggr11RedBudget C δ)) :
    InterleavedCode.lambda_le_ggr11 C δ m hm hδ_lb hδ_ub :=
  (lambda_le_ggr11_iff C δ m hm hδ_lb hδ_ub).mpr (GGR11.lambda_le_ggr11_of_treeStructure h)

/-- **Reconnect (named frontier form).** The bare bound follows from the granular
per-received-word `GGR11TreeFrontier` at the concrete GGR11 budgets. This is the budget-specific
adapter for the named frontier exposed in `GGR11Interleaved.lean`. -/
theorem lambda_le_ggr11_of_treeFrontier
    (C : Set (ι → F)) (δ : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hδ_lb : 0 ≤ δ) (hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι)
    (h : GGR11.GGR11TreeFrontier C δ m (ggr11BlueBudget C δ) (ggr11RedBudget C δ)) :
    InterleavedCode.lambda_le_ggr11 C δ m hm hδ_lb hδ_ub :=
  lambda_le_ggr11_of_treeStructure C δ m hm hδ_lb hδ_ub
    (GGR11.treeStructure_of_frontier h)

/-- **Reconnect (per-word form).** The bare bound follows from the (coarser)
per-received-word residual `GGR11PerWordBound` at the GGR11 budgets. -/
theorem lambda_le_ggr11_of_perWordBound
    (C : Set (ι → F)) (δ : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hδ_lb : 0 ≤ δ) (hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι)
    (h : GGR11.GGR11PerWordBound C δ m (ggr11BlueBudget C δ) (ggr11RedBudget C δ)) :
    InterleavedCode.lambda_le_ggr11 C δ m hm hδ_lb hδ_ub :=
  (lambda_le_ggr11_iff C δ m hm hδ_lb hδ_ub).mpr (GGR11.lambda_le_ggr11_of_perWordBound h)

/-- **Elementary regime, reconnected.** When the GGR11 Red budget already dominates
the interleaving factor (`m ≤ r`) and the base list size is at least one, the bare
`lambda_le_ggr11` holds *unconditionally* — the in-tree product bound
`encard ≤ Λ(C,δ)^m` supplies the (pure-Red) Erase-Decode tree
(`ggr11_treeStructure_of_le_exp`). No external residual is consumed. -/
theorem lambda_le_ggr11_of_le_exp [Fintype F] [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hδ_lb : 0 ≤ δ) (hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι)
    (hmr : m ≤ ggr11RedBudget C δ) (hL : 1 ≤ Lambda C δ) :
    InterleavedCode.lambda_le_ggr11 C δ m hm hδ_lb hδ_ub :=
  lambda_le_ggr11_of_treeStructure C δ m hm hδ_lb hδ_ub
    (GGR11.ggr11_treeStructure_of_le_exp hmr hL)

/-- **Infinite-list regime, reconnected.** When the base list size is infinite and
the GGR11 Red budget is positive, the right-hand side of the bound is `⊤`, so the
bare `lambda_le_ggr11` holds *unconditionally*
(`ggr11_perWordBound_of_Lambda_top`). No external residual is consumed. -/
theorem lambda_le_ggr11_of_Lambda_top
    (C : Set (ι → F)) (δ : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hδ_lb : 0 ≤ δ) (hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι)
    (hr : 0 < ggr11RedBudget C δ) (hL : Lambda C δ = ⊤) :
    InterleavedCode.lambda_le_ggr11 C δ m hm hδ_lb hδ_ub :=
  lambda_le_ggr11_of_perWordBound C δ m hm hδ_lb hδ_ub
    (GGR11.ggr11_perWordBound_of_Lambda_top hr hL)

/-! ### Regression coverage for the `Λ(C^{≡m}, δ) → Λ(C, δ)` reduction API

These lock in the shape of the reduction chain so that future refactors of either
`InterleavedCode.lambda_le_ggr11` or the `GGR11Interleaved` residual API are caught
by a build break rather than silently desynchronising (issue #50, acceptance
item 3). -/

section Regression

variable (C : Set (ι → F)) (δ : ℝ) (m : ℕ)

/-- The refined tree-existence residual dominates the coarse per-word residual at
the GGR11 budgets (the `GGR11TreeStructure → GGR11PerWordBound` step). -/
example (h : GGR11.GGR11TreeStructure C δ m (ggr11BlueBudget C δ) (ggr11RedBudget C δ)) :
    GGR11.GGR11PerWordBound C δ m (ggr11BlueBudget C δ) (ggr11RedBudget C δ) :=
  GGR11.perWordBound_of_treeStructure h

/-- The per-word residual yields the maximised interleaved list-size bound (the
`GGR11PerWordBound → Λ(C^{≡m})` step), independent of the `lambda_le_ggr11`
packaging. -/
example (h : GGR11.GGR11PerWordBound C δ m (ggr11BlueBudget C δ) (ggr11RedBudget C δ)) :
    Lambda (interleavedCodeSet (κ := Fin m) C) δ ≤
      ((ggr11BlueBudget C δ + ggr11RedBudget C δ).choose (ggr11RedBudget C δ) : ℕ∞)
        * (Lambda C δ) ^ ggr11RedBudget C δ :=
  GGR11.lambda_le_ggr11_of_perWordBound h

/-- The whole reduction chain composes: tree existence at the GGR11 budgets gives
the `lambda_le_ggr11` headline bound. -/
example (hm : 1 ≤ m) (hδ_lb : 0 ≤ δ)
    (hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι)
    (h : GGR11.GGR11TreeStructure C δ m (ggr11BlueBudget C δ) (ggr11RedBudget C δ)) :
    InterleavedCode.lambda_le_ggr11 C δ m hm hδ_lb hδ_ub :=
  lambda_le_ggr11_of_treeStructure C δ m hm hδ_lb hδ_ub h

/-- The named frontier form also composes to the headline `lambda_le_ggr11` bound. -/
example (hm : 1 ≤ m) (hδ_lb : 0 ≤ δ)
    (hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι)
    (h : GGR11.GGR11TreeFrontier C δ m (ggr11BlueBudget C δ) (ggr11RedBudget C δ)) :
    InterleavedCode.lambda_le_ggr11 C δ m hm hδ_lb hδ_ub :=
  lambda_le_ggr11_of_treeFrontier C δ m hm hδ_lb hδ_ub h

/-- Regression: the bare definition is *propositionally identical* to the explicit
GGR11-budget bound, so the budget abbreviations track the `let`-bindings inside
`InterleavedCode.lambda_le_ggr11`. -/
example (hm : 1 ≤ m) (hδ_lb : 0 ≤ δ)
    (hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι) :
    InterleavedCode.lambda_le_ggr11 C δ m hm hδ_lb hδ_ub ↔
      Lambda (interleavedCodeSet (κ := Fin m) C) δ ≤
        ((ggr11BlueBudget C δ + ggr11RedBudget C δ).choose (ggr11RedBudget C δ) : ℕ∞)
          * (Lambda C δ) ^ ggr11RedBudget C δ :=
  lambda_le_ggr11_iff C δ m hm hδ_lb hδ_ub

end Regression

-- Axiom audit: the reconnect theorems that do not consume the external residual
-- must be kernel-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`).
#print axioms lambda_le_ggr11_of_le_exp
#print axioms lambda_le_ggr11_of_Lambda_top
#print axioms lambda_le_ggr11_of_treeStructure
#print axioms lambda_le_ggr11_of_treeFrontier

end InterleavedCode.GGR11Reconnect
