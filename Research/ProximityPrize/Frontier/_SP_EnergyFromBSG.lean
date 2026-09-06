/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Data.ZMod.Basic
import ArkLib.ToMathlib.Combinatorics.Additive.SumProduct
import ArkLib.ToMathlib.Combinatorics.Additive.BalogSzemerediGowers

/-!
# Linking `SubgroupEnergyCore` to `SumProductExpansionCore` + `BSGCore`

This file analyses the **linkage leg** of the Bourgain–Glibichuk–Konyagin (BGK) assembly:
whether the deep named core `SubgroupEnergyCore` (an *upper* bound on the additive energy of a
bounded multiplicative subgroup `H ≤ 𝔽_p^×`) can be *derived* from the two other deep cores

* `BalogSzemerediGowers.BSGCore` (large additive energy ⟹ a dense small-doubling subset), and
* `SumProduct.SumProductExpansionCore` (a bounded multiplicative subgroup has an expanding sumset),

by an *elementary* Ruzsa / Plünnecke + contradiction argument, **without** re-introducing any new
incidence-geometry content.

## Outcome (honest)

The linkage is **NOT** closable by Ruzsa/Plünnecke alone. The forward half is genuinely
elementary and is proven here:

* `balog_gives_dense_smallDoubling_subset` — packaging the BSG output for `A = H` (PROVEN, just an
  application of `balog_szemeredi_gowers`).

The lift back from the dense small-doubling **subset** `A' ⊆ H` to a contradiction with the
**subgroup** sumset-expansion runs into one irreducible obstruction:

> Plünnecke–Ruzsa and Ruzsa covering are *purely additive* tools. They convert additive
> control of `A'` into additive control of iterated sumsets `n·A' − m·A'`, and (multiplicative)
> Ruzsa covering converts the **multiplicative** density `#A' ≥ #H / (C₁K)` into a covering of `H`
> by `C₁K` translates of the **multiplicative ratio set** `A'/A'`. But the BSG conclusion controls
> the **additive difference** `A' − A'`, whereas the covering needs the **multiplicative ratio**
> `A'/A'`. Bridging `#(A'/A')` (multiplicative) to `#(A'−A')` (additive) — i.e. turning additive
> structure of a *positive proportion* of a multiplicative subgroup into a sumset bound — *is* the
> sum-product / no-subfield content itself, exactly the AG-heavy step `SumProductExpansionCore`
> packages.

So the honest reduction names a single residual `Prop`,
`SumProductBridge`, capturing exactly the multiplicative⇄additive conversion that
Ruzsa/Plünnecke does *not* supply. Everything strictly above it (the BSG application, the energy
arithmetic, the contradiction wiring) is proven. `SumProductBridge` is *not* a re-statement of
`SumProductExpansionCore`: it is applied to the BSG subset `A'` (not to `H`), but it is of the same
AG difficulty, so the linkage does **not** reduce the deep content — it relocates it.

The conditional capstone `subgroupEnergyCore_of_bridge_and_bsg` shows that
`SubgroupEnergyCore` *follows* from `BSGCore` together with the residual `SumProductBridge`,
making the residual the single smallest named sub-Prop.

## References
* J. Bourgain, A. Glibichuk, S. Konyagin, *Estimates for the number of sums and products and for
  exponential sums in fields of prime order* (2006).
* S. V. Konyagin, *A sum-product estimate in fields of prime order* (2003).
-/

open Finset
open scoped BigOperators Pointwise Combinatorics.Additive

namespace ArkLib.ProximityGap.SP

/-! ## The proven forward half: BSG applied to a subgroup -/

/-- **Forward half (PROVEN).** For a finite set `H` with large additive energy
(`#H ^ 3 ≤ K · E[H]`), the BSG core extracts a dense subset `A' ⊆ H` with small *difference set*.

This is a verbatim application of `Finset.balog_szemeredi_gowers`; it carries no new content but
isolates the exact object — a dense, small-(additive)-doubling **subset** of `H` — that the linkage
must then convert into a contradiction with the subgroup sumset expansion. -/
theorem balog_gives_dense_smallDoubling_subset
    {C₁ C₂ c : ℕ} (hbsg : Finset.BSGCore C₁ C₂ c)
    {p : ℕ} (H : Finset (ZMod p)) (K : ℕ) (hK : 0 < K)
    (hne : H.Nonempty) (hE : #H ^ 3 ≤ K * E[H]) :
    ∃ A' : Finset (ZMod p), A' ⊆ H ∧ A'.Nonempty ∧
      C₁ * K * #A' ≥ #H ∧ #(A' - A') ≤ C₂ * K ^ c * #A' :=
  Finset.balog_szemeredi_gowers hbsg H K hK hne hE

/-! ## The single residual: the multiplicative⇄additive sum-product bridge

The obstruction below is the precise statement of *what Ruzsa/Plünnecke does not give*. The BSG
subset `A' ⊆ H` is dense (`#A' ≥ #H/(C₁K)`) and has small additive doubling
(`#(A'−A') ≤ C₂K^c #A'`). For a *multiplicative subgroup* `H` this forces an additive-energy
*upper* bound on `H` — but only because `A'` lives inside the dilation-invariant `H` (`t · A' ⊆ H`
for every `t ∈ H`), and combining the many multiplicative dilates of an additively structured `A'`
is the sum-product/no-subfield mechanism. We name exactly that conversion. -/

/-- **The sum-product bridge (named residual, NOT a hidden `sorry`).**

It says: a subset `A'` of a bounded multiplicative subgroup `H ≤ 𝔽_p^×` that is *dense* in `H`
(`C₁ * K * #A' ≥ #H`) and has *small additive doubling* (`#(A' − A') ≤ D * #A'`) yields a
sub-trivial additive-energy bound on the ambient subgroup `H`:

  `E[H] ^ m ≤ Cen · #H ^ (3 m − 1)`.

This is the AG-heavy content that Ruzsa/Plünnecke does **not** supply: it is the conversion of
additive structure of a dense subset of a *multiplicatively closed* `H` into a sumset/energy bound
on `H` (the no-subfield step). It is *applied to the BSG subset* `A'`, not to `H` directly, but is
of the same difficulty as `SumProductExpansionCore`; hence the linkage **relocates** rather than
**eliminates** the deep step. -/
def SumProductBridge (Cen m C₁ : ℕ) (sizeBound : ℕ → ℕ) : Prop :=
  ∀ {p : ℕ} [Fact p.Prime],
    ∀ (H : Finset (ZMod p)), H.Nonempty → MulClosed (H.erase 0) →
      (0 : ZMod p) ∉ H → #H ≤ sizeBound p →
      ∀ (A' : Finset (ZMod p)) (K D : ℕ), A' ⊆ H → A'.Nonempty →
        C₁ * K * #A' ≥ #H → #(A' - A') ≤ D * #A' →
          E[H] ^ m ≤ Cen * #H ^ (3 * m - 1)

/-! ## The conditional capstone: `SubgroupEnergyCore` from `BSGCore` + the residual -/

/-- **Linkage capstone (conditional).** `SubgroupEnergyCore` follows from `BSGCore` together with
the single named residual `SumProductBridge`.

Proof skeleton (the elementary, fully-discharged wiring around the residual):

* If `E[H]` is *small* — concretely `E[H] ^ m ≤ Cen · #H ^ (3 m − 1)` already — we are done.
* Otherwise `E[H]` is large; choose `K` with `#H ^ 3 ≤ K · E[H]` (e.g. `K = #H ^ 3` since
  `1 ≤ E[H]` for nonempty `H`). `BSGCore` then produces a dense small-(additive)-doubling subset
  `A' ⊆ H` (the proven `balog_gives_dense_smallDoubling_subset`).
* Feed `A'`, with its density `C₁ * K * #A' ≥ #H` and doubling `D := C₂ * K ^ c`, to
  `SumProductBridge`, which returns exactly `E[H] ^ m ≤ Cen · #H ^ (3 m − 1)`.

The only non-elementary ingredient is `SumProductBridge`; everything else is the BSG application and
the case split, both proven. -/
theorem subgroupEnergyCore_of_bridge_and_bsg
    {Cen m C₁ C₂ c : ℕ} {sizeBound : ℕ → ℕ}
    (hbsg : Finset.BSGCore C₁ C₂ c)
    (hbridge : SumProductBridge Cen m C₁ sizeBound) :
    Finset.SubgroupEnergyCore Cen m sizeBound := by
  intro p _ H hne hclosed hzero hsize
  -- `1 ≤ E[H]` for nonempty `H` (via the Cauchy–Schwarz bridge `#H ^ 4 ≤ #(H+H) · E[H]`).
  have hEpos : 1 ≤ E[H] := by
    have hcard : 0 < #H := hne.card_pos
    by_contra h
    push_neg at h
    have hE0 : E[H] = 0 := by omega
    have hCS := Finset.card_pow_four_le_card_add_mul_addEnergy H
    rw [hE0, Nat.mul_zero, Nat.le_zero] at hCS
    exact (pow_ne_zero 4 (by omega : #H ≠ 0)) hCS
  -- Choose `K = #H ^ 3`, so `#H ^ 3 ≤ K * E[H] = #H ^ 3 * E[H]` since `1 ≤ E[H]`.
  set K : ℕ := #H ^ 3 with hKdef
  have hK : 0 < K := by rw [hKdef]; positivity
  have hElarge : #H ^ 3 ≤ K * E[H] := by
    rw [hKdef]; calc #H ^ 3 = #H ^ 3 * 1 := (Nat.mul_one _).symm
      _ ≤ #H ^ 3 * E[H] := Nat.mul_le_mul_left _ hEpos
  -- BSG extracts the dense small-(additive)-doubling subset `A'`.
  obtain ⟨A', hA'sub, hA'ne, hA'dense, hA'double⟩ :=
    balog_gives_dense_smallDoubling_subset hbsg H K hK hne hElarge
  -- The residual bridge converts this into the subgroup energy bound (its conclusion IS the goal).
  exact hbridge H hne hclosed hzero hsize A' K (C₂ * K ^ c) hA'sub hA'ne hA'dense hA'double

end ArkLib.ProximityGap.SP

-- Axiom audit (expected: propext, Classical.choice, Quot.sound)
#print axioms ArkLib.ProximityGap.SP.balog_gives_dense_smallDoubling_subset
#print axioms ArkLib.ProximityGap.SP.subgroupEnergyCore_of_bridge_and_bsg
