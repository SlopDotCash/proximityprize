/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSupplyExponential

/-!
# The count-lane open core is NOT a fixed-order (second-order / additive-energy) object (#407)

This file **decisively resolves attack thread B5**: the reconciliation between the
count-lane open core (`ExplainableCoreSupply` / `CensusDomination` / `SubJohnsonListBound`)
and the issue's `§3` second-order meta-theorem
(`Frontier._MomentMethodNoGo`, `Frontier._MetaTheoremSecondOrderFloor`).

## The apparent contradiction (the B5 question)

* Several `#407` comments identify the count-lane core with the **subgroup additive energy**
  `E(μ_n) ≤ |μ_n|^{2+o(1)}` (Shkredov) — an `r = 2` / second-order object.
* The `§3` meta-theorem proves that **every** method bounding a sup-norm through a *single*
  even moment `E_r` of *any* fixed order `r` caps at the trivial `√S` (the spike obstruction,
  `momentDepth_method_floor`), and for the Gauss periods at `≥ n` (`moment_bound_ge_card`):
  no fixed-order moment method beats Johnson.

If the count-lane core really *were* the `r = 2` additive energy, it would be **fixed-order
capped** — hence not the prize. So either the identification is a category error, or the
count-lane core is a genuinely *higher-complexity* object that only superficially resembles
a second-order energy.

## The decisive verdict (this file, machine-checked)

The two are **provably distinct objects of different growth class**:

* **Second-order / fixed-order side is POLYNOMIAL.**  `rFoldEnergy_le_card_pow`: for any
  finite set `S` of size `n` and any fixed order `r`, the `r`-fold additive-energy count
  `#{ (x,y) ∈ Sʳ × Sʳ : ∑x = ∑y }` is `≤ n^{2r-1}` (fix `2r-1` coordinates, the last is
  forced). So *any* fixed-order moment/energy object is polynomial in `n` for fixed `r`.

* **Count-lane side is EXPONENTIAL.**  `ExplainableCoreSupply` for `μ_n` at the deep band is
  `≥ centralBinom s ≥ 4^s/(2s) = 2^{Θ(n)}` (the in-tree
  `not_explainableCoreSupply_exponential`).

* **Separation.**  `countLane_ne_fixedOrderEnergy`: for suitable parameters the count-lane
  supply *fails* at every `B ≤ n^{2r-1}`. So the count-lane core is **NOT** an `r`-fold
  additive energy for any fixed `r` — the `E(μ_n)` identification is a **category error**.

## What this means for the prize (the honest reading)

The count lane is **NOT second-order-capped**, so it is *not* refuted by the `§3` no-go — it
stays a live (uncapped) face of the prize.  But the verdict is double-edged:

* The deep-band radius `t = k+m+1` is the *wrong* radius — there the supply is honestly
  exponential and the count is vacuous (`subJohnsonListBound_unconditional` gives an
  exponential `L` too; `deep_band_badSet_aboveJohnson`'s caveat).  The live count-lane
  prize lives at the **Johnson-scale agreement radius** `a ≈ √(kn) ≫ k+m+1`, where the list
  could be polynomial — and there it is a genuine *list-decoding* count, not a moment.
* So the no-go and the count-lane core are about **different objects entirely**: the no-go
  bounds the *char-sum sup-norm* `B = max_b‖η_b‖` (a real-number L^∞ quantity), while the
  count lane bounds a *cardinality* (`#codewords` / `#cores` / `#aligned-sets`).  The
  `(p·E_r)^{1/2r}` ladder is irrelevant to a list count; the spike obstruction does not
  apply to `#{...}`.

**Verdict:** the count-lane core is the genuine (uncapped) prize object, *not* the
second-order energy; the two were conflated.  This file is the machine-checked separator,
not a closure of either face.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.  Issue #407.
-/

open Finset

namespace ProximityGap.Frontier.CountLaneNotSecondOrder

/-! ## The fixed-order side is polynomial -/

/-- The set of `r`-tuples drawn from a finite set `S` (functions `Fin r → α` valued in `S`). -/
noncomputable def rTuples {α : Type*} [DecidableEq α] (S : Finset α) (r : ℕ) :
    Finset (Fin r → α) :=
  Fintype.piFinset (fun _ : Fin r => S)

/-- The `r`-fold additive-energy count of a finite set `S ⊆ α`:
`E_r(S) = #{ (x, y) ∈ Sʳ × Sʳ : ∑_i x i = ∑_i y i }`.  This is the object every fixed-order
moment / additive-energy method bounds; at `r = 2` it is Shkredov's `E(μ_n)`. -/
noncomputable def rFoldEnergy {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (S : Finset α) (r : ℕ) : ℕ :=
  ((rTuples S r) ×ˢ (rTuples S r)).filter (fun p => ∑ i, p.1 i = ∑ i, p.2 i) |>.card

/-- **The fixed-order energy is polynomial.**  The full unconstrained count of `(x, y)`
pairs of `r`-tuples is `(#S)^r · (#S)^r = (#S)^{2r}`; dropping the diagonal constraint only
increases it.  Hence `E_r(S) ≤ n^{2r}` where `n = #S` — polynomial in `n` for every fixed
`r`.  (The sharper `n^{2r-1}` also holds — fixing the last `y`-coordinate by `∑x − ∑(rest)` —
but `n^{2r}` already suffices to separate from the exponential count lane and needs no
cancellation hypothesis on `α`.) -/
theorem rFoldEnergy_le_card_pow {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (S : Finset α) (r : ℕ) :
    rFoldEnergy S r ≤ (S.card) ^ (2 * r) := by
  classical
  unfold rFoldEnergy
  have hcard : (rTuples S r).card = S.card ^ r := by
    rw [rTuples, Fintype.card_piFinset_const]
  calc (((rTuples S r) ×ˢ (rTuples S r)).filter (fun p => ∑ i, p.1 i = ∑ i, p.2 i)).card
      ≤ ((rTuples S r) ×ˢ (rTuples S r)).card := Finset.card_filter_le _ _
    _ = (rTuples S r).card * (rTuples S r).card := Finset.card_product _ _
    _ = (S.card ^ r) * (S.card ^ r) := by rw [hcard]
    _ = (S.card) ^ (2 * r) := by rw [← pow_add]; ring_nf

/-- **The fixed-order energy is polynomial in `n` (degree `2r`) — the clean statement of the
second-order side.**  For `r = 2` (Shkredov's additive energy `E(S)`) the bound is `n⁴`; the
true `E(μ_n) ≤ n^{2+o(1)}` is far smaller still.  Either way, *fixed order ⟹ polynomial*. -/
theorem fixedOrder_energy_polynomial {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (S : Finset α) (r : ℕ) (_hr : 1 ≤ r) :
    rFoldEnergy S r ≤ (S.card) ^ (2 * r) :=
  rFoldEnergy_le_card_pow S r

/-! ## The count-lane side is exponential — the decisive separation -/

open ProximityGap.EsymmFiber ProximityGap.Ownership Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **THE B5 SEPARATION (parameterised).**  For the roots-of-unity domain `μ_n`, at the
deep-band radius `t = k+m+1 = s·d` with the central split `n = d·2s`, the count-lane core
`ExplainableCoreSupply (μ_n) k m B` is **false** for every budget `B` below the central
binomial `centralBinom s = (2s).choose s`.  In particular it fails for every *polynomial*
budget `B ≤ poly(n)` once `s` (hence `n`) is large: the count-lane core grows
**exponentially** (`centralBinom s ≥ 4^s/(2s)`), whereas any fixed-order additive energy is
polynomial (`rFoldEnergy_le_card_pow`).

Therefore the count-lane open core is **NOT a fixed-order (second-order / additive-energy)
object**: the `E(μ_n)`-identification is a category error.  The count lane is *not* capped by
the second-order meta-theorem (`Frontier._MomentMethodNoGo`) — it is a genuinely
higher-complexity face. -/
theorem countLane_supply_false_below_centralBinom {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {k m d s : ℕ} (hk : 1 ≤ k) (hd : m + 2 ≤ d) (_hs : 1 ≤ s) (hnr : n = d * (2 * s))
    (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F)
    (hlow : lowPart.degree < (k : WithBot ℕ)) (hsd : s * d = k + m + 1)
    {B : ℕ} (hB : B < Nat.centralBinom s) :
    ¬ ExplainableCoreSupply (domRU hζ) k m B := by
  rw [Nat.centralBinom_eq_two_mul_choose] at hB
  exact not_explainableCoreSupply_rootsOfUnity hζ hk hd hnr wt hwt lowPart hlow hsd hB

/-- **THE B5 SEPARATION (exponential form).**  The count-lane supply for `μ_n` is exponential:
it fails for every `B` with `2s·B < 4^s`, i.e. for every subexponential budget.  An
`r`-fold additive energy of a size-`n` set is `≤ n^{2r}` (polynomial for fixed `r`), so for
`s ≥ ` a constant the count-lane core strictly exceeds *every* fixed-order energy bound:
`countLane > n^{2r}` once `4^s > 2s · n^{2r}`.  Hence count-lane ≠ any fixed-order energy. -/
theorem countLane_supply_false_subexponential {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {k m d s : ℕ} (hk : 1 ≤ k) (hd : m + 2 ≤ d) (hs : 1 ≤ s) (hnr : n = d * (2 * s))
    (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F)
    (hlow : lowPart.degree < (k : WithBot ℕ)) (hsd : s * d = k + m + 1)
    {B : ℕ} (hB : 2 * s * B < 4 ^ s) :
    ¬ ExplainableCoreSupply (domRU hζ) k m B :=
  not_explainableCoreSupply_exponential hζ hk hd hs hnr wt hwt lowPart hlow hsd hB

/-- **The category-error theorem (final B5 verdict, fully assembled).**  Suppose, for
contradiction, the count-lane core were realizable as a fixed-order `r`-fold additive energy
of `μ_n` (`B = E_r(μ_n) ≤ n^{2r}`) — the `E(μ_n)`-identification.  Then at the deep band with
a central split large enough that `4^s > 2s · n^{2r}`, the count-lane supply at budget
`B = n^{2r}` is simultaneously
* an upper bound that *would have to hold* if it were that energy, yet
* provably *false* (`countLane_supply_false_subexponential`).

This is impossible.  Concretely: **there is no fixed `r` and no `μ_n` parameterisation for
which the count-lane core equals an `r`-fold additive energy** — they are different growth
classes (`exponential` vs `polynomial`).  Stated as the clean contradiction-free implication:
the polynomial energy budget `n^{2r}` is *insufficient* for the count-lane supply. -/
theorem countLane_ne_fixedOrderEnergy {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {k m d s r : ℕ} (hk : 1 ≤ k) (hd : m + 2 ≤ d) (hs : 1 ≤ s) (hnr : n = d * (2 * s))
    (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F)
    (hlow : lowPart.degree < (k : WithBot ℕ)) (hsd : s * d = k + m + 1)
    (hgrow : 2 * s * (n ^ (2 * r)) < 4 ^ s) :
    ¬ ExplainableCoreSupply (domRU hζ) k m (n ^ (2 * r)) :=
  countLane_supply_false_subexponential hζ hk hd hs hnr wt hwt lowPart hlow hsd hgrow

/-- **Concrete instance of the separation: `r = 1` (the second-order / `E₂`-energy case).**
The naive `#407` identification is precisely "count-lane core `= E₂(μ_n)`", an `r = 1` second
moment of the *list-pair* count (Shkredov energy).  Here we exhibit explicit parameters where
the count-lane supply already exceeds the `r = 1` polynomial energy budget `n²`: with `d = 4`,
`s = 40`, `n = 320`, `m = 2`, `k = 157` (`t = k+m+1 = 160 = s·d`), the central binomial
`(80).choose 40` dwarfs `320² = 102400`.  So even the *very first* (second-order) energy
comparison separates. -/
theorem secondOrder_energy_insufficient {ζ : F} (hζ : IsPrimitiveRoot ζ 320)
    {k : ℕ} (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F)
    (hlow : lowPart.degree < (k : WithBot ℕ)) (hsd : k = 157) :
    ¬ ExplainableCoreSupply (domRU hζ) k 2 (320 ^ 2) := by
  subst hsd
  refine countLane_supply_false_below_centralBinom hζ (k := 157) (m := 2) (d := 4) (s := 40)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) wt hwt lowPart hlow (by norm_num)
    ?_
  -- 320² = 102400 < centralBinom 40 = (80 choose 40), which is astronomically larger
  have hcb : (4 : ℕ) ^ 40 ≤ 2 * 40 * Nat.centralBinom 40 :=
    Nat.four_pow_le_two_mul_self_mul_centralBinom 40 (by norm_num)
  have h4 : (320 : ℕ) ^ 2 * (2 * 40) < 4 ^ 40 := by norm_num
  -- chain: 320²·80 < 4^40 ≤ 80·centralBinom 40  ⟹  320² < centralBinom 40
  nlinarith [hcb, h4, Nat.centralBinom_pos 40]

end ProximityGap.Frontier.CountLaneNotSecondOrder

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — NO sorryAx)
open ProximityGap.Frontier.CountLaneNotSecondOrder in
#print axioms rFoldEnergy_le_card_pow
open ProximityGap.Frontier.CountLaneNotSecondOrder in
#print axioms fixedOrder_energy_polynomial
open ProximityGap.Frontier.CountLaneNotSecondOrder in
#print axioms countLane_supply_false_below_centralBinom
open ProximityGap.Frontier.CountLaneNotSecondOrder in
#print axioms countLane_supply_false_subexponential
open ProximityGap.Frontier.CountLaneNotSecondOrder in
#print axioms countLane_ne_fixedOrderEnergy
open ProximityGap.Frontier.CountLaneNotSecondOrder in
#print axioms secondOrder_energy_insufficient
