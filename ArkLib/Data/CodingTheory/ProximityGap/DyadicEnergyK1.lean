/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingCount
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingLifting
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal

/-!
# The dyadic K1 bound, UNCONDITIONAL: `zeroSumCount(μ_{2^k}) ≤ (2r−1)!!·n^r` (#389)

The negation-closed walk bound (K1) `zeroSumCount G (2r) ≤ (2r−1)!!·|G|^r` was proven only
*conditionally* on the residual `H` (every zero-sum `2r`-tuple is antipodally paired). This file
**discharges `H` outright** for any set of `2^k`-th roots of unity in a characteristic-zero field, by
composing two now-landed bricks:

* `LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero` — a vanishing multiset sum of `2^k`-th
  roots is antipodally balanced (`count w = count (−w)`);
* `NegationClosedPairingLifting.exists_isPairing_of_count_balanced` — count-balance lifts to an
  index-level fixed-point-free involution `σ` with `c (σ i) = − c i`.

Together they give the antipodal pairing `H` requires, so `zeroSumCount_le_doubleFactorial` fires
unconditionally:

> `zeroSumCount_le_doubleFactorial_dyadic` :  for `G ⊆ μ_{2^k}` over a char-0 field and any `r`,
> `zeroSumCount G (2r) ≤ (2r−1)!!·|G|^r`.

For a negation-closed `G` this is exactly the `r`-fold additive-energy bound `E_r(G) ≤ (2r−1)!!·|G|^r`
(`zeroSumCount G (2r) = E_r(G)` via the `(v,w) ↦ (v,−w)` bijection). It closes the dyadic case of K1
with **no residual** — the energy/AVERAGE side of the prize machinery (NOT the open W4 worst-case bound).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset Nat
open ArkLib.ProximityGap.NegationClosedWalk

namespace ArkLib.ProximityGap.NegationClosedWalk

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

/-- A `2^k`-th root of unity (`k ≥ 1`) is never self-antipodal: `z ≠ −z` (char 0 ⟹ `2 ≠ 0`, and a
root of unity is nonzero). -/
theorem root_ne_neg {k : ℕ} (hk : 1 ≤ k) {z : L} (hz : z ^ (2 ^ k) = 1) : z ≠ - z := by
  intro hself
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by positivity)] at hz
    exact zero_ne_one hz
  exact hz0 (by linear_combination (1 / 2 : L) * hself)

/-- **The dyadic K1 bound, unconditional.** For a finset `G` of `2^k`-th roots of unity (`k ≥ 1`) in a
characteristic-zero field, the zero-sum `2r`-tuple count is at most `(2r−1)!!·|G|^r`. The antipodal
residual `H` is discharged by Lam–Leung (`count_antipodal_of_sum_eq_zero`) composed with the
index-involution lift (`exists_isPairing_of_count_balanced`). -/
theorem zeroSumCount_le_doubleFactorial_dyadic {k r : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) :
    zeroSumCount G (2 * r) ≤ (2 * r - 1)‼ * G.card ^ r := by
  refine zeroSumCount_le_doubleFactorial G ?_
  intro c hc hsum
  rw [Fintype.mem_piFinset] at hc
  have hMroots : ∀ z ∈ (Finset.univ.val.map c), z ^ (2 ^ k) = 1 := by
    intro z hz
    rw [Multiset.mem_map] at hz
    obtain ⟨i, _, rfl⟩ := hz
    exact hG (c i) (hc i)
  have hMsum : (Finset.univ.val.map c).sum = 0 := by
    have : (Finset.univ.val.map c).sum = ∑ i, c i := rfl
    rw [this, hsum]
  have hbal : ∀ w : L, (Finset.univ.val.map c).count w = (Finset.univ.val.map c).count (-w) :=
    LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero (k := k) hMroots hMsum
  have hself : ∀ i, c i ≠ - c i := fun i => root_ne_neg hk (hG (c i) (hc i))
  exact exists_isPairing_of_count_balanced c hbal hself

end ArkLib.ProximityGap.NegationClosedWalk

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount_le_doubleFactorial_dyadic
