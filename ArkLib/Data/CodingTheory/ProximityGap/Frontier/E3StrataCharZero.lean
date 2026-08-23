/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._E3Assembly
import Mathlib.Tactic

/-!
# The char-0 `E₃`-exact strata producer (#444)

This file packages the machine-checked, exact closed form of the **6th period moment**
`E₃(μ_n) = 15n³ − 45n² + 40n` — the input hypothesis of the already-shipped r=2 cross-step
rung (`Frontier/CrossStepRungTwo.lean`).

## What is proven (axiom-clean: `propext, Classical.choice, Quot.sound`; no gaps)

For a negation-closed finite `G ⊆ F` avoiding `0` (char ≠ 2), the count of antipodally
count-balanced 6-tuples over `G` is exactly
`negSymCount G 6 = 15·|G|³ − 45·|G|² + 40·|G|` (`negSymCount_six_closed`).

This is assembled from a complete combinatorial chain, every link axiom-clean:
* the three per-image-size value multiplicities `20 / 360 / 720`
  (`image_count_two`, `E3Shape21Scratch.image_count_four`, `image_count_six`);
* the negation-closed `2i`-subset count `C(|G|/2, i)` (`E3SubsetCount.negClosed_subset_count`);
* the partition `negSymCount_partition_negClosed`, closed by `strata_sum_eq_closed`.

The **char-free converse** `E3NegSymConverse.sum_eq_zero_of_fiber_balanced` (count-balanced
⟹ zero-sum) is the link from `negSymCount` to the energy `rEnergy μ_n 3` (it certifies that
every negation-symmetric tuple is a genuine zero-sum 6-tuple of roots of unity).

## Honest scope — this is NOT the proximity prize

The producer is **char-0 modest**. Identifying `negSymCount μ_n 6` with the full energy
`rEnergy μ_n 3 = E₃(μ_n)` needs the *forward* direction (zero-sum ⟹ count-balanced), which is
the char-0 Lam–Leung theorem (vanishing sums of `2`-power roots of unity decompose into
negation pairs) — true in char 0, but the **char-`p` transfer at depth `r ≈ ln q`** is the
open `RepThree` obstruction, i.e. the BGK/Burgess `√`-cancellation wall
`M(μ_n) ≤ C√(n·log(p/n))`. That wall is the genuine open research of issue #444 and is **not**
crossed here.
-/

set_option autoImplicit false


open ArkLib.ProximityGap.Frontier.E3StrataCount (negSymCount)

namespace ArkLib.ProximityGap.Frontier.E3StrataCharZero

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **Char-0 `E₃`-exact producer.** For a negation-closed `G ⊆ F` (`0 ∉ G`, char ≠ 2), the number
of antipodally count-balanced 6-tuples over `G` is the exact polynomial `15·|G|³ − 45·|G|² + 40·|G|`
(over `ℤ`, since the cubic dips below `0`). In char 0 with `G = μ_n` this is `E₃(μ_n)`, the 6th
period moment and the r=2 cross-step rung input. -/
theorem negSymCount_six_closed (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ z ∈ G, -z ∈ G) :
    (negSymCount G 6 : ℤ)
      = 15 * (G.card : ℤ) ^ 3 - 45 * (G.card : ℤ) ^ 2 + 40 * (G.card : ℤ) :=
  E3Assembly.negSymCount_eq_closed G h2 h0 hneg

end ArkLib.ProximityGap.Frontier.E3StrataCharZero

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.E3StrataCharZero.negSymCount_six_closed
