/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E3StrataCharZero
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.BalancedCountConcrete

/-!
# The two independent char-0 `E₃` proofs agree (#444)

`E₃(μ_n) = 15n³ − 45n² + 40n`, the depth-3 additive energy of `n` roots of unity, now has **two
independent** machine-checked char-0 proofs in tree:

* the **strata** route — `E3StrataCharZero.negSymCount_six_closed`: counts antipodally count-balanced
  6-tuples of a negation-closed value set `G` and evaluates the partition-by-image directly;
* the **convolution** route — `BalancedCountConcrete.balancedCount_eq_E3`: a field-free `ℕ → ℕ → ℤ`
  add-one-antipodal-class recursion `balancedCount`, solved in closed form by induction.

They count the same object two different ways. This file records the single bridge that says so:
with `|G| = 2m` (i.e. `m` antipodal pairs), the field-tuple strata count equals the abstract
convolution count. Pure transitivity through the shared closed form — it consumes **no** open
hypothesis (in particular none of the char-`p` √-cancellation core of #444).
-/

set_option autoImplicit false


open ArkLib.ProximityGap.Frontier.E3StrataCount (negSymCount)
open ArkLib.ProximityGap.Frontier.BalancedCountConcrete (balancedCount)

namespace ArkLib.ProximityGap.Frontier.E3RouteBridge

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **The strata and convolution char-0 `E₃` counts agree.** For a negation-closed `G ⊆ F`
(`0 ∉ G`, char ≠ 2) with `|G| = 2m`, the strata count of count-balanced 6-tuples equals the
abstract antipodal-class convolution count: `negSymCount G 6 = balancedCount 6 m`. Both routes
evaluate to `15·(2m)³ − 45·(2m)² + 40·(2m)`; the bridge is their transitivity. -/
theorem e3_routes_agree (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ z ∈ G, -z ∈ G) {m : ℕ} (hm : G.card = 2 * m) :
    (negSymCount G 6 : ℤ) = balancedCount 6 m := by
  rw [E3StrataCharZero.negSymCount_six_closed G h2 h0 hneg,
      BalancedCountConcrete.balancedCount_eq_E3 m, hm]
  push_cast
  ring

/-! ### Non-vacuity sign: the bridge fires on a concrete value set. -/

private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- **Golden path** — `μ₂ = {1,-1} = {1,4} ⊂ ZMod 5` (`m = 1`): the bridge fires,
`negSymCount {1,4} 6 = balancedCount 6 1`. A standing witness that `e3_routes_agree` is not vacuous. -/
example : (negSymCount ({1, 4} : Finset (ZMod 5)) 6 : ℤ) = balancedCount 6 1 :=
  e3_routes_agree {1, 4} (by decide) (by decide) (by decide) (by decide)

/-- **Edge — a 4-element set** `{1,2,3,4} = {±1,±2} ⊂ ZMod 5` (`m = 2`, `|G| = 4`):
`negSymCount {1,2,3,4} 6 = balancedCount 6 2` (both `400`). -/
example : (negSymCount ({1, 2, 3, 4} : Finset (ZMod 5)) 6 : ℤ) = balancedCount 6 2 :=
  e3_routes_agree {1, 2, 3, 4} (by decide) (by decide) (by decide) (by decide)

/-- **Edge — a different field** `{1,-1} = {1,12} ⊂ ZMod 13` (`m = 1`): the bridge is not
tied to one field. -/
example : (negSymCount ({1, 12} : Finset (ZMod 13)) 6 : ℤ) = balancedCount 6 1 :=
  e3_routes_agree {1, 12} (by decide) (by decide) (by decide) (by decide)

/-- **Adversarial guard** — the `|G| = 2m` hypothesis is load-bearing: numerically
`negSymCount {1,4} 6 = 20 ≠ 400 = balancedCount 6 2`, so the bridge must NOT apply at `m = 2` to a
2-element set. Indeed its hypothesis `|{1,4}| = 2*2` is decidably FALSE, so the misuse is refused. -/
example : ¬ (({1, 4} : Finset (ZMod 5)).card = 2 * 2) := by decide

end ArkLib.ProximityGap.Frontier.E3RouteBridge

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.E3RouteBridge.e3_routes_agree
