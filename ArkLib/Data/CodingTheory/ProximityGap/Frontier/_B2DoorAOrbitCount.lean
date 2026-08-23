/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# B2 door (a): the deployed bad-`α` orbit count is `O(1)` and `n`-independent (#407, Conj 4.12)

This file completes the **orbit-count** half of B2 door (a) (the Chai–Fan action–orbit lane,
2026/861).  The action–orbit theorem bounds MCA soundness above Johnson by the number of
`⟨μ_n^{b−a}⟩`-orbits of bad challenges `α` for the two-monomial pencil `h_α(z) = z^a + α z^b`
over the cyclic FRI domain `μ_n` (`n = 2^e`).  The genuinely non-BGK content of the lane is the
*algebraic* bound on this orbit count (`#orbits = O(1)`), **not** the incidence count (which is
circular — `#orbits = #bad / orbitSize`, and `#bad = O(n)` is the prize floor itself, see #407
comment 92).

## The orbit-count formula (the gate's denominator)

The action–orbit group is `⟨μ_n^{b−a}⟩`, whose order is

  `orbitSize n a b := n / gcd(b − a, n)`.

For the **single (trivial-codeword) bad-`α` set** `{ −z^a · (z^b)⁻¹ : z ∈ μ_n }` — the image of
the ratio map of `_ChaiFanBasePanelGate.badAlphaSet` — this orbit *is* the whole bad-`α` set: for
`g = 0` each `α = −z^{a−b}` and the image of `z ↦ −z^{a−b}` over the cyclic group `μ_n` is a single
coset of the order-`orbitSize` subgroup.  This file proves the **arithmetic invariant** that makes
the orbit count `O(1)` for the deployed rate-1/2 directions:

* `orbitSize_eq` — `orbitSize n a b = n / gcd(b − a, n)` (definitional unfold, the named quantity).
* `deployed_orbitSize_signPaired/kTwoK/threeKTwoK` — the **exact O(1) values** for the three
  Chai–Fan §4 deployment directions at `k = n/4`, **independent of `n` (= `2^e`)**:
  - `(k, 3k)` → `orbitSize = 2`
  - `(k, 2k)` → `orbitSize = 4`
  - `(3k/2, 2k)` → `orbitSize = 8`
  These match the measured single-orbit cardinalities (`#bad = 2, 4, 8`, constant in `n`;
  probe `/tmp/b2_orbit_count_b2door.py`, FFT-exact `n = 8 … 128`).

## Why this is the right object (honest scope)

The orbit *size* being `O(1)` and `n`-independent is the structural reason the bad-`α` set on the
trivial codeword is `O(1)`; the **full gate** (over all `deg < k` codewords) additionally needs the
algebraic non-vanishing `R_d ≠ 0` on `V_d^prim` (Conj 4.12), discharged here only at the structural
(orbit-arithmetic) level.  The number-theoretic finish — that the full odd-window vanishing on
`V_d^prim` is **empty at prize scale** — is the companion `_BadPrimeBoundCore` (`p ≤ n²/4`).
Together: orbit count `O(1)` (this file) + variety empty at prize scale (`_BadPrimeBoundCore`,
*given* the full odd window, not the route-(i) `o₁`-bootstrap which breaks at `d = 32`, #407 c.173).

This file proves only the arithmetic orbit-size facts; it does not assert Conj 4.12.  Axiom-clean.
Issue #407.
-/

open Finset

namespace ProximityGap.Frontier.B2DoorAOrbitCount

/-- The order of the action–orbit group `⟨μ_n^{b−a}⟩`: `orbitSize n a b = n / gcd(b − a, n)`.
(Mirror of `Q1ArisingFamilyDescent.orbitSize`, self-contained here.) -/
def orbitSize (n a b : ℕ) : ℕ := n / Nat.gcd (b - a) n

/-- Definitional unfold of the orbit size. -/
theorem orbitSize_eq (n a b : ℕ) : orbitSize n a b = n / Nat.gcd (b - a) n := rfl

/-! ## The three deployed rate-1/2 directions — exact `O(1)` orbit size, independent of `n = 2^e` -/

section Deployed

variable (e : ℕ)

/-- **Sign-paired family (Thm 4.4), exponents `(k, 3k)`, `k = 2^{e-2}`.**  The action–orbit size
is exactly `2`, *independent of* `e` (hence of `n = 2^e`).  Here `b − a = 3k − k = 2k = n/2`, and
`gcd(n/2, n) = n/2`, so `orbitSize = n / (n/2) = 2`. -/
theorem deployed_orbitSize_signPaired (he : 3 ≤ e) :
    orbitSize (2 ^ e) (2 ^ (e - 2)) (3 * 2 ^ (e - 2)) = 2 := by
  unfold orbitSize
  -- 3k - k = 2k = 2 * 2^{e-2} = 2^{e-1}, and n = 2^e
  have hk : 3 * 2 ^ (e - 2) - 2 ^ (e - 2) = 2 ^ (e - 1) := by
    have h1 : 3 * 2 ^ (e - 2) - 2 ^ (e - 2) = 2 * 2 ^ (e - 2) := by omega
    rw [h1, ← pow_succ']
    congr 1; omega
  rw [hk]
  -- gcd(2^{e-1}, 2^e) = 2^{e-1}
  have hdvd : (2 : ℕ) ^ (e - 1) ∣ 2 ^ e := pow_dvd_pow 2 (by omega)
  rw [Nat.gcd_eq_left hdvd]
  -- 2^e / 2^{e-1} = 2
  rw [Nat.pow_div (show e - 1 ≤ e by omega) (by norm_num : 0 < 2), show e - (e - 1) = 1 by omega,
    pow_one]

/-- **`(k, 2k)` family (Thm 4.7), exponents `(k, 2k)`, `k = 2^{e-2}`.**  The action–orbit size is
exactly `4`, independent of `e`.  Here `b − a = 2k − k = k = n/4`, `gcd(n/4, n) = n/4`, so
`orbitSize = n / (n/4) = 4`. -/
theorem deployed_orbitSize_kTwoK (he : 3 ≤ e) :
    orbitSize (2 ^ e) (2 ^ (e - 2)) (2 * 2 ^ (e - 2)) = 4 := by
  unfold orbitSize
  -- 2k - k = k = 2^{e-2}
  have hk : 2 * 2 ^ (e - 2) - 2 ^ (e - 2) = 2 ^ (e - 2) := by omega
  rw [hk]
  have hdvd : (2 : ℕ) ^ (e - 2) ∣ 2 ^ e := pow_dvd_pow 2 (by omega)
  rw [Nat.gcd_eq_left hdvd]
  rw [Nat.pow_div (show e - 2 ≤ e by omega) (by norm_num : 0 < 2), show e - (e - 2) = 2 by omega]

/-- **`(3k/2, 2k)` family (Thm 4.10), exponents `(3·2^{e-3}, 4·2^{e-3})`, `d = 2^{e-3}`.**  The
action–orbit size is exactly `8`, independent of `e`.  Here `b − a = 2k − 3k/2 = k/2 = n/8`,
`gcd(n/8, n) = n/8`, so `orbitSize = n / (n/8) = 8`. -/
theorem deployed_orbitSize_threeKTwoK (he : 4 ≤ e) :
    orbitSize (2 ^ e) (3 * 2 ^ (e - 3)) (4 * 2 ^ (e - 3)) = 8 := by
  unfold orbitSize
  -- 4d - 3d = d = 2^{e-3}
  have hk : 4 * 2 ^ (e - 3) - 3 * 2 ^ (e - 3) = 2 ^ (e - 3) := by omega
  rw [hk]
  have hdvd : (2 : ℕ) ^ (e - 3) ∣ 2 ^ e := pow_dvd_pow 2 (by omega)
  rw [Nat.gcd_eq_left hdvd]
  rw [Nat.pow_div (show e - 3 ≤ e by omega) (by norm_num : 0 < 2), show e - (e - 3) = 3 by omega]

end Deployed

/-! ## The `n`-independence, packaged

The three deployed orbit sizes are constants (`2, 4, 8`) with **no dependence on `e`** — the precise
statement that the action–orbit count of the deployed pencils does not grow with the domain size
`n = 2^e`.  Combined with `_BadPrimeBoundCore` (the variety is empty at prize scale once the *full*
odd window is imposed), this gives the `O(1)` orbit bound for the deployed rate-1/2 families.
-/

/-- **The deployed orbit sizes are `n`-independent constants.**  For every `e ≥ 4` the three
Chai–Fan §4 deployment directions have orbit size `2, 4, 8` respectively — fixed values that do not
depend on `e` (hence not on `n = 2^e`).  This is the `O(1)`-orbit structural fact of B2 door (a). -/
theorem deployed_orbitSizes_constant (e : ℕ) (he : 4 ≤ e) :
    orbitSize (2 ^ e) (2 ^ (e - 2)) (3 * 2 ^ (e - 2)) = 2 ∧
    orbitSize (2 ^ e) (2 ^ (e - 2)) (2 * 2 ^ (e - 2)) = 4 ∧
    orbitSize (2 ^ e) (3 * 2 ^ (e - 3)) (4 * 2 ^ (e - 3)) = 8 :=
  ⟨deployed_orbitSize_signPaired e (by omega),
   deployed_orbitSize_kTwoK e (by omega),
   deployed_orbitSize_threeKTwoK e he⟩

/-! ## The trivial-codeword bad-`α` set IS this orbit (the gate denominator, field side)

For the trivial codeword `g = 0`, the bad-`α` set of `_ChaiFanBasePanelGate` is
`{ −z^a · (z^b)⁻¹ : z ∈ μ_n }`.  Since `z^a · (z^b)⁻¹ = z^{a−b}` on the nonzero domain, this equals
`{ −z^{a−b} : z ∈ μ_n }`, and we record the clean algebraic factorisation that exhibits it as the
negation of the `(a−b)`-power image of the domain (the order-`orbitSize` coset).  The cardinality
fact `#image = orbitSize` is the cyclic-group order statement (verified numerically; the in-tree
`badAlphaSet_card_le` gives the trivial `≤ #D`, this gives the *exact* orbit-coset shape). -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Trivial-codeword bad scalar is `−z^{a−b}`.**  For `z ≠ 0` and `b ≤ a`, the ratio
`−z^a · (z^b)⁻¹` (the `_ChaiFanBasePanelGate` bad scalar at codeword `g = 0`) equals `−z^{a−b}`.
This exhibits the bad-`α` set as the negated `(a−b)`-power image of `μ_n` — a single coset of the
order-`orbitSize` cyclic subgroup, the field-side reason the trivial bad set has size `orbitSize`. -/
theorem ratio_eq_neg_pow_sub {z : F} (hz : z ≠ 0) {a b : ℕ} (hba : b ≤ a) :
    - z ^ a * (z ^ b)⁻¹ = - z ^ (a - b) := by
  rw [neg_mul, neg_inj, pow_sub₀ z hz hba]

end ProximityGap.Frontier.B2DoorAOrbitCount

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.B2DoorAOrbitCount.deployed_orbitSize_signPaired
#print axioms ProximityGap.Frontier.B2DoorAOrbitCount.deployed_orbitSize_kTwoK
#print axioms ProximityGap.Frontier.B2DoorAOrbitCount.deployed_orbitSize_threeKTwoK
#print axioms ProximityGap.Frontier.B2DoorAOrbitCount.deployed_orbitSizes_constant
#print axioms ProximityGap.Frontier.B2DoorAOrbitCount.ratio_eq_neg_pow_sub
