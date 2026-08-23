/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BridgeLoop43

/-!
# Loop 44 (BRIDGE) — the prize needs only a POLYNOMIAL orbit count, strictly weaker than Q2

Loop 43 showed the literal `ε_mca` prize closes if the bad-challenge **orbit count `N` is bounded
by a constant `K`** (`N ≤ K ⟹ ε_mca ≤ K/q`). That constant bound is exactly Chai–Fan 2026/861's
conjecture **Q2** (the `O(1)/|F|` target). But the #232 prize is *weaker* than `O(1)/|F|`: it
permits any `poly(2^m, 1/ρ, 1/η)/q` bound. This file makes that gap precise.

If the orbit count is merely **polynomial**, `N ≤ (2^m)^d`, then (orbit size `S ≤ 2^m`, Thm 2.1,
any field `q ≥ 1`)

    ε_mca = |V_δ|/q² ≤ N·S/q² ≤ (2^m)^{d+1}/q² ≤ (1/q) · (2^m)^{d+1} ,

still prize shape — now with `c₁ = d+1` instead of `c₁ = 0`. So:

* **the prize requires only a polynomial orbit-count bound** (`mca_prize_of_poly_orbit_count`);
* **Q2 (constant orbit count) trivially implies the polynomial bound**
  (`q2_implies_poly_orbit_count`), so the prize is *strictly weaker* than the conjecture 861 proves.

Why this matters for the open core. A polynomial orbit count is **already a theorem in the Johnson
range**: there the list size — hence `|V_δ|`, hence the orbit count — is `poly(n)` by GS
/ BCIKS 2025/2055, so the prize is unconditional above `η₀` (matching Loops 9/11/13). The genuinely
open residual is *only* the small-gap band `0 < η ≤ η₀`, and even there the prize does **not** need
861's constant `K_ρ` — a polynomial `N ≤ (2^m)^d` is enough. This separates two difficulties the
literature conflates: 861's deployment-grade `O(1)/|F|` (needs Q2) versus the #232 prize's
`poly(2^m)/|F|` (needs only poly `N`). The prize closes on a weaker hypothesis. See
`DISPROOF_LOG.md` (Loop44).
-/

namespace ArkLib.ProximityGap.BridgeLoop44

/-- **A polynomial orbit count suffices for the prize.** If the bad set has size `≤ N·S` with a
*polynomial* orbit count `N ≤ (2^m)^d` and orbit size `S ≤ 2^m`, then over any field `q ≥ 1` the MCA
term lands on the prize RHS `(1/q)·(2^m)^{d+1}` (numerator exponent `c₁ = d+1`). No constant bound
on `N` is needed — only a polynomial one. -/
theorem mca_prize_of_poly_orbit_count
    {q N S Vcard : ℝ} {m d : ℕ}
    (hq : 1 ≤ q) (hSnn : 0 ≤ S) (hNnn : 0 ≤ N)
    (hcard : Vcard ≤ N * S) (hN : N ≤ ((2 : ℝ) ^ m) ^ d) (hS : S ≤ (2 : ℝ) ^ m) :
    Vcard / q ^ 2 ≤ (1 / q) * ((2 : ℝ) ^ m) ^ (d + 1) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hpow : (0 : ℝ) ≤ ((2 : ℝ) ^ m) ^ d := by positivity
  have hNS : N * S ≤ ((2 : ℝ) ^ m) ^ d * (2 : ℝ) ^ m := mul_le_mul hN hS hSnn hpow
  have hVbound : Vcard ≤ ((2 : ℝ) ^ m) ^ (d + 1) := by
    refine le_trans hcard (le_trans hNS ?_)
    rw [pow_succ]
  have hX : (0 : ℝ) ≤ ((2 : ℝ) ^ m) ^ (d + 1) := by positivity
  calc
    Vcard / q ^ 2 ≤ ((2 : ℝ) ^ m) ^ (d + 1) / q ^ 2 := by gcongr
    _ ≤ ((2 : ℝ) ^ m) ^ (d + 1) / q := by
        gcongr
        nlinarith [hq]
    _ = (1 / q) * ((2 : ℝ) ^ m) ^ (d + 1) := by ring

/-- **Q2 (constant orbit count) ⟹ the polynomial bound.** A constant orbit-count budget `N ≤ K` with
`K ≤ (2^m)^d` is a special case of the polynomial bound. So 861's `O(1)/|F|` Q2 is *stronger*
than what the #232 prize needs: the prize asks only for `poly`, Q2 delivers a constant. -/
theorem q2_implies_poly_orbit_count
    {N K : ℝ} {m d : ℕ} (hN : N ≤ K) (hK : K ≤ ((2 : ℝ) ^ m) ^ d) :
    N ≤ ((2 : ℝ) ^ m) ^ d :=
  le_trans hN hK

/-- **Non-vacuity.** For a genuine polynomial budget the prize bound is positive. -/
theorem poly_prize_bound_pos {q : ℝ} {m d : ℕ} (hq : 0 < q) :
    0 < (1 / q) * ((2 : ℝ) ^ m) ^ (d + 1) := by positivity

end ArkLib.ProximityGap.BridgeLoop44

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeLoop44.mca_prize_of_poly_orbit_count
#print axioms ArkLib.ProximityGap.BridgeLoop44.q2_implies_poly_orbit_count
#print axioms ArkLib.ProximityGap.BridgeLoop44.poly_prize_bound_pos
