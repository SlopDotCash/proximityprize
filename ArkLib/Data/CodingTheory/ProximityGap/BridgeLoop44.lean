/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BridgeLoop43

/-!
# Loop 44 (BRIDGE) — a POLYNOMIAL orbit count already suffices arithmetically (weaker than Q2)

Loop 43 showed, in an arithmetic model, that the prize shape follows if the bad-challenge
**orbit count `N` is bounded by a constant `K`** (`N ≤ K ⟹ Vcard/q² ≤ K/q`). That constant
bound is exactly Chai–Fan 2026/861's conjecture **Q2** (the `O(1)/|F|` target). But the #232 prize is *weaker* than `O(1)/|F|`: it
permits any `poly(2^m, 1/ρ, 1/η)/q` bound. This file makes that gap precise.

If the orbit count is merely **polynomial**, `N ≤ (2^m)^d`, then (orbit size `S ≤ 2^m`, Thm 2.1,
any field `q ≥ 1`)

    ε_mca = |V_δ|/q² ≤ N·S/q² ≤ (2^m)^{d+1}/q² ≤ (1/q) · (2^m)^{d+1} ,

still prize shape — now with `c₁ = d+1` instead of `c₁ = 0`. So:

* **a polynomial orbit-count bound is sufficient for the prize shape** in this arithmetic model
  (`mca_prize_of_poly_orbit_count`); no claim is made that it is necessary;
* **Q2 (constant orbit count) trivially implies the polynomial bound**
  (`q2_implies_poly_orbit_count`), so the polynomial hypothesis is *weaker* than the constant one
  (Loop 43's "iff" reading is therefore unsupported; see
  `BridgeLoop43.bounded_orbit_count_not_necessary`).

**Scope (audit correction, 2026-10-28, PG-053).** As in Loop 43, all quantities are arbitrary
reals: this file does not identify `Vcard / q²` with the repository's actual MCA error, does not
prove `Vcard ≤ N·S` for an actual bad set, and does not fix how `d` and `m` depend on `ρ, η` and
the domain.  The protocol/event bridge is a separate obligation.

Why this matters for the open core (informal, not proved here). In the Johnson range the list
size is `poly(n)` by GS / BCIKS 2025/2055, and one expects the bad set, hence the orbit count, to
be polynomial there too (matching Loops 9/11/13); the event-level transfer from list size to
`|V_δ|` is not formalized in this file.  In the small-gap band `0 < η ≤ η₀` this arithmetic
reduction does **not** need 861's constant `K_ρ` — a polynomial `N ≤ (2^m)^d` is enough. This
separates 861's deployment-grade `O(1)/|F|` (which Q2 would give) from the #232 prize's
`poly(2^m)/|F|` (for which a polynomial `N` suffices). See
`docs/research/proximity-gap/DISPROOF_LOG.md` (Loop44).
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

/-- **Positivity of the right-hand side (sanity only).** The prize bound is positive.  This is not
a witness that the hypotheses of `mca_prize_of_poly_orbit_count` hold for an actual MCA bad set. -/
theorem poly_prize_bound_pos {q : ℝ} {m d : ℕ} (hq : 0 < q) :
    0 < (1 / q) * ((2 : ℝ) ^ m) ^ (d + 1) := by positivity

end ArkLib.ProximityGap.BridgeLoop44

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeLoop44.mca_prize_of_poly_orbit_count
#print axioms ArkLib.ProximityGap.BridgeLoop44.q2_implies_poly_orbit_count
#print axioms ArkLib.ProximityGap.BridgeLoop44.poly_prize_bound_pos
