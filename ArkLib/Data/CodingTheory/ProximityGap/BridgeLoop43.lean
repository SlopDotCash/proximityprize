/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BridgeLoop41

/-!
# Loop 43 (BRIDGE) — the orbit-count route that would close the LITERAL `ε_mca` prize

Loop 42 (threshold halving, 2026/858) bounds the FRI soundness `ε_FRI` by *avoiding* the
mutual-correlated-agreement term `ε_mca`. That settles FRI soundness but **sidesteps** the literal
#232 prize, which asks for a bound on `ε_mca` itself at radius `δ ≤ 1−ρ−η`. This file records the
*only* route that closes the literal prize — the orbit-counting bound of 2026/861 — and makes
precise exactly what is still missing.

The MCA term is a normalized bad-set count: `ε_ca(f) = |V_δ(f)| / q²` (2026/861, Conjecture 1.1),
where `V_δ(f)` is the set of bad two-round challenges. Theorem 2.1 (sound in Loop 41) forces
`V_δ` to be a **union of `⟨ω^{b−a}⟩`-orbits, each of explicit size `S = n₁/gcd(b−a, n₁) ≤ 2^m`**.
Hence, writing `N` for the number of distinct bad orbits,

    |V_δ(f)| ≤ N · S ,   so   ε_mca = |V_δ|/q² ≤ N·S/q² ≤ N·2^m/q² .

If the orbit count is bounded, `N ≤ K`, then (using `2^m ≤ q`, always true at deployment scale)

    ε_mca ≤ K · 2^m / q² ≤ K / q ,

which is **exactly the Conjecture-1.1 prize shape `ε_ca ≤ K_ρ/q`** — a bound on `ε_mca` itself, the
literal prize, not a sidestep. This file proves that arithmetic reduction, axiom-clean.

So the literal prize closes **iff the bad-orbit count `N` is bounded by a constant `K_ρ`**. Per
2026/861 this is:

* **unconditional for sparse (3-position) inputs** (their Layer 1, the twin of our Loops 33/34);
* **conjectural for general inputs** — this is precisely conjecture **Q2** (sparse-worst-case
  dominance): the worst-case orbit count is dominated by the sparse case. Empirically verified at
  scale `(32,8)`, unproven in general.

This brick therefore pins the entire remaining open content of the literal prize to a single,
sharply stated quantity: an `n`-uniform bound on the number of bad challenge-orbits. See
`DISPROOF_LOG.md` (Loop43).
-/

namespace ArkLib.ProximityGap.BridgeLoop43

/-- **Orbit-counting bound on the MCA term.** If the bad-challenge set `V_δ` has cardinality at most
`N · S` (`N` orbits of size `≤ S`, the structure Theorem 2.1 / Loop 41 forces), then the MCA term
`|V_δ|/q²` is at most `N·S/q²`. -/
theorem mca_orbit_count_bound {q Vcard N S : ℝ} (hq : 0 < q) (hcard : Vcard ≤ N * S) :
    Vcard / q ^ 2 ≤ N * S / q ^ 2 := by
  gcongr

/-- **Bounded orbit count ⟹ the literal `ε_mca` prize.** If the bad set is at most `N · S` with the
orbit count `N ≤ K` and the orbit size `S ≤ 2^m` (Theorem 2.1's `n₁/gcd ≤ 2^m`), then at any field
with `2^m ≤ q` the MCA term obeys `|V_δ|/q² ≤ K/q` — the Conjecture-1.1 prize shape, a bound on
`ε_mca` itself. This is the route that closes the *literal* prize; the only missing input is the
constant orbit-count bound `N ≤ K` (unconditional for sparse inputs; `= Q2` in general). -/
theorem mca_prize_of_bounded_orbit_count
    {q K N S Vcard : ℝ} {m : ℕ}
    (hq : 0 < q) (hKnn : 0 ≤ K) (hSnn : 0 ≤ S)
    (hcard : Vcard ≤ N * S) (hN : N ≤ K) (hS : S ≤ (2 : ℝ) ^ m)
    (hqbig : (2 : ℝ) ^ m ≤ q) :
    Vcard / q ^ 2 ≤ K / q := by
  have hNS : N * S ≤ K * (2 : ℝ) ^ m := mul_le_mul hN hS hSnn hKnn
  have hKq : K * (2 : ℝ) ^ m ≤ K * q := mul_le_mul_of_nonneg_left hqbig hKnn
  have hVKq : Vcard ≤ K * q := le_trans hcard (le_trans hNS hKq)
  calc
    Vcard / q ^ 2 ≤ (K * q) / q ^ 2 := by gcongr
    _ = K / q := by field_simp

/-- **Non-vacuity / sanity.** With a genuine positive constant orbit-count budget `K > 0` and
`q > 0`, the resulting prize bound `K/q` is positive — the reduction is not the trivial `0`. -/
theorem mca_prize_bound_pos {q K : ℝ} (hq : 0 < q) (hK : 0 < K) : 0 < K / q := by positivity

end ArkLib.ProximityGap.BridgeLoop43

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeLoop43.mca_orbit_count_bound
#print axioms ArkLib.ProximityGap.BridgeLoop43.mca_prize_of_bounded_orbit_count
#print axioms ArkLib.ProximityGap.BridgeLoop43.mca_prize_bound_pos
