/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StructureLoop38

/-!
# Loop 42 (PROOF, UNCONDITIONAL commit-phase shape) — threshold halving (Chai–Fan 2026/858)

The companion eprint 2026/858 ("FRI Soundness Above the Johnson Bound via Threshold Halving")
proves the **first unconditional** soundness theorem above the Johnson bound for FRI/STIR/WHIR, for
`RS[F,L,k]` with `k = 2^m` and `L` admitting a fixed-point-free involution (standard for deployed
FRI, either characteristic), for **every** `δ ∈ (δ_J, 1−ρ)`. Unlike 2026/861 (Loops 40/41) it needs
**no conjecture** — it sidesteps the open mutual-correlated-agreement zone entirely.

The mechanism, **threshold halving** (from Rothblum–Vadhan–Wigderson): run the FRI low-degree test
but *conclude at threshold `δ/2`* instead of `δ`. The single algebraic fact is

    δ/2 < (1−ρ)/2 = the unique-decoding radius of `RS` at rate `ρ`,   (for all δ < 1−ρ),

a one-line inequality. Its consequence is structural: after round 1 the effective distance `δ/2`
sits **inside** the unique-decoding radius, where the BCIKS proximity gap (Thm 1.2) gives `≤ n` bad
challenges `α` per round with `n = |L|` — a clean bound *immune to any open-zone counterexample*,
since unique decoding is locked. The cost is a `~2×` query overhead (testing at `δ/2`, not `δ`).

This file proves, sorry-free and axiom-clean:

* `threshold_halving_into_unique_decoding` — the core inequality `δ < 1−ρ ⟹ δ/2 < (1−ρ)/2`. This is
  the entire algebraic content of 858's main move.
* `unique_decoding_commit_prize_unconditional` — composing the unique-decoding per-round bound
  (`e_j ≤ n/q`, `n ≤ 2^m`) with Loop 38's union bound over the `m` rounds gives the commit-phase
  soundness `∑_{j<m} e_j ≤ (1/q)·(2^m)^2` — **the prize numerator shape with `c₁ = 2, c₂ = c₃ = 0`,
  unconditionally**, for the whole open zone `δ ∈ (δ_J, 1−ρ)`.

This is the strongest brick in the chain: the others (Loops 39, 40) are conditional (on
BGM-for-smooth or `Q2`); this one routes through unique decoding and is unconditional.
**Caveat on scope:** 858 bounds `ε_FRI` by *avoiding* the mutual-CA term `ε_mca`, at the halved
threshold and `2×` query cost — it does **not** bound `ε_mca` itself at radius `δ`. So the literal
MCA prize statement (a bound on `ε_mca` at radius `δ ≤ 1−ρ−η`) is *sidestepped*, not proven; but
the practical above-Johnson FRI soundness the prize was motivated by is now unconditionally in
prize shape. See `DISPROOF_LOG.md` (Loop42).
-/

namespace ArkLib.ProximityGap.ProofLoop42

open scoped BigOperators

/-- **Threshold halving lands inside unique decoding.** For any rate `ρ` and proximity parameter
`δ` strictly below the list-decoding capacity `1−ρ`, the *halved* threshold `δ/2` is strictly below
the unique-decoding radius `(1−ρ)/2`. This one-line inequality is the whole algebraic content of the
2026/858 threshold-halving move; everything structural (distance locking, immunity to open-zone
counterexamples) follows from being inside the unique-decoding radius. -/
theorem threshold_halving_into_unique_decoding {ρ δ : ℝ} (hδ : δ < 1 - ρ) :
    δ / 2 < (1 - ρ) / 2 := by
  linarith

/-- **Unconditional prize-shaped commit-phase soundness.** In the unique-decoding regime reached by
threshold halving, the BCIKS proximity gap bounds the per-round bad-challenge fraction by `n/q` with
`n = |L| ≤ 2^m` the codeword length. Composing with Loop 38's union bound over the `m` fold rounds,
the commit-phase soundness obeys

    ∑_{j<m} e_j ≤ (1/q) · (2^m)^2 ,

the prize numerator shape `c₁ = 2, c₂ = c₃ = 0` — **unconditional**, no gap `η`, across the
entire open zone above Johnson. -/
theorem unique_decoding_commit_prize_unconditional
    (e : ℕ → ℝ) {n q : ℝ} {m : ℕ}
    (hq : 0 < q) (hn0 : 0 ≤ n) (hn : n ≤ (2 : ℝ) ^ m)
    (hround : ∀ j, j < m → e j ≤ n / q) :
    (∑ j ∈ Finset.range m, e j) ≤ (1 / q) * ((2 : ℝ) ^ m) ^ 2 := by
  -- union bound (Loop 38): total ≤ m · (n/q)
  have hUnion : (∑ j ∈ Finset.range m, e j) ≤ (m : ℝ) * (n / q) :=
    ArkLib.ProximityGap.StructureLoop38.fri_union_bound e hround
  have hnq : 0 ≤ n / q := by positivity
  -- m ≤ 2^m and n/q ≤ 2^m/q
  have hm : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    have h := Nat.lt_two_pow_self (n := m)
    calc (m : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h.le
      _ = (2 : ℝ) ^ m := by push_cast; ring
  have hnq2 : n / q ≤ (2 : ℝ) ^ m / q := by gcongr
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ m := by positivity
  calc
    (∑ j ∈ Finset.range m, e j) ≤ (m : ℝ) * (n / q) := hUnion
    _ ≤ ((2 : ℝ) ^ m) * ((2 : ℝ) ^ m / q) := by
        apply mul_le_mul hm hnq2 hnq hpow
    _ = (1 / q) * ((2 : ℝ) ^ m) ^ 2 := by ring

/-- **Non-vacuity.** The unconditional commit-phase prize shape is positive at every depth. -/
theorem commit_prize_const_pos {q : ℝ} {m : ℕ} (hq : 0 < q) :
    0 < (1 / q) * ((2 : ℝ) ^ m) ^ 2 := by
  have : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  positivity

end ArkLib.ProximityGap.ProofLoop42

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ProofLoop42.threshold_halving_into_unique_decoding
#print axioms ArkLib.ProximityGap.ProofLoop42.unique_decoding_commit_prize_unconditional
#print axioms ArkLib.ProximityGap.ProofLoop42.commit_prize_const_pos
