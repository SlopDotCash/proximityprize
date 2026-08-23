/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StructureLoop38

/-!
# Loop 40 (PROOF, conditional) — the second path: sparse-worst-case dominance (Q2) ⟹ prize

A June-2026 literature pass surfaced Chai–Fan, eprint 2026/861 ("Action–Orbit FRI Soundness Above
the Johnson Radius"), which independently reaches the same frontier this disproof log reached:

* **Unconditional for sparse adversary inputs** — the per-round FRI/proximity error on a plain
  Reed–Solomon code over the *cyclic* (smooth multiplicative-subgroup) evaluation domain is bounded
  by a constant `C/|F|`, above the Johnson radius, when the adversary input is *sparse*. This is the
  literature counterpart of Loops 33/34 (bounded sparse spikes are absorbed).
* **General inputs reduce to one conjecture (Q2)** — "sparse-worst-case dominance": the worst-case
  proximity error is dominated by the sparse-input error. This `Q2` is the literature name for the
  same open core this log isolated (does the worst case reduce to the provably-safe sparse case).

This file records the resulting **second independent conditional path** to the prize, parallel to
Loop 39's BGM route. Composing the unconditional sparse bound (`C/q`) with `Q2` (general `≤` sparse)
and Loop 38's union bound over the `m` fold rounds gives the prize RHS

    err ≤ ∑_{j<m} e_j ≤ m · (C/q) ≤ (2^m) · (C/q) = (1/q) · (2^m)^1 · C ,

i.e. the single constant triple `c₁ = 1, c₂ = c₃ = 0` — even cleaner than Loop 39 (no `η` factor),
because the action-orbit bound is `q`-independent and gap-free. So under `Q2` the prize holds across
the whole band with a *constant* numerator.

**Honest status / caveats.** This brick formalizes only the *logical structure* of the reduction —
that `Q2` + the sparse bound + the union bound deliver the prize. It does **not** verify Chai–Fan's
unconditional sparse claim or their action-orbit lemma (the full eprint PDF was inaccessible at the
time of writing; the abstract advertises a "five-line proof above Johnson", a claim that warrants
scrutiny before trust). `Q2` is itself an **unproven conjecture**, exactly the open core.
Two independent conditional paths now land the prize — BGM-for-smooth (Loop 39) and sparse-dominance
`Q2` (this file) — which strengthens the "leans TRUE" position without closing it. Do **not** treat
the prize as resolved. See `DISPROOF_LOG.md` (Loop40, and the updated LITERATURE FRONTIER).
-/

namespace ArkLib.ProximityGap.ProofLoop40

open scoped BigOperators

/-- **Sparse-dominance conditional prize mass.** Given the Chai–Fan unconditional *sparse* per-round
bound `eSparse ≤ C/q` and the `Q2` sparse-worst-case dominance (`∀ j < m, e j ≤ eSparse`),
the union-bound total error over the `m` fold rounds lands on the prize RHS

    ∑_{j<m} e j ≤ (1/q) · (2^m)^1 · C ,

with the single constant triple `c₁ = 1, c₂ = c₃ = 0` — a `q`-independent constant numerator, valid
across the entire band. The per-round bound is carried *once* (the constant `C`) and accumulated
*additively* (Loop 38). -/
theorem sparse_dominance_prize_mass
    (e : ℕ → ℝ) {eSparse C q : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hq : 0 < q)
    (hsparse : eSparse ≤ C / q)
    (hQ2 : ∀ j, j < m → e j ≤ eSparse) :
    (∑ j ∈ Finset.range m, e j) ≤ (1 / q) * ((2 : ℝ) ^ m) ^ 1 * C := by
  -- Q2 + sparse bound: each per-round event is ≤ C/q
  have hround : ∀ j, j < m → e j ≤ C / q := fun j hj => le_trans (hQ2 j hj) hsparse
  -- union bound (Loop 38): total ≤ m · (C/q)
  have hUnion : (∑ j ∈ Finset.range m, e j) ≤ (m : ℝ) * (C / q) :=
    ArkLib.ProximityGap.StructureLoop38.fri_union_bound e hround
  have hCq : 0 ≤ C / q := by positivity
  -- m ≤ 2^m
  have hm : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    have h := Nat.lt_two_pow_self (n := m)
    calc (m : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h.le
      _ = (2 : ℝ) ^ m := by push_cast; ring
  calc
    (∑ j ∈ Finset.range m, e j) ≤ (m : ℝ) * (C / q) := hUnion
    _ ≤ ((2 : ℝ) ^ m) * (C / q) := by gcongr
    _ = (1 / q) * ((2 : ℝ) ^ m) ^ 1 * C := by rw [pow_one]; ring

/-- **Non-vacuity.** The sparse-dominance bound is a genuine nonnegative constant numerator:
for `C > 0`, `q > 0` the prize RHS is positive at every depth. -/
theorem sparse_dominance_const_pos {C q : ℝ} {m : ℕ} (hC : 0 < C) (hq : 0 < q) :
    0 < (1 / q) * ((2 : ℝ) ^ m) ^ 1 * C := by
  have : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  rw [pow_one]
  positivity

end ArkLib.ProximityGap.ProofLoop40

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ProofLoop40.sparse_dominance_prize_mass
#print axioms ArkLib.ProximityGap.ProofLoop40.sparse_dominance_const_pos
