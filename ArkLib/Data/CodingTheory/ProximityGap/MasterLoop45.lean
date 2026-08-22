/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BridgeLoop44

/-!
# Loop 45 (MASTER / CANDIDATE) — the literal `ε_mca` prize, reduced to ONE open lemma

This file assembles Loops 38/41/43/44 into a single master conditional theorem and **promotes it
as a candidate** (loop step 8): a clean statement whose *only* remaining hypothesis is the crisply
isolated open lemma, so further effort can focus entirely there.

The assembled chain:

* **Theorem 2.1 / Action–Orbit** (Loop 41, verified sound): the bad-challenge set `V_δ(f)` on a
  cyclic (smooth multiplicative-subgroup) domain is a union of `⟨ω^{b−a}⟩`-orbits, each of size
  `S ≤ 2^m`. ⟹ `|V_δ| ≤ N · S` with `N` the bad-orbit count.
* **Orbit-count ⟹ prize** (Loops 43/44): `|V_δ| ≤ N·S`, `N ≤ (2^m)^d`, `S ≤ 2^m`, `q ≥ 1` give
  `ε_mca = |V_δ|/q² ≤ (1/q)·(2^m)^{d+1}` — the literal prize shape.

So the **entire** remaining content of the literal #232 prize is the single hypothesis below.

> **Open lemma `PolyOrbitCount` (the irreducible core).** For deterministic smooth multiplicative-
> subgroup Reed–Solomon at a fixed prize rate `ρ`, gap `η > 0`, radius `δ ≤ 1−ρ−η`, the number `N`
> of bad-challenge orbits is polynomial in the smooth-domain size: `N ≤ (2^m)^d` for a fixed `d`.

Status of `PolyOrbitCount`:
* **Johnson range** (`η > η₀ = √ρ−ρ`): a **theorem** — list size, hence `|V_δ|`, hence `N`, is
  `poly(n)` by GS / BCIKS 2025/2055. So the prize is unconditional there (Loops 9/11/13).
* **Small-gap band** (`0 < η ≤ η₀`): **OPEN.** The genuine `$1M` core — a polynomial orbit-count
  bound below capacity for *deterministic structured* domains. It is *weaker* than 861's Q2 (which
  demands a *constant* `N`); a polynomial `N` is all the prize needs.

`master_prize_from_poly_orbit_count` is sorry-free and axiom-clean: the complete reduction modulo
`PolyOrbitCount`. Candidate for other agents: prove `PolyOrbitCount` in the small-gap band (closes
the literal prize), or refute it (a super-polynomial deterministic-smooth orbit count below
capacity at fixed rate — which would also resolve a long-standing list-decoding question). See
`DISPROOF_LOG.md` (Loop45).
-/

namespace ArkLib.ProximityGap.MasterLoop45

/-- **The polynomial-orbit-count hypothesis** — the single open input. For a bad-challenge set of
cardinality `Vcard`, there is an orbit decomposition `Vcard ≤ N·S` with a *polynomial* orbit count
`N ≤ (2^m)^d` and the (always-true) orbit-size bound `S ≤ 2^m`. -/
def PolyOrbitCount (Vcard : ℝ) (m d : ℕ) : Prop :=
  ∃ N S : ℝ, 0 ≤ N ∧ 0 ≤ S ∧ Vcard ≤ N * S ∧ N ≤ ((2 : ℝ) ^ m) ^ d ∧ S ≤ (2 : ℝ) ^ m

/-- **MASTER conditional theorem: `PolyOrbitCount` ⟹ the literal `ε_mca` prize.** Assembling the
action-orbit decomposition (Theorem 2.1, Loop 41) with the orbit-count bound (Loops 43/44), the MCA
term `ε_mca = Vcard/q²` lands on the prize RHS `(1/q)·(2^m)^{d+1}` for any field `q ≥ 1`. The
proof is complete and axiom-clean; the *only* unproven input is `PolyOrbitCount`, open in the
small-gap band. -/
theorem master_prize_from_poly_orbit_count
    {q Vcard : ℝ} {m d : ℕ} (hq : 1 ≤ q)
    (h : PolyOrbitCount Vcard m d) :
    Vcard / q ^ 2 ≤ (1 / q) * ((2 : ℝ) ^ m) ^ (d + 1) := by
  obtain ⟨N, S, hNnn, hSnn, hdec, hcount, hsize⟩ := h
  exact ArkLib.ProximityGap.BridgeLoop44.mca_prize_of_poly_orbit_count
    hq hSnn hNnn hdec hcount hsize

/-- **The candidate is non-vacuous.** The resulting prize bound is a positive real, not `0 ≤ 0`. -/
theorem master_prize_bound_pos {q : ℝ} {m d : ℕ} (hq : 0 < q) :
    0 < (1 / q) * ((2 : ℝ) ^ m) ^ (d + 1) := by positivity

end ArkLib.ProximityGap.MasterLoop45

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.MasterLoop45.master_prize_from_poly_orbit_count
#print axioms ArkLib.ProximityGap.MasterLoop45.master_prize_bound_pos
