/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BridgeLoop44

/-!
# Loop 45 (MASTER / CANDIDATE) — a sufficient arithmetic reduction toward the `ε_mca` prize

This file packages the Loop 43/44 arithmetic into a single conditional theorem and **promotes it
as a candidate** (loop step 8).

**Scope (audit correction, 2026-10-28, PG-053).** The theorem below is a statement about an
arbitrary real `Vcard` and the real-valued `PolyOrbitCount` predicate.  `PolyOrbitCount` only asks
for *some* reals `N, S` with `Vcard ≤ N·S`, `N ≤ (2^m)^d`, `S ≤ 2^m`; it does not refer to an
actual orbit decomposition of an actual bad-challenge set.  This file does **not** identify
`Vcard / q²` with the repository's one-scalar MCA error `ProximityGap.epsMCA`, does not prove the
Theorem 2.1 / Loop 41 orbit structure for that set, and does not fix uniform parameter quantifiers.
So the theorem is a sufficient arithmetic step, not a reduction of the literal prize to a single
lemma: the protocol/event bridge remains a separate obligation (partial discharges of
`Vcard ≤ N·S` live in `OrbitCountConsumerBridge` / `OrbitCountFreeActionMCA`).

The intended chain (only the second step is formalized here):

* **Theorem 2.1 / Action–Orbit** (Loop 41): the bad-challenge set `V_δ(f)` on a cyclic (smooth
  multiplicative-subgroup) domain is a union of `⟨ω^{b−a}⟩`-orbits, each of size `S ≤ 2^m`, so
  `|V_δ| ≤ N · S` with `N` the bad-orbit count.  Not connected to this file's real `Vcard`.
* **Orbit-count ⟹ prize shape** (Loops 43/44, arithmetic): `Vcard ≤ N·S`, `N ≤ (2^m)^d`,
  `S ≤ 2^m`, `q ≥ 1` give `Vcard/q² ≤ (1/q)·(2^m)^{d+1}` — the prize shape once `Vcard/q²` is
  identified with `ε_mca`.

> **Target statement (informal, not the Lean `PolyOrbitCount`).** For deterministic smooth
> multiplicative-subgroup Reed–Solomon at a fixed prize rate `ρ`, gap `η > 0`, radius
> `δ ≤ 1−ρ−η`, the number `N` of bad-challenge orbits is polynomial in the smooth-domain size:
> `N ≤ (2^m)^d` for a fixed `d`.  Together with the event bridge above, this would be
> **sufficient** for the prize shape; it is not shown to be necessary.

Status of the target statement:
* **Johnson range** (`η > η₀ = √ρ−ρ`): expected to follow from the `poly(n)` list bounds of GS /
  BCIKS 2025/2055 (matching Loops 9/11/13), but the transfer from list size to `|V_δ|` and `N` is
  not formalized here.
* **Small-gap band** (`0 < η ≤ η₀`): **OPEN.** It is *weaker* than 861's Q2 (which demands a
  *constant* `N`).

`master_prize_from_poly_orbit_count` is sorry-free and axiom-clean, but it is only the arithmetic
step modulo the real-valued `PolyOrbitCount`.  Candidate for other agents: prove the target
statement in the small-gap band together with the event bridge, or refute it. See
`Research/ProximityPrize/DISPROOF_LOG.md` (Loop45).
-/

namespace ArkLib.ProximityGap.MasterLoop45

/-- **The real-valued polynomial-orbit-count hypothesis.** For a real number `Vcard`, there exist
nonnegative reals `N, S` with `Vcard ≤ N·S`, `N ≤ (2^m)^d` and `S ≤ 2^m`.  The witnesses are
arbitrary reals, not an actual orbit decomposition of an actual bad-challenge set (indeed the
predicate is equivalent to `Vcard ≤ (2^m)^(d+1)`); connecting it to the MCA bad set is a separate
obligation. -/
def PolyOrbitCount (Vcard : ℝ) (m d : ℕ) : Prop :=
  ∃ N S : ℝ, 0 ≤ N ∧ 0 ≤ S ∧ Vcard ≤ N * S ∧ N ≤ ((2 : ℝ) ^ m) ^ d ∧ S ≤ (2 : ℝ) ^ m

/-- **`PolyOrbitCount` carries no orbit structure.** It is equivalent to the bare size bound
`Vcard ≤ (2^m)^(d+1)`: the existential witnesses `N, S` can always be taken to be `(2^m)^d` and
`2^m`. -/
theorem polyOrbitCount_iff (Vcard : ℝ) (m d : ℕ) :
    PolyOrbitCount Vcard m d ↔ Vcard ≤ ((2 : ℝ) ^ m) ^ (d + 1) := by
  constructor
  · rintro ⟨N, S, -, hSnn, hdec, hcount, hsize⟩
    have hpow : (0 : ℝ) ≤ ((2 : ℝ) ^ m) ^ d := by positivity
    calc Vcard ≤ N * S := hdec
      _ ≤ ((2 : ℝ) ^ m) ^ d * (2 : ℝ) ^ m := mul_le_mul hcount hsize hSnn hpow
      _ = ((2 : ℝ) ^ m) ^ (d + 1) := (pow_succ _ _).symm
  · intro h
    exact ⟨((2 : ℝ) ^ m) ^ d, (2 : ℝ) ^ m, by positivity, by positivity,
      by rw [← pow_succ]; exact h, le_rfl, le_rfl⟩

/-- **Conditional arithmetic step: `PolyOrbitCount` ⟹ the prize shape.** For real `q ≥ 1`, the
quantity `Vcard/q²` lands on the prize RHS `(1/q)·(2^m)^{d+1}`.  The proof is complete and
axiom-clean, but `Vcard/q²` is not identified here with the actual MCA error, so this is a
sufficient arithmetic step, not a reduction of the literal prize to `PolyOrbitCount` alone. -/
theorem master_prize_from_poly_orbit_count
    {q Vcard : ℝ} {m d : ℕ} (hq : 1 ≤ q)
    (h : PolyOrbitCount Vcard m d) :
    Vcard / q ^ 2 ≤ (1 / q) * ((2 : ℝ) ^ m) ^ (d + 1) := by
  obtain ⟨N, S, hNnn, hSnn, hdec, hcount, hsize⟩ := h
  exact ArkLib.ProximityGap.BridgeLoop44.mca_prize_of_poly_orbit_count
    hq hSnn hNnn hdec hcount hsize

/-- **Positivity of the right-hand side (sanity only).** The prize bound is a positive real.
This is not a non-vacuity witness: it does not show that `PolyOrbitCount` holds for any actual MCA bad
set. -/
theorem master_prize_bound_pos {q : ℝ} {m d : ℕ} (hq : 0 < q) :
    0 < (1 / q) * ((2 : ℝ) ^ m) ^ (d + 1) := by positivity

end ArkLib.ProximityGap.MasterLoop45

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.MasterLoop45.master_prize_from_poly_orbit_count
#print axioms ArkLib.ProximityGap.MasterLoop45.master_prize_bound_pos
#print axioms ArkLib.ProximityGap.MasterLoop45.polyOrbitCount_iff
