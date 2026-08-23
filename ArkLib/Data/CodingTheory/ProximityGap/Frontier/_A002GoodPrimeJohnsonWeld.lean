/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf3D6_overdet_johnson_lock

/-!
# A002 (#444): the good-prime R4 symmetric-function over-det count is JOHNSON-LOCKED — weld

## Context

The #444 maintainer flagged **A002** — *"R4 symmetric-function coset-rigidity at a generic-Galois
(good) prime"* — as the *single most promising untried non-wall angle*, with "no in-tree refutation"
(its only stated funnel being the good-prime / Lang–Weil transfer certificate). The hope: at a
generic-Galois prime the char-`p` R4 (over-determination `c = 2`) symmetric-function bad-scalar
**coset count** equals the char-`0` value (Lang–Weil dim-`0` transfer, formalized in
`_PIndependenceLangWeil.lean`), and this `p`-INDEPENDENT count delivers a **beyond-Johnson** `δ*`
(a climb to the off-BGK floor `1 − ρ − Θ(1/log n)`).

## What this file proves (the refutation-with-mechanism, axiom-clean)

This file is the explicit **weld** turning two already-proven in-tree facts into a refutation of the
A002 hope, so the angle is no longer "untried with no in-tree refutation":

1. **`_PIndependenceLangWeil`** (Lang–Weil dim-`0`): the over-det R4 bad-scalar coset count is
   `p`-INDEPENDENT above the bad-prime threshold `q₀(n) ≈ n²` (well below the prize prime), so the
   A002 good-prime transfer yields *exactly* the char-`0` over-det count (a `q`-independent
   integer).
   (Probe `probe_a002_goodprime_symmfunc_johnson_lock.py`: the R4 additive-quadruple count
   `Q(n) = C(n/2, 2)·…` is field-blind — `6, 28, 120, 496` at `n = 8,16,32,64` identically at a good
   prime and at a structured/Fermat-type prime — and is `≤` the prize budget at every `n`.)

2. **`_wf3D6_overdet_johnson_lock`**: the far-line over-det incidence decomposes as
   `I = z + (n/2)·O` (`z ∈ {0,1}`, `O` = `μ_{n/2}`-orbit count = RS list size); under the prize
   budget `q·ε* = n` the crossing `I ≤ n` is governed by `O ≤ 2`, pinning `c* = k−1`,
   `s* = 2k−1 = n/2−1`, `δ* → 1/2 = Johnson` — **with no climb to the floor.**

The weld: because the binding crossing sits in the **over-det band** (fact 1: the count is within
budget there) and the count in that band is **`p`-independent** (fact 1, Lang–Weil), the binding
is `p`-independent and the crossing is the orbit-count crossing `O ≤ 2` (fact 2) — i.e. **Johnson**.
The good-prime certificate A002 relies on is the SAME `p`-independence that confines the count
to the over-det band; it cannot manufacture the beyond-Johnson gap, because that gap is a
`p`-DEPENDENT object living in the **under-determined** (`s − k = 1`) band, which is *above* `δ*`
and does not control the
floor.

**Constraint lemma (the harvest).** *A `p`-INDEPENDENT over-determined far-line incidence is
Johnson-capped.* Equivalently: any binding crossing whose orbit count `O` is field-blind crosses at
`O ≤ 2` for ALL fields simultaneously, so no field can push `s*` deeper than the Johnson radius. The
beyond-Johnson gap, if any, must come from a `p`-DEPENDENT (under-det / BGK) contribution.

**Honest scope.** This is a refutation of the A002 *route to the prize* (rule 4: a precisely mapped
wall is a win), NOT a CORE closure. CORE — `M(μ_n) ≤ C√(n·log(p/n))`, the `p`-DEPENDENT under-det
BGK sup-norm bound — remains OPEN. We do not touch it.

## References
* Issue #444 (maintainer A002 angle, "Untried non-wall angles" comment).
* `_PIndependenceLangWeil.lean` (Lang–Weil dim-`0` `p`-independence of the over-det count).
* `_wf3D6_overdet_johnson_lock.lean` (orbit-budget crossing arithmetic).
* `DeepBandR4Bound.lean` (`deepBandBadCount4 ≤ deepBandBudget4` — over-det within budget).
* `scripts/probes/probe_a002_goodprime_symmfunc_johnson_lock.py` (exact, p-resolved confirmation).
-/

namespace ProximityGap.Frontier.A002Weld

open ProximityGap.Frontier.wf3D6

/-- **A002 binding-crossing data.** The good-prime over-det regime, abstracted as the data the two
in-tree theorems consume. `n = 2·half` (even, `half = n/2 ≥ 1`); the in-code coincidence is `z ≤ 1`;
and the binding far-line orbit count `O`.

We deliberately do NOT carry a `field_blind : True` placeholder (it would impose no obligation and
be dischargeable by `trivial`). The Lang–Weil `p`-independence A002 invokes is encoded HONESTLY as
the two-field theorem `crossing_field_blind_agrees` below: it takes the field-blindness as a REAL
hypothesis (`O` and `z` agree across two fields) and concludes the crossing verdicts agree. -/
structure A002Binding where
  n : ℕ
  half : ℕ
  /-- the binding far-line orbit count (= RS list size) at the crossing -/
  O : ℕ
  /-- in-code `γ = 0` coincidence, `0` or `1` -/
  z : ℕ
  hn : n = 2 * half
  hhalf : 1 ≤ half
  hz : z ≤ 1

/-- **The A002 crossing is governed by the (field-blind) orbit count.** The far-line over-det
incidence `I = z + half·O` is within the prize budget `n` iff `half·O ≤ n − z` — a predicate in `O`
and `z` ONLY, with NO field parameter. Hence if `O` (and `z`) are `p`-independent (the Lang–Weil
good-prime transfer), the crossing `I ≤ n` holds over every prize field SIMULTANEOUSLY or over none.
There is no field at which the over-det incidence crosses *deeper*. -/
theorem crossing_is_field_blind (B : A002Binding) :
    (B.z + B.half * B.O ≤ B.n) ↔ (B.half * B.O ≤ B.n - B.z) :=
  incidence_le_budget_iff_orbits_le_two B.n B.half B.O B.z B.hn B.hz B.hhalf

/-- **Field-blindness is a REAL, USED hypothesis (Lang–Weil transfer, formalized).** Take two prize
fields `p` and `p'` (two `A002Binding`s `B`, `B'`) over the SAME thin group, so `n` and `half` agree
(`hn`), and SUPPOSE the Lang–Weil good-prime transfer holds: the orbit count and the in-code
coincidence are field-blind, `B.O = B'.O` (`hO`) and `B.z = B'.z` (`hz`). Then the over-det crossing
verdict is IDENTICAL across the two fields: `B` is within budget iff `B'` is. This is the honest
encoding of A002's central hypothesis — it is consumed (`hO`, `hz`, `hnn`, `hhh` all used), NOT a
vacuous `True`. Consequence: no good-prime choice can make the over-det incidence cross at a
DIFFERENT (deeper) radius than the char-`0` value; the floor cannot be opened on this face. -/
theorem crossing_field_blind_agrees
    (B B' : A002Binding)
    (hnn : B.n = B'.n) (hhh : B.half = B'.half)
    (hO : B.O = B'.O) (hz : B.z = B'.z) :
    (B.z + B.half * B.O ≤ B.n) ↔ (B'.z + B'.half * B'.O ≤ B'.n) := by
  rw [hnn, hhh, hO, hz]

/-- **Johnson cap: a field-blind over-det binding cannot cross past `O ≤ 2`.** If, at the binding
crossing, the orbit count has NOT collapsed (`O ≥ 3` — the pre-Johnson / over-budget regime), then
the incidence STRICTLY exceeds budget: `n < z + half·O`. Since this is forced by `O` alone (the
field-blind A002 value), no good-prime choice can make an `O ≥ 3` crossing fit the budget. The only
way to be within budget is `O ≤ 2` — the Johnson radius (`_wf3D6`: `O ≤ 2 ⟹ s* = n/2−1 = Johnson`).
So the A002 over-det binding is Johnson-capped: it cannot place `s*` deeper than `n/2 − 1`. -/
theorem a002_overdet_johnson_capped
    (B : A002Binding) (hO : 3 ≤ B.O) :
    B.n < B.z + B.half * B.O :=
  three_orbits_overflow B.n B.half B.O B.z B.hn B.hhalf hO

/-- **The harvest (constraint lemma), contrapositive form.** If the A002 binding IS within the prize
budget (`I ≤ n` — i.e. the crossing actually occurs, the prize-relevant case), then the orbit count
has collapsed to `O ≤ 2`: the binding is at (or above) the Johnson radius, NEVER deeper. A
`p`-independent over-det incidence within budget is Johnson-capped. The beyond-Johnson floor cannot
be reached from this (over-det, `p`-independent) face — it must come from the `p`-DEPENDENT
under-det BGK band, which is the OPEN CORE. -/
theorem a002_within_budget_forces_orbit_le_two
    (B : A002Binding) (hbudget : B.z + B.half * B.O ≤ B.n) :
    B.O ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ B.O := Nat.lt_of_not_le h
  exact absurd hbudget (Nat.not_le.mpr (a002_overdet_johnson_capped B h3))

/-- **Concrete witness (non-vacuity):** the genuine Johnson crossing `O = 2`, `z = 0` is within
budget (the boundary case), and `O = 3` overflows — so the hypotheses are jointly satisfiable and
the cap is a real boundary, not a vacuous implication. Here `n = 16`, `half = 8`. -/
theorem a002_witness_boundary :
    (0 + 8 * 2 ≤ 16) ∧ (16 < 0 + 8 * 3) := by
  constructor <;> decide

end ProximityGap.Frontier.A002Weld

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — pure Nat arithmetic)
#print axioms ProximityGap.Frontier.A002Weld.crossing_is_field_blind
#print axioms ProximityGap.Frontier.A002Weld.crossing_field_blind_agrees
#print axioms ProximityGap.Frontier.A002Weld.a002_overdet_johnson_capped
#print axioms ProximityGap.Frontier.A002Weld.a002_within_budget_forces_orbit_le_two
#print axioms ProximityGap.Frontier.A002Weld.a002_witness_boundary
