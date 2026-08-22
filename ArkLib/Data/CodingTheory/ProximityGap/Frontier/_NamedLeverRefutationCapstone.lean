/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CampaignProvenIndex
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorTetrachotomy

/-!
# Named-lever refutation capstone for the no-fifth-door tetrachotomy (#444, Lane 3)

The no-fifth-door tetrachotomy (`_NoFifthDoorTetrachotomy.lean`) proves the *abstract* exclusion:
its capstone `forces_doorIV` takes as a hypothesis `hclassicalOvershoots` — "every classical-door
mechanism overshoots / cannot certify the prize scale" — and the docstring there defers the
*content* of that hypothesis to prose ("the proven Lever A-D refutations; see the per-lever
obstruction theorems in `CampaignProvenIndex`").

This module closes that prose gap on the **classical-side refutation budget**: it bundles the
*already-proven, axiom-clean* named-lever obstruction exports of `CampaignProvenIndex` into ONE
kernel-checked conjunction, so that "no named classical lever reaches the prize floor" is a
kernel-checked statement rather than four scattered theorems plus a prose claim.

The named levers it unifies (all `obstruction`-scoped exports already proven upstream):

* **G2 — resonance / Parseval-RMS** (`resonance_ceiling_below_prize_floor`): the resonance
  certificate `c·√n` sits strictly below the BGK floor `√(n·L)` once `c² < L`, so it gives no
  Ω-disproof of `C = O(1)` (door-(i) moment face: the symmetric-function/Parseval lever).
* **G3 — cyclotomy coefficient root** (`coeff_route_loose_export`): the Fujiwara coefficient-root
  bound is loose by a divergent factor — for every constant `C` there is an `m` beating it.
* **G4 — roughness side-condition** (`roughness_does_not_add_bad_primes_export`): a roughness
  predicate can only *shrink* the fixed bad-prime set `{p ∣ N}`, never enlarge it; roughness is
  not the driver (door-(ii)/bad-prime face).
* **cumulant-sign route** (`cumulant_sign_route_refuted`): a negative 4th cumulant with positive
  8th refutes the cumulant-sign monotonicity lever (door-(i) moment face).

**Scope.** This is a *consolidation* of the classical-side refutation budget — it re-uses the
upstream proven obstruction exports verbatim (no mathematics is changed) and packages them as one
citable "named-lever refutation budget" theorem.  It does **not** prove door (iv) is achievable, and
it does **not** by itself discharge the *abstract* `hclassicalOvershoots` quantifier of
`forces_doorIV` (which ranges over *all* mechanisms with a classical door, not only the four named
levers).  What it gives is the kernel-checked **named** content: the concrete levers Shaw enumerated
are each provably below the prize floor / loose / non-driving, with one citation surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.NamedLeverRefutationCapstone

open ArkLib.ProximityGap.Frontier.CampaignProvenIndex

/-- **Named-lever refutation budget.**  ONE kernel-checked conjunction bundling the four proven,
axiom-clean named-lever obstructions of the classical side of the tetrachotomy:

* `(G2)` the resonance/Parseval certificate `c·√n` is strictly below the BGK floor `√(n·L)`
  whenever `0 < n`, `0 ≤ c`, `c² < L`;
* `(G3)` the cyclotomy coefficient-root route is loose: for the given `C > 0` there is an `m ≥ 2`
  whose `fujiwaraAtTwo` exceeds `C · prizeScale n m` for all `n > 0`;
* `(G4)` roughness cannot enlarge the bad-prime set: `{p ∣ N ∧ rough p} ⊆ {p ∣ N}`;
* `(cumulant)` the cumulant-sign monotonicity lever is refuted by a `κ₂ < 0 < κ₄` countermodel.

Each conjunct is the *verbatim* upstream proven export — this theorem only collects them, giving the
no-fifth-door tetrachotomy's named classical-side refutations a single citation point. -/
theorem namedLeverRefutationBudget
    (c n L : ℝ) (hn : 0 < n) (hc : 0 ≤ c) (hL : c ^ 2 < L)
    (C : ℝ) (hC : 0 < C)
    (N : ℕ) (rough : ℕ → Prop)
    {κ : ℕ → ℝ} (h4 : κ 2 < 0) (h8 : 0 < κ 4) :
    -- (G2) resonance certificate strictly below the BGK floor
    (c * Real.sqrt n < Real.sqrt (n * L)) ∧
    -- (G3) cyclotomy coefficient route loose by a divergent factor
    (∃ m : ℝ, 2 ≤ m ∧
      ∀ k : ℝ, 0 < k → WF9G3.fujiwaraAtTwo (k * m + 1) k > C * WF9G3.prizeScale k m) ∧
    -- (G4) roughness cannot enlarge the bad-prime set
    ({p : ℕ | p ∣ N ∧ rough p} ⊆ {p : ℕ | p ∣ N}) ∧
    -- (cumulant) cumulant-sign monotonicity lever refuted (verbatim upstream obstruction)
    (¬ (∀ r, 2 ≤ r → κ r ≤ 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact resonance_ceiling_below_prize_floor c n L hn hc hL
  · exact coeff_route_loose_export C hC
  · exact roughness_does_not_add_bad_primes_export N rough
  · exact cumulant_sign_route_refuted h4 h8

/-- **Resonance lever stays below the prize FLOOR too**, not just below BGK, in the sub-unit regime
`c ≤ 1`.  When the measured resonance constant `c ≤ 1`, the resonance certificate `c·√n ≤ √n =
prizeScale n` — so the resonance route cannot even reach, let alone exceed, the prize floor.  This
records that the resonance (door-(i) Parseval) lever is *floor-incapable*: it certifies at most the
prize floor and gives no separation. -/
theorem resonanceLever_le_prizeFloor (c n : ℝ) (hc1 : c ≤ 1) :
    c * Real.sqrt n ≤ NoFifthDoorTetrachotomy.prizeScale n := by
  unfold NoFifthDoorTetrachotomy.prizeScale
  calc c * Real.sqrt n ≤ 1 * Real.sqrt n :=
        mul_le_mul_of_nonneg_right hc1 (Real.sqrt_nonneg n)
    _ = Real.sqrt n := one_mul _

/-- **Named classical-side refutation, in the tetrachotomy's own scale language.**  Combines the
resonance obstruction with the tetrachotomy `bgkScale`: the resonance certificate is strictly below
the BGK ceiling `bgkScale n L`, confirming the moment/Parseval lever lands *inside* the door-(iv)
corridor's lower part and never delivers a fresh evaluation.  Pure re-expression of G2 in
`bgkScale` terms (the corridor object of `_NoFifthDoorTetrachotomy`). -/
theorem resonanceLever_lt_bgkScale (c n L : ℝ) (hn : 0 < n) (hc : 0 ≤ c) (hL : c ^ 2 < L) :
    c * Real.sqrt n < NoFifthDoorTetrachotomy.bgkScale n L := by
  unfold NoFifthDoorTetrachotomy.bgkScale
  exact resonance_ceiling_below_prize_floor c n L hn hc hL

end ArkLib.ProximityGap.Frontier.NamedLeverRefutationCapstone
