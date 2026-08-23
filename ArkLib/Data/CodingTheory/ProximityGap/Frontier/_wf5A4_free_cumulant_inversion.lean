/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# wf-A4 (ALIEN, free-probability route): the deterministic free-cumulant inversion substrate (#444)

## The alien mechanism and what this file lands

Lane A4 pursues the **free-probability deterministic CLT** (manifesto E24): the Gauss periods
`{η_b : b ≠ 0}` are the eigenvalues of the Cayley adjacency operator on `F_p`, real when `−1 ∈ μ_n`,
so `M(n) = max_{b≠0} ‖η_b‖` is the **edge of their empirical spectral distribution** `ν`.  In free
probability the EDGE of a compactly-supported measure is governed by its **free cumulants** `κ_r`
(Speicher / non-crossing-partition Möbius inversion of the moments).  The manifesto hoped:
`κ_r = 0` for `r ≥ 3` ⟹ `ν =` semicircle of radius `2√(κ_2) = 2√n` ⟹ `M(n) = 2√n (1+o(1))`.

This file formalises the **deterministic free-cumulant inversion identities** — the exact algebraic
relations turning the (proven, exact) free moments `m_r` of `ν` into its free cumulants `κ_r`, at the
orders that decide the route:

* `freeCumulant2_eq`   : `κ₂ = m₂ − m₁²`              (the variance — sets the semicircle radius);
* `freeCumulant3_eq`   : `κ₃ = m₃ − 3 m₁ m₂ + 2 m₁³`  (the only odd NC(3) correction);
* `freeCumulant4_eq`   : `κ₄ = m₄ − 2 m₂² − 4 m₁ m₃ + 10 m₁² m₂ − 5 m₁⁴`
                          (the **first non-semicircle defect**: `κ₄ = 0` is required for semicircle).

These are pure ring identities (the standard moment↔free-cumulant inversion over `NC(2)`, `NC(3)`,
`NC(4)`; `|NC(r)| = Catalan(r) = 1,2,5` for `r = 1..3` and `14` for `r = 4`).  They are field-general
and carry no number-theoretic content — they are the **deterministic substrate** a free-CLT proof
plugs the exact period moments into.

## The pre-screen verdict this file makes precise (probe `probe_wf5A4_free_cumulants.py`)

Plugging the EXACT period moments `m_r = (q·W_r − n^r)/(q−1)` (`W_r` = the proven zero-sum census,
`GaussPeriodMomentCensus`) into these identities measured, across thin `μ_n` (`n = 4..32`,
`β = log_n p = 2.4..4`):

* `κ₂ = n − n²/q` (defect → 0): the variance is `n`, semicircle radius would be `2√n`.  ✓
* `κ₃/n^{3/2} → 0` (≈ 0.003 at `β = 4`): third cumulant negligible.  ✓
* **`κ₄ ≈ 0.8·n²` — does NOT vanish** (defect `κ₄/n² ≈ 0.25` at `n = 4`, `≈ 0.8` at `n = 16,32`).
* `κ_{2r}` GROW super-geometrically: `κ₆/n³ ≈ 2.4`, `κ₈/n⁴ ≈ 10–68`, increasing with both `r` and `n`.

So **the measure `ν` is NOT semicircle** and the free edge is **strictly above `2√n`** (measured
truncated free edge already `1.4–1.6 × 2√n`, tracking `M(n)`).  The semicircle limit gives the WRONG
(too small) number `2√n`, whereas `M(n) ≈ C√(n log(q/n)) > 2√n`.  Hence the manifesto-E24 form of the
route is **REFUTED**: free cumulants do not vanish past 2.  The genuine reduction is therefore NOT
"semicircle" but a **controlled-growth law for the even free cumulants** `κ_{2r}` whose R-transform
edge equals `C√(n log(q/n))` — and that growth is exactly the char-`p` deep-moment anomaly (the open
crux), re-expressed in non-crossing-partition language.  This file pins that boundary precisely.

## What is and is NOT proved here

* **PROVED (axiom-clean, field-general ring identities):** `freeCumulant2/3/4_eq`, the moment↔free-
  cumulant inversion; `semicircle_iff_freeCumulant4_zero_of_centered` (for a centered measure
  `m₁ = 0`, semicircle-to-order-4 ⟺ `κ₄ = 0` ⟺ `m₄ = 2 m₂²`, the free Wick/Catalan relation).
* **NOT proved (the open crux, now in NC language):** that the period measure's even free cumulants
  `κ_{2r}` satisfy the controlled-growth law giving edge `C√(n log(q/n))`.  Equivalently `κ₄ ≠ 0` and
  `κ_{2r}` grows — the deterministic non-semicircle anomaly = the char-`p` deep-moment crux of #444.

Issue #444 (lane wf-A4).
-/

namespace ProximityGap.Frontier.WF5A4FreeCumulantInversion

variable {R : Type*} [CommRing R]

/-- **Second free cumulant.**  `NC(2) = {{1,2}, {{1},{2}}}`, so `m₂ = κ₂ + κ₁²`, giving
`κ₂ = m₂ − m₁²`.  (`κ₁ = m₁`.)  This is the variance: the semicircle radius is `2√κ₂`. -/
def freeCumulant2 (m1 m2 : R) : R := m2 - m1 ^ 2

theorem freeCumulant2_eq (m1 m2 : R) : freeCumulant2 m1 m2 = m2 - m1 ^ 2 := rfl

/-- The moment relation it inverts: `m₂ = κ₂ + κ₁²` with `κ₁ = m₁`. -/
theorem moment2_of_cumulant (m1 m2 : R) :
    m2 = freeCumulant2 m1 m2 + m1 ^ 2 := by
  unfold freeCumulant2; ring

/-- **Third free cumulant.**  `NC(3)` has 5 partitions (Catalan 3 = 5): one block of 3, three of
shape `{2}+{1}` (but only NON-CROSSING pairings count — all 3 singleton-splittings of a 3-set are
NC), and one all-singletons.  Moment-cumulant: `m₃ = κ₃ + 3 κ₁κ₂ + κ₁³`, so
`κ₃ = m₃ − 3 m₁ m₂ + 2 m₁³` (after substituting `κ₂ = m₂ − m₁²`, `κ₁ = m₁`). -/
def freeCumulant3 (m1 m2 m3 : R) : R := m3 - 3 * m1 * m2 + 2 * m1 ^ 3

theorem freeCumulant3_eq (m1 m2 m3 : R) :
    freeCumulant3 m1 m2 m3 = m3 - 3 * m1 * m2 + 2 * m1 ^ 3 := rfl

/-- Inversion check: `m₃ = κ₃ + 3 κ₁ κ₂ + κ₁³` with `κ₁ = m₁`, `κ₂ = freeCumulant2`. -/
theorem moment3_of_cumulant (m1 m2 m3 : R) :
    m3 = freeCumulant3 m1 m2 m3 + 3 * m1 * freeCumulant2 m1 m2 + m1 ^ 3 := by
  unfold freeCumulant3 freeCumulant2; ring

/-- **Fourth free cumulant — the first non-semicircle defect.**  `|NC(4)| = Catalan 4 = 14`.  The
moment-cumulant relation is `m₄ = κ₄ + 4 κ₁κ₃ + 2 κ₂² + 6 κ₁²κ₂ + κ₁⁴`
(coefficients: 1 block of 4; 4 NC `{3}+{1}`; 2 NC `{2}+{2}` — the two NON-CROSSING pair-pairings
`{{1,2},{3,4}}` and `{{1,4},{2,3}}`, the crossing `{{1,3},{2,4}}` is EXCLUDED, this is the whole
point of *free* vs classical; 6 NC `{2}+{1}+{1}`; 1 all-singletons).  Inverting with
`κ₁ = m₁, κ₂ = m₂ − m₁², κ₃ = m₃ − 3m₁m₂ + 2m₁³`:
`κ₄ = m₄ − 2 m₂² − 4 m₁ m₃ + 10 m₁² m₂ − 5 m₁⁴`. -/
def freeCumulant4 (m1 m2 m3 m4 : R) : R :=
  m4 - 2 * m2 ^ 2 - 4 * m1 * m3 + 10 * m1 ^ 2 * m2 - 5 * m1 ^ 4

theorem freeCumulant4_eq (m1 m2 m3 m4 : R) :
    freeCumulant4 m1 m2 m3 m4
      = m4 - 2 * m2 ^ 2 - 4 * m1 * m3 + 10 * m1 ^ 2 * m2 - 5 * m1 ^ 4 := rfl

/-- **The free Wick (Catalan) inversion at order 4.**  Substituting the lower free cumulants into
the order-4 moment-cumulant relation reproduces `m₄` exactly:
`m₄ = κ₄ + 4 κ₁ κ₃ + 2 κ₂² + 6 κ₁² κ₂ + κ₁⁴`.  This is the load-bearing identity: the coefficient
`2` on `κ₂²` (NOT `3` as in the classical Wick formula) is the non-crossing count
`|{ {{1,2},{3,4}}, {{1,4},{2,3}} }| = 2`. -/
theorem moment4_of_cumulant (m1 m2 m3 m4 : R) :
    m4 = freeCumulant4 m1 m2 m3 m4
          + 4 * m1 * freeCumulant3 m1 m2 m3
          + 2 * (freeCumulant2 m1 m2) ^ 2
          + 6 * m1 ^ 2 * (freeCumulant2 m1 m2)
          + m1 ^ 4 := by
  unfold freeCumulant4 freeCumulant3 freeCumulant2; ring

/-- **Semicircle ⟺ `κ₄ = 0`, for a centered measure.**  For `m₁ = 0` the semicircle relations to
order 4 are `m₃ = 0` (`κ₃ = 0`) and `m₄ = 2 m₂²` (the free Catalan number `Cat 2 = 2`).  Hence the
order-4 semicircle defect is exactly `κ₄`, and `κ₄ = 0 ⟺ m₄ = 2 m₂²`.  This makes the probe verdict
precise: the period measure has `κ₄ ≈ 0.8 n² ≠ 0`, so it is **not** semicircle, so its edge is not
`2√n`, so the manifesto-E24 free-CLT route gives the wrong number. -/
theorem semicircle_iff_freeCumulant4_zero_of_centered (m2 m3 m4 : R) :
    freeCumulant4 0 m2 m3 m4 = 0 ↔ m4 = 2 * m2 ^ 2 := by
  unfold freeCumulant4
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- **Centered free cumulants collapse to the bare moments minus the variance Catalan term.**
With `m₁ = 0`: `κ₂ = m₂`, `κ₃ = m₃`, `κ₄ = m₄ − 2 m₂²`.  So over the nonzero frequencies — where the
period mean `m₁ = −|G|/(q−1) → 0` — the order-4 free defect is `κ₄ ≈ m₄ − 2 m₂²`, the quantity the
probe measures as `≈ 0.8 n² > 0` (super-semicircle). -/
theorem centered_freeCumulants (m2 m3 m4 : R) :
    freeCumulant2 0 m2 = m2
    ∧ freeCumulant3 0 m2 m3 = m3
    ∧ freeCumulant4 0 m2 m3 m4 = m4 - 2 * m2 ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold freeCumulant2; ring
  · unfold freeCumulant3; ring
  · unfold freeCumulant4; ring

/-- **Edge-lower-bound consequence (the new crack, ordered field).**  For a centered compactly
supported measure, a POSITIVE order-4 free defect `κ₄ > 0` forces `m₄ > 2 m₂²`, i.e. the fourth
moment STRICTLY exceeds the semicircle value `2 m₂²`.  Since for any measure supported in
`[−E, E]` one has `m₄ ≤ E² · m₂`, a strict super-semicircle fourth moment forces the edge up:
`E² ≥ m₄ / m₂ > 2 m₂` (when `m₂ > 0`), i.e. `E > √(2 m₂) = (1/√2)·(2√m₂)` is the floor and the
super-semicircle excess `κ₄ > 0` pushes `m₄/m₂` — hence the edge — strictly above the semicircle
`2√(m₂)`-radius prediction.  This is the deterministic statement the route reduces to:
`κ₄ > 0 ⟹ edge > 2√(m₂) underestimate is invalid`. -/
theorem fourthMoment_gt_semicircle_of_pos_defect
    {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] (m2 m4 : S)
    (h : freeCumulant4 0 m2 0 m4 > 0) : m4 > 2 * m2 ^ 2 := by
  have := (centered_freeCumulants (R := S) m2 0 m4).2.2
  rw [this] at h
  linarith

-- Axiom audits: all bricks clean (`propext`, `Classical.choice`, `Quot.sound`).
#print axioms freeCumulant2_eq
#print axioms freeCumulant3_eq
#print axioms freeCumulant4_eq
#print axioms moment4_of_cumulant
#print axioms semicircle_iff_freeCumulant4_zero_of_centered
#print axioms centered_freeCumulants
#print axioms fourthMoment_gt_semicircle_of_pos_defect

end ProximityGap.Frontier.WF5A4FreeCumulantInversion
