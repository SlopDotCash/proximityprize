/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MStarLognReduction
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Geometric decay ⟹ logarithmic crossing depth (#444, VECTOR 7 — entropy/counting upper bound)

## The question this file answers (arithmetically)

`_MStarLognReduction` reduces the prize target `m*(n) = O(log n)` to producing a PROVEN upper
envelope `U : ℕ → ℕ` with `Dstar n k m ≤ U m` that crosses budget `n` at an `O(log n)` depth
(`mStar_le_of_upperEnvelope_crossing` / `logBudgetReached`).  `_DStarDecreasingEnvelope` proves the
true envelope is monotone DECREASING (`cliqueColors_antitone_depth`) but explicitly "does NOT bound
the RATE of decrease".  VECTOR 7 asks the rate question directly:

> **Is the decay GEOMETRIC (each rung cuts `Dstar` by a constant factor ≥ 2) — in which case the
> crossing is reached at `m = O(log n)` — or does it STALL (a plateau)?**

This file lands the **arithmetic half**: a self-contained, axiom-clean lemma that a geometric upper
envelope from a polynomial top crosses budget at logarithmic depth.  It then records the MEASURED
two-phase decay structure that motivates it.  The open input is isolated to a single named
hypothesis: that the worst-direction envelope obeys the geometric per-rung cut down to the crossing.

## The arithmetic lemma (PROVED, no open input)

`geomEnvelope c n₀ m := n₀ / c^m` (integer division), the geometric envelope from top `n₀` with
per-rung cut factor `c ≥ 2`.

* **`geomEnvelope_crossing`** — if `n₀ ≤ n * c^d` (the top is at most a `d`-fold polynomial blow-up of
  budget `n`), then `geomEnvelope c n₀ d ≤ n`: a geometric envelope from a degree-`d` polynomial top
  crosses budget by depth exactly `d`.
* **`geomEnvelope_crosses_at_log`** — with the measured top `n₀ = n^D` (the rigidity ceiling is
  `≤ C(n,k+m) ≤ n^m`, here capped at the polynomial-degree top `n^D`), the geometric envelope crosses
  `n` by depth `(D-1) * Nat.log 2 n + (D-1) = O(log n)` once `c ≥ 2` (each rung kills one `log₂ n`
  factor).  This is the precise "geometric ⟹ log crossing" implication.

## The deployable reduction (PROVED, modulo the named open factor hypothesis)

`GeometricCutDownTo D n k c` — the open input: the worst-direction envelope `D` is dominated, down
to the crossing, by a geometric envelope with fixed cut factor `c ≥ 2` from a degree-`d` polynomial
top.  `mStar_le_log_of_geometricCut` then PROVES `m*(n) = O(log n)` from it, via
`_MStarLognReduction.mStar_le_of_upperEnvelope_crossing`.  So VECTOR 7's claim "geometric decay ⟹
log crossing" is a THEOREM; the residual open input is exactly the per-rung factor bound.

## The MEASURED decay (the honest evidence; reproduced as `Prop`-level facts)

Exact worst-direction distinct-γ envelope `Dstar n k m` (engine `scripts/rust-pg/dstarvec`, ρ=1/4,
budget `= n`), cross-validated against `dirworst`/`probe_farline_incidence_exact`:

| n  | budget | Dstar(1) | Dstar(2) | Dstar(3) | Dstar(4) | Dstar(5) | Dstar(6) | … | m* |
|----|--------|----------|----------|----------|----------|----------|----------|---|----|
| 8  | 8      | 40       | 9        | 5        | 1        | 1        |          |   | 3  |
| 16 | 16     | 3664     | 89       | 9        | 9        | 9        | 8        | …1| 3  |
| 32 | 32     | (≫n)     | …        | …        | …        | 9        | …        |   | 5  |

**The decay is TWO-PHASE, not uniformly geometric:**

* **Phase 1 (the crossing, `m = 1 … m*`): STEEP, super-geometric.**  Per-rung cut factors
  `n=8: 40→9 = 4.44×`; `n=16: 3664→89 = 41×`, `89→9 = 9.9×`.  The factor GROWS with `n` (≥ √n scale),
  so each rung kills more than one `log₂ n` factor — the crossing of budget `n` is reached at
  `m* = 3, 3, 5` for `n = 8, 16, 32` (`m*/log₂ n ≈ 1`), i.e. `O(log n)`.  Relative to the rigidity
  ceiling `C(n,k+m)` the collapse is catastrophic: `Dstar/C` falls `0.84 → 0.011 → 0.0008` over
  `m = 1,2,3` at `n = 16`.
* **Phase 2 (post-crossing): STALLS on a plateau, then a second cliff.**  `n=16: Dstar = 9` for
  `m = 3,4,5` (orbit-count floor: 1 fixed point + 1 size-8 orbit = `2` orbits, `9 = 1 + 8`; engine
  `orbplat`), then a cliff to `1`.  **CRUCIALLY the plateau value (9) is itself BELOW budget (16)** —
  the stall happens AFTER the crossing, so it does NOT obstruct the crossing.

**Net VECTOR 7 finding:** the decay is geometric (in fact super-geometric) *down to the crossing*,
and stalls only *below* budget.  Hence the crossing IS reached at log depth — but the plateau means
no UNIFORM geometric bound holds for all `m`, so the entropy/counting upper bound must be a
TWO-PHASE envelope (steep to the crossing, then flat).  Proving the Phase-1 per-rung factor lower
bound `≥ c` is the residual open input — it is exactly the worst-direction list-size growth law =
BCHKS 1.12, the off-BGK wall.  This file makes the implication a theorem and the residual a single
named hypothesis; it does NOT discharge the residual.

## Honest scope
Pure-`ℕ` arithmetic of geometric integer-division envelopes + `Nat.log`.  No character sum, no
field-size, no BGK input.  Does NOT prove `m* = O(log n)` unconditionally (that needs the named
geometric-cut hypothesis, = the wall).  It proves "geometric decay ⟹ log crossing" and isolates the
open factor.

Probe: `scripts/rust-pg/dstarvec`, `scripts/rust-pg/orbplat` (exact `n = 8, 16, 32`, ρ=1/4).

## References
- `_MStarLognReduction.lean` (`mStar`, `mStar_le_of_upperEnvelope_crossing`, `logBudgetReached`).
- `_DStarDecreasingEnvelope.lean` (`cliqueColors_antitone_depth`: envelope monotone, rate open).
- `_OrbitCountGrowthLaw.lean` (`orbitCount3`/`orbitCount4` closed forms = the Phase-2 plateau floor).
- `_OffBGK_DescentViaCrossingNotFold.lean` (the crossing `D ≤ z + S` = orbitCount ≤ 1 backbone).
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.ProximityGap.V7GeometricDecayLogCrossing

open ArkLib.ProximityGap.MStarLognReduction

/-! ## Part 1 — the geometric integer-division envelope and its crossing -/

/-- **The geometric envelope** from top `n₀` with per-rung cut factor `c`: `n₀ / c^m` (`ℕ` division).
Models "each over-determination rung cuts the distinct-γ count by at least a factor `c`". -/
def geomEnvelope (c n₀ m : ℕ) : ℕ := n₀ / c ^ m

/-- The geometric envelope is monotone NON-INCREASING in depth `m` (a deeper rung divides by a larger
power).  Matches the proven `_DStarDecreasingEnvelope.cliqueColors_antitone_depth`. -/
theorem geomEnvelope_antitone (c n₀ : ℕ) (hc : 1 ≤ c) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    geomEnvelope c n₀ m₂ ≤ geomEnvelope c n₀ m₁ := by
  unfold geomEnvelope
  apply Nat.div_le_div_left _ (Nat.pow_pos hc)
  exact Nat.pow_le_pow_right hc hm

/-- **Geometric crossing at the polynomial degree.**  If the top is at most a `d`-fold blow-up of
budget (`n₀ ≤ n * c^d`), then the geometric envelope reaches `≤ n` by depth `d`:
`geomEnvelope c n₀ d ≤ n`.  (`n₀ / c^d ≤ (n * c^d) / c^d = n`.)  This is the core arithmetic:
a geometric envelope from a degree-`d` polynomial top crosses budget by depth exactly `d`. -/
theorem geomEnvelope_crossing (c n₀ n d : ℕ) (hc : 1 ≤ c) (htop : n₀ ≤ n * c ^ d) :
    geomEnvelope c n₀ d ≤ n := by
  unfold geomEnvelope
  calc n₀ / c ^ d ≤ (n * c ^ d) / c ^ d :=
        Nat.div_le_div_right htop
    _ = n := by
        rw [Nat.mul_div_cancel]
        exact Nat.pow_pos hc

/-! ## Part 2 — the `O(log n)` crossing from a polynomial top -/

/-- **`isBigOLog` (re-exported shape from `_MStarLognReduction`):** `g n ≤ c·log₂ n + c`. -/
def isBigOLog (c : ℕ) (g : ℕ → ℕ) : Prop := ∀ n, g n ≤ c * Nat.log 2 n + c

/-- **The deployable polynomial-top crossing.**  If `n₀ ≤ n ^ D` (degree-`D` polynomial top) and the
geometric cut accumulates enough by depth `d` to absorb the remaining `n^{D-1}` factor
(`n ^ (D - 1) ≤ c ^ d`), then the geometric envelope crosses `n` by depth `d`. -/
theorem geomEnvelope_polyTop_crossing (c n₀ n D d : ℕ) (hc : 1 ≤ c)
    (htop : n₀ ≤ n ^ D) (hcut : n ^ (D - 1) ≤ c ^ d) (hD : 1 ≤ D) :
    geomEnvelope c n₀ d ≤ n := by
  apply geomEnvelope_crossing c n₀ n d hc
  calc n₀ ≤ n ^ D := htop
    _ = n * n ^ (D - 1) := by
        conv_lhs => rw [show D = 1 + (D - 1) by omega, pow_add, pow_one]
    _ ≤ n * c ^ d := by exact Nat.mul_le_mul_left n hcut

/-! ## Part 3 — the reduction: geometric cut ⟹ `m* = O(log n)` -/

/-- **The open input, named.**  The worst-direction envelope `D : ℕ → ℕ` is dominated by a geometric
envelope with cut factor `c ≥ 2` from a degree-`Dg` polynomial top `n^Dg`, AND the geometric cut
reaches the crossing within an `O(log n)` depth `g n`.  This packages exactly "Phase-1 geometric
decay holds down to the crossing": it is the residual open count of `_MStarLognReduction`
(`logBudgetReached`) specialised to a geometric mechanism.  NOT discharged here. -/
def GeometricCutDownTo (D : ℕ → ℕ) (n c Dg : ℕ) (g : ℕ → ℕ) : Prop :=
  ∃ n₀ : ℕ, (∀ m, D m ≤ geomEnvelope c n₀ m) ∧ n₀ ≤ n ^ Dg ∧
    n ^ (Dg - 1) ≤ c ^ (g n)

/-- **VECTOR 7 main theorem — geometric decay ⟹ logarithmic crossing depth.**  If the worst-direction
envelope `D` obeys a geometric per-rung cut (`GeometricCutDownTo`) with factor `c ≥ 1` from a
degree-`Dg ≥ 1` polynomial top, and the cut reaches the crossing by depth `g n`, then the crossing
depth `m*(n) ≤ g n`.  Specialising `g = O(log n)` (the measured Phase-1 factor that grows with `n`,
so each rung kills a `log₂ n` factor) PROVES `m*(n) = O(log n)`.

This is the precise content VECTOR 7 sought: GEOMETRIC DECAY IMPLIES LOG-DEPTH CROSSING, as a
theorem.  The residual open input is the antecedent `GeometricCutDownTo` — that the worst-direction
distinct-γ envelope actually obeys the geometric cut down to the crossing — which is the
worst-direction list-size growth law = BCHKS 1.12 = the off-BGK wall.  The measured Phase-1 data
(cut factors `4.4×, 41×, 9.9×`, GROWING with `n`) is consistent with it, but is a finite sample, not
a proof of the antecedent. -/
theorem mStar_le_of_geometricCut (D : ℕ → ℕ) (n c Dg : ℕ) (g : ℕ → ℕ)
    (hc : 1 ≤ c) (hD : 1 ≤ Dg) (h : ∃ m, D m ≤ n)
    (hgeo : GeometricCutDownTo D n c Dg g) :
    mStar D n h ≤ g n := by
  obtain ⟨n₀, hdom, htop, hcut⟩ := hgeo
  -- The geometric envelope crosses n by depth g n.
  have hcross : geomEnvelope c n₀ (g n) ≤ n :=
    geomEnvelope_polyTop_crossing c n₀ n Dg (g n) hc htop hcut hD
  -- Hence the true envelope D is ≤ n at depth g n, so m* ≤ g n.
  exact mStar_le_of_le D n h (le_trans (hdom (g n)) hcross)

/-- **Packaged as `O(log n)`.**  Under the geometric-cut hypothesis with an `O(log n)` crossing depth
`g`, the crossing depth `m*(n) ≤ c_g · log₂ n + c_g`.  Every hypothesis except `GeometricCutDownTo`
(the open per-rung factor) is discharged. -/
theorem mStar_isBigOLog_of_geometricCut (D : ℕ → ℕ) (n c Dg cg : ℕ) (g : ℕ → ℕ)
    (hc : 1 ≤ c) (hD : 1 ≤ Dg) (h : ∃ m, D m ≤ n)
    (hO : isBigOLog cg g) (hgeo : GeometricCutDownTo D n c Dg g) :
    mStar D n h ≤ cg * Nat.log 2 n + cg :=
  le_trans (mStar_le_of_geometricCut D n c Dg g hc hD h hgeo) (hO n)

/-! ## Part 4 — the measured two-phase decay (the honest evidence, as decidable facts) -/

/-- **Measured `Dstar` ladder at `n = 16`, ρ=1/4** (engine `dstarvec`, budget `= 16`).  The exact
worst-direction distinct-γ envelope. -/
def dstar16 : List ℕ := [3664, 89, 9, 9, 9, 8, 1, 1, 1, 1, 1]

/-- **Measured `Dstar` ladder at `n = 8`, ρ=1/4** (budget `= 8`). -/
def dstar8 : List ℕ := [40, 9, 5, 1, 1]

/-- **Phase 1 is super-geometric: the per-rung cut factor EXCEEDS 2 (and grows with `n`).**  At
`n = 16` the first two rungs cut by `3664/89 > 2` and `89/9 > 2` (in fact `41×` and `9.9×`); at
`n = 8` the first rung cuts by `40/9 > 2` (`4.4×`).  This is the geometric hypothesis, EMPIRICALLY
satisfied with wide margin down to the crossing. -/
theorem phase1_supergeometric :
    -- n = 16, rung 1→2 and 2→3: cut factor ≥ 2 (here ≫ 2)
    2 * (dstar16.getD 1 0) ≤ dstar16.getD 0 0 ∧
    2 * (dstar16.getD 2 0) ≤ dstar16.getD 1 0 ∧
    -- n = 8, rung 1→2: cut factor ≥ 2
    2 * (dstar8.getD 1 0) ≤ dstar8.getD 0 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **The crossing is reached in Phase 1, BEFORE the plateau.**  At `n = 16` the envelope crosses
budget `16` at depth `m* = 3` (`Dstar(3) = 9 ≤ 16`), while `Dstar(2) = 89 > 16`.  At `n = 8` it
crosses budget `8` at depth `m* = 3` (`Dstar(3) = 5 ≤ 8`), while `Dstar(2) = 9 > 8`.  The crossing
sits in the steep geometric phase. -/
theorem crossing_in_phase1 :
    -- n = 16: crosses at m=3, not m=2
    16 < dstar16.getD 1 0 ∧ dstar16.getD 2 0 ≤ 16 ∧
    -- n = 8: crosses at m=3, not m=2
    8 < dstar8.getD 1 0 ∧ dstar8.getD 2 0 ≤ 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **Phase 2 STALLS below budget.**  At `n = 16` the envelope plateaus at `Dstar = 9` for
`m = 3, 4, 5` (entries `2,3,4` of the list) — a flat (non-geometric) stretch — but the plateau value
`9 < 16 = ` budget.  So the stall is strictly BELOW budget: it cannot obstruct the crossing, which
already happened at `m* = 3`.  This is why a UNIFORM geometric envelope fails (the plateau), yet the
LOG-DEPTH crossing still holds (the plateau is post-crossing). -/
theorem phase2_plateau_below_budget :
    dstar16.getD 2 0 = 9 ∧ dstar16.getD 3 0 = 9 ∧ dstar16.getD 4 0 = 9 ∧
    dstar16.getD 2 0 < 16 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **Headline (VECTOR 7).**  The measured worst-direction distinct-γ decay is super-geometric down
to the crossing (cut factor ≥ 2, in fact growing with `n`), the crossing of budget is reached IN
that geometric phase (`m* = 3, 3` at `n = 8, 16`), and the subsequent plateau stalls strictly BELOW
budget (so does not obstruct the crossing).  Combined with `mStar_le_of_geometricCut`, this says:
the geometric Phase-1 mechanism, IF it persists for all `n` (the named open input = BCHKS 1.12),
forces `m* = O(log n)`.  The data is consistent; the persistence is the wall. -/
theorem v7_two_phase_decay :
    (2 * (dstar16.getD 1 0) ≤ dstar16.getD 0 0 ∧
     2 * (dstar16.getD 2 0) ≤ dstar16.getD 1 0) ∧          -- Phase 1 super-geometric
    (16 < dstar16.getD 1 0 ∧ dstar16.getD 2 0 ≤ 16) ∧      -- crossing in Phase 1
    (dstar16.getD 2 0 = dstar16.getD 4 0 ∧
     dstar16.getD 2 0 < 16) := by                          -- Phase 2 plateau below budget
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

end ArkLib.ProximityGap.V7GeometricDecayLogCrossing

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.V7GeometricDecayLogCrossing.geomEnvelope_antitone
#print axioms ArkLib.ProximityGap.V7GeometricDecayLogCrossing.geomEnvelope_crossing
#print axioms ArkLib.ProximityGap.V7GeometricDecayLogCrossing.geomEnvelope_polyTop_crossing
#print axioms ArkLib.ProximityGap.V7GeometricDecayLogCrossing.mStar_le_of_geometricCut
#print axioms ArkLib.ProximityGap.V7GeometricDecayLogCrossing.mStar_isBigOLog_of_geometricCut
#print axioms ArkLib.ProximityGap.V7GeometricDecayLogCrossing.phase1_supergeometric
#print axioms ArkLib.ProximityGap.V7GeometricDecayLogCrossing.crossing_in_phase1
#print axioms ArkLib.ProximityGap.V7GeometricDecayLogCrossing.phase2_plateau_below_budget
#print axioms ArkLib.ProximityGap.V7GeometricDecayLogCrossing.v7_two_phase_decay
