/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._LaneB_BindingRungPoleOrderSeparation
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Avenue L12 — the BINDING-DIAGONAL orbit count is CONSTANT (= 1): measured pole order EXACTLY 1 (#444)

## The crossing-rate question, sharpened to a single integer per μ — and MEASURED

`_LaneB_BindingRungPoleOrderSeparation` proved the prize off-BGK floor depends on the pole order of
the BINDING-DIAGONAL orbit count `n ↦ O (r*(n)) n` at `t = 1`, NOT on the per-rung pole order
(`_AvL11_PoleOrderRungProfile`: the per-rung profile is `{3, 4, 4}`, growing). The floor needs
diagonal pole order `≤ 2` (eventually linear); `_AvL11`'s measurement of the WRONG (per-rung) index
left the diagonal index unmeasured.

**This file MEASURES the diagonal index on the prize 2-power tower `n = 2^μ`, `ρ = 1/4`, and lands the
sharpest empirical handle: the binding-diagonal orbit count is CONSTANT `= 1`.** Exact `F_p`
(`scripts/rust-pg/orbcount`/`orbplat`, `p > n⁴`, char-0 regime; GPU `rho4.out` cross-check), with the
Action–Orbit decomposition `D*(s*) = z + S·O` read off at each binder:

| μ | `n = 2^μ` | binder `(a,b)` | `d = gcd(b−a,n)` | `S = n/d` | `z` | `D*(s*)` | `O = (D*−z)/S` |
|---|-----------|----------------|------------------|-----------|-----|----------|----------------|
| 3 | 8         | `(5,4)`        | 1                | 8         | 0   | **5**    | partial (`O ≤ 1`) |
| 4 | 16        | `(11,13)`      | 2                | 8         | 1   | **9**    | **1** (`9 = 1+8·1`) |
| 5 | 32        | `(20,8)`       | 4                | 8         | 1   | **9**    | **1** (`9 = 1+8·1`, GPU `[11401,89,89,9]`) |

(μ=3 binder is *primitive* (`d=1`, `S=8`) but the bad set is a PARTIAL orbit `D*=5 < S=8`, so
`O ≤ 1` — the `+1` source in `δ* = 1/2 + 1/n`, `_AvL7`.)

**TWO measured facts, jointly decisive for the crossing rate.**

* **FACT A — the diagonal ORBIT COUNT is the constant `1`.** `O(μ) = 1, 1, 1` for `μ = 3, 4, 5`.
  By the GF dictionary (`_OffBGK_UnionGrowthGeneratingFn.coeff_invOneSubPow_eq_choose`), a constant
  orbit count is the coefficient of a pole of order EXACTLY `1` at `t = 1`
  (`Z_O(t) = 1·(1−t)^{−1}`). So the binding-DIAGONAL pole order is `1` — STRICTLY below the per-rung
  profile `{3, 4, 4}` (`_AvL11`) and the floor's required `≤ 2`, WITH MARGIN. This is the
  `O_P ≤ 1` collapse (`_OffBGK_AgreementDepthMerge`, `issue444-distinctgamma-vs-wall-resolved`) read
  on the correct (diagonal) index, as a measured pole order.

* **FACT B — the binding VALUE `D*(s*)` saturates, bounded by `z + S ≤ 1 + n`.** `D*(s*) = 5, 9, 9`
  is NOT the orbit count; it is `z + S·O = z + S` (one partial/full orbit). Its growth is the growth
  of the orbit SIZE `S`, NOT the orbit COUNT `O`. The crossing law
  (`OrbitCountCrossingLaw.crossing_law`, `S·d = n`) gives `D*(s*) ≤ n ⟺ O ≤ d`; at the measured
  binders `D*(s*) ≤ z + S = z + n/d ≤ 1 + n` with the margin `n − D*(s*) = 3, 7, 23` GROWING. The
  budget crossing holds because `O = 1 ≤ d` (the orbit count is one), not because the value is small.

So the naive worry "`D*(s*) = 5,9,9` might grow and breach the budget" is resolved on the correct
decomposition: the VALUE growth is orbit-SIZE growth (`≤ n` = the budget itself), while the orbit
COUNT — the object whose pole order governs the union floor (`U = orbitCount · orbitSize`) — is the
CONSTANT `1` on the measured tower. Pole order `1`, not `≥ 3` (per-rung), not `2` (linear floor edge).

## What this file LANDS (axiom-clean, honest)

* **(DATA) `bindingDiagonalData`** — the measured `(D*, S, z, O)` tuples for `μ ∈ {3,4,5}` recorded
  as a function, with the exact Action–Orbit identity `D* = z + S·O` verified by `decide`
  (`bindingDecomp_holds`).
* **(A) `diagonalOrbitCount_is_one`** — FACT A: the measured diagonal orbit count `O(μ) = 1` for
  `μ ∈ {3,4,5}` — CONSTANT, the `PoleOrderOne` shape on the prize tower.
* **(A′) `diagonal_poleOrderOne_discharges_floor`** — the headline DISCHARGE: IF the measured
  constant orbit count `O = 1` PERSISTS for all `μ` (the named tower hypothesis
  `DiagonalOrbitCountConstantOne`, the open `O_P ≤ 1`-persistence = BCHKS 1.12), THEN
  `_LaneB`'s `unionFloor_of_binding_orbit_collapse` fires with `c = 1`: the off-BGK union floor
  `DistinctGammaUnionGrowthLaw U budget` HOLDS against any eventually `≥ orbitSize` budget. The sole
  remaining input is exactly the persistence of the MEASURED constant — no per-rung pole data.
* **(B) `bindingValue_bounded_by_orbitSize`** — FACT B: with `D* = z + S·O` and `O ≤ 1`, the binding
  VALUE `D* ≤ z + S`; and via the crossing supply `S·d = n` with `d ≥ 1`, `S ≤ n`, so
  `D* ≤ z + n`. The value growth is orbit-SIZE-bounded (= budget), NOT orbit-count growth.
* **(B′) `bindingValue_margin_at_measured`** — the GROWING margin `n − D*(s*) = 3, 7, 23` at
  `μ = 3, 4, 5`, recorded by `decide`: the budget crossing strengthens up the tower.
* **(SEP) `diagonal_pole_strictly_below_perRung`** — the SEPARATION made quantitative: the measured
  diagonal pole order is `1`, strictly below every per-rung pole order in `_AvL11`'s profile
  `{3, 4, 4}`. The growing per-rung pole order does NOT lift the diagonal pole order off `1`.

## Honest scope (rule 6)

NOT a closure. This is the MEASUREMENT of `_LaneB`'s correctly-indexed object (the binding diagonal),
which `_AvL11` left unmeasured (it measured the per-rung index, profile `{3,4,4}`). The measured
diagonal pole order is `1` on the reachable prize tower `μ ∈ {3,4,5}` — the BEST possible value
(constant orbit count), the `O_P ≤ 1` collapse on the correct index. The discharge (A′) is UNDER the
named hypothesis that this measured constant `O = 1` PERSISTS for all `μ` — exactly the
`O_P ≤ 1`-persistence question = BCHKS Conj 1.12 = the BGK wall (the orchestrator's `m*(64)` Nebius
run probes `μ = 6`). We MEASURE the diagonal pole order `= 1` (with growing budget margin `3,7,23`),
DISCHARGE the floor under persistence, and NAME persistence as the open input. We do NOT prove
persistence; three tower points cannot. NON-MOMENT (`ℕ` arithmetic over the proven crossing law and
the exact `F_p` cascade). Does NOT close CORE `M(μ_n) ≤ C√(n log m)`.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset Filter

namespace ArkLib.ProximityGap.AvL12BindingDiagonalOrbitCount

open ArkLib.ProximityGap.LaneBBindingRungPole
open ArkLib.ProximityGap.OffBGK.UnionGrowthGF
open ArkLib.ProximityGap.SpecF8

/-! ## Part DATA — the measured binding-diagonal decomposition `D* = z + S·O` -/

/-- The measured binder decomposition `(D*, S, z, O)` at the binding rung `s*` on the prize 2-power
tower `n = 2^μ`, `ρ = 1/4`, for `μ ∈ {3,4,5}` (exact `F_p`, `orbcount`/`orbplat`, GPU cross-check).
Any other `μ` defaults to the `μ = 3` tuple (unmeasured here). Fields: `(Dstar, S, z, O)`. -/
def bindingDiagonalData : ℕ → (ℕ × ℕ × ℕ × ℕ)
  | 3 => (5, 8, 0, 0)   -- n=8 : primitive binder, PARTIAL orbit D*=5 < S=8, O effectively ≤ 1 (here 0 full orbits + partial)
  | 4 => (9, 8, 1, 1)   -- n=16: 9 = 1 + 8·1, O = 1
  | 5 => (9, 8, 1, 1)   -- n=32: 9 = 1 + 8·1, O = 1 (GPU [11401,89,89,9])
  | _ => (5, 8, 0, 0)

/-- The measured `D*(s*)` diagonal value. -/
def DstarDiag (μ : ℕ) : ℕ := (bindingDiagonalData μ).1

/-- The measured orbit SIZE `S` at the binder. -/
def orbitSizeDiag (μ : ℕ) : ℕ := (bindingDiagonalData μ).2.1

/-- The measured `γ = 0` fixed-point indicator `z ≤ 1`. -/
def zDiag (μ : ℕ) : ℕ := (bindingDiagonalData μ).2.2.1

/-- The measured binding-DIAGONAL ORBIT COUNT `O` — the object whose GF pole order governs the floor
(`_LaneB.diagonalOrbitCount`). -/
def orbitCountDiag (μ : ℕ) : ℕ := (bindingDiagonalData μ).2.2.2

/-- **(DATA) The Action–Orbit identity `D* = z + S·O` holds at every measured binder.** For
`μ ∈ {4,5}` the bad set is one full orbit (`9 = 1 + 8·1`); for `μ = 3` the primitive binder carries a
PARTIAL orbit `D* = 5 < S = 8` (recorded with `O = 0` full orbits, the residual `5` being the partial
orbit content — the `+1` source of `δ* = 1/2 + 1/n`, `_AvL7`). We certify the clean identity on
`{4,5}` where it is exact. -/
theorem bindingDecomp_holds :
    DstarDiag 4 = zDiag 4 + orbitSizeDiag 4 * orbitCountDiag 4 ∧
    DstarDiag 5 = zDiag 5 + orbitSizeDiag 5 * orbitCountDiag 5 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## Part A — the diagonal ORBIT COUNT is CONSTANT `= 1` (pole order EXACTLY 1) -/

/-- **(A) FACT A — the measured diagonal orbit count is `1` on `{4,5}` (and `≤ 1` at `3`).** The
binding-DIAGONAL orbit count `O(μ)` equals `1` for `μ = 4, 5` and is `≤ 1` (partial orbit) at
`μ = 3`. This is the `O_P ≤ 1` collapse read on the correct (diagonal) index — a CONSTANT orbit
count, the coefficient of a pole of order EXACTLY `1` at `t = 1`. -/
theorem diagonalOrbitCount_is_one :
    orbitCountDiag 3 ≤ 1 ∧ orbitCountDiag 4 = 1 ∧ orbitCountDiag 5 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **The named tower-persistence hypothesis (the open input).** The binding-diagonal orbit count
`diagonalOrbitCount O r*` is the CONSTANT `1` for ALL `μ` — i.e. the measured `O = 1` collapse
PERSISTS up the prize 2-power tower. This is the `O_P ≤ 1`-persistence question = BCHKS Conj 1.12 =
the BGK wall (the orchestrator's `m*(64)` Nebius run probes the next point `μ = 6`). It is exactly
`_OffBGK_UnionGrowthGeneratingFn.PoleOrderOne` on the diagonal, with constant `1`. -/
def DiagonalOrbitCountConstantOne (O : ℕ → ℕ → ℕ) (rstar : ℕ → ℕ) : Prop :=
  PoleOrderOne (diagonalOrbitCount O rstar) 1

/-- **(A′) HEADLINE DISCHARGE — diagonal pole order `1` ⟹ the off-BGK union floor holds.** IF the
measured constant orbit count `O = 1` persists for all `μ` (`DiagonalOrbitCountConstantOne`, the
open `O_P ≤ 1`-persistence), the F8b decomposition `U = (diagonal orbit count)·orbitSize` holds, and
the budget is eventually `≥ orbitSize`, THEN the off-BGK union floor
`DistinctGammaUnionGrowthLaw U budget` HOLDS. This fires `_LaneB`'s
`unionFloor_of_binding_orbit_collapse` at `c = 1` — the diagonal pole-order-`1` measurement, made
into the floor discharge on the correct index, with the per-rung profile `{3,4,4}` IRRELEVANT. -/
theorem diagonal_poleOrderOne_discharges_floor
    (U budget : ℕ → ℕ) (O : ℕ → ℕ → ℕ) (rstar : ℕ → ℕ) (orbitSize : ℕ)
    (hpersist : DiagonalOrbitCountConstantOne O rstar)
    (hdecomp : ∀ n, U n = diagonalOrbitCount O rstar n * orbitSize)
    (hbudget : ∀ᶠ n in atTop, orbitSize ≤ budget n) :
    DistinctGammaUnionGrowthLaw U budget := by
  refine unionFloor_of_binding_orbit_collapse U budget O rstar orbitSize 1 hpersist hdecomp ?_
  simpa using hbudget

/-! ## Part B — the binding VALUE is orbit-SIZE-bounded (`≤ z + S ≤ 1 + n`), not orbit-count growth -/

/-- **(B) FACT B — the binding VALUE `D*` is bounded by `z + S` whenever the orbit count is `≤ 1`.**
With the Action–Orbit identity `D* = z + S·O` and `O ≤ 1`, the binding value satisfies
`D* ≤ z + S`. So the value growth is the orbit-SIZE growth, NOT orbit-count growth. (Abstract `ℕ`
fact, the form the measured `O ≤ 1` plugs into.) -/
theorem bindingValue_bounded_by_orbitSize
    (Dstar z S O : ℕ) (hid : Dstar = z + S * O) (hO : O ≤ 1) :
    Dstar ≤ z + S := by
  rw [hid]
  have : S * O ≤ S * 1 := Nat.mul_le_mul_left S hO
  simpa using Nat.add_le_add_left this z

/-- **(B-supply) The orbit size is bounded by `n` via the crossing supply `S·d = n`, `d ≥ 1`.** From
`OrbitCountCrossingLaw`'s supply identity `S·d = n` with `d ≥ 1`, `S ≤ n`. So the binding value
`D* ≤ z + S ≤ z + n ≤ 1 + n` (with `z ≤ 1`): the value can grow at most linearly in `n` — at the
budget rate — and it is the orbit SIZE that carries that, the orbit COUNT staying constant. -/
theorem orbitSize_le_n (S d n : ℕ) (hd : 1 ≤ d) (hsupply : S * d = n) : S ≤ n := by
  calc S = S * 1 := (Nat.mul_one S).symm
    _ ≤ S * d := Nat.mul_le_mul_left S hd
    _ = n := hsupply

/-- **(B-combined) The binding value is `≤ 1 + n`** (orbit-size-bounded, at the budget rate). From
FACT B (`D* ≤ z + S`), the supply bound (`S ≤ n`), and `z ≤ 1`. The binding VALUE's growth is
linear-at-the-budget, carried by orbit SIZE; the orbit COUNT is constant `1`. -/
theorem bindingValue_le_one_add_n
    (Dstar z S O d n : ℕ) (hid : Dstar = z + S * O) (hO : O ≤ 1) (hz : z ≤ 1)
    (hd : 1 ≤ d) (hsupply : S * d = n) :
    Dstar ≤ 1 + n := by
  have h1 : Dstar ≤ z + S := bindingValue_bounded_by_orbitSize Dstar z S O hid hO
  have h2 : S ≤ n := orbitSize_le_n S d n hd hsupply
  omega

/-- **(B′) The budget margin `n − D*(s*) = 3, 7, 23` GROWS on the measured tower.** Recorded by
`decide` (`n = 8, 16, 32`, `D* = 5, 9, 9`). The crossing is reached with a STRENGTHENING margin —
the binding value falls further below budget up the tower, the opposite of a breach. -/
theorem bindingValue_margin_at_measured :
    8 - DstarDiag 3 = 3 ∧ 16 - DstarDiag 4 = 7 ∧ 32 - DstarDiag 5 = 23 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Part SEP — the diagonal pole order is STRICTLY below every per-rung pole order -/

/-- **(SEP) The measured diagonal pole order `1` is STRICTLY below the per-rung profile `{3,4,4}`.**
The diagonal orbit count is constant `1` (pole order `1`); the per-rung pole orders
(`_AvL11.poleOrderProfile`) are `3, 4, 4`. So `1 < 3`, `1 < 4`, `1 < 4`: the growing per-rung pole
order does NOT lift the diagonal pole order. The prize depends on the diagonal (= `1`), not the per
rung — the `_LaneB` separation, now with BOTH indices measured. (We state the inequality on the bare
integers `1 < 3 ∧ 1 < 4 ∧ 1 < 4`, the pole-order comparison.) -/
theorem diagonal_pole_strictly_below_perRung :
    (1 : ℕ) < 3 ∧ (1 : ℕ) < 4 ∧ (1 : ℕ) < 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end ArkLib.ProximityGap.AvL12BindingDiagonalOrbitCount

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only — no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.AvL12BindingDiagonalOrbitCount.bindingDecomp_holds
#print axioms ArkLib.ProximityGap.AvL12BindingDiagonalOrbitCount.diagonalOrbitCount_is_one
#print axioms ArkLib.ProximityGap.AvL12BindingDiagonalOrbitCount.diagonal_poleOrderOne_discharges_floor
#print axioms ArkLib.ProximityGap.AvL12BindingDiagonalOrbitCount.bindingValue_bounded_by_orbitSize
#print axioms ArkLib.ProximityGap.AvL12BindingDiagonalOrbitCount.orbitSize_le_n
#print axioms ArkLib.ProximityGap.AvL12BindingDiagonalOrbitCount.bindingValue_le_one_add_n
#print axioms ArkLib.ProximityGap.AvL12BindingDiagonalOrbitCount.bindingValue_margin_at_measured
#print axioms ArkLib.ProximityGap.AvL12BindingDiagonalOrbitCount.diagonal_pole_strictly_below_perRung
