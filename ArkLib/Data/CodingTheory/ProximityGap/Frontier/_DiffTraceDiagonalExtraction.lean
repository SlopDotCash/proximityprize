/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NextDifferenceVariety

/-!
# EXTEND — the diagonal-extraction bridge `FullTrace = #Rel + DiffTrace` (#444)

**Frontier-movement extension of `_NextDifferenceVariety`.**  That file reduced the off-diagonal
*second* moment to the *punctured first moment* of `Jphase` over the difference variety,
`DiffTrace θ Rel = Σ_T Σ_{T' ≠ T} Jphase θ (diffTuple T T')`, where the inner sum runs over
`Rel.erase T` (i.e. `T' ≠ T`).  The named open core is a bound on `(DiffTrace).re`, to be supplied
by a Lang–Weil / Katz character-sum estimate on the variety `V_diff`.

But a Lang–Weil / Katz point count naturally produces the **FULL** (unpunctured) sum — the one that
ALSO ranges over the diagonal `T = T'`.  This file pins the exact relationship between the punctured
object the variance core needs and the unpunctured object an algebraic-geometry estimate produces,
by **extracting the diagonal explicitly**.

## The mechanism — the diagonal terms are each `1`

For a unit additive character `θ`, every `Jphase θ x` is a **unit** (`Jphase_normSq_eq_one`:
`(∏ θ(x_i))·conj(θ(Σ x_i))` is a product of unit-modulus factors).  Hence by the summand reduction
`pairCorr_eq_diff` of `_NextDifferenceVariety` specialized to `T' = T`,
```
        Jphase θ (diffTuple T T)  =  Jphase θ T · conj (Jphase θ T)  =  |Jphase θ T|²  =  1.
                                                                     (diffTuple_diag_eq_one)
```
The diagonal of the full first moment is therefore exactly `#Rel · 1 = #Rel` (`fullDiagonal_eq_card`).

## The headline identity — `fullTrace_eq_card_add_diffTrace`

Define the **full** (unpunctured) first moment over `Rel × Rel`:
```
        FullTrace θ Rel  :=  Σ_T Σ_{T' ∈ Rel} Jphase θ (diffTuple T T').
```
Splitting the inner sum over `Rel` into the diagonal `{T}` and the off-diagonal `Rel.erase T` gives
the EXACT decomposition
```
        FullTrace θ Rel  =  #Rel  +  DiffTrace θ Rel,
```
equivalently `DiffTrace θ Rel = FullTrace θ Rel − #Rel`.  This is the **explicit main term**: a
Katz/Lang–Weil estimate on the full point count `FullTrace` must have its `#Rel`-sized diagonal main
term subtracted to recover the variance-core object `DiffTrace`.  The off-diagonal cancellation the
prize needs is the FULL count minus this explicit, computed, real, integer main term `#Rel`.

## Consequence for the open core

Combined with `_DiffTraceReality` (`DiffTrace` is real) and the modulus bridge
`firstMoment_modulus_to_re`, this gives the clean consumer chain a future third-party estimate plugs
into:
```
   |FullTrace − #Rel| ≤ S    (Katz/Lang–Weil, main term #Rel subtracted)
        ⟹ |DiffTrace| ≤ S                              (fullTrace_eq_card_add_diffTrace)
        ⟹ (DiffTrace).re ≤ S = FirstMomentDiffCancellation θ Rel S   (firstMoment_modulus_to_re)
        ⟹ off-diagonal second-moment real part ≤ S      (firstMoment_to_secondMoment_bound).
```
`fullTrace_sub_card_modulus_to_core` packages exactly this: a modulus bound on the
**diagonal-subtracted full trace** discharges the named open core with the same slack.

## Probe

`scripts/probes/probe_dooriv_difftrace_diagonal_extraction.py` (proper `μ_n < F_p^*`, `p ≫ n³`,
never `n = q−1`, `n = 16,32,64`, `β ∈ {4,4.5}`, `r ∈ {3,4,5}`): each diagonal term
`Jphase(diffTuple T T)` equals `1` to `≤ 4·10⁻¹⁵` (float noise), the factorization
`Jphase(diffTuple T T') = Jphase(T)·conj Jphase(T')` holds to `≤ 5·10⁻¹⁵`, and the decomposition
`FullTrace = #Rel + DiffTrace` holds to `≤ 8·10⁻¹⁴`.  Concretely `Full.re = #Rel²` and
`Diff.re = #Rel² − #Rel`, so the diagonal is exactly `#Rel`.

## What this file PROVES (axiom-clean, no `sorry`)

* `Jphase_normSq_eq_one` — `Jphase θ x` is a unit (modulus `1`) for a unit additive character `θ`;
* `diffTuple_diag_eq_one` — each diagonal term `Jphase θ (diffTuple T T) = 1`;
* `FullTrace` / `fullDiagonal_eq_card` — the full (unpunctured) first moment, and that its diagonal
  contribution is exactly `#Rel`;
* `fullTrace_eq_card_add_diffTrace` — THE identity `FullTrace θ Rel = #Rel + DiffTrace θ Rel`;
* `diffTrace_eq_fullTrace_sub_card` — the inverted form `DiffTrace = FullTrace − #Rel`;
* `fullTrace_sub_card_modulus_to_core` — a modulus bound on the diagonal-subtracted full trace
  discharges the named open core `FirstMomentDiffCancellation`.

NO CORE / cancellation / completion / moment-saving / capacity claim: `FullTrace` is NOT bounded
here.  This is a structural diagonal-extraction identity plus the consumer bridge that tells an
third-party Katz/Lang–Weil estimate the explicit `#Rel` main term to subtract.  #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ}

/-! ## §1 The iterated Jacobi phase is a unit -/

/-- **`Jphase_normSq_eq_one`** — for a unit additive character `θ` (each `θ s` has
`Complex.normSq (θ s) = 1`), the iterated Jacobi phase `Jphase θ x = (∏ θ(x_i))·conj(θ(Σ x_i))` is a
unit: `Complex.normSq (Jphase θ x) = 1`.  A product of unit-modulus factors (`∏ θ(x_i)` is a product
of units, and `conj` preserves `normSq`). -/
theorem Jphase_normSq_eq_one (hunit : ∀ s, Complex.normSq (θ s) = 1) (x : Fin r → R) :
    Complex.normSq (Jphase θ x) = 1 := by
  unfold Jphase
  rw [map_mul, Complex.normSq_conj]
  have hprod : Complex.normSq (∏ i, θ (x i)) = 1 := by
    rw [map_prod]
    rw [Finset.prod_congr rfl (fun i _ => hunit (x i))]
    simp
  rw [hprod, hunit, mul_one]

/-! ## §2 The diagonal terms of the difference variety are each `1` -/

/-- **`diffTuple_diag_eq_one`** — for a unit additive character `θ`, each *diagonal* first-moment
term is exactly `1`: `Jphase θ (diffTuple T T) = 1`.  By `pairCorr_eq_diff` (specialized to `T' = T`)
the diagonal term is `Jphase θ T · conj (Jphase θ T) = |Jphase θ T|² = 1` since `Jphase θ T` is a
unit. -/
theorem diffTuple_diag_eq_one (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (T : Fin r → R) :
    Jphase θ (diffTuple T T) = 1 := by
  rw [← pairCorr_eq_diff hmul hone hunit T T]
  have h := Complex.mul_conj (Jphase θ T)
  rw [Jphase_normSq_eq_one hunit T] at h
  simpa using h

/-! ## §3 The full (unpunctured) first moment and its diagonal -/

variable [DecidableEq (Fin r → R)]

/-- **`FullTrace`** — the **full** (unpunctured) first moment of `Jphase` over the difference variety:
`Σ_T Σ_{T' ∈ Rel} Jphase θ (diffTuple T T')`, the inner sum ranging over ALL of `Rel` (INCLUDING the
diagonal `T = T'`).  This is the object a Lang–Weil / Katz point count produces; `DiffTrace` (the
punctured version) is what the variance core needs. -/
noncomputable def FullTrace (θ : R → ℂ) (Rel : Finset (Fin r → R)) : ℂ :=
  ∑ T ∈ Rel, ∑ T' ∈ Rel, Jphase θ (diffTuple T T')

/-- **`fullDiagonal_eq_card`** — the diagonal contribution to the full trace is exactly `#Rel`:
`Σ_T Jphase θ (diffTuple T T) = #Rel` (each diagonal term is `1`). -/
theorem fullDiagonal_eq_card (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (∑ T ∈ Rel, Jphase θ (diffTuple T T)) = (Rel.card : ℂ) := by
  rw [Finset.sum_congr rfl (fun T _ => diffTuple_diag_eq_one hmul hone hunit T)]
  simp

/-! ## §4 The headline identity: full = #Rel + off-diagonal -/

/-- **`fullTrace_eq_card_add_diffTrace`** — THE diagonal-extraction identity.  Splitting the inner
sum of the full trace over `Rel` into the diagonal singleton `{T}` and the off-diagonal `Rel.erase T`
(`Finset.sum_eq_sum_diff_singleton_add`, equivalently `add_sum_erase`), the diagonal contributes
exactly `#Rel` (`fullDiagonal_eq_card`) and the off-diagonal contributes exactly `DiffTrace`:
```
        FullTrace θ Rel  =  #Rel  +  DiffTrace θ Rel.
```
The `#Rel`-sized diagonal is the explicit main term a Katz/Lang–Weil estimate on the full point
count must subtract to recover the variance-core off-diagonal cancellation. -/
theorem fullTrace_eq_card_add_diffTrace (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    FullTrace θ Rel = (Rel.card : ℂ) + DiffTrace θ Rel := by
  unfold FullTrace DiffTrace
  -- split each inner sum over Rel into {T}-diagonal + (Rel.erase T) off-diagonal
  have hsplit : ∀ T ∈ Rel,
      (∑ T' ∈ Rel, Jphase θ (diffTuple T T'))
        = Jphase θ (diffTuple T T) + ∑ T' ∈ Rel.erase T, Jphase θ (diffTuple T T') := by
    intro T hT
    rw [← Finset.add_sum_erase Rel (fun T' => Jphase θ (diffTuple T T')) hT]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
      fullDiagonal_eq_card hmul hone hunit Rel]

/-- **`diffTrace_eq_fullTrace_sub_card`** — the inverted form: the variance-core off-diagonal first
moment equals the full point count minus the explicit `#Rel` main term:
`DiffTrace θ Rel = FullTrace θ Rel − #Rel`. -/
theorem diffTrace_eq_fullTrace_sub_card (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    DiffTrace θ Rel = FullTrace θ Rel - (Rel.card : ℂ) := by
  rw [fullTrace_eq_card_add_diffTrace hmul hone hunit Rel]; ring

/-! ## §5 The consumer bridge: a modulus bound on (FullTrace − #Rel) discharges the core -/

/-- **`fullTrace_sub_card_modulus_to_core`** — end-to-end consumer.  A modulus bound on the
**diagonal-subtracted** full trace, `‖FullTrace θ Rel − #Rel‖ ≤ S` (the natural output of a
Lang–Weil / Katz point count with the explicit `#Rel` main term subtracted), yields the named open
core `FirstMomentDiffCancellation θ Rel S` (the `.re` bound on `DiffTrace`) with the SAME slack `S`.
Routes through `diffTrace_eq_fullTrace_sub_card` (identify the subtracted full count with `DiffTrace`)
and `Complex.re_le_norm`.  This is the precise statement of what an third-party algebraic-geometry
estimate must supply, with the main term made explicit. -/
theorem fullTrace_sub_card_modulus_to_core (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (h : ‖FullTrace θ Rel - (Rel.card : ℂ)‖ ≤ S) :
    FirstMomentDiffCancellation θ Rel S := by
  unfold FirstMomentDiffCancellation
  rw [diffTrace_eq_fullTrace_sub_card hmul hone hunit Rel]
  exact le_trans (Complex.re_le_norm _) h

end ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction.Jphase_normSq_eq_one
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction.diffTuple_diag_eq_one
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction.fullDiagonal_eq_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction.fullTrace_eq_card_add_diffTrace
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction.diffTrace_eq_fullTrace_sub_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction.fullTrace_sub_card_modulus_to_core
