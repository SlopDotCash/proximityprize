/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A finite countermodel to the abstract rate-quarter cocircuit count

The cycle matroid of `K_8` has rank seven on 28 edges. Its singleton and
two-vertex bonds give 36 cocircuits of weights seven and twelve, both strictly
below half the ground-set size. Over `F_59`, the two displayed linear forms
put their normals in one affine chart with 36 distinct gamma coordinates.

This file checks the finite cardinality, support-weight, and affine-coordinate
facts by kernel-checked finite proofs. The exact Gaussian-elimination check
that every displayed support is a cocircuit is in
`scripts/probes/probe_rate_quarter_k8_cocircuit_counterexample.py`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterAbstractCocircuitRefuted

abbrev Vertex := Fin 8
abbrev NormalCoordinate := Fin 7
abbrev Edge := {e : Vertex × Vertex // e.1 < e.2}
abbrev F := ZMod 59

instance primeFact_HalfPredecessorRateQuarterAbstractCocircuitRefuted_1 : Fact (Nat.Prime 59) := ⟨by norm_num⟩

/-- Left endpoints for the eight singleton shores followed by the 28
lexicographically ordered two-vertex shores. -/
def leftVertex : Fin 36 → Vertex :=
  ![0, 1, 2, 3, 4, 5, 6, 7,
    0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 1, 1,
    2, 2, 2, 2, 2,
    3, 3, 3, 3,
    4, 4, 4,
    5, 5,
    6]

/-- Right endpoints for the same shore enumeration. The first eight entries
are unused. -/
def rightVertex : Fin 36 → Vertex :=
  ![0, 1, 2, 3, 4, 5, 6, 7,
    1, 2, 3, 4, 5, 6, 7,
    2, 3, 4, 5, 6, 7,
    3, 4, 5, 6, 7,
    4, 5, 6, 7,
    5, 6, 7,
    6, 7,
    7]

/-- The eight singleton and 28 two-vertex shores of `K_8`. -/
def shore (i : Fin 36) : Finset Vertex :=
  if i.1 < 8 then {leftVertex i} else {leftVertex i, rightVertex i}

def Crosses (S : Finset Vertex) (e : Edge) : Prop :=
  (e.1.1 ∈ S) ≠ (e.1.2 ∈ S)

def cutSupport (S : Finset Vertex) : Finset Edge :=
  Finset.univ.filter fun e => (e.1.1 ∈ S) ≠ (e.1.2 ∈ S)

/-- A cut potential modulo constants, in the gauge where vertex eight has
potential zero. -/
def cutNormal (S : Finset Vertex) (i : NormalCoordinate) : F :=
  (if Fin.castSucc i ∈ S then 1 else 0) -
    (if Fin.last 7 ∈ S then 1 else 0)

def dot (a b : NormalCoordinate → F) : F :=
  ∑ i, a i * b i

def ell0 : NormalCoordinate → F :=
  ![19, 48, 49, 55, 22, 42, 5]

def ell1 : NormalCoordinate → F :=
  ![35, 30, 32, 42, 17, 43, 52]

def affineGamma (S : Finset Vertex) : F :=
  dot ell1 (cutNormal S) / dot ell0 (cutNormal S)

/-- Exact gamma table for the displayed chart, in `shore` order. -/
def gammaTable : Fin 36 → F :=
  ![36, 8, 44, 19, 41, 53, 34, 48,
    45, 14, 13, 43, 39, 11, 21,
    42, 7, 15, 29, 6, 58,
    20, 9, 30, 54, 3,
    0, 10, 35, 4,
    12, 55, 46,
    56, 38,
    37]

theorem edge_card : Fintype.card Edge = 28 := by
  decide

/-- Singleton shores cut seven edges and two-vertex shores cut twelve. -/
theorem shore_cutSupport_card (i : Fin 36) :
    (cutSupport (shore i)).card = if i.1 < 8 then 7 else 12 := by
  fin_cases i <;> decide

theorem shore_strictly_below_half (i : Fin 36) :
    2 * (cutSupport (shore i)).card < Fintype.card Edge := by
  rw [shore_cutSupport_card, edge_card]
  split <;> omega

/-- Every displayed normal lies in the chosen affine chart. -/
theorem ell0_ne_zero_on_shore (i : Fin 36) :
    dot ell0 (cutNormal (shore i)) ≠ 0 := by
  fin_cases i <;> decide

/-- Direct evaluation of the two chart coordinates. -/
theorem affineGamma_eq_table (i : Fin 36) :
    affineGamma (shore i) = gammaTable i := by
  fin_cases i <;> decide

theorem gammaTable_injective : Function.Injective gammaTable := by
  decide

theorem affineGamma_shore_injective :
    Function.Injective (fun i : Fin 36 => affineGamma (shore i)) := by
  intro i j hij
  apply gammaTable_injective
  simpa only [affineGamma_eq_table] using hij

/-- The finite core of the counterexample: 36 short supports have distinct
affine gamma coordinates on a ground set of size 28. -/
theorem abstract_short_affine_count_le_ground_REFUTED :
    Fintype.card Edge < Fintype.card (Fin 36) := by
  norm_num [edge_card]

/-- The rank inequality in integer form: `7 <= 28/4 + 2`. -/
theorem rank_regime : 4 * (7 - 2) ≤ Fintype.card Edge := by
  norm_num [edge_card]

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterAbstractCocircuitRefuted

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterAbstractCocircuitRefuted
#print axioms shore_cutSupport_card
#print axioms shore_strictly_below_half
#print axioms ell0_ne_zero_on_shore
#print axioms affineGamma_eq_table
#print axioms affineGamma_shore_injective
#print axioms abstract_short_affine_count_le_ground_REFUTED
