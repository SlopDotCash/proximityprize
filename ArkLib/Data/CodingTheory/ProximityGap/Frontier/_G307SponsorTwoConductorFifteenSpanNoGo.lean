/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G287CanonicalQuadraticKernelNoGo

/-!
# G307: the sponsor-two invariant conductor-fifteen span is non-separating

The second sponsor quotient order

```text
m₂ = 2^129 + 13
```

is divisible by `75`. After the binary phase class is excluded by oddness and the primitive
order-three and order-five traces are tested, the first generator-invariant mixed conductor is
fifteen. Its complete rational trace span has the four standard Ramanujan coordinates

```text
(P, L₃, L₅, L₁₅).
```

Every fixed generator-invariant linear normal supported on quotient characters of conductor
dividing fifteen is a linear combination of these four coordinates. This file gives an exact
positive Farkas circuit on five proper dyadic cells, proving that no such combination has the
coefficient-two CORE sign with a strict uniform margin.

The target-oriented feature vectors and positive relation are recomputed by
`scripts/probes/g307_sponsor_two_conductor15_span_nogo.py`. No floating-point computation enters
the Lean payload. The result closes a bounded sponsor-two trace class; it does not exclude a
non-invariant or full-family Gross--Koblitz normal. CORE remains open / on-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G307SponsorTwoConductorFifteenSpanNoGo

open ArkLib.ProximityGap.Frontier.G287CanonicalQuadraticKernelNoGo

/-- Quotient order at the second certified sponsor prime. -/
def sponsorOrderTwo : ℕ := 2 ^ 129 + 13

/-- Sponsor two supports every primitive trace of conductor dividing `75`. -/
theorem seventyFive_dvd_sponsorOrderTwo : 75 ∣ sponsorOrderTwo := by
  norm_num [sponsorOrderTwo]

/-- Coefficient-two CORE targets on the five exact circuit cells. -/
def target : Fin 5 → ℤ :=
  ![177136, 681872, 303520, -936608, 167714720]

/-- Signs orienting every invariant feature toward its coefficient-two target. -/
def gateSign : Fin 5 → ℤ := ![1, 1, 1, -1, 1]

/-- Ranks of the five cells. The circuit uses both adjacent live ranks. -/
def cellRank : Fin 5 → ℕ := ![5, 5, 6, 5, 6]

/-- Principal quotient coordinates `P` on the exact cells. -/
def principalCoordinate : Fin 5 → ℤ :=
  ![-134448, -382128, -189392, -1509408, -380423760]

/-- Primitive order-three Ramanujan traces `L₃`. -/
def orderThreeCoordinate : Fin 5 → ℤ :=
  ![-1688928, -2971344, -1149112, -9786528, 20338363872]

/-- Primitive order-five Ramanujan traces `L₅`. -/
def orderFiveCoordinate : Fin 5 → ℤ :=
  ![888808, -10164112, -4500288, -11055152, -568602320]

/-- Primitive order-fifteen Ramanujan traces `L₁₅`. -/
def orderFifteenCoordinate : Fin 5 → ℤ :=
  ![-4046872, -1043336, -389448, -25013872, -689514592]

/-- Every chosen gate sign is the actual nonzero sign of its CORE target. -/
theorem gateSign_orients_target (i : Fin 5) : 0 < gateSign i * target i := by
  fin_cases i <;> norm_num [gateSign, target]

/-- Exact target-oriented coordinates `(P,L₃,L₅,L₁₅)`. -/
def signedInvariantFeature (i : Fin 5) : Fin 4 → ℚ :=
  ![((gateSign i * principalCoordinate i : ℤ) : ℚ),
    ((gateSign i * orderThreeCoordinate i : ℤ) : ℚ),
    ((gateSign i * orderFiveCoordinate i : ℤ) : ℚ),
    ((gateSign i * orderFifteenCoordinate i : ℤ) : ℚ)]

/-- Strictly positive integer weights of the exact five-cell Farkas circuit. -/
def circuitWeight : Fin 5 → ℚ :=
  ![8238733293377050110946,
    754877671516756422812,
    3385823540912886383052,
    1425371395806543001161,
    299870825764606156]

/-- Every circuit coefficient is strictly positive. -/
theorem circuitWeight_pos (i : Fin 5) : 0 < circuitWeight i := by
  fin_cases i <;> norm_num [circuitWeight]

/-- The target-oriented conductor-fifteen coordinates have an exact positive dependence. -/
theorem conductorFifteen_positive_circuit (j : Fin 4) :
    ∑ i, circuitWeight i * signedInvariantFeature i j = 0 := by
  fin_cases j <;>
    norm_num [circuitWeight, signedInvariantFeature, gateSign, principalCoordinate,
      orderThreeCoordinate, orderFiveCoordinate, orderFifteenCoordinate, Fin.sum_univ_succ]

/-- The positive circuit is not a fixed-rank island. -/
theorem circuit_uses_both_ranks :
    (∃ i, cellRank i = 5) ∧ (∃ i, cellRank i = 6) := by
  exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩

/-- No fixed linear combination of `(P,L₃,L₅,L₁₅)` has the coefficient-two CORE sign on all
five exact cells. -/
theorem no_sponsor_two_conductorFifteen_separator :
    ¬ ∃ a : Fin 4 → ℚ, ∀ i, 0 < ∑ j, a j * signedInvariantFeature i j := by
  exact no_strict_separator_of_positive_relation signedInvariantFeature circuitWeight
    circuitWeight_pos conductorFifteen_positive_circuit

/-- Calibrated form: no conductor-fifteen invariant normal has any strictly positive uniform
oriented margin on the circuit. -/
theorem no_sponsor_two_conductorFifteen_positive_margin :
    ¬ ∃ (a : Fin 4 → ℚ) (eta : ℚ),
      0 < eta ∧ ∀ i, eta ≤ ∑ j, a j * signedInvariantFeature i j := by
  rintro ⟨a, eta, heta, hmargin⟩
  apply no_sponsor_two_conductorFifteen_separator
  exact ⟨a, fun i => lt_of_lt_of_le heta (hmargin i)⟩

#print axioms seventyFive_dvd_sponsorOrderTwo
#print axioms gateSign_orients_target
#print axioms conductorFifteen_positive_circuit
#print axioms circuit_uses_both_ranks
#print axioms no_sponsor_two_conductorFifteen_separator
#print axioms no_sponsor_two_conductorFifteen_positive_margin

end ArkLib.ProximityGap.Frontier.G307SponsorTwoConductorFifteenSpanNoGo
