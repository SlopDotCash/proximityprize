/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# G287: the canonical quadratic weighted-kernel feature class is sign-infeasible (#466)

G286 uses the reflection fixed-point law of the actual sponsor cone to exclude reflection-odd
**linear** separators. The same fixed-point argument does not use linearity: every reflection-odd
statistic, at any degree, vanishes on every realizable reflection-even profile. Consequently the
smallest nonlinear class not annihilated by parity is reflection-even and quadratic.

This file tests that first surviving class exactly. For kernel class masses `H_j`, let

```text
T_d(H) = p * sum_j c_d(j) H_j,  d in {2,4,8,16},
```

be the complete generator-independent Ramanujan feature vector at `n=16`. A homogeneous canonical
quadratic has the form

```text
Q_a(T) = sum_{d <= e} a_(d,e) T_d T_e.
```

There are ten monomials. The accompanying exact probe evaluates them on every `n=16`, `p<2600`,
`p=1 mod 16`, rank-five/rank-six census cell. A max-margin LP returns zero. More decisively, eleven
cells with `p>=113` form an exact positive Farkas circuit: after dividing each `T` by its positive
row gcd, positive integer weights combine the ten **gate-signed** quadratic feature vectors to zero.
Therefore no fixed coefficient vector can make `Q_a(T)` have the CORE gate sign on all eleven cells.
The witness avoids the degenerate `p=17` cell and is checked coordinatewise below.

This closes the complete canonical homogeneous quadratic extension of the weighted-kernel character
surface. It is a certificate-shape no-go, not a sponsor estimate. A surviving statistic must begin
at degree at least three, be non-polynomial, or use additional row-labelled arithmetic; none is
supplied here. CORE remains open / on-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G287CanonicalQuadraticKernelNoGo

open scoped BigOperators

/-! ## Reflection-odd nonlinear statistics vanish too -/

/-- The fixed-point obstruction uses no linearity: every reflection-odd rational statistic vanishes
on every reflection-fixed profile. This corrects the proposed "odd quadratic or higher" escape from
G286. -/
theorem fixed_point_odd_statistic_zero {X : Type*} (sigma : X -> X) (F : X -> ℚ) {x : X}
    (hfixed : sigma x = x) (hodd : ∀ y, F (sigma y) = -F y) : F x = 0 := by
  have h : F x = -F x := by
    calc
      F x = F (sigma x) := (congrArg F hfixed).symm
      _ = -F x := hodd x
  linarith

/-- No reflection-odd statistic, linear or nonlinear, has a positive margin on a fixed point. -/
theorem fixed_point_odd_statistic_no_margin {X : Type*} (sigma : X -> X) (F : X -> ℚ)
    {x : X} (hfixed : sigma x = x) (hodd : ∀ y, F (sigma y) = -F y) : ¬ 0 < F x := by
  rw [fixed_point_odd_statistic_zero sigma F hfixed hodd]
  exact lt_irrefl 0

/-! ## A reusable positive-circuit obstruction -/

/-- A positive linear dependence among signed feature vectors rules out a strict linear separator.
Applied to degree-two monomials, this is the exact Farkas obstruction to one homogeneous quadratic
having the prescribed gate signs. -/
theorem no_strict_separator_of_positive_relation
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (v : ι -> κ -> ℚ) (weight : ι -> ℚ)
    (hweight : ∀ i, 0 < weight i)
    (hrel : ∀ j, ∑ i, weight i * v i j = 0) :
    ¬ ∃ a : κ -> ℚ, ∀ i, 0 < ∑ j, a j * v i j := by
  classical
  rintro ⟨a, ha⟩
  have hzero : (∑ i, weight i * ∑ j, a j * v i j) = 0 := by
    calc
      (∑ i, weight i * ∑ j, a j * v i j) =
          ∑ i, ∑ j, a j * (weight i * v i j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ j, ∑ i, a j * (weight i * v i j) := Finset.sum_comm
      _ = ∑ j, a j * ∑ i, weight i * v i j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
      _ = 0 := by simp [hrel]
  have hpos : 0 < ∑ i, weight i * ∑ j, a j * v i j := by
    apply Finset.sum_pos
    · intro i _
      exact mul_pos (hweight i) (ha i)
    · exact Finset.univ_nonempty
  linarith

/-! ## Exact closure of the complete canonical linear span

G285 records the first two canonical features. Generator independence gives the complete linear
basis `(T2,T4,T8,T16)` at `n=16`. Five genuine cells already form a positive circuit, so no fixed
linear combination of the complete basis tracks every gate sign.
-/

/-- Primitive canonical feature vectors at `(p,r)=(113,6),(1889,6),(2129,6),(2593,5),(2593,6)`. -/
def linearPrimitiveFeatures : Fin 5 -> Fin 4 -> ℤ :=
  ![![1, 4, -6, -12],
    ![10545, 23232, 53984, 113160],
    ![655, 4782, 15455, 15128],
    ![4451, 10468, 16700, 49928],
    ![5977, 15129, 22602, 72588]]

/-- Exact gate signs on the five linear-circuit cells. -/
def linearGateSign : Fin 5 -> ℤ := ![-1, -1, 1, 1, -1]

/-- Gate-signed complete canonical linear features. -/
def signedLinearFeatures (i : Fin 5) (j : Fin 4) : ℚ :=
  ((linearGateSign i * linearPrimitiveFeatures i j : ℤ) : ℚ)

/-- Strictly positive weights for the five-cell linear circuit. -/
def linearFarkasWeight : Fin 5 -> ℚ :=
  ![201509006170048, 579259743381, 520097612828, 4174444248727, 2109973613412]

/-- Every linear-circuit weight is positive. -/
theorem linearFarkasWeight_pos (i : Fin 5) : 0 < linearFarkasWeight i := by
  fin_cases i <;> norm_num [linearFarkasWeight]

/-- Exact positive dependence in all four canonical linear coordinates. -/
theorem linear_farkas_relation (j : Fin 4) :
    ∑ i, linearFarkasWeight i * signedLinearFeatures i j = 0 := by
  fin_cases j <;>
    norm_num [linearFarkasWeight, signedLinearFeatures, linearGateSign, linearPrimitiveFeatures,
      Fin.sum_univ_succ]

/-- No fixed linear combination of `(T2,T4,T8,T16)` has the CORE sign on all five cells. -/
theorem no_canonical_linear_sign_separator :
    ¬ ∃ a : Fin 4 -> ℚ, ∀ i, 0 < ∑ j, a j * signedLinearFeatures i j := by
  exact no_strict_separator_of_positive_relation signedLinearFeatures linearFarkasWeight
    linearFarkasWeight_pos linear_farkas_relation

/-! ## Exact canonical quadratic circuit

The feature order is
`(T2^2,T2*T4,T2*T8,T2*T16,T4^2,T4*T8,T4*T16,T8^2,T8*T16,T16^2)`.
Each recorded `T` vector is divided by its positive row gcd. Homogeneity gives
`Q(T)=gcd(T)^2 Q(T/gcd(T))`, so this normalization preserves every quadratic sign.
-/

/-- The ten homogeneous degree-two monomials in four canonical linear features. -/
def quadraticFeatures (t : Fin 4 -> ℤ) : Fin 10 -> ℤ :=
  ![t 0 * t 0, t 0 * t 1, t 0 * t 2, t 0 * t 3, t 1 * t 1,
    t 1 * t 2, t 1 * t 3, t 2 * t 2, t 2 * t 3, t 3 * t 3]

/-- Eleven primitive canonical feature vectors from genuine `n=16` rank-five/rank-six cells.
Rows correspond respectively to `(p,r)=(113,5),(241,6),(337,6),(353,5),(449,5),(769,5),
(977,6),(1217,5),(1249,6),(1777,6),(2273,6)`. -/
def primitiveFeatures : Fin 11 -> Fin 4 -> ℤ :=
  ![![-171, -378, 1444, 1832],
    ![965, 596, 3488, 3224],
    ![343, 2590, -554, 3365],
    ![2944, 1293, 5364, 15624],
    ![2335, 3742, 6688, 23368],
    ![3737, 6826, 8880, 16768],
    ![2333, 18060, 50912, 111320],
    ![1741, 8329, 2802, 19108],
    ![5295, 3984, 17278, 36568],
    ![2217, 9682, 14986, 47536],
    ![7425, 2384, 9202, 34302]]

/-- Signs of the exact CORE gates on the eleven witness cells. -/
def gateSign : Fin 11 -> ℤ := ![1, -1, 1, -1, -1, 1, -1, -1, 1, 1, 1]

/-- Gate-signed quadratic feature vectors, coerced to rationals for separation. -/
def signedQuadraticFeatures (i : Fin 11) (j : Fin 10) : ℚ :=
  ((gateSign i * quadraticFeatures (primitiveFeatures i) j : ℤ) : ℚ)

/-- Strictly positive integer Farkas weights for the eleven-cell circuit. -/
def farkasWeight : Fin 11 -> ℚ :=
  ![11308242874832261572052183566626781414659316407602105031566717756454192,
    5545395965739983420010862625442000127212733512612622606100727773394813,
    3492805965182985206647536641660394624909840337611522612856160317309184,
    13983000195570496051288545395768579696389962745181207272025935188289232,
    1573179179079669437886174590565848493435097834355219103296674926056580,
    244142748137291338636829266720419636475465291169939190898370781168416,
    110241997960278095030459289115345232313710872887127117460361113618015,
    1007251487898994986904786060080228399921905389253337700472740655923488,
    1526486021713370574044212582355307680990040413804551200469942473851104,
    891416934309140711299857485350182791519957500800239422684400646229632,
    1582720926493957971050302814118779667794269851352565398079629218360128]

/-- Every Farkas weight is strictly positive. -/
theorem farkasWeight_pos (i : Fin 11) : 0 < farkasWeight i := by
  fin_cases i <;> norm_num [farkasWeight]

/-- Exact positive dependence: every one of the ten signed quadratic coordinates sums to zero. -/
theorem quadratic_farkas_relation (j : Fin 10) :
    ∑ i, farkasWeight i * signedQuadraticFeatures i j = 0 := by
  fin_cases j <;>
    simp [farkasWeight, signedQuadraticFeatures, gateSign, quadraticFeatures,
      primitiveFeatures, Fin.sum_univ_succ] <;>
    norm_num

/-- **Canonical quadratic no-go.** No fixed homogeneous quadratic in the complete
`(T2,T4,T8,T16)` generator-independent feature vector has the exact CORE sign on all eleven
sponsor-faithful census cells. -/
theorem no_canonical_quadratic_sign_separator :
    ¬ ∃ a : Fin 10 -> ℚ, ∀ i, 0 < ∑ j, a j * signedQuadraticFeatures i j := by
  exact no_strict_separator_of_positive_relation signedQuadraticFeatures farkasWeight
    farkasWeight_pos quadratic_farkas_relation

#print axioms fixed_point_odd_statistic_zero
#print axioms fixed_point_odd_statistic_no_margin
#print axioms no_strict_separator_of_positive_relation
#print axioms linear_farkas_relation
#print axioms no_canonical_linear_sign_separator
#print axioms quadratic_farkas_relation
#print axioms no_canonical_quadratic_sign_separator

end ArkLib.ProximityGap.Frontier.G287CanonicalQuadraticKernelNoGo
