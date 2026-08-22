/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G237FiberLargeSieveInputA

/-!
# G240: correct quotient-incidence normalization for the Jacobi large sieve (#466)

G237 isolated the correct structural inequality, fiber Cauchy, but its proposed discharge of the
quotient-Jacobi operator used a carrier of cardinality `n` together with

```text
sum_u ‖F u‖² = n * ‖a‖².
```

For the actual Jacobi fanout this indexing is wrong. The coefficient vector has length
`m = (p-1)/n` and is indexed by multiplicative characters trivial on the subgroup `G`. Every such
character restricts to `1` on `G`, so there is no `m`-character Parseval identity on `G`.

The honest carrier is all nonzero field elements, or equivalently the quotient `Q = F_p^*/G` of
cardinality `m`. For quotient coefficients `a`, the exact normalizations are

```text
sum_{A in Q} ‖F_a(A)‖² = m * ‖a‖²,
sum_{x in F_p^*} ‖F_a(x)‖² = n*m * ‖a‖².
```

The map `x ↦ class(2-x)` has fibers of size at most `n`. Fiber Cauchy therefore gives class-sum
energy at most `n` times the lifted input energy, while quotient-character Parseval contributes the
normalizing factor `1/m` on the output. The factors cancel exactly:

```text
outputEnergy ≤ classEnergy/m
             ≤ n * inputEnergy/m
             = n * (n*m*‖a‖²)/m
             = n² * ‖a‖².
```

This file kernel-checks that correctly normalized composition and wires it into G233's coefficient
mass floor. It supersedes only the *normalization narrative* of G237's final capstone, not G237's
valid fiber-Cauchy theorem. The remaining character-theory obligations are now correctly typed:
quotient Parseval on `Q` and the unitary identification of the Jacobi matrix with the quotient
incidence matrix `N[A,B] = #{x in A : 2-x in B}`.

This is a keystone correctness repair, not a prize closure. The signed sponsor-prime covariance at
ranks 5 and 6 remains open and on the BGK/Paley wall.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G240QuotientIncidenceNormalization

open Finset
open ArkLib.ProximityGap.Frontier.G237FiberLargeSieveInputA
open ArkLib.ProximityGap.Frontier.G233JacobiL2MassFloorNoGo

variable {α β : Type*}

/-- **Correctly normalized quotient-incidence large sieve.**

`inputEnergy` is the energy after lifting a quotient Fourier polynomial from `Q` to all nonzero
field elements, so its Parseval normalization is `n*m*aNorm2`. `classEnergy` is the energy of the
fiber sums under `x ↦ class(2-x)`. `outputEnergy` is the Jacobi output energy; quotient Parseval
contributes `outputEnergy ≤ classEnergy/m`. A fiber ceiling `n` then yields the desired operator
bound `outputEnergy ≤ n²*aNorm2`.

Unlike G237's earlier `n`-point Parseval capstone, the two independent cardinalities `n` (subgroup
size / fiber ceiling) and `m` (quotient size / Fourier normalization) are explicit here. -/
theorem quotient_largesieve_normalized
    (n m : ℕ) (hm : 0 < m) (aNorm2 inputEnergy classEnergy outputEnergy : ℝ)
    (hClass : classEnergy ≤ (n : ℝ) * inputEnergy)
    (hInputParseval : inputEnergy = (n : ℝ) * m * aNorm2)
    (hOutputParseval : outputEnergy ≤ classEnergy / m) :
    outputEnergy ≤ (n : ℝ) ^ 2 * aNorm2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hClass' : classEnergy / (m : ℝ) ≤ (n : ℝ) ^ 2 * aNorm2 := by
    rw [hInputParseval] at hClass
    apply (div_le_iff₀ hm0).2
    calc
      classEnergy ≤ (n : ℝ) * ((n : ℝ) * (m : ℝ) * aNorm2) := hClass
      _ = (n : ℝ) ^ 2 * aNorm2 * m := by ring
  exact hOutputParseval.trans hClass'

/-- **Concrete fiber form of the corrected normalization.**

G237's structural `fiber_largesieve_operator_bound` supplies `classEnergy ≤ n*inputEnergy` from the
actual fiber ceiling `#fiber ≤ n`. With the correctly scaled quotient Parseval hypotheses, the
Jacobi operator bound follows with constant `n²`. -/
theorem quotient_largesieve_of_fibers
    [DecidableEq β] (G : Finset α) (cls : α → β) (D : Finset β) (F : α → ℂ)
    (n m : ℕ) (hm : 0 < m) (aNorm2 outputEnergy : ℝ)
    (hmaps : ∀ u ∈ G, cls u ∈ D)
    (hfib : ∀ d ∈ D, ((G.filter (fun u => cls u = d)).card : ℝ) ≤ n)
    (hInputParseval : ∑ u ∈ G, ‖F u‖ ^ 2 = (n : ℝ) * m * aNorm2)
    (hOutputParseval : outputEnergy ≤
      (∑ d ∈ D, ‖∑ u ∈ G.filter (fun u => cls u = d), F u‖ ^ 2) / m) :
    outputEnergy ≤ (n : ℝ) ^ 2 * aNorm2 := by
  let classEnergy : ℝ :=
    ∑ d ∈ D, ‖∑ u ∈ G.filter (fun u => cls u = d), F u‖ ^ 2
  let inputEnergy : ℝ := ∑ u ∈ G, ‖F u‖ ^ 2
  have hClass : classEnergy ≤ (n : ℝ) * inputEnergy := by
    exact fiber_largesieve_operator_bound G cls D F (n : ℝ) hmaps hfib
  exact quotient_largesieve_normalized n m hm aNorm2 inputEnergy classEnergy outputEnergy
    hClass hInputParseval hOutputParseval

/-- **G233 mass floor with the corrected quotient normalization.**

The large-sieve input is no longer supplied by the false `m`-character Parseval-on-`G` narrative.
It is obtained from quotient output Parseval (`1/m`), lifted quotient input Parseval (`n*m`), and
the fiber ceiling `n`. -/
theorem l2_mass_floor_of_quotient_fibers
    [DecidableEq β] (G : Finset α) (cls : α → β) (D : Finset β) (F : α → ℂ)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (aNorm2 outputEnergy sNorm2 : ℝ)
    (hmaps : ∀ u ∈ G, cls u ∈ D)
    (hfib : ∀ d ∈ D, ((G.filter (fun u => cls u = d)).card : ℝ) ≤ n)
    (hInputParseval : ∑ u ∈ G, ‖F u‖ ^ 2 = (n : ℝ) * m * aNorm2)
    (hOutputParseval : outputEnergy ≤
      (∑ d ∈ D, ‖∑ u ∈ G.filter (fun u => cls u = d), F u‖ ^ 2) / m)
    (hSponsor : (n : ℝ) * ((m : ℝ) - n) ≤ sNorm2)
    (hHalf : sNorm2 / 4 ≤ outputEnergy) :
    (m : ℝ) - n ≤ 4 * n * aNorm2 := by
  apply l2_mass_floor_of_largesieve_parseval n m hn aNorm2 outputEnergy sNorm2
  · exact quotient_largesieve_of_fibers G cls D F n m hm aNorm2 outputEnergy
      hmaps hfib hInputParseval hOutputParseval
  · exact hSponsor
  · exact hHalf

end ArkLib.ProximityGap.Frontier.G240QuotientIncidenceNormalization
