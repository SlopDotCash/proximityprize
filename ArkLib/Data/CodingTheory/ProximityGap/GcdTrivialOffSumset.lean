/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupRepCountGcdExact
import ArkLib.Data.CodingTheory.ProximityGap.AddEnergySumsetSupport

/-!
# The gcd-degree is trivial off the sumset (#444, #357)

For a root-of-unity subgroup `G = {z : zⁿ = 1}` on a smooth domain (`char F ∤ n`,
`Xⁿ−1` splits), the additive representation count `r(c) = #{z ∈ G : c − z ∈ G}` equals
the gcd degree `deg gcd(Xⁿ−1, (C c − X)ⁿ − 1)` exactly
(`SubgroupRepresentationRoots.representationCount_eq_gcd_degree`). Combined with the
sumset-support fact `r(c) = 0` off `G + G`
(`SubgroupGaussSumFourthMoment.repFilter_card_eq_zero_of_not_mem_sumset`), this pins the
**gcd itself** to be trivial off the sumset, not merely the representation count:

* `gcd_natDegree_eq_zero_of_not_mem_sumset` : `c ∉ G + G ⟹ deg gcd(Xⁿ−1, (C c−X)ⁿ−1) = 0`.
* `gcd_isUnit_of_not_mem_sumset` : `c ∉ G + G ⟹ IsUnit (gcd (Xⁿ−1) (reprPoly c n))`.
* `sum_gcd_degree_sq_eq_sum_sumset` : the Stepanov target `Σ_c (deg gcd_c)²` over `F` EQUALS the
  sum over `G + G` exactly (each off-sumset summand is `0`, not just dominated).

This is **strictly stronger** than the rep-count support fact (which only says `r(c) = 0`):
on a smooth domain the entire `gcd` polynomial degenerates to a unit off the sumset, so the
Stepanov / resultant target `Σ_c (deg gcd_c)²` is itself supported on `G + G` at the
polynomial-degree level (each off-sumset summand is `0² = 0`, exactly).

**Probe.** `scripts/probes/probe_gcd_trivial_offsumset.py` (seeded; EXACT mod-`p` polynomial
gcd via Euclid; thin `μ_n = G` proper subgroup; primes `97,193,257,337,1153,12289` spanning
`p ≤ n³` and `p > n³`; never `n = q − 1`): over 248 off-sumset `c` the gcd has natDegree `0`
in **all 248**, confirming the trivial-gcd (not just zero-count) statement.

**Honest scope.** NOT a CORE / Conjecture-7.1 closure. A structural support sharpening: it
strengthens the rep-count sumset-support (`AddEnergySumsetSupport`) to the gcd-degree /
polynomial level on smooth domains. It does NOT bound `Σ_{c ∈ G+G} (deg gcd_c)²` (that on-sumset
sum is the open Stepanov input). NON-MOMENT (polynomial-method / gcd-degree, no even-moment or
energy estimate). The `Splits`/separability hypotheses are exactly those of the in-tree exact
gcd-degree theorem it extends.
-/

set_option linter.style.longLine false
set_option autoImplicit false
set_option linter.unusedFintypeInType false


open Polynomial
open scoped Pointwise

namespace ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

open ArkLib.ProximityGap.SubgroupRepresentationRoots

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The gcd degree is `0` off the sumset.** On a smooth domain (`(n : F) ≠ 0` and `Xⁿ−1`
splits), the representation count equals the gcd degree, and the count vanishes off `G + G`, so
the gcd degree is `0` for `c ∉ G + G`. Strengthens `repFilter_card_eq_zero_of_not_mem_sumset`
from the count to the polynomial degree. -/
theorem gcd_natDegree_eq_zero_of_not_mem_sumset (G : Finset F) {n : ℕ} (hn : 0 < n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hsep : (n : F) ≠ 0)
    (hsplit : (X ^ n - 1 : F[X]).Splits) {c : F} (hc : c ∉ G + G) :
    (gcd (X ^ n - 1 : F[X]) (reprPoly c n)).natDegree = 0 := by
  have hcount : (G.filter (fun z => c - z ∈ G)).card
      = (gcd (X ^ n - 1 : F[X]) (reprPoly c n)).natDegree :=
    representationCount_eq_gcd_degree G hn hGmem hsep hsplit c
  have hzero : (G.filter (fun z => c - z ∈ G)).card = 0 :=
    repFilter_card_eq_zero_of_not_mem_sumset G hc
  rw [hcount] at hzero
  exact hzero

/-- **The gcd is a unit off the sumset.** A nonzero polynomial of `natDegree 0` is a unit, so the
off-sumset gcd degenerates to a constant unit, the strongest form of the trivial-gcd statement. -/
theorem gcd_isUnit_of_not_mem_sumset (G : Finset F) {n : ℕ} (hn : 0 < n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hsep : (n : F) ≠ 0)
    (hsplit : (X ^ n - 1 : F[X]).Splits) {c : F} (hc : c ∉ G + G) :
    IsUnit (gcd (X ^ n - 1 : F[X]) (reprPoly c n)) := by
  have hdeg : (gcd (X ^ n - 1 : F[X]) (reprPoly c n)).natDegree = 0 :=
    gcd_natDegree_eq_zero_of_not_mem_sumset G hn hGmem hsep hsplit hc
  have hne : gcd (X ^ n - 1 : F[X]) (reprPoly c n) ≠ 0 := by
    intro h
    rw [_root_.gcd_eq_zero_iff] at h
    exact X_pow_sub_one_ne_zero hn h.1
  exact Polynomial.isUnit_iff_degree_eq_zero.mpr
    (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mp hdeg |>.antisymm
      (Polynomial.zero_le_degree_iff.mpr hne))

/-- **The squared-gcd-degree sum collapses to the sumset (exact).** Since each off-sumset gcd
degree is `0` (hence its square is `0`), the full Stepanov target sum over `F` equals the sum
restricted to `G + G`. This is the gcd-degree-`²`-level analogue of the rep-count identity
`addEnergy_eq_sum_sumset_repFilter_sq`, applied to the actual Stepanov object
`Σ (deg gcd_c)²`. -/
theorem sum_gcd_degree_sq_eq_sum_sumset (G : Finset F) {n : ℕ} (hn : 0 < n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hsep : (n : F) ≠ 0)
    (hsplit : (X ^ n - 1 : F[X]).Splits) :
    (∑ c : F, ((gcd (X ^ n - 1 : F[X]) (reprPoly c n)).natDegree) ^ 2)
      = ∑ c ∈ G + G, ((gcd (X ^ n - 1 : F[X]) (reprPoly c n)).natDegree) ^ 2 := by
  classical
  refine (Finset.sum_subset (Finset.subset_univ (G + G)) ?_).symm
  intro c _ hc
  rw [gcd_natDegree_eq_zero_of_not_mem_sumset G hn hGmem hsep hsplit hc, pow_two, Nat.mul_zero]

end ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
