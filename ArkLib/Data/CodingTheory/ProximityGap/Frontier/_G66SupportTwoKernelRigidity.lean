/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G56AllDepthPatternDecomposition

/-!
# G66: support-two characteristic-p kernel relations have only one lag

This file isolates the first genuinely fixed-prime gain in the G56 characteristic-`p`
wraparound census. A folded support-two relation has the form

`a * ζ^i + b * ζ^j = 0`,

where `ζ` has order `n = 2m`, `i,j < m`, and `b ≠ 0`. For fixed coefficients `(a,b)` and a
fixed first coordinate `i`, primitivity makes the second coordinate `j` unique. Consequently
there are at most `m = n/2` placements of that coefficient pair in the half-domain, rather
than the `m(m-1)` placements seen by the characteristic-zero full-shape histogram.

The primitive-depth-one cases are absent altogether. Distinct half-domain powers are neither
equal nor negatives of one another: equality contradicts power injectivity, while negation
would identify an exponent below `m` with one in `[m,2m)` using `ζ^m = -1`.

This changes the binding count for the binomial/rank-one sector. For a depth-`r` signed-walk
endpoint with primitive depth `s = (|a|+|b|)/2`, the elementary factorial estimate gives

`m * NR_r(a,b) / Wick_r ≤ r!/(r-s)! / (m^(s-1) |a|! |b|!)`.

Summing all ordered nonzero signed coefficient pairs and starting at `s=2` gives the uniform
envelope

`Support2/Wick ≤ 4 * Σ_{s=2}^r r!/(r-s)! * (4^s-2) / ((2s)! m^(s-1))`.

The exact probe `/tmp/arklib-reports/g56_support2_kernel_probe.py` verifies the structural
`maxlag = 1` law at every tested prime and evaluates the envelope at the nominal prize point
`n=2^30`, `r=110` as `5.21106040058e-5`. Thus all support-two characteristic-`p` relations,
including resonant shapes such as `(-3,1)`, cost under `0.006%` of one Wick budget there. They
cannot carry the wall; the remaining wraparound mass is forced into support at least three,
consistent with the existing r366-r370b web census.

The Lean content below kernel-checks the load-bearing fixed-prime rigidity and the depth-one
exclusion. It does not claim the full analytic envelope as a theorem and does not close CORE.
Issue #466. Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

open Finset
open scoped Classical

namespace ArkLib.ProximityGap.Frontier.G66SupportTwoKernelRigidity

open ArkLib.ProximityGap.Frontier.G56AllDepthPatternDecomposition (zeta_pow_m)

variable {F : Type*} [Field F]

/-- Ordered half-domain placements of a support-two relation with coefficients `(a,b)`.
The inequality `i ≠ j` makes the support genuinely two. -/
noncomputable def twoTermPlacements (ζ a b : F) (m : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((range m).product (range m)).filter fun ij =>
    ij.1 ≠ ij.2 ∧ a * ζ ^ ij.1 + b * ζ ^ ij.2 = 0

/-- **Fixed-prime support-two rigidity.** For fixed nonzero second coefficient `b`, projection
onto the first coordinate is injective on support-two relation placements. Equivalently, after
choosing `i`, there is at most one `j < m` satisfying `a ζ^i + b ζ^j = 0`.

This is the exact mechanism replacing the characteristic-zero `m(m-1)` placement count by at
most `m`: two solutions with the same `i` imply `b ζ^j = b ζ^j'`, hence `ζ^j = ζ^j'`, and
primitivity identifies `j = j'`. -/
theorem fst_injOn_twoTermPlacements {ζ a b : F} {m : ℕ}
    (hprim : IsPrimitiveRoot ζ (2 * m)) (hb : b ≠ 0) :
    Set.InjOn Prod.fst (twoTermPlacements ζ a b m : Set (ℕ × ℕ)) := by
  classical
  intro x hx y hy hfst
  have hxmem := Finset.mem_filter.mp hx
  have hymem := Finset.mem_filter.mp hy
  have hxprod := Finset.mem_product.mp hxmem.1
  have hyprod := Finset.mem_product.mp hymem.1
  have hxj : x.2 < m := Finset.mem_range.mp hxprod.2
  have hyj : y.2 < m := Finset.mem_range.mp hyprod.2
  have hxrel := hxmem.2.2
  rw [hfst] at hxrel
  have hmul : b * (ζ ^ x.2 - ζ ^ y.2) = 0 := by
    linear_combination hxrel - hymem.2.2
  have hpow : ζ ^ x.2 = ζ ^ y.2 := by
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · exact (hb hzero).elim
    · exact sub_eq_zero.mp hzero
  have hj : x.2 = y.2 := hprim.pow_inj (by omega) (by omega) hpow
  exact Prod.ext hfst hj

/-- A fixed nonzero coefficient pair has at most `m` ordered support-two placements in the
half-domain. This is the cardinality form consumed by the weighted-kernel envelope. -/
theorem twoTermPlacements_card_le {ζ a b : F} {m : ℕ}
    (hprim : IsPrimitiveRoot ζ (2 * m)) (hb : b ≠ 0) :
    (twoTermPlacements ζ a b m).card ≤ m := by
  classical
  calc
    (twoTermPlacements ζ a b m).card ≤ (range m).card :=
      Finset.card_le_card_of_injOn Prod.fst
        (by
          intro x hx
          exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1)
        (fst_injOn_twoTermPlacements hprim hb)
    _ = m := Finset.card_range m

/-- Distinct powers in the first half of a primitive `2m`-th root cannot be equal. This excludes
one of the two primitive-depth-one sign patterns. -/
theorem pow_ne_pow_of_lt_half {ζ : F} {m i j : ℕ}
    (hprim : IsPrimitiveRoot ζ (2 * m))
    (hi : i < m) (hj : j < m) (hij : i ≠ j) :
    ζ ^ i ≠ ζ ^ j := by
  intro hpow
  exact hij (hprim.pow_inj (by omega) (by omega) hpow)

/-- Two powers in the first half of a primitive `2m`-th root cannot be negatives. Negation shifts
an exponent by exactly `m`, so this would equate an exponent below `m` with one in `[m,2m)`. This
excludes the other primitive-depth-one sign pattern. -/
theorem pow_ne_neg_pow_of_lt_half {ζ : F} {m i j : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    (hi : i < m) (hj : j < m) :
    ζ ^ i ≠ -(ζ ^ j) := by
  intro hneg
  have hshift : ζ ^ (j + m) = -(ζ ^ j) := by
    rw [pow_add, zeta_pow_m hm hprim]
    ring
  have hpow : ζ ^ i = ζ ^ (j + m) := hneg.trans hshift.symm
  have hijm : i = j + m := hprim.pow_inj (by omega) (by omega) hpow
  omega

/-- Honest scope marker: G66 removes the support-two/binomial sector from the prize-scale
wraparound budget; support at least three remains the open characteristic-`p` web. -/
def isPrizeClosure : Prop := False

theorem not_prizeClosure : ¬ isPrizeClosure := id

#print axioms fst_injOn_twoTermPlacements
#print axioms twoTermPlacements_card_le
#print axioms pow_ne_pow_of_lt_half
#print axioms pow_ne_neg_pow_of_lt_half
#print axioms not_prizeClosure

end ArkLib.ProximityGap.Frontier.G66SupportTwoKernelRigidity
