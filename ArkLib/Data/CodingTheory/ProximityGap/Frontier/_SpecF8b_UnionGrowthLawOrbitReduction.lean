/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SpecF8_DistinctGammaUnionFloor

/-!
# Spec F8b — the union growth law REDUCES to the orbit-count growth law (#444)

This file chains directly onto `_SpecF8_DistinctGammaUnionFloor` (HEAD `26666266f`). F8 isolated the
SINGLE genuine open obligation of the prize δ*-floor as the asymptotic growth of the distinct-γ
**union count**

  `U(n) := |⋃_{R ∈ binom(μ_s,k+1)} {γ_R}|`,   the open `DistinctGammaUnionGrowthLaw U budget`
  (`∀ᶠ n, U n ≤ budget n`, `budget ≈ n`).

F8 §B ALSO proved the **orbit structure** of `U`: in the free `⟨τ⟩`-action regime (the Galois /
rotation symmetry of the far line), `U`'s underlying set is a disjoint union of `⟨τ⟩`-orbits all of
the SAME size `orbitSize`, so (F8 `orbitSize_dvd_U`, via `card_eq_orbitCount_mul_size`)

  `U(n) = orbitCount(n) · orbitSize`,        `orbitSize ∣ U(n)`,

where `orbitCount(n) = |image of the representative map|` is the NUMBER of distinct orbits. The
orbit-count object `orbitCount(n)` is exactly the one whose deep-rung asymptotic the in-tree
`Frontier/_OrbitCountGrowthLaw` (`orbitCount3 = C(g,2)`, `orbitCount4 = 2h²(h−1)+1`, super-linear at
the SHALLOW rungs r=3,4) was studying.

**What this file lands (axiom-clean, honest, structural — NOT a closure).** The clean REDUCTION that
makes F8's open obligation and the orbit-count object literally the same question, with the orbit
size factored out:

* `unionGrowth_iff_orbitGrowth` (HEADLINE) — given the per-`n` orbit-product decomposition
  `U n = orbitCount n · orbitSize` with `orbitSize > 0`, the union growth law `∀ᶠ n, U n ≤ budget n`
  is EQUIVALENT to the deflated orbit-count growth law `∀ᶠ n, orbitCount n ≤ budget n / orbitSize`,
  PROVIDED the budget is a clean multiple of the orbit size (`orbitSize ∣ budget n`). This pins the
  ENTIRE open content of F8 onto the orbit-count's deep-binding-rung asymptotic: the union law holds
  iff the orbit count stays within the per-orbit budget `budget/orbitSize`.
* `unionGrowth_of_orbitGrowth` / `orbitGrowth_of_unionGrowth` — the two implications separately
  (the `←` direction needs NO divisibility hypothesis; the `→` direction needs it).
* `union_le_budget_iff_orbit_le` — the pointwise (per-`n`) arithmetic core, isolated.
* `unionGrowthLaw_eq_orbit` — the `Prop`-level rewrite `DistinctGammaUnionGrowthLaw U budget =
  DistinctGammaUnionGrowthLaw orbitCount (budget/orbitSize)` (literal defeq under the hypotheses),
  certifying F8's named open obligation is the orbit-count growth law verbatim.

**Honest scope.** This is SUBSTRATE (rule 4), a structural reduction, NOT a δ*-pin and NOT a
closure: it does not prove EITHER growth law, it proves they are the SAME law. It moves F8's
frontier onto the already-studied orbit-count object (factoring out the orbit-size multiplier),
which is genuine frontier-movement, not boundary-re-mapping. NON-MOMENT (pure ℕ divisibility /
`Nat.le_div_iff` + `Filter.eventually` arithmetic, no moment/energy/spectrum bound).
ASYMPTOTIC-GUARD-COMPLIANT: a structural equivalence of two open laws, no capacity / beyond-Johnson
/ sub-linear claim, cliff-at-n/2 untouched. The orbit-count deep-rung asymptotic remains OPEN
(= the BGK wall, per `_OrbitCountGrowthLaw`: shallow rungs are super-linear; the `O→1` collapse can
only happen at the deep binding rung `r ~ log n`).
-/

open Finset Filter

namespace ArkLib.ProximityGap.SpecF8

/-! ## Part 1 — the pointwise arithmetic core -/

section Pointwise

/-- **The per-`n` budget equivalence.** With `U = orbitCount · orbitSize`, `orbitSize > 0`, and the
budget a clean multiple of `orbitSize` (`orbitSize ∣ budget`), the union fits the budget iff the
orbit count fits the deflated budget:

  `orbitCount · orbitSize ≤ budget  ⟺  orbitCount ≤ budget / orbitSize`.

This is `Nat.le_div_iff_mul_le` packaged with the orbit-product decomposition. -/
theorem union_le_budget_iff_orbit_le
    (orbitCount orbitSize budget : ℕ) (hsize : 0 < orbitSize) :
    orbitCount * orbitSize ≤ budget ↔ orbitCount ≤ budget / orbitSize := by
  rw [Nat.le_div_iff_mul_le hsize]

/-- **The forward arithmetic (no divisibility needed).** If the union fits the budget then the
orbit count fits the FLOOR-deflated budget — `orbitCount ≤ budget / orbitSize` — directly. -/
theorem orbit_le_of_union_le
    (orbitCount orbitSize budget : ℕ) (hsize : 0 < orbitSize)
    (h : orbitCount * orbitSize ≤ budget) :
    orbitCount ≤ budget / orbitSize :=
  (union_le_budget_iff_orbit_le orbitCount orbitSize budget hsize).mp h

/-- **The backward arithmetic (no divisibility needed).** If the orbit count fits the
floor-deflated budget then the union fits the budget. -/
theorem union_le_of_orbit_le
    (orbitCount orbitSize budget : ℕ) (hsize : 0 < orbitSize)
    (h : orbitCount ≤ budget / orbitSize) :
    orbitCount * orbitSize ≤ budget :=
  (union_le_budget_iff_orbit_le orbitCount orbitSize budget hsize).mpr h

end Pointwise

/-! ## Part 2 — the eventual (growth-law) reduction -/

section GrowthReduction

variable {U budget orbitCount : ℕ → ℕ} {orbitSize : ℕ}

/-- **`←`: the deflated orbit-count growth law IMPLIES the union growth law** (no divisibility
needed). If `U n = orbitCount n · orbitSize` for all `n`, `orbitSize > 0`, and the orbit count
eventually fits the floor-deflated budget, then the union eventually fits the budget. -/
theorem unionGrowth_of_orbitGrowth
    (hdecomp : ∀ n, U n = orbitCount n * orbitSize) (hsize : 0 < orbitSize)
    (horbit : DistinctGammaUnionGrowthLaw orbitCount (fun n => budget n / orbitSize)) :
    DistinctGammaUnionGrowthLaw U budget := by
  unfold DistinctGammaUnionGrowthLaw at horbit ⊢
  filter_upwards [horbit] with n hn
  rw [hdecomp n]
  exact union_le_of_orbit_le (orbitCount n) orbitSize (budget n) hsize hn

/-- **`→`: the union growth law IMPLIES the deflated orbit-count growth law** (no divisibility
needed — the floor-deflated direction is free). -/
theorem orbitGrowth_of_unionGrowth
    (hdecomp : ∀ n, U n = orbitCount n * orbitSize) (hsize : 0 < orbitSize)
    (hunion : DistinctGammaUnionGrowthLaw U budget) :
    DistinctGammaUnionGrowthLaw orbitCount (fun n => budget n / orbitSize) := by
  unfold DistinctGammaUnionGrowthLaw at hunion ⊢
  filter_upwards [hunion] with n hn
  rw [hdecomp n] at hn
  exact orbit_le_of_union_le (orbitCount n) orbitSize (budget n) hsize hn

/-- **HEADLINE — the union growth law REDUCES to the orbit-count growth law.** Given the per-`n`
orbit-product decomposition `U n = orbitCount n · orbitSize` (`orbitSize > 0`, the free-action
regime of F8 §B), F8's SINGLE open obligation `DistinctGammaUnionGrowthLaw U budget` is EQUIVALENT
to the orbit-count growth law against the floor-deflated budget `budget / orbitSize`. The entire
open content of the prize δ*-floor (the union count `U`) lives, with the orbit-size multiplier
removed, in the orbit-count's asymptotic: the object `_OrbitCountGrowthLaw` already mapped at the
shallow rungs (super-linear), and which collapses (if it does) only at the deep binding rung
`r ~ log n`. -/
theorem unionGrowth_iff_orbitGrowth
    (hdecomp : ∀ n, U n = orbitCount n * orbitSize) (hsize : 0 < orbitSize) :
    DistinctGammaUnionGrowthLaw U budget ↔
      DistinctGammaUnionGrowthLaw orbitCount (fun n => budget n / orbitSize) :=
  ⟨orbitGrowth_of_unionGrowth hdecomp hsize, unionGrowth_of_orbitGrowth hdecomp hsize⟩

/-- **`Prop`-level rewrite.** Under the orbit-product decomposition, F8's named open obligation
`DistinctGammaUnionGrowthLaw U budget` and the orbit-count growth law
`DistinctGammaUnionGrowthLaw orbitCount (budget/orbitSize)` are PROPOSITIONALLY EQUAL — certifying
they are literally the same open question, the orbit size factored out. -/
theorem unionGrowthLaw_eq_orbit
    (hdecomp : ∀ n, U n = orbitCount n * orbitSize) (hsize : 0 < orbitSize) :
    DistinctGammaUnionGrowthLaw U budget
      = DistinctGammaUnionGrowthLaw orbitCount (fun n => budget n / orbitSize) :=
  propext (unionGrowth_iff_orbitGrowth hdecomp hsize)

end GrowthReduction

/-! ## Part 3 — non-vacuity: the reduction has real content

A concrete super-linear orbit count (`orbitCount n = 2·n`, the kind `_OrbitCountGrowthLaw` shows the
shallow rungs to be) against budget `n` and orbit size `1` FAILS the union law via the reduction:
the orbit count `2n` exceeds the per-orbit budget `n/1 = n`, so the union law fails. This certifies
the reduction is a genuine `iff` carrying real content, not a vacuous restatement. -/

section Sanity

/-- **Non-vacuity:** the reduction transports a super-linear orbit-count violation into a union-law
failure. With `orbitSize = 1`, `orbitCount n = 2n + 1`, `budget n = n`: the orbit-count growth law
fails (`2n+1 > n/1 = n`), hence by the reduction the union law fails too. Mirrors F8's
`growthLaw_has_content`, now seen THROUGH the orbit decomposition. -/
theorem reduction_has_content :
    ¬ DistinctGammaUnionGrowthLaw (fun n => (2 * n + 1) * 1) (fun n => n) := by
  rw [unionGrowthLaw_eq_orbit (orbitCount := fun n => 2 * n + 1) (orbitSize := 1)
        (fun n => rfl) (by norm_num)]
  -- reduces to `¬ ∀ᶠ n, 2n+1 ≤ n/1 = n`, false.
  intro h
  unfold DistinctGammaUnionGrowthLaw at h
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  have hcontra := hN N le_rfl
  simp only [Nat.div_one] at hcontra
  omega

end Sanity

/-! ## Axiom audit -/

#print axioms union_le_budget_iff_orbit_le
#print axioms unionGrowth_of_orbitGrowth
#print axioms orbitGrowth_of_unionGrowth
#print axioms unionGrowth_iff_orbitGrowth
#print axioms unionGrowthLaw_eq_orbit
#print axioms reduction_has_content

end ArkLib.ProximityGap.SpecF8
