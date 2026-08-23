/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ38SylvesterInjectivity

/-!
# SYZ39 — arithmetic of `SylvesterInjective`: symmetry and unit-scaling invariance

SYZ38 localized the entire rate-`1/2` proximity residual to `SylvesterInjective WAB WAC WBC bAC bBC`
— the generalized Sylvester map of a pairwise-coprime band triple is injective on the in-budget
cofactor window.  This file records two elementary but structurally load-bearing invariances of that
predicate, both discharged by pure divisibility algebra (axiom-clean, no new hypotheses):

* `sylvester_injective_symm` — the predicate is **symmetric** under swapping the two cofactor slots
  `(WAC, bAC) ↔ (WBC, bBC)`.  Mechanism: `W_AB ∣ (W_AC r_AC − W_BC r_BC)` iff
  `W_AB ∣ (W_BC r_BC − W_AC r_AC)` (divisibility is closed under negation).
* `sylvester_injective_unit_scale` — the predicate is **invariant under scaling** either band factor
  by a nonzero field constant (`W_AC ↦ c · W_AC`, `c ≠ 0`).  Mechanism: a nonzero constant is a unit
  in `K[X]`, so it can be absorbed into the cofactor via the bijection `r_AC ↦ c⁻¹ r_AC` of the
  degree-`b_AC` window onto itself (`natDegree` is unchanged by nonzero-constant multiplication).

## Why this is the right bookkeeping (the SYZ39 probe)

The probe `scripts/probes/probe_syz39_sylvester_badprime_structure.py` computes, over the `μ_n`
domain, the **char-0 obstruction** of `SylvesterInjective`: the gcd of the maximal minors of the
Sylvester evaluation matrix, a cyclotomic integer whose rational norm `N = Res(Φ_n, minor)` is a
concrete integer, and whose prime factors are exactly the **bad primes** at which injectivity can
fail.  Two invariances above are precisely the reason that norm is a well-defined invariant of the
*configuration up to the natural symmetry*: the norm is unchanged (up to sign / a unit) by swapping
the two carrying pairs and by rescaling the band factors — i.e. it descends to the orbit space of
the band triple under the pair-relabelling and projective-scaling action.  Concretely (probe):

* `N` is always divisible by the **ramified primes** — exactly the primes dividing `n` (the atomic
  root-difference norms `N(ω^a − ω^b) = N(ω^{a−b} − 1)` only ever involve primes `∣ n`);
* the *genuine* field-dependent bad primes (e.g. `n=13`: `53, 79, 103, 131, 157, 181`; `n=16`:
  `17, 31`) do **not** divide `n`, so they do **not** arise from any product of cyclotomic
  root-difference norms — they are a genuine determinant/resultant (additive cancellation), not a
  product of atomic norms;
* for every fixed small `(n, k)` config `|N|` is tiny (`≤ 2^{67}` through `n = 16`), so any prime
  above the prize characteristic is clean; the open wall is the growth of `|N|` (bit-length linear
  in the minor size, hence `∝ n`) as `n → 2^{30}`, over `∼ C(n, s)^3` configurations.

See `docs/kb/deltastar-466-syz39-resultant-structure-2026-07-11.md` for the full bad-prime law and
the brutally-honest comparison with the BGK exponential-sum wall.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ39

open Polynomial ArkLib.ProximityGap.SYZ38

/-- **Symmetry of Sylvester injectivity.**  Injectivity of the generalized Sylvester map is
invariant under swapping the two carrying pairs `(WAC, bAC) ↔ (WBC, bBC)`.  The divisibility
`W_AB ∣ (W_BC r_BC − W_AC r_AC)` is the negation of `W_AB ∣ (W_AC r_AC − W_BC r_BC)`, so the two
in-budget kernels coincide. -/
theorem sylvester_injective_symm {K : Type*} [Field K] (WAB WAC WBC : K[X]) (bAC bBC : ℕ)
    (h : SylvesterInjective WAB WAC WBC bAC bBC) :
    SylvesterInjective WAB WBC WAC bBC bAC := by
  intro rBC rAC hbBC hbAC hdvd
  -- `hdvd : WAB ∣ (WBC * rBC - WAC * rAC)`; negate to feed the original predicate.
  have hdvd' : WAB ∣ (WAC * rAC - WBC * rBC) := by
    have heq : WAC * rAC - WBC * rBC = -(WBC * rBC - WAC * rAC) := by ring
    rw [heq]; exact (dvd_neg).mpr hdvd
  obtain ⟨hAC, hBC⟩ := h rAC rBC hbAC hbBC hdvd'
  exact ⟨hBC, hAC⟩

/-- **Unit-scaling invariance (left factor).**  Scaling the band factor `W_AC` by a nonzero field
constant `c` leaves Sylvester injectivity unchanged: `c` is a unit in `K[X]`, absorbed into the
cofactor by `r_AC ↦ c⁻¹ r_AC`, a degree-preserving bijection of the in-budget window.  This is the
projective-scaling equivariance that makes the char-0 resultant norm a well-defined orbit
invariant. -/
theorem sylvester_injective_unit_scale {K : Type*} [Field K] (WAB WAC WBC : K[X]) (bAC bBC : ℕ)
    (c : K) (hc : c ≠ 0)
    (h : SylvesterInjective WAB WAC WBC bAC bBC) :
    SylvesterInjective WAB (C c * WAC) WBC bAC bBC := by
  intro rAC rBC hbAC hbBC hdvd
  -- Rewrite the divisibility so the scalar sits on the cofactor: `(C c * WAC) * rAC = WAC * (C c * rAC)`.
  have hdvd' : WAB ∣ (WAC * (C c * rAC) - WBC * rBC) := by
    have hrw : WAC * (C c * rAC) - WBC * rBC = (C c * WAC) * rAC - WBC * rBC := by ring
    rw [hrw]; exact hdvd
  -- `C c * rAC` has the same degree budget as `rAC` (nonzero-constant multiplication).
  have hbudget : C c * rAC ≠ 0 → (C c * rAC).natDegree ≤ bAC := by
    intro hne
    have hrAC : rAC ≠ 0 := by
      intro h0; apply hne; rw [h0, mul_zero]
    rw [natDegree_C_mul hc]
    exact hbAC hrAC
  obtain ⟨hAC0, hBC0⟩ := h (C c * rAC) rBC hbudget hbBC hdvd'
  refine ⟨?_, hBC0⟩
  -- `C c * rAC = 0` with `c ≠ 0` forces `rAC = 0`.
  rcases mul_eq_zero.mp hAC0 with hcc | hr
  · exact absurd (C_eq_zero.mp hcc) hc
  · exact hr

end ArkLib.ProximityGap.SYZ39

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ39.sylvester_injective_symm
#print axioms ArkLib.ProximityGap.SYZ39.sylvester_injective_unit_scale
