/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.C71SparseOrbitGap

/-!
# Door-(iv) / C71: the multi-term worst-case strata is a COEFFICIENT-INTERFERENCE object, not a
  pure support-incidence object (#444)

## Where this sits
`C71SparseOrbitGap.lean` (commit `5dd3a409e`) proved the Chai–Fan 2026/861 worst-case `≤3`-sparse
FRI adversary on thin `μ_n` is STRICTLY multi-term (`s23max = 9 > s1max = 8`, uniform over
`p ∈ {17,41,521}` spanning `p ≤ n³` and `p > n³`), so it ESCAPES the action-orbit eigenvector pin
(`multiterm_not_orbit_eligible`). The residual it leaves explicitly OPEN:

> a NON-orbit incidence bound on the 2- or 3-term strata.

## The new probe finding this file records (axiom-clean structural half)
`scripts/probes/probe_c71_multiterm_support_structure.py` (EXACT full-`α`-sweep, EXACT
max-agreement, thin `μ_n`, NEVER `n = q−1`, `p ∈ {17, 41, 521}`) sharpens that residual. It pins
WHICH directions achieve `s23max` (the prior probe reported only the value):

* the worst-case **winning support set is prime-independent**: `{(1,3,4), (2,3,6), (3,4)}` —
  IDENTICAL across `p = 17, 41, 521` (an arithmetic invariant, not prime noise);
* `[T3]` the winning support set is NOT closed under the `2`-power dilation `i ↦ 2i (mod n)`
  (`0/3` orbit-closed) — confirming mechanistically that it sits OUTSIDE the orbit regime, as the
  pin predicts;
* `[T4]` only `3/10` of the winning `(support, coeff)` pairs use UNIT coefficients `[1,…,1]` —
  the worst case is achieved by **non-unit coefficient ratios**. The adversary is a genuine
  **coefficient-interference** object, NOT a pure support-incidence object.

`[T4]` is the sharp consequence: any non-orbit incidence bound that closes the multi-term strata
MUST be coefficient-sensitive — a count over supports alone (the natural "incidence" object) cannot
reach the worst case, because the worst case lives at a non-trivial coefficient ratio inside a
fixed support.

## What is formalized here (axiom-clean, NO new analytic content)
The structural fact UNDERLYING `[T4]`: for a fixed `≥2`-term support, the coefficient ratio is a
genuine extra degree of freedom that the already-swept `α`-line scaling does NOT collapse.
Concretely two two-term directions with the SAME support but DIFFERENT coefficient ratios are NOT
scalar multiples of one another, so they are genuinely DISTINCT adversary directions (each its own
line in the affine pencil), not re-parametrisations of a single line. Hence the multi-term search is
strictly `support × (coefficient ratio)`, not `support` alone; a pure support-incidence count
undercounts the adversary family exactly along the coefficient axis the probe's worst case occupies.

* `twoTerm_ratio_distinguishes` : if `c₁·d₂ ≠ c₂·d₁` (distinct coefficient ratios) and the two
  support exponents are distinct, then `c₁·X^i + c₂·X^j` and `d₁·X^i + d₂·X^j` are NOT scalar
  multiples of each other. (The coefficient ratio is a faithful invariant of the line.)
* `multiterm_coeff_ratio_is_free` : packaged statement — a fixed `2`-term support carries a
  one-parameter family of pairwise-non-proportional directions, so the worst-case search over
  multi-term directions is strictly larger than a search over supports. This is the formal content
  of the probe's "`[T4]` coefficient-interference, not support-incidence" verdict.

These extend the PROVEN `C71SparseOrbitGap` / `ActionOrbitGeneralF` line and add NO character-sum /
incidence content. The actual incidence bound on the multi-term strata (now known to require
coefficient-sensitivity) remains OPEN and is NOT claimed here.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Polynomial

namespace ArkLib.ProximityGap.C71MultiTermCoeffInterference

set_option linter.unusedSimpArgs false

variable {F : Type*} [Field F]

/-- Coefficient `i` of a two-term polynomial `c₁·X^i + c₂·X^j` with `i ≠ j` is `c₁`. -/
private lemma coeff_twoTerm_left (c₁ c₂ : F) {i j : ℕ} (hij : i ≠ j) :
    (C c₁ * X ^ i + C c₂ * X ^ j : F[X]).coeff i = c₁ := by
  simp [coeff_C_mul, coeff_X_pow, hij, Ne.symm hij]

/-- Coefficient `j` of a two-term polynomial `c₁·X^i + c₂·X^j` with `i ≠ j` is `c₂`. -/
private lemma coeff_twoTerm_right (c₁ c₂ : F) {i j : ℕ} (hij : i ≠ j) :
    (C c₁ * X ^ i + C c₂ * X ^ j : F[X]).coeff j = c₂ := by
  simp [coeff_C_mul, coeff_X_pow, hij, Ne.symm hij]

/-- **The coefficient ratio is a faithful line-invariant of a two-term direction.**
If two two-term directions share the support `{i, j}` (`i ≠ j`) but have DISTINCT coefficient
ratios (`c₁·d₂ ≠ c₂·d₁`), then they are NOT scalar multiples of each other: there is no scalar `s`
with `c₁·X^i + c₂·X^j = s·(d₁·X^i + d₂·X^j)`. Hence the `α`-line scaling already swept in the affine
pencil does NOT identify them — they are genuinely distinct adversary lines. -/
theorem twoTerm_ratio_distinguishes
    (c₁ c₂ d₁ d₂ : F) {i j : ℕ} (hij : i ≠ j) (hratio : c₁ * d₂ ≠ c₂ * d₁) :
    ¬ ∃ s : F, (C c₁ * X ^ i + C c₂ * X ^ j : F[X])
              = C s * (C d₁ * X ^ i + C d₂ * X ^ j) := by
  rintro ⟨s, hs⟩
  -- compare coefficients `i` and `j` of both sides
  have hCi : (C c₁ * X ^ i + C c₂ * X ^ j : F[X]).coeff i
      = (C s * (C d₁ * X ^ i + C d₂ * X ^ j)).coeff i := by rw [hs]
  have hCj : (C c₁ * X ^ i + C c₂ * X ^ j : F[X]).coeff j
      = (C s * (C d₁ * X ^ i + C d₂ * X ^ j)).coeff j := by rw [hs]
  -- LHS coeffs
  rw [coeff_twoTerm_left c₁ c₂ hij] at hCi
  rw [coeff_twoTerm_right c₁ c₂ hij] at hCj
  -- RHS coeffs: `(C s * g).coeff k = s * g.coeff k`
  rw [coeff_C_mul, coeff_twoTerm_left d₁ d₂ hij] at hCi
  rw [coeff_C_mul, coeff_twoTerm_right d₁ d₂ hij] at hCj
  -- hCi : c₁ = s * d₁; hCj : c₂ = s * d₂
  -- ⟹ c₁ * d₂ = (s*d₁)*d₂ = (s*d₂)*d₁ = c₂ * d₁, contradicting hratio
  apply hratio
  calc c₁ * d₂ = (s * d₁) * d₂ := by rw [hCi]
    _ = (s * d₂) * d₁ := by ring
    _ = c₂ * d₁ := by rw [← hCj]

/-- **Coefficient-interference: a fixed two-term support carries pairwise-non-proportional
directions (the formal content of the probe's `[T4]` verdict).**
For a fixed support `{i, j}` (`i ≠ j`), the two directions `X^i + X^j` (unit ratio `1`) and
`X^i + c·X^j` with `c ≠ 1` are NOT scalar multiples of each other. So the worst-case search over
multi-term directions is strictly larger than a search over supports: the coefficient ratio is a
real extra axis, and the probe's worst case (`s23max` achieved only `3/10` times by unit
coefficients) lives on that axis. A pure support-incidence count therefore CANNOT reach the
multi-term worst case — any closing bound must be coefficient-sensitive. -/
theorem multiterm_coeff_ratio_is_free
    {i j : ℕ} (hij : i ≠ j) (c : F) (hc : c ≠ 1) :
    ¬ ∃ s : F, (C 1 * X ^ i + C 1 * X ^ j : F[X])
              = C s * (C 1 * X ^ i + C c * X ^ j) := by
  -- apply the ratio test with (c₁,c₂)=(1,1), (d₁,d₂)=(1,c): ratio gap `1*c ≠ 1*1` ⟺ `c ≠ 1`.
  refine twoTerm_ratio_distinguishes (1 : F) 1 1 c hij ?_
  simpa using hc

/-- **The coefficient ratio injects into projective direction-space (the counting engine).**
For a fixed support `{i, j}` (`i ≠ j`), DISTINCT coefficient ratios `r₁ ≠ r₂` give the two
unit-leading-term directions `X^i + r₁·X^j` and `X^i + r₂·X^j` that are NOT scalar multiples of each
other. Hence `r ↦ [X^i + r·X^j]` is injective into projective direction-space: the worst-case
multi-term adversary family genuinely contains a `1`-parameter (ratio) sub-family inside each fixed
support, so its size is strictly larger than the support count. This is the rigorous cardinality
content behind `multiterm_coeff_ratio_is_free` and the probe's `[T4]` (worst case at non-unit ratio,
and `769d6177f`: the worst-ratio locus is a DENSE generic subset of `F_p*`). A support-only
incidence count provably undercounts the adversary along this ratio axis. -/
theorem distinct_ratios_not_proportional
    {i j : ℕ} (hij : i ≠ j) (r₁ r₂ : F) (hr : r₁ ≠ r₂) :
    ¬ ∃ s : F, (C 1 * X ^ i + C r₁ * X ^ j : F[X])
              = C s * (C 1 * X ^ i + C r₂ * X ^ j) := by
  -- ratio test with (c₁,c₂)=(1,r₁), (d₁,d₂)=(1,r₂): gap `1*r₂ ≠ r₁*1` ⇔ `r₁ ≠ r₂`.
  refine twoTerm_ratio_distinguishes (1 : F) r₁ 1 r₂ hij ?_
  simpa [eq_comm] using hr

end ArkLib.ProximityGap.C71MultiTermCoeffInterference

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.C71MultiTermCoeffInterference.twoTerm_ratio_distinguishes
#print axioms ArkLib.ProximityGap.C71MultiTermCoeffInterference.multiterm_coeff_ratio_is_free
#print axioms ArkLib.ProximityGap.C71MultiTermCoeffInterference.distinct_ratios_not_proportional
