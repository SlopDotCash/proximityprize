/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.Sweep_A50_SpectrumGeneratingFunction
import Mathlib.Tactic

/-!
# The char-0 subset-sum spectrum COEFFICIENT palindrome `N_r = N_{2m−r}` (#444)

`Sweep_A50_SpectrumGeneratingFunction` defines the spectrum generating function
`G(x) = spectrumGF x m` and its header reads off the `x^r`-coefficient in closed form
> `N_r = ∑_{k ≡ r (2),  k ≤ min(r, 2m−r)} C(m,k)·2^k`.
`SpectrumGFFunctionalEquation` then proves the GF-level self-reciprocity
`x^{2m}·G(x⁻¹) = G(x)`, which it states is "⟺ the complement-symmetry palindrome `N_r = N_{2m−r}`".

This file makes that coefficient-level palindrome a **standalone arithmetic theorem about the
coefficient `N_r` itself** (not just the polynomial functional equation): it pins the closed-form
coefficient `spectrumCoeff m r := ∑_{k ≤ min(r,2m−r), k ≡ r (2)} C(m,k)·2^k` and proves
`spectrumCoeff m r = spectrumCoeff m (2m−r)` for ALL `r ≤ 2m` (the depth-reflection symmetry).

Note on scope of the closed form: the cutoff `min(r, 2m−r)` makes the closed form the genuine
`x^r`-coefficient only on the support `r ≤ 2m`; for `r > 2m` the *raw* closed form is NOT the GF
coefficient (at even `r > 2m` the `k=0` term survives), so the palindrome is stated and proved on
its valid domain `r ≤ 2m`. This boundary was confirmed by probe BEFORE formalizing.

**Mechanism (the summation set is literally identical, no cancellation).** Two facts collapse it:
(1) parity: `2m − r ≡ r (mod 2)` since `2m` is even, so the residue filter `k ≡ r (2)` is the SAME
predicate as `k ≡ (2m−r) (2)`; (2) the cutoff is symmetric: `min(r, 2m−r) = min(2m−r, r)`. Hence the
filtered index range `{k ≤ min(·,·) : k ≡ · (2)}` and the summand `C(m,k)·2^k` are unchanged under
`r ↦ 2m−r` — the two sums are the SAME `Finset` sum. This is the complement-symmetry `S ↦ μ_n ∖ S`
on the cross-polytope made coefficient-explicit (the depth support being `[0, 2m]`).

**Honest scope (the wall is untouched).** Char-0 / cross-polytope palindrome (the depth reflection
`r ↦ 2m−r`, NOT the asymptotic incidence cliff-at-`n/2`). It equals the `F_p` subset-sum object only
in the dilute `N_r ≪ p` regime; at prize-binding depth `r = ρn` the `F_p` count is
collision-saturated and the BGK / BCHKS-1.12 defect is the open core, untouched here.
NO capacity / beyond-Johnson / growth-law / cliff claim.
`CORE M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN.

Axiom-clean: `⊆ {propext, Classical.choice, Quot.sound}`. No `sorry`/`axiom`/`native_decide`.
-/

namespace ArkLib.ProximityGap.EvenOddDescent

open Finset

/-- **The char-0 subset-sum spectrum coefficient** (the `x^r`-coefficient of `spectrumGF`):
`N_r = ∑_{k ≤ min(r, 2m−r),  k ≡ r (mod 2)} C(m,k)·2^k`, as a natural number. -/
def spectrumCoeff (m r : ℕ) : ℕ :=
  ∑ k ∈ (range (min r (2 * m - r) + 1)).filter (fun k => k % 2 = r % 2),
    m.choose k * 2 ^ k

/-- `2m − r` has the same parity as `r` (since `2m` is even). The parity-filter half of the
palindrome mechanism. -/
theorem reflect_mod_two_eq (m r : ℕ) (hr : r ≤ 2 * m) :
    (2 * m - r) % 2 = r % 2 := by
  omega

/-- The cutoff `min(r, 2m−r)` is symmetric under `r ↦ 2m−r`. The range half of the mechanism. -/
theorem min_reflect_symm (m r : ℕ) :
    min (2 * m - r) (2 * m - (2 * m - r)) = min r (2 * m - r) := by
  omega

/-- **The coefficient palindrome `N_r = N_{2m−r}` (the complement-symmetry of the cross-polytope
spectrum, made coefficient-explicit).** For every `r ≤ 2m`,
`spectrumCoeff m r = spectrumCoeff m (2m − r)`. The two sums range over the SAME filtered `Finset`
(same parity predicate by `reflect_mod_two_eq`, same cutoff by `min_reflect_symm`) with the SAME
summand — a pure reindex-free equality of `Finset` sums, no cancellation. -/
theorem spectrumCoeff_palindrome (m r : ℕ) (hr : r ≤ 2 * m) :
    spectrumCoeff m r = spectrumCoeff m (2 * m - r) := by
  unfold spectrumCoeff
  have hpar : (2 * m - r) % 2 = r % 2 := reflect_mod_two_eq m r hr
  have hmin : min (2 * m - r) (2 * m - (2 * m - r)) = min r (2 * m - r) := min_reflect_symm m r
  -- Rewrite the reflected side's range cutoff and parity filter to match the original.
  rw [hmin]
  refine Finset.sum_congr ?_ (fun k _ => rfl)
  -- The two filter predicates `k % 2 = r % 2` and `k % 2 = (2m−r) % 2` are equal.
  apply Finset.filter_congr
  intro k _
  rw [hpar]

/-- **Self-palindrome at the center.** At the central depth `r = m` (`2m − r = m`) the reflection
is its own fixed point — recorded for completeness. -/
theorem spectrumCoeff_center (m : ℕ) :
    spectrumCoeff m m = spectrumCoeff m (2 * m - m) := by
  have h : 2 * m - m = m := by omega
  rw [h]

end ArkLib.ProximityGap.EvenOddDescent

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.EvenOddDescent.reflect_mod_two_eq
#print axioms ArkLib.ProximityGap.EvenOddDescent.min_reflect_symm
#print axioms ArkLib.ProximityGap.EvenOddDescent.spectrumCoeff_palindrome
#print axioms ArkLib.ProximityGap.EvenOddDescent.spectrumCoeff_center
