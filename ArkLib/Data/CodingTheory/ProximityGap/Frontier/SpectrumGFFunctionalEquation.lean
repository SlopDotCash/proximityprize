/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.Sweep_A50_SpectrumGeneratingFunction
import Mathlib.Tactic

/-!
# The char-0 subset-sum spectrum GF functional equation `x^{2m}·G(1/x) = G(x)` (#444)

`Sweep_A50_SpectrumGeneratingFunction` proved `(x²−1)·G(x) = x^{m+2}(x+2)^m − (2x+1)^m` and its
header asserts the **functional equation** `G(x) = x^{2m}·G(1/x)` as the third subsuming
consequence — "⟺ the complement-symmetry palindrome `N_r = N_{2m−r}`". This file discharges that
asserted functional equation into a theorem.

`G = spectrumGF` is a degree-`2m` polynomial in `x` whose `x^r`-coefficient is `N_r`. The functional
equation is the statement that `G` is **self-reciprocal** (palindromic): `x^{2m}·G(x⁻¹) = G(x)` for
`x ≠ 0`, equivalently `N_r = N_{2m−r}`.

**Mechanism (inner reindex, NO cancellation).** In the manifest net-vector sum the term
`C(m,k)2^k · x^{k+2i}` maps under `x ↦ x⁻¹` then `× x^{2m}` to `C(m,k)2^k · x^{2m−k−2i}`, and
`2m − k − 2i = k + 2(m−k−i)`, with `i' = m−k−i` ranging over the SAME `range (m−k+1)` as `i` (the
involution `i ↦ m−k−i` of `range (m−k+1)`). So the whole double sum is invariant — a pure
reindexing, requiring no field cancellation beyond `x ≠ 0` (to clear the negative powers). The proof
is `Finset.sum_nbij'` on the inner sum with the reflection involution.

**Honest scope (the wall is untouched).** Char-0 / cross-polytope palindrome (this is the
GF-level restatement of the complement-symmetry brick); equals the `F_p` object only in the dilute
`N_r ≪ p` regime. The prize-binding depth is collision-saturated and the BGK / BCHKS-1.12 defect is
the open core, NOT addressed here. No capacity / beyond-Johnson / growth-law claim. The reflection
index `r ↦ 2m−r` is a DEPTH reflection, NOT the asymptotic-guard incidence cliff-at-n/2.
CORE `M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN.

Axiom-clean: `⊆ {propext, Classical.choice, Quot.sound}`. No `sorry`/`axiom`/`native_decide`.
-/

namespace ArkLib.ProximityGap.EvenOddDescent

open Finset

variable {F : Type*} [Field F]

/-- **The inner geometric block is reciprocal-symmetric.** For `x ≠ 0`,
`x^{2m} · ∑_{i<m−k+1} (x⁻¹)^{k+2i} = ∑_{i<m−k+1} x^{k+2i}` when `k ≤ m`, via the reflection
involution `i ↦ (m−k)−i` of `range (m−k+1)` (`2m − k − 2i = k + 2((m−k)−i)`). -/
private theorem inner_recip (x : F) (hx : x ≠ 0) (m k : ℕ) (hk : k ≤ m) :
    x ^ (2 * m) * ∑ i ∈ range (m - k + 1), (x⁻¹) ^ (k + 2 * i)
      = ∑ i ∈ range (m - k + 1), x ^ (k + 2 * i) := by
  rw [Finset.mul_sum]
  -- reflect the RHS index i ↦ (m-k+1-1) - i = (m-k) - i
  rw [← Finset.sum_range_reflect (fun i => x ^ (k + 2 * i)) (m - k + 1)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [mem_range] at hi
  -- x^{2m} · (x⁻¹)^{k+2i} = x^{k + 2*((m-k+1-1) - i)}
  rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hx), ← pow_add]
  congr 1
  omega

/-- **The GF functional equation (A50's asserted consequence, discharged).**
`x^{2m} · spectrumGF (x⁻¹) m = spectrumGF x m` for every `x ≠ 0` — `G` is self-reciprocal
(palindromic), the GF restatement of the complement-symmetry palindrome `N_r = N_{2m−r}`. -/
theorem spectrumGF_functional_equation (x : F) (hx : x ≠ 0) (m : ℕ) :
    x ^ (2 * m) * spectrumGF (x⁻¹) m = spectrumGF x m := by
  unfold spectrumGF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkm : k ≤ m := by simpa [Nat.lt_succ_iff] using mem_range.mp hk
  rw [← mul_assoc, mul_comm (x ^ (2 * m)) ((m.choose k : F) * 2 ^ k), mul_assoc,
    inner_recip x hx m k hkm]

end ArkLib.ProximityGap.EvenOddDescent
