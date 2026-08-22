/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# The char-0 subset-sum spectrum generating function, closed form (#444)

A single closed-form generating function that **unifies** the three landed char-0
subset-sum-spectrum census facts of `μ_{2^μ}` (`m = 2^{μ-1} = n/2`):

  `(x² − 1) · G(x) = x^{m+2}·(x+2)^m − (2x+1)^m`,   where `G(x) = ∑_r N_r · x^r`.

Here `N_r = #{ ∑_{z∈S} z : S ⊆ μ_n, |S| = r }` is the char-0 (cross-polytope) subset-sum
spectrum count. Enumerating net-vector classes — `k` nonzero antipodal coordinates contribute
`C(m,k)·2^k` classes, reachable at depths `r = k + 2i` for `0 ≤ i ≤ m − k` — gives `G` as the
manifest double sum `∑_k C(m,k)2^k ∑_{i} x^{k+2i}` (this file's `spectrumGF`); the `x^r`-coefficient
is then exactly `N_r = ∑_{k ≡ r (2),\ k ≤ min(r, 2m−r)} C(m,k) 2^k`.

This subsumes the prior bricks as evaluations / structure of the **2-term** right-hand side:
* `x = 1` (removable):     total mass `T(m) = 3^{m-1}(m+3)`  (`spectotal`, O193);
* `x = −1` (removable):    alternating sum `(−1)^{m+1}(m−1)`  (new here);
* functional equation:     `G(x) = x^{2m}·G(1/x)`  ⟺ the palindrome `N_r = N_{2m−r}`
                           (`spectsym` / complement symmetry, O186).

The identity is fully general — it holds for **any element `x` of any commutative ring** — and the
proof is elementary Mathlib (`geom_sum_mul` for the inner geometric series, then the binomial
theorem `add_pow` twice). Numerically cross-checked exactly for `m = 1 … 12`
(`scripts/probes/_probe_444_charzero_census_audit.py`).

**Honest scope (the wall is untouched).** This is the char-0 / cross-polytope count. It equals the
`F_p` object only in the dilute regime `N_r ≪ p`; at the prize-binding depth `r = ρn` the `F_p`
count is collision-saturated and `p`-dependent — that excess (`Ψ_p − Ψ₀ > 0` = the BGK/BCHKS-1.12
defect) is the open core and is **not** addressed here. No capacity / beyond-Johnson / sub-linear /
growth-law claim. CORE `M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN.

Axiom-clean: `⊆ {propext, Classical.choice, Quot.sound}`. No `sorry`/`axiom`/`native_decide`.
-/

namespace ArkLib.ProximityGap.EvenOddDescent

open Finset

variable {R : Type*} [CommRing R]

/-- The char-0 subset-sum spectrum generating function of `μ_{2^μ}` (`m = n/2`), written as the
manifest net-vector double sum: a class with `k` nonzero antipodal coordinates contributes
`C(m,k)·2^k` and lives at depths `r = k + 2i` (`0 ≤ i ≤ m − k`). Thus the `x^r`-coefficient is
exactly `N_r = ∑_{k ≡ r (2),\ k ≤ min(r, 2m−r)} C(m,k) 2^k`. -/
def spectrumGF (x : R) (m : ℕ) : R :=
  ∑ k ∈ range (m + 1), ((m.choose k : R) * 2 ^ k) * ∑ i ∈ range (m - k + 1), x ^ (k + 2 * i)

/-- Per-depth contribution telescopes: `(x²−1)·∑_{i<m−k+1} x^{k+2i} = x^{2m−k+2} − x^k`. -/
private theorem mul_inner (x : R) (m k : ℕ) (hk : k ≤ m) :
    (x ^ 2 - 1) * ∑ i ∈ range (m - k + 1), x ^ (k + 2 * i)
      = x ^ (2 * m - k + 2) - x ^ k := by
  have hfac : ∑ i ∈ range (m - k + 1), x ^ (k + 2 * i)
      = x ^ k * ∑ i ∈ range (m - k + 1), (x ^ 2) ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [pow_add, pow_mul])
  have hexp : k + 2 * (m - k + 1) = 2 * m - k + 2 := by omega
  have hgeom : (x ^ 2 - 1) * ∑ i ∈ range (m - k + 1), (x ^ 2) ^ i
      = (x ^ 2) ^ (m - k + 1) - 1 := by rw [mul_comm, geom_sum_mul]
  rw [hfac, ← mul_assoc, mul_comm (x ^ 2 - 1) (x ^ k), mul_assoc, hgeom, mul_sub, mul_one,
    ← pow_mul, ← pow_add, hexp]

/-- **The char-0 subset-sum spectrum generating function in closed form.**
`(x² − 1)·G(x) = x^{m+2}·(x+2)^m − (2x+1)^m` for every element `x` of any commutative ring.
Unifies the spectrum total (`x=1`), the alternating sum (`x=−1`), and the complement-symmetry
palindrome (functional equation of the RHS) — see the file header. -/
theorem spectrumGF_mul_eq (x : R) (m : ℕ) :
    (x ^ 2 - 1) * spectrumGF x m = x ^ (m + 2) * (x + 2) ^ m - (2 * x + 1) ^ m := by
  unfold spectrumGF
  rw [Finset.mul_sum]
  have hterm : ∀ k ∈ range (m + 1),
      (x ^ 2 - 1) * (((m.choose k : R) * 2 ^ k) * ∑ i ∈ range (m - k + 1), x ^ (k + 2 * i))
        = ((m.choose k : R) * 2 ^ k) * x ^ (2 * m - k + 2)
          - ((m.choose k : R) * 2 ^ k) * x ^ k := by
    intro k hk
    have hk' : k ≤ m := by simpa [Nat.lt_succ_iff] using mem_range.mp hk
    rw [← mul_assoc, mul_comm (x ^ 2 - 1) ((m.choose k : R) * 2 ^ k), mul_assoc,
      mul_inner x m k hk', mul_sub]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have hlow : ∑ k ∈ range (m + 1), ((m.choose k : R) * 2 ^ k) * x ^ k = (2 * x + 1) ^ m := by
    rw [add_pow]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [one_pow, mul_one, mul_pow]
    ring
  have hhigh : ∑ k ∈ range (m + 1), ((m.choose k : R) * 2 ^ k) * x ^ (2 * m - k + 2)
      = x ^ (m + 2) * (x + 2) ^ m := by
    rw [add_comm x (2 : R), add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≤ m := by simpa [Nat.lt_succ_iff] using mem_range.mp hk
    have hexp : 2 * m - k + 2 = (m + 2) + (m - k) := by omega
    rw [hexp, pow_add]
    ring
  rw [hlow, hhigh]

end ArkLib.ProximityGap.EvenOddDescent
