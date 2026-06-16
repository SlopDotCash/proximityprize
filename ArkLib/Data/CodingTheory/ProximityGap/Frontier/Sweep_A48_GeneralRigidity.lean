/-
# The assembled general char-0 dyadic rigidity (#444, capstone)

Chains the three proven pieces — `Sweep_A46.multiscale_dvd`, `Sweep_A47.dyadic_telescope`, and
`Sweep_A47.coeff_periodic_of_geom_dvd` — into one statement: a polynomial `g ∈ ℚ[X]` of degree `< 2^μ`
that vanishes at every dyadic-tower root `ζ, ζ², …, ζ^{2^r}` of a primitive `2^μ`-th root has
coefficients **periodic with period `2^{μ-1-r}`**. For the indicator of a lacunary subset `S ⊆ μ_{2^μ}`
(`p₁ = p₂ = … = 0`, equivalently `g(ζ^{2^i}) = 0`), this says `S` is a **union of cosets** of the
order-`2^{r+1}` subgroup — the general char-0 `lacunary ⟹ coset` rigidity (dyadic Fourier-uncertainty
for the prime 2), now for ALL rates, not just the trinomial (`Sweep_A45`) case.

Key identity (`multiscale_prod_eq_geom`): the multi-scale cyclotomic product equals the step-`2^{μ-1-r}`
all-ones polynomial, proven by a clean difference-of-squares induction
`(X^{2^{μ-1-r}}-1)·∏_{i≤r}(X^{2^{μ-1-i}}+1) = X^{2^μ}-1`.

The char-`p` failure is unchanged: `multiscale_dvd` rests on the dyadic cyclotomics being irreducible
over `ℚ`, which splits mod `p ≡ 1 mod 2^μ` — the defect, the open core.

Axiom-clean. No `sorry`.
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.Sweep_A46_MultiScaleRigidity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.Sweep_A47_DyadicPeriodicity

namespace ArkLib.ProximityGap.EvenOddDescent

open Polynomial Finset

variable {F : Type*} [Field F]

/-- `(X^{2^{μ-1-r}} - 1) · ∏_{i≤r} (X^{2^{μ-1-i}} + 1) = X^{2^μ} - 1` (difference-of-squares induction). -/
theorem mul_multiscale_prod {μ : ℕ} :
    ∀ r : ℕ, r < μ →
      (X ^ (2 ^ (μ - 1 - r)) - 1 : F[X]) * ∏ i ∈ Finset.range (r + 1), (X ^ (2 ^ (μ - 1 - i)) + 1)
        = X ^ (2 ^ μ) - 1 := by
  intro r
  induction r with
  | zero =>
    intro hr
    rw [Finset.prod_range_one, show μ - 1 - 0 = μ - 1 from by omega,
      show (2 : ℕ) ^ μ = 2 ^ (μ - 1) * 2 from by
        rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ μ by omega)], pow_mul]
    ring
  | succ r ih =>
    intro hr
    have hcomb : (X ^ (2 ^ (μ - 1 - (r + 1))) - 1 : F[X]) * (X ^ (2 ^ (μ - 1 - (r + 1))) + 1)
        = X ^ (2 ^ (μ - 1 - r)) - 1 := by
      rw [show (2 : ℕ) ^ (μ - 1 - r) = 2 ^ (μ - 1 - (r + 1)) * 2 from by
        rw [show μ - 1 - r = (μ - 1 - (r + 1)) + 1 from by omega, pow_succ], pow_mul]
      ring
    rw [Finset.prod_range_succ, mul_comm _ (X ^ (2 ^ (μ - 1 - (r + 1))) + 1), ← mul_assoc, hcomb]
    exact ih (by omega)

/-- **The multi-scale cyclotomic product equals the step-`2^{μ-1-r}` all-ones polynomial.** -/
theorem multiscale_prod_eq_geom {μ r : ℕ} (hr : r < μ) :
    (∏ i ∈ Finset.range (r + 1), (X ^ (2 ^ (μ - 1 - i)) + 1) : F[X])
      = ∑ k ∈ Finset.range (2 ^ (r + 1)), (X ^ (2 ^ (μ - 1 - r))) ^ k := by
  have hne : (X ^ (2 ^ (μ - 1 - r)) - 1 : F[X]) ≠ 0 := by
    intro h
    have hd : (X ^ (2 ^ (μ - 1 - r)) - C (1 : F)).natDegree = 2 ^ (μ - 1 - r) := natDegree_X_pow_sub_C
    rw [map_one, h, natDegree_zero] at hd
    exact absurd hd.symm (pow_pos (by norm_num) (μ - 1 - r)).ne'
  apply mul_left_cancel₀ hne
  rw [mul_multiscale_prod r hr, geom_mul_eq (2 ^ (μ - 1 - r)) (2 ^ (r + 1)),
    show 2 ^ (μ - 1 - r) * 2 ^ (r + 1) = 2 ^ μ from by rw [← pow_add]; congr 1; omega]

/-- **General char-0 dyadic rigidity (assembled).** A polynomial `g ∈ ℚ[X]` with `deg g < 2^μ` that
vanishes at every dyadic-tower root `ζ, ζ², …, ζ^{2^r}` of a primitive `2^μ`-th root `ζ` has periodic
coefficients: `g.coeff j = g.coeff (j - 2^{μ-1-r})` for `2^{μ-1-r} ≤ j < 2^μ`. For a lacunary subset's
indicator this is "the support is a union of cosets" — the general (any-rate) char-0 `lacunary ⟹ coset`
rigidity. -/
theorem general_dyadic_rigidity {μ r : ℕ} (hr : r < μ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 ^ μ))
    (g : ℚ[X]) (hdeg : g.natDegree < 2 ^ μ) (hvanish : ∀ i ≤ r, (aeval (ζ ^ 2 ^ i)) g = 0)
    {j : ℕ} (hj : 2 ^ (μ - 1 - r) ≤ j) (hjm : j < 2 ^ μ) :
    g.coeff j = g.coeff (j - 2 ^ (μ - 1 - r)) := by
  have hdvd : (∑ k ∈ Finset.range (2 ^ (r + 1)), (X ^ (2 ^ (μ - 1 - r))) ^ k : ℚ[X]) ∣ g := by
    rw [← multiscale_prod_eq_geom hr]; exact multiscale_dvd ζ hζ g r hr hvanish
  have hdm : 2 ^ (μ - 1 - r) * 2 ^ (r + 1) = 2 ^ μ := by rw [← pow_add]; congr 1; omega
  refine coeff_periodic_of_geom_dvd (d := 2 ^ (μ - 1 - r)) (m := 2 ^ (r + 1))
    (by positivity) g ?_ hdvd hj ?_
  · rw [hdm]; exact hdeg
  · rw [hdm]; exact hjm

end ArkLib.ProximityGap.EvenOddDescent
