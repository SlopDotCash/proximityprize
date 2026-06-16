/-
# Multi-scale char-0 rigidity: the engine of the general (iterated) dyadic rigidity (#444)

`Sweep_A44` proved the *first level* of the char-0 rigidity (a vanishing-sum subset of `μ_{2^μ}` is
negation-closed) via `g(ζ) = 0 ⟹ (X^{2^{μ-1}}+1) ∣ g`. The *general* fixed-rate rigidity
(`e₁ = … = e_{n/8} = 0 ⟹ union of cosets`, beyond the trinomial case of `Sweep_A45`) needs the
**iterated** form: vanishing of the higher power sums forces divisibility by the cyclotomics at
*descending* dyadic levels simultaneously. This file proves that engine (two-scale form, with the
general `r`-scale statement following by the same coprime-product argument): if `g` vanishes at both
`ζ` and `ζ²` (i.e. `p₁ = p₂ = 0` on the indicator), then `g` is divisible by the product of the two
dyadic cyclotomic binomials `(X^{2^{μ-1}}+1)(X^{2^{μ-2}}+1)`, giving coefficient symmetry at the two
scales `2^{μ-1}` and `2^{μ-2}` (via the `Sweep_A43` engine) — the second level of coset rigidity.

The char-0 input is the irreducibility of the dyadic cyclotomics over `ℚ`; in characteristic
`p ≡ 1 mod 2^μ` they split and this fails — the open core.

Axiom-clean: cyclotomic + minpoly + coprimality. No `sorry`.
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.Complex.Basic

namespace ArkLib.ProximityGap.EvenOddDescent

open Polynomial

/-- The dyadic cyclotomic value over `ℚ`: `cyclotomic (2^k) ℚ = X^{2^{k-1}} + 1` for `k ≥ 1`. -/
theorem dyadic_cyclotomic_eq {k : ℕ} (hk : 1 ≤ k) :
    cyclotomic (2 ^ k) ℚ = X ^ (2 ^ (k - 1)) + 1 := by
  have hk' : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk
  have h := cyclotomic_prime_pow_eq_geom_sum (R := ℚ) (p := 2) (n := k - 1) Nat.prime_two
  rw [hk'] at h
  rw [h, Finset.sum_range_succ, Finset.sum_range_one]; ring

/-- **Per-scale divisibility (general engine).** If `g ∈ ℚ[X]` vanishes at `ζ^{2^i}` for a primitive
`2^μ`-th root `ζ` (`i < μ`), then the dyadic cyclotomic binomial at scale `μ-i`, i.e.
`X^{2^{μ-1-i}} + 1 = Φ_{2^{μ-i}}`, divides `g`. (`ζ^{2^i}` is a primitive `2^{μ-i}`-th root, whose
minimal polynomial over `ℚ` is that irreducible cyclotomic.) The full `r`-scale product divisibility
follows from this by `IsCoprime.mul_dvd` over the pairwise-coprime distinct-conductor cyclotomics
(`two_scale_dvd` is the `r=1` instance); iterating the resulting `Sweep_A43` coefficient symmetries to
the bottom scale gives the general `lacunary ⟹ coset` char-0 rigidity. -/
theorem scale_dvd {μ : ℕ} (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (g : ℚ[X]) {i : ℕ} (hi : i < μ)
    (h : (aeval (ζ ^ 2 ^ i)) g = 0) : (X ^ (2 ^ (μ - 1 - i)) + 1 : ℚ[X]) ∣ g := by
  have hpos : 0 < 2 ^ (μ - i) := pow_pos (by norm_num) (μ - i)
  haveI : NeZero ((2 ^ (μ - i) : ℕ) : ℚ) :=
    ⟨by exact_mod_cast pow_ne_zero (μ - i) (two_ne_zero (α := ℕ))⟩
  have hprim : IsPrimitiveRoot (ζ ^ 2 ^ i) (2 ^ (μ - i)) := by
    have hprod : (2 : ℕ) ^ μ = 2 ^ i * 2 ^ (μ - i) := by rw [← pow_add]; congr 1; omega
    exact IsPrimitiveRoot.pow (pow_pos (by norm_num) μ) hζ hprod
  rw [show μ - 1 - i = (μ - i) - 1 by omega, ← dyadic_cyclotomic_eq (show 1 ≤ μ - i by omega),
    hprim.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hpos)]
  exact minpoly.dvd ℚ (ζ ^ 2 ^ i) h

/-- **Two-scale char-0 rigidity (engine of the iterated rigidity).** If `g ∈ ℚ[X]` vanishes at a
primitive `2^μ`-th root `ζ` and at `ζ²` (`μ ≥ 2`), then `g` is divisible by the product of the two
dyadic cyclotomic binomials `(X^{2^{μ-1}}+1)·(X^{2^{μ-2}}+1)`. Combined with the `Sweep_A43` engine this
forces coefficient symmetry at scales `2^{μ-1}` and `2^{μ-2}` — the second level of the dyadic coset
rigidity. (The general `r`-scale form follows by the same coprime-product argument over the descending
levels `ζ, ζ², …, ζ^{2^r}`; iterating to the bottom gives the full `lacunary ⟹ coset` rigidity.) -/
theorem two_scale_dvd {μ : ℕ} (hμ : 2 ≤ μ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 ^ μ))
    (g : ℚ[X]) (h0 : (aeval ζ) g = 0) (h1 : (aeval (ζ ^ 2)) g = 0) :
    ((X ^ (2 ^ (μ - 1)) + 1) * (X ^ (2 ^ (μ - 2)) + 1) : ℚ[X]) ∣ g := by
  have hμpos : 0 < 2 ^ μ := pow_pos (by norm_num) μ
  haveI : NeZero ((2 ^ μ : ℕ) : ℚ) := ⟨by exact_mod_cast pow_ne_zero μ (two_ne_zero (α := ℕ))⟩
  -- scale 0: `(X^{2^{μ-1}}+1) = minpoly ℚ ζ ∣ g`
  have hd0 : (X ^ (2 ^ (μ - 1)) + 1 : ℚ[X]) ∣ g := by
    rw [← dyadic_cyclotomic_eq (show 1 ≤ μ by omega),
      hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hμpos)]
    exact minpoly.dvd ℚ ζ h0
  -- scale 1: `ζ²` is a primitive `2^{μ-1}`-th root, so `(X^{2^{μ-2}}+1) = minpoly ℚ ζ² ∣ g`
  have hprod : (2 : ℕ) ^ μ = 2 * 2 ^ (μ - 1) := by rw [← pow_succ']; congr 1; omega
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) (2 ^ (μ - 1)) := IsPrimitiveRoot.pow hμpos hζ hprod
  have hμ1pos : 0 < 2 ^ (μ - 1) := pow_pos (by norm_num) (μ - 1)
  haveI : NeZero ((2 ^ (μ - 1) : ℕ) : ℚ) :=
    ⟨by exact_mod_cast pow_ne_zero (μ - 1) (two_ne_zero (α := ℕ))⟩
  have hd1 : (X ^ (2 ^ (μ - 2)) + 1 : ℚ[X]) ∣ g := by
    rw [show μ - 2 = (μ - 1) - 1 by omega,
      ← dyadic_cyclotomic_eq (show 1 ≤ μ - 1 by omega),
      hζ2.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hμ1pos)]
    exact minpoly.dvd ℚ (ζ ^ 2) h1
  -- the two dyadic cyclotomics are coprime over `ℚ` (distinct conductors)
  have hcop : IsCoprime (X ^ (2 ^ (μ - 1)) + 1 : ℚ[X]) (X ^ (2 ^ (μ - 2)) + 1) := by
    rw [← dyadic_cyclotomic_eq (show 1 ≤ μ by omega),
      show μ - 2 = (μ - 1) - 1 by omega, ← dyadic_cyclotomic_eq (show 1 ≤ μ - 1 by omega)]
    refine cyclotomic.isCoprime_rat (fun heq => ?_)
    have : μ = μ - 1 := Nat.pow_right_injective (le_refl 2) heq
    omega
  exact hcop.mul_dvd hd0 hd1

/-- **General `r`-scale char-0 rigidity (the full dyadic engine).** If `g ∈ ℚ[X]` vanishes at every
dyadic-tower root `ζ, ζ², ζ⁴, …, ζ^{2^r}` of a primitive `2^μ`-th root `ζ` (`r < μ`), then `g` is
divisible by the **product of all `r+1` dyadic cyclotomic binomials**
`∏_{i=0}^{r} (X^{2^{μ-1-i}} + 1)`. Proof: each factor divides `g` (`scale_dvd`), and the factors are
pairwise coprime (distinct-conductor cyclotomics), so `IsCoprime.mul_dvd` composes them. Combined with
the `Sweep_A43` engine at each scale this gives coefficient symmetry simultaneously at all scales
`2^{μ-1}, …, 2^{μ-1-r}` — the multi-scale rigidity whose bottom-scale limit is the general
`lacunary ⟹ coset` characteristic-0 rigidity. -/
theorem multiscale_dvd {μ : ℕ} (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (g : ℚ[X]) :
    ∀ r : ℕ, r < μ → (∀ i ≤ r, (aeval (ζ ^ 2 ^ i)) g = 0) →
      (∏ i ∈ Finset.range (r + 1), (X ^ (2 ^ (μ - 1 - i)) + 1 : ℚ[X])) ∣ g := by
  intro r
  induction r with
  | zero =>
    intro _ h
    simpa using scale_dvd ζ hζ g (show 0 < μ by omega) (h 0 (le_refl 0))
  | succ r ih =>
    intro hr h
    rw [Finset.prod_range_succ]
    have hIH : (∏ i ∈ Finset.range (r + 1), (X ^ (2 ^ (μ - 1 - i)) + 1 : ℚ[X])) ∣ g :=
      ih (by omega) (fun i hi => h i (by omega))
    have hlast : (X ^ (2 ^ (μ - 1 - (r + 1))) + 1 : ℚ[X]) ∣ g :=
      scale_dvd ζ hζ g (show r + 1 < μ by omega) (h (r + 1) (le_refl _))
    -- the new factor is coprime to every factor already in the product, hence to their product
    have hcop : IsCoprime (X ^ (2 ^ (μ - 1 - (r + 1))) + 1 : ℚ[X])
        (∏ i ∈ Finset.range (r + 1), (X ^ (2 ^ (μ - 1 - i)) + 1)) := by
      refine IsCoprime.prod_right (fun i hi => ?_)
      have hi' : i ≤ r := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hi
      rw [show μ - 1 - (r + 1) = (μ - (r + 1)) - 1 by omega,
        ← dyadic_cyclotomic_eq (show 1 ≤ μ - (r + 1) by omega),
        show μ - 1 - i = (μ - i) - 1 by omega, ← dyadic_cyclotomic_eq (show 1 ≤ μ - i by omega)]
      refine cyclotomic.isCoprime_rat (fun heq => ?_)
      have : μ - (r + 1) = μ - i := Nat.pow_right_injective (le_refl 2) heq
      omega
    rw [mul_comm]
    exact hcop.mul_dvd hlast hIH

end ArkLib.ProximityGap.EvenOddDescent
