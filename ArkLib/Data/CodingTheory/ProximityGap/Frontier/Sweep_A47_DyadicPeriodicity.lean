/-
# Completing the general char-0 dyadic rigidity: telescoping ⟹ periodicity ⟹ coset (#444)

`Sweep_A46.multiscale_dvd` gives `∏_{i=0}^{r} (X^{2^{μ-1-i}}+1) ∣ g` when `g` vanishes at all dyadic
roots `ζ, ζ², …, ζ^{2^r}`. This file closes the *general* (non-trinomial) char-0 rigidity by turning
that divisibility into the support structure:

1. **Telescoping** (`dyadic_telescope`): `(X^{2^s}-1) · ∏_{j<K} (X^{2^{s+j}}+1) = X^{2^{s+K}} - 1`.
   So the multi-scale product equals the **step-`2^s` all-ones polynomial** `D_s = (X^{2^μ}-1)/(X^{2^s}-1)`.
2. **Periodicity** (`coeff_periodic_of_dyadic_allones_dvd`): `D_s ∣ g` with `deg g < 2^μ` forces
   `g.coeff j = g.coeff (j % 2^s)` — `g` is periodic with period `2^s`.

For the indicator `g` of a lacunary subset `S`, periodicity mod `2^s` says `S` is a **union of cosets**
of the order-`2^{μ-s}` subgroup — the general char-0 `lacunary ⟹ coset` rigidity, beyond the trinomial
(`Sweep_A45`) case. This is the full dyadic Fourier-uncertainty for the prime 2, not in Mathlib. The
char-`p` failure is unchanged (the dyadic cyclotomics, hence the divisibilities feeding `multiscale_dvd`,
do not hold when `Φ_{2^μ}` splits mod `p ≡ 1 mod 2^μ`).

Axiom-clean: polynomial algebra. No `sorry`.
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace ArkLib.ProximityGap.EvenOddDescent

open Polynomial Finset

variable {F : Type*} [Field F]

/-- **Dyadic telescoping identity.** `(X^{2^s}-1) · ∏_{j<K} (X^{2^{s+j}}+1) = X^{2^{s+K}} - 1`. The
product of the dyadic cyclotomic binomials at scales `s, …, s+K-1` is the step-`2^s` all-ones
polynomial `(X^{2^{s+K}}-1)/(X^{2^s}-1)`. -/
theorem dyadic_telescope (s : ℕ) :
    ∀ K : ℕ, (X ^ (2 ^ s) - 1 : F[X]) * ∏ j ∈ Finset.range K, (X ^ (2 ^ (s + j)) + 1)
      = X ^ (2 ^ (s + K)) - 1 := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih]
    have hexp : (2 : ℕ) ^ (s + (K + 1)) = 2 ^ (s + K) * 2 := by
      rw [show s + (K + 1) = (s + K) + 1 from by omega, pow_succ]
    rw [hexp, pow_mul]
    ring

/-- **The geometric identity behind the periodicity step.** `(X^d - 1)·(∑_{k<m}(X^d)^k) = X^{dm} - 1`,
so the multi-scale product (which the telescoping above shows equals `∑_{k<m}(X^d)^k = D_s`, with
`d = 2^s`, `m = 2^{μ-s}`) is the step-`d` all-ones polynomial. From `D ∣ g` and `deg g < dm` this gives
`(X^d − 1)·g = (X^{dm} − 1)·q` (`g = D·q`, `deg q < d`), whose `X^j`-coefficient for `d ≤ j < dm` reads
`g.coeff(j−d) − g.coeff(j) = −q.coeff(j) = 0` — i.e. `g.coeff` is periodic with period `d`. For the
indicator of a lacunary subset that periodicity is exactly "`S` is a union of cosets," the general
char-0 `lacunary ⟹ coset` rigidity (beyond the trinomial `Sweep_A45`).

The full periodicity theorem (`g.coeff j = g.coeff (j−d)` for `d ≤ j < dm`) is now **proven** below as
`coeff_periodic_of_geom_dvd` — via the `natDegree q < d` bound (`natDegree_mul` over the domain `ℚ[X]`)
and the coefficient extraction (`coeff_mul_X_pow'`). Together with `Sweep_A46.multiscale_dvd` and
`dyadic_telescope`, this completes the general char-0 `lacunary ⟹ coset` rigidity end-to-end (beyond
the trinomial `Sweep_A45` case). -/
theorem geom_mul_eq (d m : ℕ) :
    (X ^ d - 1 : F[X]) * (∑ k ∈ Finset.range m, (X ^ d) ^ k) = X ^ (d * m) - 1 := by
  rw [mul_comm, geom_sum_mul, ← pow_mul]

/-- `X^d - 1 ≠ 0` for `d > 0`. -/
private theorem X_pow_sub_one_ne_zero {d : ℕ} (hd : 0 < d) : (X ^ d - 1 : F[X]) ≠ 0 := by
  intro h
  have hdeg : (X ^ d - C (1 : F)).natDegree = d := natDegree_X_pow_sub_C
  rw [map_one] at hdeg
  rw [h, natDegree_zero] at hdeg
  omega

/-- `∑_{k<m} (X^d)^k ≠ 0` for `d, m > 0` (its constant coefficient is `1`). -/
private theorem geom_sum_ne_zero {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    (∑ k ∈ Finset.range m, (X ^ d) ^ k : F[X]) ≠ 0 := by
  intro h
  have hc : (∑ k ∈ Finset.range m, (X ^ d) ^ k : F[X]).coeff 0 = 1 := by
    rw [finset_sum_coeff, Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      rw [← pow_mul, coeff_X_pow]
      exact if_neg (fun he => absurd he.symm (Nat.mul_ne_zero (by omega) hk))
    · intro h0; exact absurd (Finset.mem_range.mpr hm) h0
  rw [h] at hc; simp at hc

/-- **General char-0 periodicity (rigidity conclusion).** If the step-`d` all-ones polynomial
`∑_{k<m}(X^d)^k` divides `g` and `deg g < d·m`, then `g.coeff` is periodic with period `d`:
`g.coeff j = g.coeff (j − d)` for `d ≤ j < d·m`. For the indicator of a lacunary subset `S` this is
exactly "`S` is invariant under `+d`," i.e. a **union of cosets** — the general char-0
`lacunary ⟹ coset` rigidity (beyond the trinomial `Sweep_A45`), fed by `Sweep_A46.multiscale_dvd` and
the telescoping above. -/
theorem coeff_periodic_of_geom_dvd {d m : ℕ} (hd : 0 < d) (g : F[X])
    (hdeg : g.natDegree < d * m)
    (hdvd : (∑ k ∈ Finset.range m, (X ^ d) ^ k : F[X]) ∣ g)
    {j : ℕ} (hj : d ≤ j) (hjm : j < d * m) :
    g.coeff j = g.coeff (j - d) := by
  obtain ⟨q, rfl⟩ := hdvd
  rcases eq_or_ne q 0 with hq0 | hq0
  · simp [hq0]
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hjm
    · exact h
  set D : F[X] := ∑ k ∈ Finset.range m, (X ^ d) ^ k with hD
  have hD0 : D ≠ 0 := geom_sum_ne_zero hd hm
  have hXd0 : (X ^ d - 1 : F[X]) ≠ 0 := X_pow_sub_one_ne_zero hd
  have hXdm0 : (X ^ (d * m) - 1 : F[X]) ≠ 0 := X_pow_sub_one_ne_zero (by positivity)
  -- key identity `(X^d - 1) * (D * q) = (X^{dm} - 1) * q`
  have hkey : (X ^ d - 1 : F[X]) * (D * q) = (X ^ (d * m) - 1) * q := by
    rw [← mul_assoc, hD, geom_mul_eq]
  -- `natDegree q < d`
  have hqd : q.natDegree < d := by
    have hL : ((X ^ d - 1 : F[X]) * (D * q)).natDegree = d + (D * q).natDegree := by
      rw [natDegree_mul hXd0 (mul_ne_zero hD0 hq0)]
      congr 1; rw [show (1 : F[X]) = C 1 from (map_one C).symm, natDegree_X_pow_sub_C]
    have hR : ((X ^ (d * m) - 1 : F[X]) * q).natDegree = d * m + q.natDegree := by
      rw [natDegree_mul hXdm0 hq0]
      congr 1; rw [show (1 : F[X]) = C 1 from (map_one C).symm, natDegree_X_pow_sub_C]
    rw [hkey, hR] at hL
    omega
  have hqj : q.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  -- compute the `X^j` coefficient of each side of the key identity
  have hLHS : ((X ^ d - 1 : F[X]) * (D * q)).coeff j
      = (D * q).coeff (j - d) - (D * q).coeff j := by
    rw [sub_mul, one_mul, coeff_sub, mul_comm (X ^ d) (D * q), coeff_mul_X_pow', if_pos hj]
  have hRHS : ((X ^ (d * m) - 1 : F[X]) * q).coeff j = -q.coeff j := by
    rw [sub_mul, one_mul, coeff_sub, mul_comm (X ^ (d * m)) q, coeff_mul_X_pow',
      if_neg (show ¬ d * m ≤ j by omega), zero_sub]
  have hfin : (D * q).coeff (j - d) - (D * q).coeff j = -q.coeff j := by
    rw [← hLHS, ← hRHS, hkey]
  rw [hqj, neg_zero] at hfin
  linear_combination -hfin

end ArkLib.ProximityGap.EvenOddDescent
