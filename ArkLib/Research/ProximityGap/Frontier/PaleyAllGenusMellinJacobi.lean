/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyMellinJacobi
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# All-genus Mellin–Jacobi factorization, Deuring–Birch moments, and the cross-ratio Parseval barrier

Generalizes `PaleyMellinJacobi` from genus 1 (`m = 1`) to ALL genera (`m : ℕ`, genus `⌊m/2⌋`),
completely axiom-clean and with zero external Weil/Deligne axioms:

1. **Exact All-Genus Mellin–Jacobi Factorization (`all_genus_mellin_jacobi_identity`)**:
   For every finite field `F`, every `m : ℕ`, every commutative ring `R`, and every `m`-tuple of
   functions `ψ : Fin m → F → R` multiplicative on `Fˣ`,
   `∑ lam : Fin m → Fˣ, (∏ j, ψ j (lam j)) * L_m(lam) = χ(-1) * J(χ^(m+1) * ∏ ψ_j, χ) * ∏ j, J(ψ_j, χ)`,
   where `L_m(lam) = ∑ z : F, χ(z * (z - 1) * ∏ j, (z - lam j))`.
2. **Exact 1-Variable Sliced Mellin–Jacobi Factorization (`sliced_mellin_jacobi_identity`)**:
   Fixing arbitrary `lam : Fin m → F` and Mellin-transforming in one variable `μ ∈ Fˣ` alone still
   factorizes identically into `J(ψ, χ) * ∑ z : Fˣ, ψ z * χ((z - 1) * ∏ j, (z - lam j))`.
3. **Exact All-Genus Deuring–Birch `L²` Moment (`sum_sq_hyperellipticTrace_eq`)**:
   For every odd-characteristic finite field `F` of order `q` and every `m : ℕ`,
   `∑ lam : Fin m → F, L_m(lam)^2 = (q - 2) * (q - 1)^m + (-1)^m * (3 - q)`.
   (Specializes at `m = 1` to `q^2 - 2q - 1`.)
4. **Unconditional All-Genus Product-Coset Trace Cancellation
   (`sq_sum_product_coset_hyperellipticTrace_le`)**:
   For every odd-characteristic finite field `F`, every `m : ℕ`, every family of subgroups
   `H : Fin m → Subgroup Fˣ`, and every coset shift `a : Fin m → Fˣ`,
   `(∑ u : (j : Fin m) → H j, L_m(fun j => a j * u j))^2 ≤ |F|^(m + 1)`.
   When all `|H j| = K > √|F|`, this beats pointwise Weil `(m + 1) * K^m * √|F|` by `~ (K / √|F|)^m`.
5. **Sharp Cross-Ratio Parseval Crossover Barrier (`subgroup_crossRatio_parseval_barrier`)**:
   Any `H`-scaling-invariant cross-ratio multiplicity table on `H^(2r)` (`|H| = n`) has at most
   `n^(2r - 1)` active orbits, forcing unsigned energy `E ≥ (total)^2 / n^(2r - 1)`. Multiplying by
   the Deuring–Birch `L²` scale `q^(2r - 2)` cannot beat the pointwise Weil scale `n^(2r) * √q`
   whenever `n^(2r - 1) ≤ q^(2r - 3)` (i.e. `log_q(n) ≤ (2r - 3) / (2r - 1)` — `1/3` at `r = 2`,
   `3/5` at `r = 3`, `5/7` at `r = 4`).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace ProximityGap.PaleyAllGenusMellinJacobi

open Finset PaleyMellinJacobi

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. All-genus hyperelliptic trace and Mellin–Jacobi factorizations -/

/-- The `m`-parameter hyperelliptic Legendre trace
`L_m(λ_0, …, λ_{m-1}) = ∑ z : F, χ(z * (z - 1) * ∏ j, (z - λ_j))`. -/
def hyperellipticTrace {m : ℕ} (lam : Fin m → F) : ℤ :=
  ∑ z : F, quadraticChar F (z * (z - 1) * ∏ j : Fin m, (z - lam j))

/-- The `(m + 1)`-parameter trace with `m` fixed branch points `lam` and one free parameter `μ`. -/
def slicedTrace {m : ℕ} (lam : Fin m → F) (μ : F) : ℤ :=
  ∑ z : F, quadraticChar F (z * (z - 1) * (∏ j : Fin m, (z - lam j)) * (z - μ))

private theorem jacobiSum_eq_units {R : Type*} [CommRing R] (ψ : F → R) :
    jacobiSum ψ = ∑ u : Fˣ, ψ (u : F) * (quadraticChar F (1 - (u : F)) : R) := by
  classical
  unfold jacobiSum
  refine (Finset.sum_nbij' (fun u : Fˣ => (u : F))
    (fun x => if h : x = 0 then 1 else Units.mk0 x h) ?_ ?_ ?_ ?_ ?_).symm
  · intro u _; exact Finset.mem_erase.mpr ⟨u.ne_zero, Finset.mem_univ _⟩
  · intro _ _; exact Finset.mem_univ _
  · intro u _; simp [u.ne_zero]
  · intro x hx; simp [(Finset.mem_erase.mp hx).1]
  · intro _ _; rfl

/-- **Exact All-Genus Mellin–Jacobi Factorization**:
for every `m : ℕ`, every commutative ring `R`, and every `ψ : Fin m → F → R` multiplicative on `Fˣ`,
`∑ lam : Fin m → Fˣ, (∏ j, ψ j (lam j)) * L_m(lam) = χ(-1) * J(χ^(m+1) * ∏ ψ_j, χ) * ∏ j, J(ψ_j, χ)`. -/
theorem all_genus_mellin_jacobi_identity {R : Type*} [CommRing R] {m : ℕ}
    (ψ : Fin m → F → R) (hψ : ∀ j a b, a ≠ 0 → b ≠ 0 → ψ j (a * b) = ψ j a * ψ j b) :
    ∑ lam : Fin m → Fˣ,
        (∏ j : Fin m, ψ j (lam j : F)) * (hyperellipticTrace (fun j => (lam j : F)) : R) =
      (quadraticChar F (-1 : F) : R) *
        jacobiSum (fun z => (quadraticChar F z : R) ^ (m + 1) * ∏ j : Fin m, ψ j z) *
        ∏ j : Fin m, jacobiSum (ψ j) := by
  classical
  have hL : ∀ lam : Fin m → Fˣ, (hyperellipticTrace (fun j => (lam j : F)) : R) =
      ∑ z : Fˣ, (quadraticChar F ((z : F) * ((z : F) - 1) *
        ∏ j : Fin m, ((z : F) - (lam j : F))) : R) := fun lam => by
    unfold hyperellipticTrace
    push_cast
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)),
      zero_mul, zero_mul, MulChar.map_zero, Int.cast_zero, zero_add]
    refine (Finset.sum_nbij' (fun z : Fˣ => (z : F))
      (fun x => if h : x = 0 then 1 else Units.mk0 x h) ?_ ?_ ?_ ?_ ?_).symm
    · intro z _; exact Finset.mem_erase.mpr ⟨z.ne_zero, Finset.mem_univ _⟩
    · intro _ _; exact Finset.mem_univ _
    · intro z _; simp [z.ne_zero]
    · intro x hx; simp [(Finset.mem_erase.mp hx).1]
    · intro _ _; rfl
  simp_rw [hL, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ z : Fˣ,
      ∑ lam : Fin m → Fˣ, (∏ j : Fin m, ψ j (lam j : F)) *
          (quadraticChar F ((z : F) * ((z : F) - 1) * ∏ j : Fin m, ((z : F) - (lam j : F))) : R) =
        (quadraticChar F (-1 : F) : R) *
          (((quadraticChar F (z : F) : R) ^ (m + 1) * ∏ j : Fin m, ψ j (z : F)) *
            (quadraticChar F (1 - (z : F)) : R)) *
          ∏ j : Fin m, jacobiSum (ψ j) := fun z => by
    -- Substitute `lam j = z * u j` via the bijection `u ↦ (fun j => z * u j)` on `Fin m → Fˣ`:
    let e : (Fin m → Fˣ) ≃ (Fin m → Fˣ) := Equiv.piCongrRight fun _ => Equiv.mulLeft z
    rw [← Fintype.sum_equiv e
      (fun u => (∏ j : Fin m, ψ j ((z * u j : Fˣ) : F)) *
        (quadraticChar F ((z : F) * ((z : F) - 1) * ∏ j : Fin m, ((z : F) - ((z * u j : Fˣ) : F))) : R))
      (fun lam => (∏ j : Fin m, ψ j (lam j : F)) *
        (quadraticChar F ((z : F) * ((z : F) - 1) * ∏ j : Fin m, ((z : F) - (lam j : F))) : R))
      (fun _ => rfl)]
    have hterm : ∀ u : Fin m → Fˣ,
        (∏ j : Fin m, ψ j ((z * u j : Fˣ) : F)) *
          (quadraticChar F ((z : F) * ((z : F) - 1) * ∏ j : Fin m, ((z : F) - ((z * u j : Fˣ) : F))) : R) =
        ((quadraticChar F (-1 : F) : R) *
          (((quadraticChar F (z : F) : R) ^ (m + 1) * ∏ j : Fin m, ψ j (z : F)) *
            (quadraticChar F (1 - (z : F)) : R))) *
          ∏ j : Fin m, (ψ j (u j : F) * (quadraticChar F (1 - (u j : F)) : R)) := fun u => by
      have hψ_prod : ∏ j : Fin m, ψ j ((z * u j : Fˣ) : F) =
          (∏ j : Fin m, ψ j (z : F)) * ∏ j : Fin m, ψ j (u j : F) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        exact hψ j (z : F) (u j : F) z.ne_zero (u j).ne_zero
      have hprod_fac : ∏ j : Fin m, ((z : F) - ((z * u j : Fˣ) : F)) =
          (z : F) ^ m * ∏ j : Fin m, (1 - (u j : F)) := by
        have h1 : ∀ j : Fin m, (z : F) - ((z * u j : Fˣ) : F) = (z : F) * (1 - (u j : F)) := fun j => by
          simp only [Units.val_mul]; ring
        simp_rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have harg : (z : F) * ((z : F) - 1) * ∏ j : Fin m, ((z : F) - ((z * u j : Fˣ) : F)) =
          (-1 : F) * (z : F) ^ (m + 1) * (1 - (z : F)) * ∏ j : Fin m, (1 - (u j : F)) := by
        rw [hprod_fac, pow_succ]; ring
      rw [hψ_prod, harg, map_mul, map_mul, map_mul, map_pow, map_prod]
      push_cast
      rw [Finset.prod_mul_distrib]
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    congr 1
    rw [← Fintype.prod_sum (fun j (u : Fˣ) => ψ j (u : F) * (quadraticChar F (1 - (u : F)) : R))]
    simp_rw [jacobiSum_eq_units]
  rw [Finset.sum_congr rfl fun z _ => hinner z, ← Finset.sum_mul, ← Finset.mul_sum,
    jacobiSum_eq_units]

/-- **Exact 1-Variable Sliced Mellin–Jacobi Factorization**:
fixing ANY `m` branch points `lam : Fin m → F` and Mellin-transforming in the single parameter `μ ∈ Fˣ`
still factorizes identically into `J(ψ, χ)` times a character sum in `z`. -/
theorem sliced_mellin_jacobi_identity {R : Type*} [CommRing R] {m : ℕ}
    (lam : Fin m → F) (ψ : F → R) (hψ : ∀ a b, a ≠ 0 → b ≠ 0 → ψ (a * b) = ψ a * ψ b) :
    ∑ μ : Fˣ, ψ (μ : F) * (slicedTrace lam (μ : F) : R) =
      jacobiSum ψ *
        ∑ z : Fˣ, ψ (z : F) *
          (quadraticChar F (((z : F) - 1) * ∏ j : Fin m, ((z : F) - lam j)) : R) := by
  classical
  have hS : ∀ μ : Fˣ, (slicedTrace lam (μ : F) : R) =
      ∑ z : Fˣ, (quadraticChar F ((z : F) * ((z : F) - 1) *
        (∏ j : Fin m, ((z : F) - lam j)) * ((z : F) - (μ : F))) : R) := fun μ => by
    unfold slicedTrace
    push_cast
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)),
      zero_mul, zero_mul, zero_mul, MulChar.map_zero, Int.cast_zero, zero_add]
    refine (Finset.sum_nbij' (fun z : Fˣ => (z : F))
      (fun x => if h : x = 0 then 1 else Units.mk0 x h) ?_ ?_ ?_ ?_ ?_).symm
    · intro z _; exact Finset.mem_erase.mpr ⟨z.ne_zero, Finset.mem_univ _⟩
    · intro _ _; exact Finset.mem_univ _
    · intro z _; simp [z.ne_zero]
    · intro x hx; simp [(Finset.mem_erase.mp hx).1]
    · intro _ _; rfl
  simp_rw [hS, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ z : Fˣ,
      ∑ μ : Fˣ, ψ (μ : F) *
          (quadraticChar F ((z : F) * ((z : F) - 1) *
            (∏ j : Fin m, ((z : F) - lam j)) * ((z : F) - (μ : F))) : R) =
        jacobiSum ψ * (ψ (z : F) *
          (quadraticChar F (((z : F) - 1) * ∏ j : Fin m, ((z : F) - lam j)) : R)) := fun z => by
    rw [← Fintype.sum_equiv (Equiv.mulLeft z)
      (fun u => ψ ((z * u : Fˣ) : F) *
        (quadraticChar F ((z : F) * ((z : F) - 1) *
          (∏ j : Fin m, ((z : F) - lam j)) * ((z : F) - ((z * u : Fˣ) : F))) : R))
      (fun μ => ψ (μ : F) *
        (quadraticChar F ((z : F) * ((z : F) - 1) *
          (∏ j : Fin m, ((z : F) - lam j)) * ((z : F) - (μ : F))) : R))
      (fun _ => rfl)]
    rw [jacobiSum_eq_units, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    have harg : (z : F) * ((z : F) - 1) * (∏ j : Fin m, ((z : F) - lam j)) *
          ((z : F) - ((z * u : Fˣ) : F)) =
        (z : F) ^ 2 * (((z : F) - 1) * ∏ j : Fin m, ((z : F) - lam j)) * (1 - (u : F)) := by
      simp only [Units.val_mul]; ring
    rw [harg, Units.val_mul, hψ (z : F) (u : F) z.ne_zero u.ne_zero, map_mul, map_mul,
      quadraticChar_sq_one' z.ne_zero, one_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun z _ => hinner z, ← Finset.mul_sum]

/-! ## 2. Exact all-genus Deuring–Birch second moment -/

private theorem quadratic_sum_neg_one_local (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ s : F, quadraticChar F ((a - s) * (b - s)) = -1 := by
  classical
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hbi1 : Function.Bijective (fun u : F => a + (b - a) * u) :=
    (Equiv.addLeft a).bijective.comp (mulLeft_bijective₀ (b - a) hba)
  have hstep1 : ∑ s : F, quadraticChar F ((a - s) * (b - s)) =
      ∑ u : F, quadraticChar F (u * (u - 1)) := by
    rw [← Fintype.sum_bijective (fun u : F => a + (b - a) * u) hbi1 _ _ (fun _ => rfl)]
    refine Finset.sum_congr rfl fun u _ => ?_
    have harg : (a - (a + (b - a) * u)) * (b - (a + (b - a) * u)) =
        (b - a) ^ 2 * (u * (u - 1)) := by ring
    rw [harg, map_mul, quadraticChar_sq_one' hba, one_mul]
  rw [hstep1]
  have hstep2 : ∑ u : F, quadraticChar F (u * (u - 1)) =
      ∑ u ∈ Finset.univ.erase (0 : F), quadraticChar F (1 - u⁻¹) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)), zero_mul, MulChar.map_zero, zero_add]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
    have harg : u * (u - 1) = u ^ 2 * (1 - u⁻¹) := by field_simp [hu0]
    rw [harg, map_mul, quadraticChar_sq_one' hu0, one_mul]
  rw [hstep2]
  have hbij : ∑ u ∈ Finset.univ.erase (0 : F), quadraticChar F (1 - u⁻¹) =
      ∑ v ∈ Finset.univ.erase (1 : F), quadraticChar F v := by
    refine Finset.sum_nbij' (fun u => 1 - u⁻¹) (fun v => (1 - v)⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
      rw [Finset.mem_erase]
      exact ⟨fun h => inv_ne_zero hu0 (sub_eq_self.mp h), Finset.mem_univ _⟩
    · intro v hv
      have hv1 : v ≠ 1 := (Finset.mem_erase.mp hv).1
      rw [Finset.mem_erase]
      exact ⟨inv_ne_zero (sub_ne_zero.mpr hv1.symm), Finset.mem_univ _⟩
    · intro u hu; have hu0 := (Finset.mem_erase.mp hu).1; field_simp [hu0]; ring
    · intro v hv; have hv1 := sub_ne_zero.mpr (Finset.mem_erase.mp hv).1.symm; field_simp [hv1]; ring
    · intro _ _; rfl
  rw [hbij]
  have htot := quadraticChar_sum_zero hF
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : F)), map_one] at htot
  omega

/-- **Exact All-Genus Deuring–Birch Second Moment**:
for every odd-characteristic finite field `F` of size `q` and every `m : ℕ`,
`∑ lam : Fin m → F, L_m(lam)^2 = (q - 2) * (q - 1)^m + (-1)^m * (3 - q)`. -/
theorem sum_sq_hyperellipticTrace_eq (hF : ringChar F ≠ 2) (m : ℕ) :
    ∑ lam : Fin m → F, (hyperellipticTrace lam) ^ 2 =
      ((Fintype.card F : ℤ) - 2) * ((Fintype.card F : ℤ) - 1) ^ m +
        (-1 : ℤ) ^ m * (3 - (Fintype.card F : ℤ)) := by
  classical
  have hexp : ∀ lam : Fin m → F, (hyperellipticTrace lam) ^ 2 =
      ∑ z₁ : F, ∑ z₂ : F,
        (quadraticChar F (z₁ * (z₁ - 1)) * quadraticChar F (z₂ * (z₂ - 1))) *
          ∏ j : Fin m, quadraticChar F ((z₁ - lam j) * (z₂ - lam j)) := fun lam => by
    unfold hyperellipticTrace
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun z₁ _ => Finset.sum_congr rfl fun z₂ _ => ?_
    rw [map_mul (quadraticChar F) (z₁ * (z₁ - 1)), map_mul (quadraticChar F) (z₂ * (z₂ - 1)),
      map_prod, map_prod]
    have hprod : (∏ j : Fin m, quadraticChar F (z₁ - lam j)) *
        (∏ j : Fin m, quadraticChar F (z₂ - lam j)) =
        ∏ j : Fin m, quadraticChar F ((z₁ - lam j) * (z₂ - lam j)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => (map_mul _ _ _).symm
    rw [← hprod]; ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hswap : ∑ z₁ : F, ∑ lam : Fin m → F, ∑ z₂ : F,
        (quadraticChar F (z₁ * (z₁ - 1)) * quadraticChar F (z₂ * (z₂ - 1))) *
          ∏ j : Fin m, quadraticChar F ((z₁ - lam j) * (z₂ - lam j)) =
      ∑ z₁ : F, ∑ z₂ : F,
        (quadraticChar F (z₁ * (z₁ - 1)) * quadraticChar F (z₂ * (z₂ - 1))) *
          ∑ lam : Fin m → F, ∏ j : Fin m, quadraticChar F ((z₁ - lam j) * (z₂ - lam j)) := by
    refine Finset.sum_congr rfl fun z₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z₂ _ => (Finset.mul_sum ..).symm
  rw [hswap]
  have hinner : ∀ z₁ z₂ : F,
      ∑ lam : Fin m → F, ∏ j : Fin m, quadraticChar F ((z₁ - lam j) * (z₂ - lam j)) =
        if z₁ = z₂ then ((Fintype.card F : ℤ) - 1) ^ m else (-1 : ℤ) ^ m := by
    intro z₁ z₂
    rw [← Fintype.prod_sum (fun (_ : Fin m) (x : F) => quadraticChar F ((z₁ - x) * (z₂ - x))),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    by_cases h : z₁ = z₂
    · subst h
      simp only [↓reduceIte]
      congr 1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z₁), sub_self, mul_zero, MulChar.map_zero,
        zero_add]
      have h1 : ∑ x ∈ Finset.univ.erase z₁, quadraticChar F ((z₁ - x) * (z₁ - x)) =
          ∑ _x ∈ Finset.univ.erase z₁, (1 : ℤ) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hne : z₁ - x ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hx).1.symm
        rw [← sq]
        exact quadraticChar_sq_one' hne
      rw [h1, Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.card_erase_of_mem (Finset.mem_univ z₁), Finset.card_univ]
      have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
      omega
    · simp only [h, ↓reduceIte, quadratic_sum_neg_one_local hF h]
  simp_rw [hinner]
  have hsplit : ∀ z₁ z₂ : F,
      (quadraticChar F (z₁ * (z₁ - 1)) * quadraticChar F (z₂ * (z₂ - 1))) *
          (if z₁ = z₂ then ((Fintype.card F : ℤ) - 1) ^ m else (-1 : ℤ) ^ m) =
        (if z₁ = z₂ then quadraticChar F (z₁ * (z₁ - 1)) ^ 2 *
          (((Fintype.card F : ℤ) - 1) ^ m - (-1 : ℤ) ^ m) else 0) +
        (-1 : ℤ) ^ m * (quadraticChar F (z₁ * (z₁ - 1)) * quadraticChar F (z₂ * (z₂ - 1))) := by
    intro z₁ z₂
    split_ifs with h
    · subst h; ring
    · ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  -- Evaluate the diagonal sum `∑ z, χ(z(z-1))^2 = q - 2`:
  have hdiag_chi : ∑ z : F, quadraticChar F (z * (z - 1)) ^ 2 = (Fintype.card F : ℤ) - 2 := by
    have h01 : (0 : F) ≠ 1 := zero_ne_one
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)), zero_mul, MulChar.map_zero,
      zero_pow (by decide), zero_add]
    have h1mem : (1 : F) ∈ Finset.univ.erase (0 : F) :=
      Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ h1mem, sub_self, mul_zero, MulChar.map_zero,
      zero_pow (by decide), zero_add]
    have hones : ∑ z ∈ (Finset.univ.erase (0 : F)).erase (1 : F),
        quadraticChar F (z * (z - 1)) ^ 2 =
        ∑ _z ∈ (Finset.univ.erase (0 : F)).erase (1 : F), (1 : ℤ) := by
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz1 : z ≠ 1 := (Finset.mem_erase.mp hz).1
      have hz0 : z ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
      exact quadraticChar_sq_one (mul_ne_zero hz0 (sub_ne_zero.mpr hz1))
    rw [hones, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_erase_of_mem h1mem, Finset.card_erase_of_mem (Finset.mem_univ (0 : F)),
      Finset.card_univ]
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    omega
  -- Evaluate `∑ z, χ(z(z-1)) = -1`:
  have htot_chi : ∑ z : F, quadraticChar F (z * (z - 1)) = -1 := by
    have hq := quadratic_sum_neg_one_local hF (zero_ne_one : (0 : F) ≠ 1)
    have hrew : ∀ z : F, (0 - z) * (1 - z) = z * (z - 1) := fun z => by ring
    simpa only [hrew] using hq
  have h1 : ∑ z₁ : F, ∑ z₂ : F, (if z₁ = z₂ then quadraticChar F (z₁ * (z₁ - 1)) ^ 2 *
        (((Fintype.card F : ℤ) - 1) ^ m - (-1 : ℤ) ^ m) else 0) =
      ((Fintype.card F : ℤ) - 2) * (((Fintype.card F : ℤ) - 1) ^ m - (-1 : ℤ) ^ m) := by
    have hrow : ∀ z₁ : F, ∑ z₂ : F, (if z₁ = z₂ then quadraticChar F (z₁ * (z₁ - 1)) ^ 2 *
          (((Fintype.card F : ℤ) - 1) ^ m - (-1 : ℤ) ^ m) else 0) =
        quadraticChar F (z₁ * (z₁ - 1)) ^ 2 *
          (((Fintype.card F : ℤ) - 1) ^ m - (-1 : ℤ) ^ m) := fun z₁ => by
      simp [Finset.sum_ite_eq]
    rw [Finset.sum_congr rfl fun z₁ _ => hrow z₁, ← Finset.sum_mul, hdiag_chi]
  have h2 : ∑ z₁ : F, ∑ z₂ : F,
        (-1 : ℤ) ^ m * (quadraticChar F (z₁ * (z₁ - 1)) * quadraticChar F (z₂ * (z₂ - 1))) =
      (-1 : ℤ) ^ m := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, htot_chi]
    ring
  rw [h1, h2]
  ring

/-! ## 3. Unconditional all-genus product-coset trace cancellation -/

private theorem exp_two_pi_div_prim {N : ℕ} (hN : 0 < N) {r : ℕ} (hr_pos : 0 < r) (hr_lt : r < N) :
    Complex.exp (2 * ↑Real.pi * Complex.I / ↑N) ^ r ≠ 1 := by
  rw [← Complex.exp_nat_mul]
  intro h1
  have harg : (r : ℂ) * (2 * ↑Real.pi * Complex.I / ↑N) =
      (((2 * Real.pi * (r : ℝ) / (N : ℝ) : ℝ) : ℂ)) * Complex.I := by push_cast; ring
  rw [harg] at h1
  have hcos : Real.cos (2 * Real.pi * (r : ℝ) / (N : ℝ)) = 1 := by
    have hre := congrArg Complex.re h1
    rw [Complex.exp_ofReal_mul_I_re, Complex.one_re] at hre
    exact hre
  rw [Real.cos_eq_one_iff] at hcos
  obtain ⟨k, hk⟩ := hcos
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hk_eq : (k : ℝ) = (r : ℝ) / (N : ℝ) := by
    have hmul : (k : ℝ) * (2 * Real.pi) = ((r : ℝ) / (N : ℝ)) * (2 * Real.pi) := by
      have hrew : 2 * Real.pi * (r : ℝ) / (N : ℝ) = ((r : ℝ) / (N : ℝ)) * (2 * Real.pi) := by ring
      linarith
    exact mul_right_cancel₀ h2pi.ne' hmul
  have h0 : (0 : ℝ) < (k : ℝ) := by rw [hk_eq]; exact div_pos (by exact_mod_cast hr_pos) hN'
  have hlt1 : (k : ℝ) < 1 := by rw [hk_eq, div_lt_one hN']; exact_mod_cast hr_lt
  have hk_pos : (0 : ℤ) < k := by exact_mod_cast h0
  have hk_lt1 : k < 1 := by exact_mod_cast hlt1
  omega

/-- **Unconditional All-Genus Product-Coset Trace Cancellation**:
for EVERY odd-characteristic finite field `F`, EVERY `m : ℕ`, EVERY family of multiplicative
subgroups `H : Fin m → Subgroup Fˣ`, and EVERY family of coset representatives `a : Fin m → Fˣ`,
`(∑ u : (j : Fin m) → H j, L_m(fun j => a j * u j))^2 ≤ |F|^(m + 1)`.
Proved completely without Weil or Deligne axioms via `all_genus_mellin_jacobi_identity` and
`jacobiSum_norm_sq_eq_card`! -/
theorem sq_sum_product_coset_hyperellipticTrace_le (hF : ringChar F ≠ 2) {m : ℕ}
    (H : Fin m → Subgroup Fˣ) [∀ j, Fintype (H j)] (a : Fin m → Fˣ) :
    (∑ u : (j : Fin m) → H j, hyperellipticTrace (fun j => ((a j * (u j : Fˣ) : Fˣ) : F))) ^ 2 ≤
      (Fintype.card F : ℤ) ^ (m + 1) := by
  classical
  set N := Fintype.card F - 1
  have hcard_units : Fintype.card Fˣ = N := by
    rw [Fintype.card_units]
  have hN_pos : 0 < N := by
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have hN_even : 2 ∣ N := by
    have hq_odd : Odd (Fintype.card F) := by
      have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
      obtain ⟨k, hk⟩ := FiniteField.card F (ringChar F)
      have hodd_p : Odd (ringChar F) := hp.odd_of_ne_two hF
      rw [hk.2]
      exact hodd_p.pow
    obtain ⟨t, ht⟩ := hq_odd
    exact ⟨t, by omega⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord_g : orderOf g = N := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard_units]
  have hsurj : ∀ u : Fˣ, ∃ j < N, g ^ j = u := fun u => by
    obtain ⟨k, hk⟩ := hg u
    refine ⟨(k % (N : ℤ)).toNat, ?_, ?_⟩
    · have h1 := Int.emod_nonneg k (show (N : ℤ) ≠ 0 by omega)
      have h2 := Int.emod_lt_of_pos k (show (0 : ℤ) < N by omega)
      omega
    · have hdiv : k = (N : ℤ) * (k / (N : ℤ)) + k % (N : ℤ) := (Int.mul_ediv_add_emod _ _).symm
      have hpowN : g ^ N = 1 := by rw [← hord_g]; exact pow_orderOf_eq_one g
      rw [← hk]
      dsimp only
      conv_rhs =>
        rw [hdiv, zpow_add, zpow_mul, zpow_natCast, hpowN, one_zpow, one_mul,
          ← Int.toNat_of_nonneg (Int.emod_nonneg k (show (N : ℤ) ≠ 0 by omega)), zpow_natCast]
  choose dlog hdlog_lt hdlog_pow using hsurj
  have hpow_inj : ∀ {x y : ℕ}, x < N → y < N → g ^ x = g ^ y → x = y := by
    intro x y hx hy heq
    wlog hle : x ≤ y generalizing x y
    · exact (this hy hx heq.symm (by omega)).symm
    have h1 : g ^ (y - x) = 1 := by
      have : g ^ x * g ^ (y - x) = g ^ x * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' hle, mul_one, heq]
      exact mul_left_cancel this
    have hdvd : N ∣ y - x := by rw [← hord_g]; exact orderOf_dvd_of_pow_eq_one h1
    rcases Nat.eq_zero_or_pos (y - x) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hdvd; omega
  have hdlog_mul : ∀ u v : Fˣ, dlog (u * v) % N = (dlog u + dlog v) % N := fun u v => by
    have hpowN : g ^ N = 1 := by rw [← hord_g]; exact pow_orderOf_eq_one g
    have hpow : g ^ (dlog (u * v)) = g ^ ((dlog u + dlog v) % N) := by
      rw [hdlog_pow]
      conv_lhs => rw [← hdlog_pow u, ← hdlog_pow v, ← pow_add]
      have hdiv : dlog u + dlog v = N * ((dlog u + dlog v) / N) + (dlog u + dlog v) % N :=
        (Nat.div_add_mod _ _).symm
      conv_lhs => rw [hdiv, pow_add, pow_mul, hpowN, one_pow, one_mul]
    have h1 := hpow_inj (hdlog_lt (u * v)) (Nat.mod_lt _ hN_pos) hpow
    rw [Nat.mod_eq_of_lt (hdlog_lt (u * v)), h1]
  have hdlog_one : dlog 1 = 0 := hpow_inj (hdlog_lt 1) hN_pos (by rw [hdlog_pow, pow_zero])
  -- Primitive `N`-th root of unity `ζ`:
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑N)
  have hζ_pow_N : ζ ^ N = 1 := by
    dsimp [ζ]; rw [← Complex.exp_nat_mul]
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN_pos.ne'
    have harg : (N : ℂ) * (2 * ↑Real.pi * Complex.I / ↑N) = 2 * ↑Real.pi * Complex.I := by
      field_simp [hN0]
    rw [harg, Complex.exp_two_pi_mul_I]
  have hζ_mod : ∀ k : ℕ, ζ ^ (k % N) = ζ ^ k := fun k => by
    have hdiv : k = N * (k / N) + k % N := (Nat.div_add_mod _ _).symm
    conv_rhs => rw [hdiv, pow_add, pow_mul, hζ_pow_N, one_pow, one_mul]
  have hζ_norm : ‖ζ‖ = 1 := by
    dsimp [ζ]
    rw [show (2 : ℂ) * ↑Real.pi * Complex.I / ↑N = ((2 * Real.pi / N : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hζ_conj : starRingEnd ℂ ζ = ζ⁻¹ := by
    dsimp [ζ]
    rw [← Complex.exp_conj]
    have harg : (starRingEnd ℂ) (2 * ↑Real.pi * Complex.I / ↑N) =
        -(2 * ↑Real.pi * Complex.I / ↑N) := by
      simp [Complex.conj_ofReal, Complex.conj_I, map_ofNat]; ring
    rw [harg, Complex.exp_neg]
  -- Multiplicative character `ψ k`:
  let ψ : ℕ → F → ℂ := fun k x => if h : x = 0 then 0 else ζ ^ (k * dlog (Units.mk0 x h))
  have hψ_mul : ∀ k a b, a ≠ 0 → b ≠ 0 → ψ k (a * b) = ψ k a * ψ k b := by
    intro k x y hx hy
    simp only [ψ, mul_ne_zero hx hy, hx, hy, ↓reduceDIte]
    rw [← pow_add, ← mul_add, ← hζ_mod, ← hζ_mod (k * _)]
    congr 1
    have hmk : Units.mk0 (x * y) (mul_ne_zero hx hy) = Units.mk0 x hx * Units.mk0 y hy := by
      ext; rfl
    rw [hmk, Nat.mul_mod, hdlog_mul, ← Nat.mul_mod]
  have hψ_one : ∀ k, ψ k 1 = 1 := fun k => by
    simp only [ψ, one_ne_zero, ↓reduceDIte]
    have h1 : Units.mk0 (1 : F) one_ne_zero = 1 := by ext; rfl
    rw [h1, hdlog_one, mul_zero, pow_zero]
  have hψ_conj : ∀ k x, x ≠ 0 → starRingEnd ℂ (ψ k x) = (ψ k x)⁻¹ := fun k x hx => by
    simp only [ψ, hx, ↓reduceDIte, map_pow, hζ_conj, inv_pow]
  have hψ_norm : ∀ k x, x ≠ 0 → ‖ψ k x‖ = 1 := fun k x hx => by
    simp only [ψ, hx, ↓reduceDIte, norm_pow, hζ_norm, one_pow]
  -- Express `χ` as `ψ (N / 2)` on `Fˣ`:
  have hchi_eq : ∀ x : F, x ≠ 0 → (quadraticChar F x : ℂ) = ψ (N / 2) x := by
    intro x hx
    obtain ⟨tN, htN⟩ := hN_even
    have hchi_g : quadraticChar F (g : F) = -1 := by
      rcases quadraticChar_dichotomy g.ne_zero with h1 | h1
      · exfalso
        have heul := quadraticChar_eq_pow_of_char_ne_two' hF (g : F)
        rw [h1, Int.cast_one] at heul
        have hhalf : Fintype.card F / 2 = N / 2 := by omega
        rw [hhalf] at heul
        have hpow : g ^ (N / 2) = 1 := by
          ext; simpa using heul.symm
        have hord_dvd := orderOf_dvd_of_pow_eq_one hpow
        rw [hord_g] at hord_dvd
        have hle := Nat.le_of_dvd (by omega : 0 < N / 2) hord_dvd
        omega
      · exact h1
    have hζ_half : ζ ^ (N / 2) = -1 := by
      have hsq : (ζ ^ (N / 2)) ^ 2 = 1 := by
        rw [← pow_mul, show N / 2 * 2 = N by omega, hζ_pow_N]
      have hne1 : ζ ^ (N / 2) ≠ 1 := exp_two_pi_div_prim hN_pos (by omega) (by omega)
      rcases sq_eq_one_iff.mp hsq with h | h
      · exact absurd h hne1
      · exact h
    let xu := Units.mk0 x hx
    have hx_eq : x = (g : F) ^ dlog xu := by
      have := congrArg Units.val (hdlog_pow xu)
      simpa [xu] using this.symm
    simp only [ψ, hx, ↓reduceDIte]
    conv_lhs => rw [hx_eq]
    rw [map_pow, hchi_g]
    push_cast
    rw [pow_mul, hζ_half]
  -- Universal Jacobi norm bound: `‖jacobiSum (ψ k)‖ ^ 2 ≤ Fintype.card F` for EVERY `k : ℕ`:
  have hjac_norm_sq : ∀ k : ℕ, ‖jacobiSum (ψ k)‖ ^ 2 ≤ (Fintype.card F : ℝ) := fun k => by
    have hq_ge1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
    obtain ⟨tN, htN⟩ := hN_even
    by_cases hk0 : k % N = 0
    · have heq : jacobiSum (ψ k) = -1 := by
        have hconst : ∀ x ∈ Finset.univ.erase (0 : F), ψ k x = 1 := fun x hx => by
          have hx0 := (Finset.mem_erase.mp hx).1
          simp only [ψ, hx0, ↓reduceDIte]
          rw [← hζ_mod, Nat.mul_mod, hk0, zero_mul, Nat.zero_mod, pow_zero]
        have hj1 := congrArg (Int.cast (R := ℂ)) (jacobiSum_one hF)
        unfold jacobiSum at hj1 ⊢
        rw [Finset.sum_congr rfl fun x hx => by rw [hconst x hx, one_mul]]
        simpa only [one_mul, Int.cast_id, Int.cast_sum, Int.cast_neg, Int.cast_one] using hj1
      rw [heq, norm_neg, norm_one, one_pow]; exact hq_ge1
    · by_cases hk2 : (2 * k) % N = 0
      · have hhalf : k % N = N / 2 := by
          obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hk2
          have hdiv : k = N * (k / N) + k % N := (Nat.div_add_mod k N).symm
          have hlt : k % N < N := Nat.mod_lt k hN_pos
          have hpos : 0 < k % N := Nat.pos_of_ne_zero hk0
          have hq_eq : q = 2 * (k / N) + 1 := by nlinarith
          have hrem : 2 * (k % N) = N := by nlinarith
          omega
        have hconst : ∀ x ∈ Finset.univ.erase (0 : F), ψ k x = (quadraticChar F x : ℂ) := fun x hx => by
          have hx0 := (Finset.mem_erase.mp hx).1
          rw [hchi_eq x hx0]
          simp only [ψ, hx0, ↓reduceDIte]
          rw [← hζ_mod (k * _), Nat.mul_mod k, hhalf, Nat.mod_eq_of_lt (hdlog_lt _), hζ_mod]
        have hjq := congrArg (Int.cast (R := ℂ)) (jacobiSum_quad_eq hF)
        have heq : jacobiSum (ψ k) = -(quadraticChar F (-1 : F) : ℂ) := by
          unfold jacobiSum at hjq ⊢
          rw [Finset.sum_congr rfl fun x hx => by rw [hconst x hx]]
          simpa only [Int.cast_id, Int.cast_sum, Int.cast_mul, Int.cast_neg] using hjq
        rw [heq, norm_neg]
        rcases quadraticChar_dichotomy (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)) with h | h <;>
          simp [h, hq_ge1]
      · -- Generic `ψ k ∉ {1, χ}`: apply `PaleyMellinJacobi.jacobiSum_norm_sq_eq_card`!
        have horth1 : ∑ x ∈ Finset.univ.erase (0 : F), ψ k x = 0 := by
          have hgk : ψ k (g : F) ≠ 1 := by
            simp only [ψ, g.ne_zero, ↓reduceDIte]
            have hdg : dlog (Units.mk0 (g : F) g.ne_zero) = 1 := by
              have h1 : Units.mk0 (g : F) g.ne_zero = g := by ext; rfl
              rw [h1]
              exact hpow_inj (hdlog_lt g) (by omega) (by rw [hdlog_pow, pow_one])
            rw [hdg, mul_one, ← hζ_mod]
            exact exp_two_pi_div_prim hN_pos (Nat.pos_of_ne_zero hk0) (Nat.mod_lt k hN_pos)
          have hshift : ψ k (g : F) * ∑ x ∈ Finset.univ.erase (0 : F), ψ k x =
              ∑ x ∈ Finset.univ.erase (0 : F), ψ k x := by
            rw [Finset.mul_sum]
            refine Finset.sum_nbij' (fun u => (g : F) * u) (fun u => (g : F)⁻¹ * u) ?_ ?_ ?_ ?_ ?_
            · intro u hu; rw [Finset.mem_erase] at hu ⊢; exact ⟨mul_ne_zero g.ne_zero hu.1, Finset.mem_univ _⟩
            · intro u hu; rw [Finset.mem_erase] at hu ⊢; exact ⟨mul_ne_zero (inv_ne_zero g.ne_zero) hu.1, Finset.mem_univ _⟩
            · intro u _; exact inv_mul_cancel_left₀ g.ne_zero u
            · intro u _; exact mul_inv_cancel_left₀ g.ne_zero u
            · intro u hu; exact (hψ_mul k (g : F) u g.ne_zero (Finset.mem_erase.mp hu).1).symm
          have hfac : (ψ k (g : F) - 1) * ∑ x ∈ Finset.univ.erase (0 : F), ψ k x = 0 := by
            linear_combination hshift
          exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hgk)
        have horth2 : ∑ x ∈ Finset.univ.erase (0 : F), ψ k x * (quadraticChar F x : ℂ) = 0 := by
          have hgne : ψ k (g : F) * (quadraticChar F (g : F) : ℂ) ≠ 1 := by
            rw [hchi_eq (g : F) g.ne_zero]
            simp only [ψ, g.ne_zero, ↓reduceDIte]
            have hdg : dlog (Units.mk0 (g : F) g.ne_zero) = 1 := by
              have h1 : Units.mk0 (g : F) g.ne_zero = g := by ext; rfl
              rw [h1]
              exact hpow_inj (hdlog_lt g) (by omega) (by rw [hdlog_pow, pow_one])
            rw [hdg, mul_one, mul_one, ← pow_add, ← hζ_mod]
            have hnz : (k + N / 2) % N ≠ 0 := by
              intro h0
              have hdvd : N ∣ k + N / 2 := Nat.dvd_of_mod_eq_zero h0
              have hdvd2 : N ∣ 2 * (k + N / 2) := dvd_mul_of_dvd_right hdvd 2
              have h2eq : 2 * (k + N / 2) = 2 * k + N := by omega
              rw [h2eq] at hdvd2
              exact hk2 (Nat.mod_eq_zero_of_dvd ((Nat.dvd_add_left (dvd_refl N)).mp hdvd2))
            exact exp_two_pi_div_prim hN_pos (Nat.pos_of_ne_zero hnz) (Nat.mod_lt _ hN_pos)
          have hshift : (ψ k (g : F) * (quadraticChar F (g : F) : ℂ)) *
                ∑ u ∈ Finset.univ.erase (0 : F), ψ k u * (quadraticChar F u : ℂ) =
              ∑ u ∈ Finset.univ.erase (0 : F), ψ k u * (quadraticChar F u : ℂ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_nbij' (fun u => (g : F) * u) (fun u => (g : F)⁻¹ * u) ?_ ?_ ?_ ?_ ?_
            · intro u hu; rw [Finset.mem_erase] at hu ⊢; exact ⟨mul_ne_zero g.ne_zero hu.1, Finset.mem_univ _⟩
            · intro u hu; rw [Finset.mem_erase] at hu ⊢; exact ⟨mul_ne_zero (inv_ne_zero g.ne_zero) hu.1, Finset.mem_univ _⟩
            · intro u _; exact inv_mul_cancel_left₀ g.ne_zero u
            · intro u _; exact mul_inv_cancel_left₀ g.ne_zero u
            · intro u hu
              rw [hψ_mul k (g : F) u g.ne_zero (Finset.mem_erase.mp hu).1, map_mul]
              push_cast; ring
          have hfac : (ψ k (g : F) * (quadraticChar F (g : F) : ℂ) - 1) *
              ∑ u ∈ Finset.univ.erase (0 : F), ψ k u * (quadraticChar F u : ℂ) = 0 := by
            linear_combination hshift
          exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hgne)
        have hψ_conj_inv : ∀ x : F, x ≠ 0 → starRingEnd ℂ (ψ k x) = ψ k x⁻¹ := fun x hx => by
          rw [hψ_conj k x hx]
          have hmul : ψ k x * ψ k x⁻¹ = 1 := by
            rw [← hψ_mul k x x⁻¹ hx (inv_ne_zero hx), mul_inv_cancel₀ hx, hψ_one k]
          have hne0 : ψ k x ≠ 0 := fun h0 => by rw [h0, zero_mul] at hmul; exact zero_ne_one hmul
          exact inv_eq_of_mul_eq_one_right hmul
        exact le_of_eq (jacobiSum_norm_sq_eq_card hF (ψ k) (hψ_mul k) (hψ_one k)
          hψ_conj_inv horth1 horth2)
  have hjac_norm : ∀ k : ℕ, ‖jacobiSum (ψ k)‖ ≤ Real.sqrt (Fintype.card F : ℝ) := fun k =>
    Real.le_sqrt_of_sq_le (hjac_norm_sq k)
  -- Subgroup parameters `mj = |H j|` and `dj = N / mj`:
  let mj : Fin m → ℕ := fun j => Fintype.card (H j)
  let dj : Fin m → ℕ := fun j => N / mj j
  have hmj_pos : ∀ j, 0 < mj j := fun j => Fintype.card_pos
  have hmj_dvd : ∀ j, mj j ∣ N := fun j => by
    rw [← hcard_units]
    simpa only [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card (H j)
  have hdm : ∀ j, dj j * mj j = N := fun j => Nat.div_mul_cancel (hmj_dvd j)
  have hdj_pos : ∀ j, 0 < dj j := fun j =>
    Nat.div_pos (Nat.le_of_dvd hN_pos (hmj_dvd j)) (hmj_pos j)
  have hmem_H : ∀ (j : Fin m) (u : Fˣ), u ∈ H j ↔ dj j ∣ dlog u := fun j u => by
    have hpow_iff : u ∈ H j ↔ u ^ mj j = 1 := by
      constructor
      · intro hu
        have h1 : (⟨u, hu⟩ : H j) ^ mj j = 1 := pow_card_eq_one
        exact congrArg Subtype.val h1
      · intro hpow
        have hmem_sub : ∀ x : Fˣ, x ∈ H j → x ^ mj j = 1 := fun x hx =>
          congrArg Subtype.val (pow_card_eq_one (x := (⟨x, hx⟩ : H j)))
        let K : Subgroup Fˣ := {
          carrier := {x : Fˣ | x ^ mj j = 1}
          mul_mem' := fun hx hy => by simp only [Set.mem_ofPred_eq, mul_pow] at hx hy ⊢; rw [hx, hy, one_mul]
          one_mem' := by simp
          inv_mem' := fun hx => by simp only [Set.mem_ofPred_eq, inv_pow] at hx ⊢; rw [hx, inv_one]
        }
        have hHK : H j ≤ K := fun x hx => hmem_sub x hx
        have hK_card : Fintype.card K ≤ mj j := by
          have hroots : ∀ x : K, Polynomial.eval ((x.1 : Fˣ) : F) (Polynomial.X ^ mj j - 1) = 0 := fun x => by
            simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
            have h1 := congrArg Units.val x.2
            simpa [sub_eq_zero] using h1
          have hpoly_ne : (Polynomial.X ^ mj j - 1 : Polynomial F) ≠ 0 := by
            intro h0
            have hdeg := congrArg Polynomial.natDegree h0
            rw [← Polynomial.C_1, Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_zero] at hdeg
            exact (hmj_pos j).ne' hdeg
          have hinj : Function.Injective (fun x : K => ((x.1 : Fˣ) : F)) :=
            Units.val_injective.comp Subtype.val_injective
          have hsub : (Finset.univ.image fun x : K => ((x.1 : Fˣ) : F)) ⊆
              (Polynomial.X ^ mj j - 1 : Polynomial F).roots.toFinset := by
            intro y hy
            obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
            rw [Multiset.mem_toFinset, Polynomial.mem_roots hpoly_ne, Polynomial.IsRoot]
            exact hroots x
          calc Fintype.card K = (Finset.univ.image fun x : K => ((x.1 : Fˣ) : F)).card :=
                (Finset.card_image_of_injective _ hinj).symm
            _ ≤ (Polynomial.X ^ mj j - 1 : Polynomial F).roots.toFinset.card := Finset.card_le_card hsub
            _ ≤ (Polynomial.X ^ mj j - 1 : Polynomial F).roots.card := Multiset.toFinset_card_le _
            _ ≤ (Polynomial.X ^ mj j - 1 : Polynomial F).natDegree := Polynomial.card_roots' _
            _ = mj j := by rw [← Polynomial.C_1, Polynomial.natDegree_X_pow_sub_C]
        have hcard_eq : Fintype.card (H j) = Fintype.card K :=
          le_antisymm (Fintype.card_le_of_injective (Set.inclusion hHK) (Set.inclusion_injective hHK)) hK_card
        have hHeqK : H j = K := Subgroup.eq_of_le_of_card_ge hHK (by simpa [Nat.card_eq_fintype_card] using hcard_eq.ge)
        rw [hHeqK]; exact hpow
    rw [hpow_iff]
    conv_lhs => rw [← hdlog_pow u, ← pow_mul]
    constructor
    · intro h1
      have hdvdN : N ∣ dlog u * mj j := by rw [← hord_g]; exact orderOf_dvd_of_pow_eq_one h1
      rw [← hdm j] at hdvdN
      exact (Nat.mul_dvd_mul_iff_right (hmj_pos j)).mp hdvdN
    · rintro ⟨k, hk⟩
      rw [hk, mul_assoc, mul_comm k (mj j), ← mul_assoc, hdm j, pow_mul, ← hord_g,
        pow_orderOf_eq_one, one_pow]
  -- 1D Fourier indicator of coset `a j * H j`:
  have hcoset_ind : ∀ (j : Fin m) (x : Fˣ),
      ∑ t : Fin (dj j), ψ (t.val * mj j) (a j : F)⁻¹ * ψ (t.val * mj j) (x : F) =
        if x * (a j)⁻¹ ∈ H j then (dj j : ℂ) else 0 := by
    intro j x
    set u := x * (a j)⁻¹
    have hterm : ∀ t : Fin (dj j),
        ψ (t.val * mj j) (a j : F)⁻¹ * ψ (t.val * mj j) (x : F) = (ζ ^ (mj j * dlog u)) ^ t.val := fun t => by
      have ha0 : (a j : F)⁻¹ ≠ 0 := inv_ne_zero (a j).ne_zero
      rw [← hψ_mul (t.val * mj j) (a j : F)⁻¹ (x : F) ha0 x.ne_zero]
      have hu_eq : Units.mk0 ((a j : F)⁻¹ * (x : F)) (mul_ne_zero ha0 x.ne_zero) = u := by
        ext; simp [u, mul_comm]
      simp only [ψ, mul_ne_zero ha0 x.ne_zero, ↓reduceDIte, hu_eq]
      rw [← pow_mul]; congr 1; ring
    simp_rw [hterm]
    rw [Fin.sum_univ_eq_sum_range (fun t => (ζ ^ (mj j * dlog u)) ^ t) (dj j)]
    by_cases huH : u ∈ H j
    · simp only [huH, ↓reduceIte]
      obtain ⟨k, hk⟩ := (hmem_H j u).mp huH
      have h1 : ζ ^ (mj j * dlog u) = 1 := by
        rw [hk, show mj j * (dj j * k) = N * k by rw [← hdm j]; ring, pow_mul, hζ_pow_N, one_pow]
      simp only [h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    · simp only [huH, ↓reduceIte]
      have hne1 : ζ ^ (mj j * dlog u) ≠ 1 := by
        intro h1
        have hrem : (mj j * dlog u) % N = 0 := by
          by_contra hnz
          exact exp_two_pi_div_prim hN_pos (Nat.pos_of_ne_zero hnz) (Nat.mod_lt _ hN_pos)
            (by rw [hζ_mod, h1])
        have hdvdN : N ∣ mj j * dlog u := Nat.dvd_of_mod_eq_zero hrem
        rw [← hdm j] at hdvdN
        exact huH ((hmem_H j u).mpr ((Nat.mul_dvd_mul_iff_left (hmj_pos j)).mp
          (by rwa [mul_comm (mj j) (dj j)])))
      have hgeom := geom_sum_mul (ζ ^ (mj j * dlog u)) (dj j)
      have hpow_d : (ζ ^ (mj j * dlog u)) ^ (dj j) = 1 := by
        rw [← pow_mul, show mj j * dlog u * dj j = N * dlog u by rw [← hdm j]; ring,
          pow_mul, hζ_pow_N, one_pow]
      rw [hpow_d, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne1)
  -- `m`-fold Fourier identity for the product-coset sum:
  set D : ℕ := ∏ j : Fin m, dj j
  have hD_pos : 0 < D := Finset.prod_pos fun j _ => hdj_pos j
  have hfourier : (D : ℂ) *
        ((∑ u : (j : Fin m) → H j,
          hyperellipticTrace (fun j => ((a j * (u j : Fˣ) : Fˣ) : F)) : ℤ) : ℂ) =
      ∑ t : (j : Fin m) → Fin (dj j),
        (∏ j : Fin m, ψ ((t j).val * mj j) (a j : F)⁻¹) *
          ((quadraticChar F (-1 : F) : ℂ) *
            jacobiSum (fun z => (quadraticChar F z : ℂ) ^ (m + 1) *
              ∏ j : Fin m, ψ ((t j).val * mj j) z) *
            ∏ j : Fin m, jacobiSum (ψ ((t j).val * mj j))) := by
    have hmell : ∀ t : (j : Fin m) → Fin (dj j),
        (quadraticChar F (-1 : F) : ℂ) *
          jacobiSum (fun z => (quadraticChar F z : ℂ) ^ (m + 1) *
            ∏ j : Fin m, ψ ((t j).val * mj j) z) *
          ∏ j : Fin m, jacobiSum (ψ ((t j).val * mj j)) =
        ∑ lam : Fin m → Fˣ, (∏ j : Fin m, ψ ((t j).val * mj j) (lam j : F)) *
          (hyperellipticTrace (fun j => (lam j : F)) : ℂ) := fun t =>
      (all_genus_mellin_jacobi_identity (fun j => ψ ((t j).val * mj j))
        (fun j => hψ_mul ((t j).val * mj j))).symm
    simp_rw [hmell, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hcoeff : ∀ lam : Fin m → Fˣ,
        ∑ t : (j : Fin m) → Fin (dj j),
            (∏ j : Fin m, ψ ((t j).val * mj j) (a j : F)⁻¹) *
              ((∏ j : Fin m, ψ ((t j).val * mj j) (lam j : F)) *
                (hyperellipticTrace (fun j => (lam j : F)) : ℂ)) =
          (if ∀ j : Fin m, lam j * (a j)⁻¹ ∈ H j then (D : ℂ) else 0) *
            (hyperellipticTrace (fun j => (lam j : F)) : ℂ) := fun lam => by
      have hfac : ∀ t : (j : Fin m) → Fin (dj j),
          (∏ j : Fin m, ψ ((t j).val * mj j) (a j : F)⁻¹) *
            ((∏ j : Fin m, ψ ((t j).val * mj j) (lam j : F)) *
              (hyperellipticTrace (fun j => (lam j : F)) : ℂ)) =
          (∏ j : Fin m, (ψ ((t j).val * mj j) (a j : F)⁻¹ *
            ψ ((t j).val * mj j) (lam j : F))) *
            (hyperellipticTrace (fun j => (lam j : F)) : ℂ) := fun t => by
        rw [← mul_assoc, Finset.prod_mul_distrib]
      simp_rw [hfac, ← Finset.sum_mul]
      congr 1
      rw [← Fintype.prod_sum
        (fun j (t : Fin (dj j)) => ψ (t.val * mj j) (a j : F)⁻¹ * ψ (t.val * mj j) (lam j : F))]
      simp_rw [hcoset_ind]
      by_cases hall : ∀ j : Fin m, lam j * (a j)⁻¹ ∈ H j
      · simp only [hall, implies_true, ↓reduceIte, D, Nat.cast_prod]
      · simp only [hall, ↓reduceIte]
        push Not at hall
        obtain ⟨j₀, hj₀⟩ := hall
        exact Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [hj₀])
    simp_rw [hcoeff]
    have hite : ∀ lam : Fin m → Fˣ,
        (if ∀ j : Fin m, lam j * (a j)⁻¹ ∈ H j then (D : ℂ) else 0) *
            (hyperellipticTrace (fun j => (lam j : F)) : ℂ) =
          if ∀ j : Fin m, lam j * (a j)⁻¹ ∈ H j then
            (D : ℂ) * (hyperellipticTrace (fun j => (lam j : F)) : ℂ) else 0 := fun lam => by
      split_ifs <;> ring
    simp_rw [hite, ← Finset.sum_filter, ← Finset.mul_sum]
    congr 1
    -- Bijection between `{lam | ∀ j, lam j * (a j)⁻¹ ∈ H j}` and `(j : Fin m) → H j`:
    have hbij : ∑ lam ∈ Finset.univ.filter (fun lam : Fin m → Fˣ => ∀ j, lam j * (a j)⁻¹ ∈ H j),
          (hyperellipticTrace (fun j => (lam j : F)) : ℂ) =
        ∑ u : (j : Fin m) → H j,
          (hyperellipticTrace (fun j => ((a j * (u j : Fˣ) : Fˣ) : F)) : ℂ) := by
      refine (Finset.sum_nbij' (fun (u : (j : Fin m) → H j) (j : Fin m) => a j * (u j : Fˣ))
        (fun lam j => if h : lam j * (a j)⁻¹ ∈ H j then ⟨lam j * (a j)⁻¹, h⟩ else 1)
        ?_ ?_ ?_ ?_ ?_).symm
      · intro u _
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun j => ?_⟩
        dsimp only
        rw [mul_comm (a j) (u j : Fˣ), mul_assoc, mul_inv_cancel, mul_one]
        exact (u j).2
      · intro _ _; exact Finset.mem_univ _
      · intro u _
        funext j
        have hmem : a j * (u j : Fˣ) * (a j)⁻¹ ∈ H j := by
          rw [mul_comm (a j) (u j : Fˣ), mul_assoc, mul_inv_cancel, mul_one]; exact (u j).2
        simp only [hmem, ↓reduceDIte]
        ext; simp [mul_comm (a j) (u j : Fˣ), mul_assoc]
      · intro lam hlam
        funext j
        have hmem : lam j * (a j)⁻¹ ∈ H j := (Finset.mem_filter.mp hlam).2 j
        simp only [hmem, ↓reduceDIte]
        rw [mul_comm (a j) (lam j * (a j)⁻¹), mul_assoc, inv_mul_cancel, mul_one]
      · intro _ _; rfl
    rw [hbij]
    simp [Int.cast_sum]
  -- Bound every Fourier term by `√q ^ (m + 1)`:
  have hterm_le : ∀ t : (j : Fin m) → Fin (dj j),
      ‖(∏ j : Fin m, ψ ((t j).val * mj j) (a j : F)⁻¹) *
        ((quadraticChar F (-1 : F) : ℂ) *
          jacobiSum (fun z => (quadraticChar F z : ℂ) ^ (m + 1) *
            ∏ j : Fin m, ψ ((t j).val * mj j) z) *
          ∏ j : Fin m, jacobiSum (ψ ((t j).val * mj j)))‖ ≤
        Real.sqrt (Fintype.card F : ℝ) ^ (m + 1) := fun t => by
    rw [norm_mul, norm_mul, norm_mul, norm_prod, norm_prod]
    have hp1 : ∏ j : Fin m, ‖ψ ((t j).val * mj j) (a j : F)⁻¹‖ = 1 :=
      Finset.prod_eq_one fun j _ => hψ_norm _ _ (inv_ne_zero (a j).ne_zero)
    have hchi1 : ‖(quadraticChar F (-1 : F) : ℂ)‖ = 1 := by
      rcases quadraticChar_dichotomy (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)) with h | h <;>
        simp [h]
    -- Identify the combined character `z ↦ χ(z)^(m+1) * ∏ j, ψ (t j * m j) z` as `ψ K`:
    set K : ℕ := (m + 1) * (N / 2) + ∑ j : Fin m, (t j).val * mj j
    have hcomb_eq : jacobiSum (fun z => (quadraticChar F z : ℂ) ^ (m + 1) *
          ∏ j : Fin m, ψ ((t j).val * mj j) z) = jacobiSum (ψ K) := by
      unfold jacobiSum
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
      congr 1
      dsimp only
      rw [hchi_eq z hz0]
      simp only [ψ, hz0, ↓reduceDIte]
      rw [← pow_mul, Finset.prod_pow_eq_pow_sum, ← pow_add]
      congr 1
      dsimp [K]
      rw [add_mul, Finset.sum_mul]
      ring
    rw [hp1, hchi1, one_mul, one_mul, hcomb_eq, pow_succ']
    refine mul_le_mul (hjac_norm K) ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Real.sqrt_nonneg _)
    have hprod_le : ∀ (s : Finset (Fin m)), ∏ j ∈ s, ‖jacobiSum (ψ ((t j).val * mj j))‖ ≤
        Real.sqrt (Fintype.card F : ℝ) ^ s.card := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert j s hjs ih =>
        rw [Finset.prod_insert hjs, Finset.card_insert_of_notMem hjs, pow_succ']
        exact mul_le_mul (hjac_norm _) ih (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          (Real.sqrt_nonneg _)
    simpa [Finset.card_univ, Fintype.card_fin] using hprod_le Finset.univ
  have hnorm_D : ‖(D : ℂ) * ((∑ u : (j : Fin m) → H j,
        hyperellipticTrace (fun j => ((a j * (u j : Fˣ) : Fˣ) : F)) : ℤ) : ℂ)‖ ≤
      (D : ℝ) * Real.sqrt (Fintype.card F : ℝ) ^ (m + 1) := by
    rw [hfourier]
    calc ‖∑ t : (j : Fin m) → Fin (dj j), _‖
        ≤ ∑ t : (j : Fin m) → Fin (dj j), ‖_‖ := norm_sum_le _ _
      _ ≤ ∑ _t : (j : Fin m) → Fin (dj j), Real.sqrt (Fintype.card F : ℝ) ^ (m + 1) :=
          Finset.sum_le_sum fun t _ => hterm_le t
      _ = (D : ℝ) * Real.sqrt (Fintype.card F : ℝ) ^ (m + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi]
          simp [D, nsmul_eq_mul]
  rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast] at hnorm_D
  have hD_posR : (0 : ℝ) < D := by exact_mod_cast hD_pos
  have habsR : |(∑ u : (j : Fin m) → H j,
      hyperellipticTrace (fun j => ((a j * (u j : Fˣ) : Fˣ) : F)) : ℝ)| ≤
      Real.sqrt (Fintype.card F : ℝ) ^ (m + 1) := by
    have := le_of_mul_le_mul_left hnorm_D hD_posR
    simpa [Int.cast_abs] using this
  have hsqR : ((∑ u : (j : Fin m) → H j,
      hyperellipticTrace (fun j => ((a j * (u j : Fˣ) : Fˣ) : F)) : ℝ)) ^ 2 ≤
      (Fintype.card F : ℝ) ^ (m + 1) := by
    rw [← sq_abs]
    calc _ ≤ (Real.sqrt (Fintype.card F : ℝ) ^ (m + 1)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) habsR 2
      _ = (Real.sqrt (Fintype.card F : ℝ) ^ 2) ^ (m + 1) := by rw [← pow_mul, mul_comm, pow_mul]
      _ = (Fintype.card F : ℝ) ^ (m + 1) := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  exact_mod_cast hsqR

/-! ## 4. Sharp Cross-Ratio Parseval Crossover Barrier (`α > (2r - 3) / (2r - 1)`) -/

/-- **Sharp Higher-Genus Cross-Ratio Parseval Barrier**:
For ANY `r ≥ 2`, ANY active set `S` of `(2r - 3)`-cross-ratio orbits with `|S| ≤ n^(2r - 1)`
(as forced by `H`-scaling invariance on `H^(2r)` for a subgroup `|H| = n`), ANY multiplicity table
`V : α → ℕ` supported on `S` with total mass `∑ x ∈ S, V x = T`, and ANY field size `q` with
`n^(2r - 1) ≤ q^(2r - 3)` (i.e. `log_q(n) ≤ (2r - 3) / (2r - 1)`), the Parseval square product
`q^(2r - 2) * ∑ x ∈ S, V(x)^2` is AT LEAST `T^2 * q` — so raw `(2r - 3)`-variable Parseval against
the Deuring–Birch `L²` norm `q^(r - 1)` can NEVER beat the pointwise Weil scale `T * √q`! -/
theorem subgroup_crossRatio_parseval_barrier {α : Type*} [DecidableEq α]
    (S : Finset α) (V : α → ℕ) {r n q T : ℕ} (hr : 2 ≤ r)
    (hS : S.card ≤ n ^ (2 * r - 1))
    (hsum : ∑ x ∈ S, V x = T)
    (hregime : n ^ (2 * r - 1) ≤ q ^ (2 * r - 3)) :
    T ^ 2 * q ≤ q ^ (2 * r - 2) * ∑ x ∈ S, V x ^ 2 := by
  have hcs : T ^ 2 ≤ S.card * ∑ x ∈ S, V x ^ 2 := by
    rw [← hsum]
    exact sq_sum_le_card_mul_sum_sq
  have h1 : T ^ 2 ≤ n ^ (2 * r - 1) * ∑ x ∈ S, V x ^ 2 :=
    hcs.trans (Nat.mul_le_mul_right _ hS)
  have h2 : T ^ 2 * q ≤ (n ^ (2 * r - 1) * q) * ∑ x ∈ S, V x ^ 2 := by
    calc T ^ 2 * q ≤ (n ^ (2 * r - 1) * ∑ x ∈ S, V x ^ 2) * q := Nat.mul_le_mul_right q h1
      _ = (n ^ (2 * r - 1) * q) * ∑ x ∈ S, V x ^ 2 := by ring
  have hq_exp : q ^ (2 * r - 3) * q = q ^ (2 * r - 2) := by
    rw [← pow_succ, show 2 * r - 3 + 1 = 2 * r - 2 by omega]
  have h3 : n ^ (2 * r - 1) * q ≤ q ^ (2 * r - 2) := by
    rw [← hq_exp]
    exact Nat.mul_le_mul_right q hregime
  exact h2.trans (Nat.mul_le_mul_right _ h3)

/-- Concrete production-regime specialization (`n = 2^30`, `q ≥ 2^158`): for EVERY `r ≥ 2`,
`n^(2r - 1) < q^(2r - 3)`, so raw higher-genus cross-ratio Parseval cannot beat pointwise Weil
at ANY moment order `r ≥ 2` on the Proximity Prize smooth-subgroup parameters! -/
theorem production_parseval_barrier_all_r {r q : ℕ} (hr : 2 ≤ r) (hq : 2 ^ 158 ≤ q) :
    (2 ^ 30) ^ (2 * r - 1) ≤ q ^ (2 * r - 3) := by
  calc (2 ^ 30) ^ (2 * r - 1)
      = 2 ^ (30 * (2 * r - 1)) := by rw [← pow_mul]
    _ ≤ 2 ^ (158 * (2 * r - 3)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = (2 ^ 158) ^ (2 * r - 3) := by rw [pow_mul]
    _ ≤ q ^ (2 * r - 3) := Nat.pow_le_pow_left hq _

end ProximityGap.PaleyAllGenusMellinJacobi

#print axioms ProximityGap.PaleyAllGenusMellinJacobi.all_genus_mellin_jacobi_identity
#print axioms ProximityGap.PaleyAllGenusMellinJacobi.sliced_mellin_jacobi_identity
#print axioms ProximityGap.PaleyAllGenusMellinJacobi.sum_sq_hyperellipticTrace_eq
#print axioms ProximityGap.PaleyAllGenusMellinJacobi.sq_sum_product_coset_hyperellipticTrace_le
#print axioms ProximityGap.PaleyAllGenusMellinJacobi.subgroup_crossRatio_parseval_barrier
#print axioms ProximityGap.PaleyAllGenusMellinJacobi.production_parseval_barrier_all_r
