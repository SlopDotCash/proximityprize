/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Norm.Basic
import Mathlib.FieldTheory.PrimitiveElement
import ArkLib.Data.CodingTheory.ProximityGap.ConverseLamLeung2Power

/-!
# gate-norm-bound: the spurious-vanishing height gate, PROVED (#407)

Target: discharge the `NoSpuriousVanishing` obligation by the algebraic-integer NORM HEIGHT
bound (a real theorem, looser than the conjectured `(n/2-1)^{n/4}` but PROVABLE):

> Let `K` be a number field, `Σ = Σ_{i∈s} u_i ∈ 𝓞_K` a sum of roots of unity (`u_i^{k_i}=1`,
> `k_i ≠ 0`).  Its integer norm satisfies `|N_{K/ℚ}(Σ)| ≤ (#s)^{[K:ℚ]}`.  Hence for a rational
> prime `p` with `p > (#s)^{[K:ℚ]}`:  **if `p ∣ N(Σ)` (the spurious-mod-`p` condition) then
> `Σ = 0`.**

MECHANISM.  `Σ ∈ 𝓞_K` is an algebraic integer, so `N(Σ) := Algebra.norm ℤ Sg` is a genuine
RATIONAL INTEGER (`Algebra.coe_norm_int`).  Its size is bounded by the house power
`house(Σ)^{[K:ℚ]} ≤ (#s)^{[K:ℚ]}` (each root of unity has house `≤ 1`; this is the
`RootSumNormBound.lean` substrate, re-derived here at integer level).  If `Σ ≠ 0` then
`N(Σ) ≠ 0` (`Algebra.norm_eq_zero_iff` — `ℤ ↪ 𝓞_K` is a finite free domain extension), and a
nonzero integer divisible by `p` has absolute value `≥ p`; combined with `|N(Σ)| < p` this is a
contradiction.  So `p ∣ N(Σ) ⟹ Σ = 0`.

The bound `(#s)^{[K:ℚ]}` over `K = ℚ(ζ_{2^a})` is `m^{2^{a-1}} = m^{φ(2^a)}` — exactly the
"provable" height of the gate (looser than the conjectured `(n/2-1)^{n/4}`, but a THEOREM).

What is PROVED (axiom-clean): the number-field-side gate `gate_sum_zero_of_prime_dvd_norm` and
its specialization to a primitive `2^a`-th root group `gate_2power`.  The remaining (NOT proved
here) step is the reduction-mod-`p` LIFT that identifies "vanishes in `F_p`" with "`p ∣ N(Σ)`";
that is the named bridge, kept explicit.
-/
set_option linter.style.longLine false
set_option autoImplicit false


open Finset NumberField Module

namespace ArkLib.ProximityGap.GateNorm

variable {K : Type*} [Field K] [NumberField K]

/-! ## Integer-level house bound (lifts the rational `RootSumNorm` chain into `𝓞_K`) -/

/-- The house (largest conjugate modulus) of a root of unity in `K` is `≤ 1`. -/
theorem house_rootOfUnity_le_one {u : K} {k : ℕ} (hk : k ≠ 0) (hu : u ^ k = 1) :
    house u ≤ 1 := by
  rw [house_eq_sup', ← NNReal.coe_one, NNReal.coe_le_coe]
  refine Finset.sup'_le _ _ (fun σ _ => ?_)
  rw [Complex.nnnorm_eq_one_of_pow_eq_one (by rw [← map_pow, hu, map_one]) hk]

/-- `|N_{K/ℚ}(α)| ≤ house(α)^{[K:ℚ]}` (the rational norm). -/
theorem abs_norm_le_house_pow (α : K) :
    ((|Algebra.norm ℚ α| : ℚ) : ℝ) ≤ house α ^ finrank ℚ K := by
  have key : (algebraMap ℚ ℂ) (Algebra.norm ℚ α) = ∏ σ : K →ₐ[ℚ] ℂ, σ α :=
    Algebra.norm_eq_prod_embeddings ℚ ℂ α
  have hnorm : ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ α)‖ = ((|Algebra.norm ℚ α| : ℚ) : ℝ) := by
    simp [eq_ratCast, Complex.norm_ratCast, Rat.cast_abs]
  calc ((|Algebra.norm ℚ α| : ℚ) : ℝ)
      = ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ α)‖ := hnorm.symm
    _ = ‖∏ σ : K →ₐ[ℚ] ℂ, σ α‖ := by rw [key]
    _ = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ := by rw [norm_prod]
    _ ≤ ∏ _σ : K →ₐ[ℚ] ℂ, house α :=
        Finset.prod_le_prod (fun σ _ => norm_nonneg _)
          (fun σ _ => norm_embedding_le_house α σ.toRingHom)
    _ = house α ^ (Fintype.card (K →ₐ[ℚ] ℂ)) := by rw [Finset.prod_const, Finset.card_univ]
    _ = house α ^ finrank ℚ K := by
        rw [AlgHom.card_of_splits ℚ K ℂ (fun _ ↦ IsAlgClosed.splits _)]

/-- **The (rational) norm of a sum of roots of unity is bounded by `(#terms)^{[K:ℚ]}`.** -/
theorem abs_norm_sum_rootsOfUnity_le {ι : Type*} (s : Finset ι) (u : ι → K)
    (k : ι → ℕ) (hk : ∀ i ∈ s, k i ≠ 0) (hu : ∀ i ∈ s, u i ^ (k i) = 1) :
    ((|Algebra.norm ℚ (∑ i ∈ s, u i)| : ℚ) : ℝ) ≤ (s.card : ℝ) ^ finrank ℚ K := by
  refine (abs_norm_le_house_pow _).trans ?_
  apply pow_le_pow_left₀ (house_nonneg _)
  calc house (∑ i ∈ s, u i)
      ≤ ∑ i ∈ s, house (u i) := house_sum_le_sum_house s u
    _ ≤ ∑ _i ∈ s, (1 : ℝ) :=
        Finset.sum_le_sum (fun i hi => house_rootOfUnity_le_one (hk i hi) (hu i hi))
    _ = (s.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ## The gate: prime divides integer norm ⟹ the sum is zero -/

/-- **The spurious-vanishing height GATE (number-field side).**

Let `Σ = ∑_{i∈s} u_i ∈ 𝓞_K` be a sum of roots of unity (each `(u_i : K)^{k_i} = 1`, `k_i ≠ 0`).
If a NATURAL number `p` exceeds the provable height `(#s)^{[K:ℚ]}` and `(p : ℤ)` divides the
INTEGER norm `N_{K/ℚ}(Σ) := Algebra.norm ℤ Sg`, then `Σ = 0`.

This is the contrapositive of `p > height ⟹ (Σ ≠ 0 ⟹ p ∤ N(Σ))`: a nonzero `Σ` has
`N(Σ) ≠ 0` (`Algebra.norm_eq_zero_iff` over the finite-free domain extension `ℤ → 𝓞_K`), with
`|N(Σ)| ≤ (#s)^{[K:ℚ]} < p`, so `p ∣ N(Σ)` would force `p ≤ |N(Σ)| < p`, absurd. -/
theorem gate_sum_zero_of_prime_dvd_norm {ι : Type*} (s : Finset ι) (u : ι → 𝓞 K)
    (k : ι → ℕ) (hk : ∀ i ∈ s, k i ≠ 0) (hu : ∀ i ∈ s, ((u i : K)) ^ (k i) = 1)
    {p : ℕ} (hp : (s.card : ℝ) ^ finrank ℚ K < p)
    (hdvd : (p : ℤ) ∣ Algebra.norm ℤ (∑ i ∈ s, u i)) :
    (∑ i ∈ s, u i) = 0 := by
  classical
  set Sg : 𝓞 K := ∑ i ∈ s, u i with hSg
  -- The integer norm equals the rational norm of the image in `K`.
  set N : ℤ := Algebra.norm ℤ Sg with hN
  have hcoe : (N : ℚ) = Algebra.norm ℚ ((Sg : K)) := Algebra.coe_norm_int Sg
  -- The image in `K` is the sum of the roots of unity.
  have hSgK : (Sg : K) = ∑ i ∈ s, ((u i : K)) := by
    rw [hSg]; push_cast; rfl
  -- Suppose `Σ ≠ 0`; derive a contradiction.
  by_contra hne
  -- `N ≠ 0` because the norm of a nonzero element is nonzero (finite-free domain extension).
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact (Algebra.norm_ne_zero_iff).mpr hne
  -- `|N| < p` from the house bound (transported to the integer norm via `hcoe`).
  have hbound : ((|N| : ℤ) : ℝ) < (p : ℝ) := by
    have hb : ((|Algebra.norm ℚ ((Sg : K))| : ℚ) : ℝ) ≤ (s.card : ℝ) ^ finrank ℚ K := by
      rw [hSgK]
      exact abs_norm_sum_rootsOfUnity_le s (fun i => (u i : K)) k hk hu
    have hb2 : ((|Algebra.norm ℚ ((Sg : K))| : ℚ) : ℝ) < (p : ℝ) := lt_of_le_of_lt hb hp
    -- `|N : ℤ| = |Algebra.norm ℚ (Sg : K)|` as rationals via `hcoe`.
    have heqQ : ((|N| : ℤ) : ℚ) = (|Algebra.norm ℚ ((Sg : K))| : ℚ) := by
      rw [Int.cast_abs, hcoe]
    -- transport `hb2` to `|N|` via this rational equality.
    have heq : ((|N| : ℤ) : ℝ) = ((|Algebra.norm ℚ ((Sg : K))| : ℚ) : ℝ) := by
      have : (((|N| : ℤ) : ℚ) : ℝ) = ((|Algebra.norm ℚ ((Sg : K))| : ℚ) : ℝ) := by
        rw [heqQ]
      simpa using this
    rw [heq]; exact hb2
  -- `p ∣ N` with `N ≠ 0` ⟹ `p ≤ |N|`, contradiction with `|N| < p`.
  have hple : (p : ℤ) ≤ |N| := by
    have hppos : (0 : ℤ) < |N| := abs_pos.mpr hN0
    have := Int.le_of_dvd hppos ((dvd_abs _ _).mpr hdvd)
    exact this
  -- contradiction
  have : (p : ℝ) ≤ ((|N| : ℤ) : ℝ) := by exact_mod_cast hple
  exact absurd (lt_of_le_of_lt this hbound) (lt_irrefl _)

/-! ## Specialization: a 2-power root-of-unity group -/

/-- **The gate for the prize group `μ_n`, `n = 2^a`.**  If each `u_i` is an `n`-th root of unity
(`n = 2^a ≥ 2`), `p > m^{φ(n)}` with `m = #s`, and `p ∣ N(Σ)`, then `Σ = ∑ u_i = 0`.

The exponent `finrank ℚ K = [K:ℚ]` equals `φ(2^a) = 2^{a-1}` precisely when `K = ℚ(ζ_{2^a})`,
giving the height `m^{2^{a-1}}` of the gate; here we keep `finrank ℚ K` so the lemma holds for
any number field containing the roots.  (All `u_i^{2^a} = 1`, `2^a ≠ 0`.) -/
theorem gate_2power {ι : Type*} {a : ℕ} (_ha : 1 ≤ a) (s : Finset ι) (u : ι → 𝓞 K)
    (hu : ∀ i ∈ s, ((u i : K)) ^ (2 ^ a) = 1)
    {p : ℕ} (hp : (s.card : ℝ) ^ finrank ℚ K < p)
    (hdvd : (p : ℤ) ∣ Algebra.norm ℤ (∑ i ∈ s, u i)) :
    (∑ i ∈ s, u i) = 0 := by
  refine gate_sum_zero_of_prime_dvd_norm s u (fun _ => 2 ^ a)
    (fun i _ => by positivity) hu hp hdvd

/-! ## Capstone: the gate forces ANTIPODALITY of the exponent set

Chaining `gate_2power` (`p ∣ N(Σ) ⟹ Σ = 0` in `𝓞_K`) with the LANDED char-0 converse
`RouVanishingCount.zero_sum_imp_antipodal` (`Σ_{i∈S} ζ^i = 0 ⟹ S` is antipodal): the prime
height gate alone (no Lam–Leung machinery beyond the 2-power minpoly fact) forces a
spurious-mod-`p`-vanishing subset of `2^a`-th roots to be a disjoint union of negation pairs. -/

open ArkLib.ProximityGap.RouVanishingCount in
/-- **The spurious-vanishing gate ⟹ antipodality (`2^a` group).**

Let `ζ : 𝓞_K` have `(ζ : K)` a primitive `2^a`-th root of unity (`a ≥ 1`), and `S ⊆ {0,…,2^a-1}`
a subset of exponents.  If the prime height bound `p > (#S)^{[K:ℚ]}` holds and `p` divides the
integer norm `N(∑_{i∈S} ζ^i)`, then the exponent set `S` is **antipodal**:
`j ∈ S ↔ j + 2^{a-1} ∈ S` for every `j < 2^{a-1}`.

This is the END-TO-END height gate: the only escape for a char-`p` count exceeding the char-0
count would be a non-antipodal subset whose root-sum vanishes mod `p` — and `p > (#S)^{[K:ℚ]}`
provably forbids exactly that. -/
theorem gate_2power_antipodal {a : ℕ} (ha : 1 ≤ a) {ζ : 𝓞 K}
    (hζ : IsPrimitiveRoot ((ζ : K)) (2 ^ a)) {S : Finset ℕ} (hS : S ⊆ Finset.range (2 ^ a))
    {p : ℕ} (hp : (S.card : ℝ) ^ finrank ℚ K < p)
    (hdvd : (p : ℤ) ∣ Algebra.norm ℤ (∑ i ∈ S, ζ ^ i)) :
    ExponentAntipodal a S := by
  classical
  -- each summand `(ζ^i : K) = (ζ:K)^i` is a `2^a`-th root of unity.
  have hu : ∀ i ∈ S, (((ζ ^ i : 𝓞 K) : K)) ^ (2 ^ a) = 1 := by
    intro i _
    push_cast
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  -- gate: the sum is zero in `𝓞_K`.
  have hzero : (∑ i ∈ S, (ζ ^ i : 𝓞 K)) = 0 :=
    gate_2power ha S (fun i => ζ ^ i) hu hp hdvd
  -- transport to `K` (the coercion `𝓞_K → K` is a ring hom): cast `hzero` and `push_cast`.
  have hzeroK : (∑ i ∈ S, ((ζ : K)) ^ i) = 0 := by
    have hcastZero : ((∑ i ∈ S, (ζ ^ i : 𝓞 K) : 𝓞 K) : K) = ((0 : 𝓞 K) : K) := by
      rw [hzero]
    push_cast at hcastZero
    simpa using hcastZero
  -- char-0 converse Lam–Leung for 2-power order.
  exact zero_sum_imp_antipodal ha hζ hS hzeroK

end ArkLib.ProximityGap.GateNorm

#print axioms ArkLib.ProximityGap.GateNorm.gate_sum_zero_of_prime_dvd_norm
#print axioms ArkLib.ProximityGap.GateNorm.gate_2power
#print axioms ArkLib.ProximityGap.GateNorm.gate_2power_antipodal
