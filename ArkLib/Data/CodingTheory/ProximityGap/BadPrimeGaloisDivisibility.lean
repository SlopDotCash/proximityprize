/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.House
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Discharging the Galois-divisibility hypothesis of the bad-prime norm bound (#407)

`BadPrimeNormBound.lean` proves the elementary `divisibility ⟹ size` chain for the δ*
antipodal-rigidity gate **conditionally** on a *Galois divisibility input*: that the rational
integer `N = ∏_{a ∈ (ℤ/m)*} f(ζ^a)` (the field norm of `f(ζ)`, `f ∈ ℤ[X]`) is **nonzero** and
divisible by `p^r` whenever `r` distinct conjugates `f(ζ^j)` vanish modulo `p`.  That file took
those facts as the bundled hypotheses `hN_ne, hN_dvd` (and `hN_prod` for the size half), noting
they require the cyclotomic / `Algebra.norm` / `NumberField` machinery.

**This file PROVES that input axiom-clean**, using Mathlib's number-field norm machinery, and is
fully unconditional (no `sorry`, no custom axiom).  It works for an arbitrary Galois number field
`K` (the cyclotomic field `ℚ(ζ_m)` is the intended instance).  The three pieces from the target
spec are:

* **(i) `N` is a rational integer** — `Algebra.norm ℤ x : ℤ` for `x ∈ 𝓞 K`, and
  `Algebra.coe_norm_int : (Algebra.norm ℤ x : ℚ) = Algebra.norm ℚ (x : K)` (Mathlib).
* **(ii) `N ≠ 0`** — `norm_int_ne_zero_of_ne_zero`: from `x ≠ 0` in `𝓞 K` (e.g. `f(ζ) ≠ 0`
  because `deg f < φ(m) = deg (minpoly ℚ ζ)`), `Algebra.norm ℤ x ≠ 0` via
  `Algebra.norm_ne_zero_iff`.
* **(iii) `p^r ∣ N`** — `prime_pow_dvd_norm_int_of_conjugates_vanish`: the norm is the product
  of the Galois conjugates `σ(x)` over `Gal(K/ℚ)` (`norm_eq_prod_automorphisms`, lifted to
  `𝓞 K` by `norm_int_eq_prod_galRestrictO`); `r` conjugates each divisible by `p` contribute
  `p^r` to the product (`pow_card_dvd_prod_of_subset`); and the integer divisibility descends
  from `𝓞 K` to `ℤ` because `ℤ` is integrally closed in `ℚ`
  (`int_dvd_of_dvd_in_ringOfIntegers`).

The packaged consumer `prime_pow_le_norm_aeval` produces, for a `±1` (or any integer) polynomial
`f` and a primitive root `ξ : 𝓞 K`, the clean inequality `p^r ≤ |Algebra.norm ℤ (f(ξ))|` from
`r` distinct conjugates vanishing mod `p` — exactly `BadPrimeBound`'s `bad_prime_pow_le` with the
Galois divisibility input now *proven*.  The archimedean size half (`house_aeval_rootOfUnity_le`
+ `abs_norm_le_house_pow`) gives the matching upper bound `|N| ≤ (Σ|coeff|)^{[K:ℚ]}`, so the
fully assembled `bad_prime_galois_unconditional` is `p^r ≤ (Σ|coeff f|)^{[K:ℚ]}` with **no
hypotheses about `N` at all** — the bad-prime soundness bound is now unconditional.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open scoped NumberField
open NumberField Algebra Module Finset Polynomial

namespace ArkLib.ProximityGap.BadPrimeGalois

/-! ### A general product-divisibility lemma -/

/-- If each element of a subset `T ⊆ S` has `a` as a divisor of `f i`, then `a ^ #T` divides the
full product `∏_{i ∈ S} f i`.  (Split `∏_S = ∏_T · ∏_{S∖T}`; `a^#T ∣ ∏_T`.) -/
theorem pow_card_dvd_prod_of_subset {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    {S T : Finset ι} (hTS : T ⊆ S) (f : ι → M) {a : M}
    (h : ∀ i ∈ T, a ∣ f i) : a ^ T.card ∣ ∏ i ∈ S, f i := by
  rw [← Finset.prod_sdiff hTS]
  have hstep : a ^ T.card ∣ ∏ i ∈ T, f i := by
    have := Finset.prod_dvd_prod_of_dvd (fun _ => a) f h
    rwa [Finset.prod_const] at this
  exact hstep.mul_left _

variable {K : Type*} [Field K] [NumberField K]

/-! ### Galois conjugation on the ring of integers -/

/-- The action of a `ℚ`-automorphism `σ` of `K` restricted to `𝓞 K` (it preserves algebraic
integers).  Models `f(ζ) ↦ f(ζ^j)` when `σ : ζ ↦ ζ^j`. -/
noncomputable def galRestrictO (σ : K ≃ₐ[ℚ] K) (x : 𝓞 K) : 𝓞 K :=
  ⟨σ (x : K), x.2.map (σ : K →+* K).toIntAlgHom⟩

@[simp] lemma coe_galRestrictO (σ : K ≃ₐ[ℚ] K) (x : 𝓞 K) :
    ((galRestrictO σ x : 𝓞 K) : K) = σ (x : K) := rfl

/-- `σ` commutes with `aeval` of an integer polynomial: `σ(f(ξ)) = f(σ ξ)` in `𝓞 K`. -/
theorem coe_galRestrictO_aeval (σ : K ≃ₐ[ℚ] K) (ξ : 𝓞 K) (f : Polynomial ℤ) :
    ((galRestrictO σ (aeval ξ f) : 𝓞 K) : K) = aeval (σ (ξ : K)) f := by
  show σ ((aeval ξ f : 𝓞 K) : K) = aeval (σ (ξ:K)) f
  have hcoe : ((aeval ξ f : 𝓞 K) : K) = aeval (ξ:K) f := by
    rw [aeval_algebraMap_apply K ξ f]
  rw [hcoe]
  have h := aeval_algHom_apply (σ.restrictScalars ℤ) (ξ:K) f
  simp only [AlgEquiv.restrictScalars_apply] at h
  exact h.symm

/-! ### (i)+(ii): the integer norm and its nonvanishing -/

/-- **(ii) `N ≠ 0`.**  For a number field `K` and `x ∈ 𝓞 K` with `x ≠ 0`, the rational-integer
norm `Algebra.norm ℤ x` is nonzero.  (In the bad-prime application `x = f(ζ) ≠ 0` because
`deg f < φ(m) = deg (minpoly ℚ ζ)` and `f ≠ 0`.) -/
theorem norm_int_ne_zero_of_ne_zero {x : 𝓞 K} (hx : x ≠ 0) : Algebra.norm ℤ x ≠ 0 := by
  intro h
  have hcoe : (Algebra.norm ℤ x : ℚ) = 0 := by rw [h]; simp
  rw [Algebra.coe_norm_int] at hcoe
  have hxK : (x : K) ≠ 0 := by
    simpa using (RingOfIntegers.coe_eq_zero_iff (K := K)).not.mpr hx
  exact (Algebra.norm_ne_zero_iff).mpr hxK hcoe

/-- The rational-integer norm of `x ∈ 𝓞 K` is, in `𝓞 K`, the product of its Galois conjugates
`σ(x)` over `Gal(K/ℚ)`.  This lifts `Algebra.norm_eq_prod_automorphisms` to the ring of
integers (each conjugate `σ(x)` is again an algebraic integer). -/
theorem norm_int_eq_prod_galRestrictO [IsGalois ℚ K] (x : 𝓞 K) :
    algebraMap ℤ (𝓞 K) (Algebra.norm ℤ x) = ∏ σ : K ≃ₐ[ℚ] K, galRestrictO σ x := by
  apply RingOfIntegers.ext
  rw [show ((algebraMap ℤ (𝓞 K) (Algebra.norm ℤ x) : 𝓞 K) : K)
        = algebraMap ℚ K (Algebra.norm ℚ (x:K)) from ?_]
  · rw [norm_eq_prod_automorphisms]; push_cast
    apply Finset.prod_congr rfl; intro σ _; simp
  · rw [← Algebra.coe_norm_int]; simp

/-! ### Descent of integer divisibility from `𝓞 K` to `ℤ` -/

/-- If `a ∣ b` in `𝓞 K` for rational integers `a, b` with `a ≠ 0`, then `a ∣ b` in `ℤ`.  The
witness `c = b/a ∈ 𝓞 K` lies in `ℚ`, and `ℤ` is integrally closed in `ℚ`, so `c ∈ ℤ`. -/
theorem int_dvd_of_dvd_in_ringOfIntegers {a b : ℤ} (ha : a ≠ 0)
    (h : (algebraMap ℤ (𝓞 K)) a ∣ (algebraMap ℤ (𝓞 K)) b) : a ∣ b := by
  obtain ⟨c, hc⟩ := h
  have hcK : (b : K) = (a : K) * ((c : 𝓞 K) : K) := by
    have h2 := congrArg (algebraMap (𝓞 K) K) hc
    push_cast at h2 ⊢; simpa using h2
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha
  set q : ℚ := (b : ℚ) / (a : ℚ) with hq
  have hmapq : algebraMap ℚ K q = (b : K) / (a : K) := by rw [hq, map_div₀]; norm_num
  have hcq : ((c : 𝓞 K) : K) = algebraMap ℚ K q := by
    rw [hmapq, eq_div_iff haK, mul_comm]; exact hcK.symm
  have hint : IsIntegral ℤ (((c : 𝓞 K) : K)) := c.2
  rw [hcq] at hint
  have hintq : IsIntegral ℤ q := IsIntegral.tower_bot_of_field hint
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hintq
  have hmq : (m : ℚ) = (b : ℚ) / (a : ℚ) := by rw [← hq, ← hm]; simp
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hbq : (b : ℚ) = (a : ℚ) * (m : ℚ) := by rw [hmq]; field_simp
  exact ⟨m, by exact_mod_cast hbq⟩

/-! ### (iii): the Galois divisibility theorem -/

/-- **(iii) Galois divisibility (abstract form).**  If `r := #T` distinct automorphisms
`σ ∈ T ⊆ Gal(K/ℚ)` each map `x` into `p · 𝓞 K`, then `p^r ∣ Algebra.norm ℤ x` in `ℤ`. -/
theorem prime_pow_dvd_norm_int_of_conjugates_vanish [IsGalois ℚ K]
    {p : ℕ} (hp : (p : ℤ) ≠ 0) (x : 𝓞 K) (T : Finset (K ≃ₐ[ℚ] K))
    (h : ∀ σ ∈ T, (algebraMap ℤ (𝓞 K) (p : ℤ)) ∣ galRestrictO σ x) :
    (p : ℤ) ^ T.card ∣ Algebra.norm ℤ x := by
  classical
  have hdvdO :
      (algebraMap ℤ (𝓞 K) (p:ℤ)) ^ T.card ∣ algebraMap ℤ (𝓞 K) (Algebra.norm ℤ x) := by
    rw [norm_int_eq_prod_galRestrictO]
    exact pow_card_dvd_prod_of_subset (Finset.subset_univ T) _ h
  rw [← map_pow] at hdvdO
  exact int_dvd_of_dvd_in_ringOfIntegers (pow_ne_zero _ hp) hdvdO

/-- **(ii)+(iii) packaged for the bad-prime gate.**  For an integer polynomial `f`, a primitive
root `ξ : 𝓞 K` with `f(ξ) ≠ 0`, and `r := #T` distinct automorphisms each making
`f(σ ξ) ≡ 0 mod p`, the rational integer `N := Algebra.norm ℤ (f(ξ))` satisfies `p^r ≤ |N|`.
This is `BadPrimeBound.bad_prime_pow_le` with the Galois divisibility input now *proven*. -/
theorem prime_pow_le_norm_aeval [IsGalois ℚ K]
    {p : ℕ} (hp : (p : ℤ) ≠ 0) (ξ : 𝓞 K) (f : Polynomial ℤ)
    (hne : aeval ξ f ≠ 0) (T : Finset (K ≃ₐ[ℚ] K))
    (h : ∀ σ ∈ T, (algebraMap ℤ (𝓞 K) (p : ℤ)) ∣ aeval (galRestrictO σ ξ) f) :
    (p : ℤ) ^ T.card ≤ |Algebra.norm ℤ (aeval ξ f)| := by
  have hNne : Algebra.norm ℤ (aeval ξ f) ≠ 0 := norm_int_ne_zero_of_ne_zero hne
  have h' : ∀ σ ∈ T, (algebraMap ℤ (𝓞 K) (p : ℤ)) ∣ galRestrictO σ (aeval ξ f) := by
    intro σ hσ
    have heq : galRestrictO σ (aeval ξ f) = aeval (galRestrictO σ ξ) f := by
      apply RingOfIntegers.ext
      rw [coe_galRestrictO_aeval σ ξ f]
      rw [show ((aeval (galRestrictO σ ξ) f : 𝓞 K) : K) = aeval ((galRestrictO σ ξ : 𝓞 K):K) f
            from (aeval_algebraMap_apply K (galRestrictO σ ξ) f).symm]
      rw [coe_galRestrictO]
    rw [heq]; exact h σ hσ
  have hdvd : (p : ℤ) ^ T.card ∣ Algebra.norm ℤ (aeval ξ f) :=
    prime_pow_dvd_norm_int_of_conjugates_vanish hp (aeval ξ f) T h'
  exact Int.le_of_dvd (abs_pos.mpr hNne) ((dvd_abs _ _).mpr hdvd)

/-! ### Archimedean size half: `|N| ≤ (Σ|coeff|)^{[K:ℚ]}` -/

/-- The house (largest conjugate modulus) of a root of unity is `≤ 1`. -/
theorem house_rootOfUnity_le_one {u : K} {k : ℕ} (hk : k ≠ 0) (hu : u ^ k = 1) :
    house u ≤ 1 := by
  rw [house_eq_sup', ← NNReal.coe_one, NNReal.coe_le_coe]
  refine Finset.sup'_le _ _ (fun σ _ => ?_)
  rw [Complex.nnnorm_eq_one_of_pow_eq_one (by rw [← map_pow, hu, map_one]) hk]

/-- `house (u^i) ≤ 1` for a root of unity `u`. -/
theorem house_pow_rootOfUnity_le_one {u : K} {k : ℕ} (hk : k ≠ 0) (hu : u ^ k = 1) (i : ℕ) :
    house (u ^ i) ≤ 1 := by
  calc house (u^i) ≤ house u ^ i := house_pow_le u i
    _ ≤ 1 ^ i := by apply pow_le_pow_left₀ (house_nonneg _) (house_rootOfUnity_le_one hk hu)
    _ = 1 := one_pow i

/-- **Archimedean triangle bound for `f(u)` at a root of unity `u`.**
`house (f(u)) ≤ Σ_{i ≤ deg f} |coeff f i|` — specialised to `±1` coefficients of degree `< 2k`
this is `|f(ζ^a)| ≤ 2k`. -/
theorem house_aeval_rootOfUnity_le {u : K} {k : ℕ} (hk : k ≠ 0) (hu : u ^ k = 1)
    (f : Polynomial ℤ) :
    house (aeval u f) ≤ ∑ i ∈ Finset.range (f.natDegree + 1), |(f.coeff i : ℝ)| := by
  rw [aeval_eq_sum_range]
  refine (house_sum_le_sum_house _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [zsmul_eq_mul]
  calc house (((f.coeff i : ℤ) : K) * u ^ i)
      ≤ house ((f.coeff i : ℤ) : K) * house (u ^ i) := house_mul_le _ _
    _ ≤ |(f.coeff i : ℝ)| * 1 := by
        apply mul_le_mul
        · rw [house_intCast]; simp
        · exact house_pow_rootOfUnity_le_one hk hu i
        · exact house_nonneg _
        · positivity
    _ = |(f.coeff i : ℝ)| := by ring

/-- `|N(α)| ≤ house(α)^{[K:ℚ]}`.  (Reproved inline from `RootSumNorm.abs_norm_le_house_pow` to
keep this file's dependency set minimal — Mathlib only.) -/
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

/-! ### The fully assembled UNCONDITIONAL bad-prime bound -/

/-- **The bad-prime bound, fully unconditional.**  Let `K = ℚ(ζ)` be a Galois number field,
`ξ : 𝓞 K` a root of unity of order `k ≠ 0`, and `f ∈ ℤ[X]` with `f(ξ) ≠ 0`.  If `r := #T`
distinct automorphisms `σ ∈ T` each make `f(σ ξ) ≡ 0 mod p`, then
`p^r ≤ (Σ_{i ≤ deg f}|coeff f i|)^{[K:ℚ]}`.

For `f` a `±1` polynomial of degree `< 2k` this is `p^r ≤ (2k)^{φ(4k)}` — the
`BadPrimeBound.bad_prime_pow_le_of_modulus_prod` conclusion with **every** Galois-norm input
(`N ≠ 0`, `p^r ∣ N`, `|N| ≤ …`) now *proven*, not hypothesised. -/
theorem bad_prime_galois_unconditional [IsGalois ℚ K]
    {p k : ℕ} (hp : (p : ℤ) ≠ 0) (hk : k ≠ 0) {ξ : 𝓞 K} (hξ : (ξ : K) ^ k = 1)
    (f : Polynomial ℤ) (hne : aeval ξ f ≠ 0) (T : Finset (K ≃ₐ[ℚ] K))
    (h : ∀ σ ∈ T, (algebraMap ℤ (𝓞 K) (p : ℤ)) ∣ aeval (galRestrictO σ ξ) f) :
    (p : ℝ) ^ T.card ≤ (∑ i ∈ Finset.range (f.natDegree + 1), |(f.coeff i : ℝ)|) ^ finrank ℚ K := by
  -- divisibility half: p^r ≤ |N|
  have hdvd : (p : ℤ) ^ T.card ≤ |Algebra.norm ℤ (aeval ξ f)| :=
    prime_pow_le_norm_aeval hp ξ f hne T h
  have hdvdR : (p : ℝ) ^ T.card ≤ (|Algebra.norm ℤ (aeval ξ f)| : ℝ) := by exact_mod_cast hdvd
  -- size half: |N| = |N(f(ξ))_ℚ| ≤ house(f(ξ))^finrank ≤ (Σ|coeff|)^finrank
  have hNcoe : (|Algebra.norm ℤ (aeval ξ f)| : ℝ) = ((|Algebra.norm ℚ ((aeval ξ f : 𝓞 K):K)| : ℚ) : ℝ) := by
    have hci := Algebra.coe_norm_int (aeval ξ f)
    rw [← hci]
    push_cast
    rfl
  have hsize : ((|Algebra.norm ℚ ((aeval ξ f : 𝓞 K):K)| : ℚ) : ℝ)
      ≤ house ((aeval ξ f : 𝓞 K):K) ^ finrank ℚ K := abs_norm_le_house_pow _
  have hhouse : house ((aeval ξ f : 𝓞 K):K)
      ≤ ∑ i ∈ Finset.range (f.natDegree + 1), |(f.coeff i : ℝ)| := by
    rw [show ((aeval ξ f : 𝓞 K):K) = aeval (ξ:K) f from (aeval_algebraMap_apply K ξ f).symm]
    exact house_aeval_rootOfUnity_le hk hξ f
  have hhousepow : house ((aeval ξ f : 𝓞 K):K) ^ finrank ℚ K
      ≤ (∑ i ∈ Finset.range (f.natDegree + 1), |(f.coeff i : ℝ)|) ^ finrank ℚ K :=
    pow_le_pow_left₀ (house_nonneg _) hhouse _
  calc (p : ℝ) ^ T.card
      ≤ (|Algebra.norm ℤ (aeval ξ f)| : ℝ) := hdvdR
    _ = ((|Algebra.norm ℚ ((aeval ξ f : 𝓞 K):K)| : ℚ) : ℝ) := hNcoe
    _ ≤ house ((aeval ξ f : 𝓞 K):K) ^ finrank ℚ K := hsize
    _ ≤ (∑ i ∈ Finset.range (f.natDegree + 1), |(f.coeff i : ℝ)|) ^ finrank ℚ K := hhousepow

end ArkLib.ProximityGap.BadPrimeGalois
