/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.KummerExtension

/-!
# Factorization Rigidity (proximity-prize δ* optimality core, #407)

Machinery relating "`∏_{z∈S}(X-z)` is `m`-sparse" to "`S` is a union of cosets of `μ_m`", used to
reduce the Kambiré-construction optimality (the δ* lower bracket) to polynomial-in-`Xᵐ` structure.
What is proved here (axiom-clean, from `Polynomial.expand`) is:

* **support face** (`mem_range_expand_iff`): `f ∈ range (expand m)` **iff** every coefficient of
  degree not divisible by `m` vanishes — an iff about coefficients, not about root sets;
* **root face** (`isRoot_smul_of_mem_range_expand`, `isRoot_smul_of_support`): one-way — an
  `m`-sparse polynomial has a root *set* closed under multiplication by any `ω` with `ωᵐ = 1`
  (this says nothing about multiplicities);
* **coset face** (`prod_cosets_eq_expand`, `coeff_prod_cosets_eq_zero`): a converse under explicit
  hypotheses — over a field with a *primitive* `m`-th root of unity, the generating polynomial of a
  multiset that is a union of full `μ_m`-cosets (with multiplicity) is `m`-sparse.

The unqualified equivalence "`∏_{z∈S}(X-z)` is `m`-sparse ⟺ `S` is a union of `μ_m`-cosets" is
**false** without such hypotheses: over `𝔽₂` with `m = 2`, `μ₂ = {1}`, so `S = {1}` is a union of
cosets while `X − 1 ∉ 𝔽₂[X²]`; and root-set invariance ignores multiplicity for a general
polynomial.
-/

namespace ArkLib.ProximityGap.FactorizationRigidity

open Polynomial

variable {R : Type*} [CommRing R]

/-- **Factorization rigidity — support face.** A polynomial is in the image of `expand R m`
(a polynomial in `Xᵐ`, i.e. "`m`-sparse": supported only on degrees divisible by `m`) **iff**
its support lies in the multiples of `m`. -/
theorem mem_range_expand_iff {m : ℕ} (hm : m ≠ 0) (f : R[X]) :
    (∃ g, expand R m g = f) ↔ ∀ n, ¬ m ∣ n → f.coeff n = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ n hn
    rw [coeff_expand (Nat.pos_of_ne_zero hm)]; exact if_neg hn
  · intro h
    refine ⟨contract m f, ?_⟩
    ext n
    rw [coeff_expand (Nat.pos_of_ne_zero hm)]
    split_ifs with hdvd
    · obtain ⟨k, rfl⟩ := hdvd
      rw [Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hm), coeff_contract hm, Nat.mul_comm]
    · exact (h n hdvd).symm

/-- **Factorization rigidity — root face.** If `f = g(Xᵐ)` is a polynomial in `Xᵐ` and `ω` is an
`m`-th root of unity, then the root set of `f` is closed under multiplication by `ω`. Hence the
agreement set of an `m`-sparse near-codeword `Xᵃ + γXᵇ − c` (`a,b` multiples of `m`) is a union of
cosets of `μ_m` — the structural input that turns the bad-scalar count into the subgroup sumset. -/
theorem isRoot_smul_of_mem_range_expand {m : ℕ} {g : R[X]} {ω z : R}
    (hω : ω ^ m = 1) (hz : (expand R m g).IsRoot z) :
    (expand R m g).IsRoot (ω * z) := by
  simp only [IsRoot.def, expand_eval, mul_pow, hω, one_mul] at hz ⊢
  exact hz

/-- Convenience corollary: divisible-support polynomials have `μ_m`-invariant root sets directly. -/
theorem isRoot_smul_of_support {m : ℕ} (hm : m ≠ 0) {f : R[X]} {ω z : R}
    (hsupp : ∀ n, ¬ m ∣ n → f.coeff n = 0) (hω : ω ^ m = 1) (hz : f.IsRoot z) :
    f.IsRoot (ω * z) := by
  obtain ⟨g, rfl⟩ := (mem_range_expand_iff hm f).2 hsupp
  exact isRoot_smul_of_mem_range_expand hω hz

/-- **Factorization rigidity — coset face (a hypothesised converse).** Over a field containing a
*primitive* `m`-th root of unity `ω` (so `μ_m = {ωⁱ : i < m}` has exactly `m` elements), the monic
generating polynomial of a root multiset presented as a multiset-union of **full** `μ_m`-cosets
`t·μ_m` (each coset counted with multiplicity one per element) is `m`-sparse:
`∏_{t∈T} ∏_{i<m} (X − ωⁱt) = expand m (∏_{t∈T} (X − tᵐ))`.

The primitive-root hypothesis is essential: over `𝔽₂` with `m = 2` the only square root of unity
is `1`, so `S = {1}` is a union of `{1}`-cosets, yet `X − 1 ∉ 𝔽₂[X²]`. -/
theorem prod_cosets_eq_expand {K : Type*} [Field K] {m : ℕ} (hm : 0 < m) {ω : K}
    (hω : IsPrimitiveRoot ω m) (T : Multiset K) :
    ((T.bind fun t => (Multiset.range m).map fun i => ω ^ i * t).map fun a => X - C a).prod
      = expand K m ((T.map fun t => X - C (t ^ m)).prod) := by
  rw [Multiset.map_bind, Multiset.prod_bind, map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun t _ => ?_
  simp only [Function.comp_apply, map_sub, expand_X, expand_C]
  rw [X_pow_sub_C_eq_prod hω hm rfl, Finset.prod_eq_multiset_prod, Multiset.map_map]
  rfl

/-- The coset face in `mem_range_expand_iff` form: the generating polynomial of a full
`μ_m`-coset union (primitive `ω`) has support in the multiples of `m`. -/
theorem coeff_prod_cosets_eq_zero {K : Type*} [Field K] {m : ℕ} (hm : 0 < m) {ω : K}
    (hω : IsPrimitiveRoot ω m) (T : Multiset K) (n : ℕ) (hn : ¬ m ∣ n) :
    ((T.bind fun t => (Multiset.range m).map fun i => ω ^ i * t).map
      fun a => X - C a).prod.coeff n = 0 := by
  rw [prod_cosets_eq_expand hm hω T]
  exact (mem_range_expand_iff hm.ne' _).1 ⟨_, rfl⟩ n hn

end ArkLib.ProximityGap.FactorizationRigidity
