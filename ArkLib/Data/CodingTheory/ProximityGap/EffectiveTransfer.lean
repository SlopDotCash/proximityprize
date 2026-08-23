/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Issue #232 — O49: the effective characteristic-zero → `F_p` transfer, machine-checked

The O48 tower theorem pins the multi-symmetric fiber `{S : e₁(S) = ⋯ = e_t(S) = 0}` on
2-power-torsion domains **in characteristic zero**.  DISPROOF_LOG entry O49 records the
elementary norm argument transporting it to `F_p` above an explicit height threshold:

> If `e_j` of a lifted subset is nonzero in `ℤ[ζ_n]`, its algebraic norm is a nonzero
> integer of absolute value at most `C(w,j)^φ(n)`, so `p` above that bound cannot kill it.

This file machine-checks that argument end to end (tier T1 of the task ladder):

* `norm_embedding_eq_one`, `norm_embedding_sum_le` (**T3**) — every complex embedding sends
  a root of unity to a complex number of modulus `1`, hence sends a sum of `B` roots of
  unity to a complex number of modulus `≤ B`.
* `abs_norm_le`, `intNorm_abs_le` (**T2**) — for an algebraic integer `x` in a number field
  `K` that is a sum of `B` roots of unity, `|N_{K/ℚ}(x)| ≤ B ^ [K : ℚ]`, as an integer
  inequality via `Algebra.norm ℤ`; and `intNorm_ne_zero` — the norm of a nonzero algebraic
  integer is a nonzero integer.
* `dvd_intNorm_of_eq_zero` — if **any** ring homomorphism `𝓞 K →+* ZMod p` (any reduction
  at any prime above `p`) kills `x`, then `p ∣ N_{K/ℚ}(x)` in `ℤ` (uses `x ∣ N(x)` in
  `𝓞 K`, valid since `K/ℚ` is Galois).
* `reduction_ne_zero` (**T1**, general form) — a nonzero sum of `B` roots of unity in a
  Galois number field survives every reduction `𝓞 K →+* ZMod p` once
  `B ^ [K : ℚ] < p`.
* `esymm_reduction_ne_zero`, `esymm_eq_zero_iff`, `esymm_eq_zero_iff_of_middle` (**T1**,
  the O49 statement) — in `K = ℚ(ζ_n)`, for a `w`-element subset `S̃ ⊆ 𝓞 K` of `n`-th
  roots of unity, `e_j(S̃) = 0 ↔ e_j(red S̃) = 0` for every reduction
  `red : 𝓞 K →+* F_p` as soon as `C(w,j)^φ(n) < p` (uniformly in `j` once
  `C(w,⌊w/2⌋)^φ(n) < p`).

Consequently the `F_p` fiber computations of the tower theory agree with the
characteristic-zero fiber for all `p` above the explicit threshold
`C(w,⌊w/2⌋)^φ(n)`: a vanishing `e_j` over `F_p` lifts to a vanishing `e_j` in `ℤ[ζ_n]`
whenever the subset itself lifts (which it does for `n ∣ p − 1`, the cyclic case — the
lift plumbing is the in-tree O42/O53 bijection and is not duplicated here).

The threshold is the one recorded in O49 and is necessary: the `p = 17, n = 16` extra
solutions (O47 data) live below it.

Every theorem is fully proved and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace EffectiveTransfer

open NumberField Module

open scoped NumberField

/-! ### T3 — archimedean bounds: embeddings of sums of roots of unity -/

section Archimedean

variable {K : Type*} [Field K]

/-- A root of unity has modulus `1` under every embedding into `ℂ`. -/
lemma norm_embedding_eq_one (σ : K →+* ℂ) {u : K} {n : ℕ} (hn : 0 < n)
    (hu : u ^ n = 1) : ‖σ u‖ = 1 := by
  have hpow : ‖σ u‖ ^ n = 1 := by
    rw [← norm_pow, ← map_pow, hu, map_one, norm_one]
  rcases lt_trichotomy ‖σ u‖ 1 with h | h | h
  · exact absurd hpow (ne_of_lt (pow_lt_one₀ (norm_nonneg _) h hn.ne'))
  · exact h
  · exact absurd hpow (ne_of_gt (one_lt_pow₀ h hn.ne'))

/-- **T3.** A sum of `B` `n`-th roots of unity has every complex embedding of modulus
at most `B`. -/
theorem norm_embedding_sum_le (σ : K →+* ℂ) {n : ℕ} (hn : 0 < n)
    (t : Multiset K) (ht : ∀ u ∈ t, u ^ n = 1) :
    ‖σ t.sum‖ ≤ (Multiset.card t : ℝ) := by
  rw [map_multiset_sum]
  refine (norm_multiset_sum_le _).trans (le_of_eq ?_)
  rw [Multiset.map_map]
  have h1 : t.map ((fun x : ℂ => ‖x‖) ∘ σ) = t.map (fun _ => (1 : ℝ)) :=
    Multiset.map_congr rfl fun u hu => norm_embedding_eq_one σ hn (ht u hu)
  rw [h1, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]

end Archimedean

/-! ### T2 — the norm bound `|N_{K/ℚ}(x)| ≤ B ^ [K : ℚ]` -/

section NormBound

variable {K : Type*} [Field K] [NumberField K]

/-- **T2 (rational form).** The field norm of a sum of `B` roots of unity in a number
field has absolute value at most `B ^ [K : ℚ]`: the norm is the product of the values at
all `[K : ℚ]` complex embeddings, each of modulus `≤ B` by `norm_embedding_sum_le`. -/
theorem abs_norm_le {n : ℕ} (hn : 0 < n) (t : Multiset K)
    (ht : ∀ u ∈ t, u ^ n = 1) :
    |Algebra.norm ℚ t.sum| ≤ (Multiset.card t : ℚ) ^ finrank ℚ K := by
  have key : algebraMap ℚ ℂ (Algebra.norm ℚ t.sum) = ∏ σ : K →ₐ[ℚ] ℂ, σ t.sum :=
    Algebra.norm_eq_prod_embeddings ℚ ℂ t.sum
  have hnorm : ‖algebraMap ℚ ℂ (Algebra.norm ℚ t.sum)‖
      ≤ (Multiset.card t : ℝ) ^ finrank ℚ K := by
    rw [key, norm_prod]
    calc ∏ σ : K →ₐ[ℚ] ℂ, ‖σ t.sum‖
        ≤ ∏ _σ : K →ₐ[ℚ] ℂ, (Multiset.card t : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _)
            (fun σ _ => norm_embedding_sum_le (σ : K →+* ℂ) hn t ht)
      _ = (Multiset.card t : ℝ) ^ finrank ℚ K := by
          rw [Finset.prod_const, Finset.card_univ, AlgHom.card]
  rw [eq_ratCast (algebraMap ℚ ℂ), Complex.norm_ratCast] at hnorm
  exact_mod_cast hnorm

/-- **T2 (integer form).** For an algebraic integer `x` whose image in `K` is a sum of
`B` roots of unity, `|N_{K/ℚ}(x)| ≤ B ^ [K : ℚ]` as integers. -/
theorem intNorm_abs_le (x : 𝓞 K) {n : ℕ} (hn : 0 < n) (t : Multiset K)
    (hx : (x : K) = t.sum) (ht : ∀ u ∈ t, u ^ n = 1) :
    |Algebra.norm ℤ x| ≤ (Multiset.card t : ℤ) ^ finrank ℚ K := by
  have h := abs_norm_le hn t ht
  rw [← hx, ← Algebra.coe_norm_int x] at h
  exact_mod_cast h

/-- The integer norm of a nonzero algebraic integer is nonzero. -/
theorem intNorm_ne_zero (x : 𝓞 K) (hx : x ≠ 0) : Algebra.norm ℤ x ≠ 0 := by
  intro h
  apply hx
  have h0 : Algebra.norm ℚ (x : K) = 0 := by
    rw [← Algebra.coe_norm_int x, h, Int.cast_zero]
  exact RingOfIntegers.coe_eq_zero_iff.mp (Algebra.norm_eq_zero_iff.mp h0)

end NormBound

/-! ### The reduction-kill lemma: a reduction killing `x` forces `p ∣ N_{K/ℚ}(x)` -/

section Kill

variable {K : Type*} [Field K] [NumberField K]

/-- The morphism-level norm `RingOfIntegers.norm ℚ x : 𝓞 ℚ`, pushed into `𝓞 K`, is the
integer norm `Algebra.norm ℤ x` (as an integer of `𝓞 K`). -/
lemma algebraMap_ringOfIntegersNorm_eq_intCast (x : 𝓞 K) :
    algebraMap (𝓞 ℚ) (𝓞 K) (RingOfIntegers.norm ℚ x) = (Algebra.norm ℤ x : 𝓞 K) := by
  apply NumberField.RingOfIntegers.ext
  rw [RingOfIntegers.coe_algebraMap_norm, ← Algebra.coe_norm_int x]
  simp

/-- **The kill lemma.** If a ring homomorphism `𝓞 K →+* ZMod p` (e.g. reduction at any
prime above `p`) kills `x`, then `p` divides the integer norm of `x`.  Uses
`x ∣ N_{K/ℚ}(x)` in `𝓞 K`, valid since `K/ℚ` is Galois. -/
theorem dvd_intNorm_of_eq_zero [IsGalois ℚ K] {p : ℕ} (φ : 𝓞 K →+* ZMod p)
    {x : 𝓞 K} (h : φ x = 0) :
    (p : ℤ) ∣ Algebra.norm ℤ x := by
  have hdvd : x ∣ algebraMap (𝓞 ℚ) (𝓞 K) (RingOfIntegers.norm ℚ x) :=
    RingOfIntegers.dvd_norm ℚ x
  rw [algebraMap_ringOfIntegersNorm_eq_intCast] at hdvd
  obtain ⟨y, hy⟩ := hdvd
  have hφ : φ ((Algebra.norm ℤ x : ℤ) : 𝓞 K) = 0 := by
    rw [hy, map_mul, h, zero_mul]
  rwa [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at hφ

end Kill

/-! ### T1 — the effective transfer theorem, general Galois form -/

section Transfer

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

/-- **T1 (general form).** Let `x ≠ 0` be an algebraic integer in a Galois number field
`K` whose image in `K` is a sum of `B` `n`-th roots of unity.  Then **no** ring
homomorphism `𝓞 K →+* ZMod p` can kill `x` once `B ^ [K : ℚ] < p`: the integer norm of
`x` is nonzero of absolute value `≤ B ^ [K : ℚ]`, while a kill would force
`p ∣ N_{K/ℚ}(x)`. -/
theorem reduction_ne_zero {p : ℕ} (φ : 𝓞 K →+* ZMod p) {x : 𝓞 K} (hx : x ≠ 0)
    {n : ℕ} (hn : 0 < n) (t : Multiset K) (hxt : (x : K) = t.sum)
    (ht : ∀ u ∈ t, u ^ n = 1)
    (hp : (Multiset.card t : ℤ) ^ finrank ℚ K < (p : ℤ)) :
    φ x ≠ 0 := by
  intro h
  have hN : Algebra.norm ℤ x ≠ 0 := intNorm_ne_zero x hx
  have hle : (p : ℤ) ≤ |Algebra.norm ℤ x| :=
    Int.le_of_dvd (abs_pos.mpr hN) ((dvd_abs _ _).mpr (dvd_intNorm_of_eq_zero φ h))
  have hub : |Algebra.norm ℤ x| ≤ (Multiset.card t : ℤ) ^ finrank ℚ K :=
    intNorm_abs_le x hn t hxt ht
  omega

end Transfer

/-! ### Elementary symmetric polynomial plumbing -/

section Esymm

/-- A product of `n`-th roots of unity is an `n`-th root of unity. -/
lemma pow_prod_eq_one {R : Type*} [CommMonoid R] {n : ℕ} (m : Multiset R)
    (h : ∀ u ∈ m, u ^ n = 1) : m.prod ^ n = 1 := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, mul_pow, h a (Multiset.mem_cons_self a s), one_mul]
    exact ih fun u hu => h u (Multiset.mem_cons_of_mem hu)

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- The image in `K` of the `j`-th elementary symmetric polynomial of a finite set of
algebraic integers is the sum of the `C(w,j)` products over `j`-element sub-multisets of
the image multiset. -/
lemma coe_esymm (S : Finset (𝓞 K)) (j : ℕ) :
    ((S.val.esymm j : 𝓞 K) : K)
      = (((S.val.map (algebraMap (𝓞 K) K)).powersetCard j).map Multiset.prod).sum := by
  simp only [Multiset.esymm]
  rw [RingOfIntegers.coe_eq_algebraMap, map_multiset_sum,
    Multiset.map_map, Multiset.powersetCard_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun m _ => ?_
  exact map_multiset_prod (algebraMap (𝓞 K) K) m

end Esymm

/-! ### T1 at the O49 statement: `e_j` of lifted subsets in `ℚ(ζ_n)` -/

section Cyclotomic

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [CharZero K]
  [IsCyclotomicExtension {n} ℚ K]

/-- **T1, the O49 effective transfer.**  Let `K = ℚ(ζ_n)` and let `S̃ ⊆ 𝓞 K` be a
`w`-element set of `n`-th roots of unity (a lifted subset of `μ_n`).  If
`e_j(S̃) ≠ 0` in `𝓞 K`, then **no** ring homomorphism `𝓞 K →+* ZMod p` (reduction at any
prime above `p`) can kill `e_j(S̃)`, as soon as `p > C(w,j)^φ(n)`:
`e_j(S̃)` is a sum of `C(w,j)` roots of unity, so its norm is a nonzero integer of
absolute value at most `C(w,j)^φ(n)`. -/
theorem esymm_reduction_ne_zero {p : ℕ} (φ : 𝓞 K →+* ZMod p)
    (S : Finset (𝓞 K)) (hS : ∀ a ∈ S, (a : K) ^ n = 1) (j : ℕ)
    (hx : S.val.esymm j ≠ 0)
    (hp : (S.card.choose j : ℤ) ^ n.totient < (p : ℤ)) :
    φ (S.val.esymm j) ≠ 0 := by
  haveI : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  -- the multiset of `C(w,j)` products of `j`-element subsets, viewed in `K`
  set t : Multiset K :=
    ((S.val.map (algebraMap (𝓞 K) K)).powersetCard j).map Multiset.prod with hts
  have hcard : Multiset.card t = S.card.choose j := by
    rw [hts, Multiset.card_map, Multiset.card_powersetCard, Multiset.card_map]
    rfl
  have ht : ∀ u ∈ t, u ^ n = 1 := by
    intro u hu
    obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp hu
    refine pow_prod_eq_one m fun v hv => ?_
    have hvS : v ∈ S.val.map (algebraMap (𝓞 K) K) :=
      Multiset.mem_of_le (Multiset.mem_powersetCard.mp hm).1 hv
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hvS
    exact hS a ha
  refine reduction_ne_zero φ hx (NeZero.pos n) t (coe_esymm S j) ht ?_
  rw [hcard, IsCyclotomicExtension.Rat.finrank n K]
  exact hp

/-- **The transfer as an equivalence** (the form the tower theory consumes): above the
threshold `C(w,j)^φ(n)`, the `j`-th elementary symmetric polynomial of a lifted subset
vanishes in `ℤ[ζ_n]` **iff** it vanishes after reduction.  Hence the `F_p` fiber
computation agrees with the characteristic-zero fiber of the O48 tower theorem. -/
theorem esymm_eq_zero_iff {p : ℕ} (φ : 𝓞 K →+* ZMod p)
    (S : Finset (𝓞 K)) (hS : ∀ a ∈ S, (a : K) ^ n = 1) (j : ℕ)
    (hp : (S.card.choose j : ℤ) ^ n.totient < (p : ℤ)) :
    S.val.esymm j = 0 ↔ φ (S.val.esymm j) = 0 := by
  constructor
  · intro h; rw [h, map_zero]
  · intro h
    by_contra hx
    exact esymm_reduction_ne_zero φ S hS j hx hp h

/-- **The uniform O49 threshold**: a single bound `p > C(w,⌊w/2⌋)^φ(n)` covers all
windows `j` at once, since `C(w,j) ≤ C(w,⌊w/2⌋)`. -/
theorem esymm_eq_zero_iff_of_middle {p : ℕ} (φ : 𝓞 K →+* ZMod p)
    (S : Finset (𝓞 K)) (hS : ∀ a ∈ S, (a : K) ^ n = 1)
    (hp : (S.card.choose (S.card / 2) : ℤ) ^ n.totient < (p : ℤ)) (j : ℕ) :
    S.val.esymm j = 0 ↔ φ (S.val.esymm j) = 0 := by
  refine esymm_eq_zero_iff φ S hS j (lt_of_le_of_lt ?_ hp)
  have hchoose : (S.card.choose j : ℤ) ≤ (S.card.choose (S.card / 2) : ℤ) := by
    exact_mod_cast Nat.choose_le_middle j S.card
  exact pow_le_pow_left₀ (by positivity) hchoose _

end Cyclotomic

-- The `respectTransparency` relaxation is the same one Mathlib itself uses to
-- instantiate `IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ)` concretely
-- (cf. `fermatLastTheoremThree` in `Mathlib.NumberTheory.FLT.Three`): the `ℚ`-algebra
-- structure on `CyclotomicField n ℚ` reaches the instance only up to reducible defeq.
set_option backward.isDefEq.respectTransparency false in
/-- Concrete instantiation at `K := CyclotomicField n ℚ` (all instances resolve; the
headline transfer is non-vacuous). -/
theorem esymm_eq_zero_iff_cyclotomicField {n : ℕ} [NeZero n] {p : ℕ}
    (φ : 𝓞 (CyclotomicField n ℚ) →+* ZMod p)
    (S : Finset (𝓞 (CyclotomicField n ℚ)))
    (hS : ∀ a ∈ S, (a : CyclotomicField n ℚ) ^ n = 1) (j : ℕ)
    (hp : (S.card.choose j : ℤ) ^ n.totient < (p : ℤ)) :
    S.val.esymm j = 0 ↔ φ (S.val.esymm j) = 0 :=
  esymm_eq_zero_iff φ S hS j hp

end EffectiveTransfer
