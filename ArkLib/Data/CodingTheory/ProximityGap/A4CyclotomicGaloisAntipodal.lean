/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic

/-!
# A4 cyclotomic-Galois antipodal: `e₂(S)=0 ⟹ σ(P(ζ)) = ±P(ζ)` (#407)

THREAD A4 (cyclotomic Galois). For `S ⊆ μ_n` (`n = 2^μ`), the period
`P(ζ) = ∑_{x∈S} x ∈ ℤ[ζ_n]`.  The order-2 Galois element `σ : ζ ↦ −ζ` of
`ℚ(ζ_n)/ℚ(ζ_{n/2})` acts on each root `x = ζ^a` by `x ↦ (−1)^a x = ±x`.

The chain the THREAD specifies:

```
e₂(S) = 0  ⟺  P(ζ)² = P(ζ²)            (Newton: p₁² = p₂ + 2 e₂)
P(ζ²) ∈ ℤ[ζ_{n/2}] = fixed field of σ   (σ(ζ²) = (−ζ)² = ζ², so each x² is σ-fixed)
⟹ P(ζ)² is σ-fixed
⟹ σ(P(ζ))² = P(ζ)²
⟹ σ(P(ζ)) = ± P(ζ)                       (domain: a² = b² ⟹ a = ±b)
```

This file formalizes that chain.  We isolate the genuine algebraic content as a
char-free ring lemma (`aut_apply_eq_pm`) and then instantiate it with the
cyclotomic data: `σ` a ring automorphism whose action on each root is `±`
(exactly what `σ : ζ ↦ −ζ` does on monomials `ζ^a`).  Char-free; works for any
domain, any abelian period.  Mathlib supplies the Galois automorphism existence
(`IsPrimitiveRoot` / `IsCyclotomicExtension`); here we take `σ` as given and
verify the σ-fixedness of `P(ζ²)` purely algebraically — that is the load-bearing
cyclotomic step (`σ(x²) = x²` because `σ x = ± x`) — and we *ground* the `±`
hypothesis (`rootsActPM_of_aut_neg_zeta`) in the two defining facts of that
automorphism (`σ ζ = −ζ`, `S ⊆ ⟨ζ⟩`).

It complements the in-tree char-free even/odd crux
`ProximityGap.EvenOddAntipodal.image_neg_eq_of_prod_comp_neg` (all *odd* `eᵢ = 0`
⟹ `S = −S`, set-level antipodality): A4 here is the **Galois/period** half — the
single `e₂ = 0` constraint forces the *period* to be antipodally fixed up to sign,
`σ(P(ζ)) = ±P(ζ)`, the functional equation feeding the `r = 2` Gauss-period moment.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.  Issue #407.
-/

open Finset

namespace ArkLib.ProximityGap.A4CyclotomicGalois

/-! ## Layer 1 — the char-free algebraic core (square-fixed ⟹ image is ±) -/

variable {R : Type*}

/-- **The algebraic core.**  If a ring hom `σ` fixes `u = t²`, then `σ t` and `t`
have equal squares.  (No domain needed yet.) -/
theorem aut_sq_eq_sq [CommRing R] (σ : R →+* R) (t u : R)
    (htu : t ^ 2 = u) (hfix : σ u = u) :
    (σ t) ^ 2 = t ^ 2 := by
  have : (σ t) ^ 2 = σ (t ^ 2) := by rw [map_pow]
  rw [this, htu, hfix, ← htu]

/-- **The char-free antipodal endpoint.**  In a domain, if a ring hom `σ` fixes
`u = t²`, then `σ t = t` or `σ t = −t`. -/
theorem aut_apply_eq_pm [CommRing R] [IsDomain R] (σ : R →+* R) (t u : R)
    (htu : t ^ 2 = u) (hfix : σ u = u) :
    σ t = t ∨ σ t = -t := by
  have hsq : (σ t) ^ 2 = t ^ 2 := aut_sq_eq_sq σ t u htu hfix
  have hfac : (σ t - t) * (σ t + t) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)

/-! ## Layer 2 — Newton: `e₂(S) = 0 ⟺ (∑x)² = ∑x²` (char-free) -/

variable {F : Type*} [CommRing F] [DecidableEq F]

/-- The off-diagonal product sum `e2off S = ∑_{x∈S} ∑_{y∈S.erase x} x·y`, which equals
`2·e₂(S)` in any commutative ring (char-free).  We use this rather than `e₂` itself to keep
the Newton identity division-free (no `/2`), hence valid in every characteristic. -/
noncomputable def e2off (S : Finset F) : F :=
  ∑ x ∈ S, ∑ y ∈ S.erase x, x * y

/-- **Newton's identity, char-free form.**  `(∑_{x∈S} x)² = ∑_{x∈S} x² + e2off S`,
where `e2off S = 2·e₂(S)` is the off-diagonal product sum.  Hence
`(∑x)² = ∑x² ⟺ e2off S = 0`. -/
theorem sq_sum_eq_sum_sq_add_e2off (S : Finset F) :
    (∑ x ∈ S, x) ^ 2 = (∑ x ∈ S, x ^ 2) + e2off S := by
  classical
  rw [sq, Finset.sum_mul_sum]
  unfold e2off
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x hx
  -- inner: ∑_{y∈S} x*y = x² + ∑_{y∈S.erase x} x*y, via add_sum_erase splitting off the diagonal.
  rw [← Finset.add_sum_erase S (fun y => x * y) hx]
  congr 1
  rw [← sq]

/-- **`e2off` vanishes ⟺ the period squares to the power-sum.**  Direct corollary of Newton:
`e2off S = 0 ↔ (∑x)² = ∑x²`. -/
theorem e2off_eq_zero_iff_sq_period (S : Finset F) :
    e2off S = 0 ↔ (∑ x ∈ S, x) ^ 2 = (∑ x ∈ S, x ^ 2) := by
  rw [sq_sum_eq_sum_sq_add_e2off]
  constructor
  · intro h; rw [h, add_zero]
  · intro h
    -- h : (∑ x²) + e2off = (∑ x²); cancel the power-sum.
    have h' : (∑ x ∈ S, x ^ 2) + e2off S = (∑ x ∈ S, x ^ 2) + 0 := by
      rw [add_zero]; exact h
    exact add_left_cancel h'

/-! ## Layer 3 — the cyclotomic instantiation: `σ : ζ ↦ −ζ` acts as `±` on roots

For `S ⊆ μ_n`, write `S = {ζ^{a₁},…}`.  The order-2 Galois element `σ : ζ ↦ −ζ` of
`ℚ(ζ_n)/ℚ(ζ_{n/2})` sends `x = ζ^a ↦ (−ζ)^a = (−1)^a ζ^a = ± x`.  We capture this as the
hypothesis `RootsActPM σ S : ∀ x ∈ S, σ x = x ∨ σ x = −x` — exactly what the antipodal `σ`
provides on each monomial.  The consequence `σ(x²) = x²` (each `x²` lands in the fixed field
`ℚ(ζ_{n/2})`, since `σ(ζ²) = ζ²`) is then immediate, so the power-sum `u = ∑ x²` is σ-fixed. -/

variable {K : Type*} [Field K]

/-- The action of `σ : ζ ↦ −ζ` is `±` on every root of `S` (the antipodal Galois action on
monomials `ζ^a ↦ (−1)^a ζ^a`).  This is the load-bearing cyclotomic hypothesis. -/
def RootsActPM (σ : K →+* K) (S : Finset K) : Prop :=
  ∀ x ∈ S, σ x = x ∨ σ x = -x

/-- The period `P(ζ) = ∑_{x∈S} x` of `S`. -/
noncomputable def period (S : Finset K) : K := ∑ x ∈ S, x

/-- **σ fixes every square `x²` for `x ∈ S`** (`σ(ζ^{2a}) = ζ^{2a}`): the `±` action squares
away.  Hence the power-sum `∑ x²` lands in the fixed field of `σ`. -/
theorem aut_fixes_sq_of_rootsActPM {σ : K →+* K} {S : Finset K}
    (h : RootsActPM σ S) {x : K} (hx : x ∈ S) :
    σ (x ^ 2) = x ^ 2 := by
  rw [map_pow]
  rcases h x hx with hpos | hneg
  · rw [hpos]
  · rw [hneg]; ring

/-- **σ fixes the power-sum `∑_{x∈S} x²`** (which is `P(ζ²) ∈ ℚ(ζ_{n/2}) =` fixed field of `σ`). -/
theorem aut_fixes_powerSum_of_rootsActPM {σ : K →+* K} {S : Finset K}
    (h : RootsActPM σ S) :
    σ (∑ x ∈ S, x ^ 2) = ∑ x ∈ S, x ^ 2 := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun x hx => aut_fixes_sq_of_rootsActPM h hx)

/-- **The A4 cyclotomic-Galois antipodal closure.**  For a finite set `S ⊆ μ_n` of a field `K`
and a ring automorphism `σ` whose action on each root is `±` (the order-2 Galois element
`σ : ζ ↦ −ζ` of `ℚ(ζ_n)/ℚ(ζ_{n/2})`), if the second elementary symmetric function vanishes
(`e2off S = 0`, i.e. `e₂(S) = 0`), then the period `P(ζ) = ∑_{x∈S} x` is sent to `±` itself:
`σ(P(ζ)) = P(ζ)` or `σ(P(ζ)) = −P(ζ)`.

This is precisely the THREAD chain:
`e₂=0 ⟹ P(ζ)² = P(ζ²)`; `P(ζ²) = ∑ x²` is σ-fixed; so `σ(P(ζ))² = P(ζ)²`; so `σ(P(ζ)) = ±P(ζ)`. -/
theorem aut_period_eq_pm_of_e2off_zero [DecidableEq K] {σ : K →+* K} {S : Finset K}
    (hpm : RootsActPM σ S) (he2 : e2off S = 0) :
    σ (period S) = period S ∨ σ (period S) = -period S := by
  -- e₂ = 0 gives P(ζ)² = ∑ x² =: u, and u is σ-fixed.
  have hsq : (period S) ^ 2 = ∑ x ∈ S, x ^ 2 :=
    (e2off_eq_zero_iff_sq_period S).mp he2
  have hfix : σ (∑ x ∈ S, x ^ 2) = ∑ x ∈ S, x ^ 2 :=
    aut_fixes_powerSum_of_rootsActPM hpm
  exact aut_apply_eq_pm σ (period S) (∑ x ∈ S, x ^ 2) hsq hfix

/-! ## Layer 4 — grounding `RootsActPM`: the genuine antipodal automorphism `σ : ζ ↦ −ζ`

The hypothesis `RootsActPM σ S` is exactly what the order-2 Galois element `σ : ζ ↦ −ζ`
provides on `S ⊆ μ_n = ⟨ζ⟩`.  Here we *prove* `RootsActPM` from the two defining facts of that
automorphism: `σ ζ = −ζ`, and each `x ∈ S` is a power `x = ζ^a`.  Indeed
`σ(ζ^a) = (σ ζ)^a = (−ζ)^a = (−1)^a ζ^a = ± ζ^a`. -/

/-- A single monomial's `±` action: `σ ζ = −ζ ⟹ σ(ζ^a) = ± ζ^a` (sign `(−1)^a`). -/
theorem aut_pow_eq_pm {σ : K →+* K} {ζ : K} (hζ : σ ζ = -ζ) (a : ℕ) :
    σ (ζ ^ a) = ζ ^ a ∨ σ (ζ ^ a) = -(ζ ^ a) := by
  rw [map_pow, hζ, neg_pow]
  rcases Nat.even_or_odd a with he | ho
  · exact Or.inl (by rw [he.neg_one_pow, one_mul])
  · exact Or.inr (by rw [ho.neg_one_pow, neg_one_mul])

/-- **`RootsActPM` from the antipodal automorphism.**  If `σ ζ = −ζ` and every `x ∈ S` is a
power of `ζ` (i.e. `S ⊆ ⟨ζ⟩ = μ_n`), then `σ` acts as `±` on every root of `S`.  This grounds
the load-bearing hypothesis of `aut_period_eq_pm_of_e2off_zero` in the actual cyclotomic Galois
element of `ℚ(ζ_n)/ℚ(ζ_{n/2})`. -/
theorem rootsActPM_of_aut_neg_zeta {σ : K →+* K} {ζ : K} {S : Finset K}
    (hζ : σ ζ = -ζ) (hpow : ∀ x ∈ S, ∃ a : ℕ, x = ζ ^ a) :
    RootsActPM σ S := by
  intro x hx
  obtain ⟨a, rfl⟩ := hpow x hx
  exact aut_pow_eq_pm hζ a

/-- **End-to-end A4 (cyclotomic-grounded).**  For `S ⊆ μ_n = ⟨ζ⟩` and the order-2 Galois
element `σ : ζ ↦ −ζ`, if `e₂(S) = 0` then the period `P(ζ) = ∑_{x∈S} x` satisfies
`σ(P(ζ)) = ± P(ζ)`.  The hypotheses are exactly the cyclotomic data; the conclusion is the
THREAD's antipodal functional equation. -/
theorem aut_period_eq_pm_of_e2off_zero_zeta [DecidableEq K]
    {σ : K →+* K} {ζ : K} {S : Finset K}
    (hζ : σ ζ = -ζ) (hpow : ∀ x ∈ S, ∃ a : ℕ, x = ζ ^ a) (he2 : e2off S = 0) :
    σ (period S) = period S ∨ σ (period S) = -period S :=
  aut_period_eq_pm_of_e2off_zero (rootsActPM_of_aut_neg_zeta hζ hpow) he2

end ArkLib.ProximityGap.A4CyclotomicGalois

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.A4CyclotomicGalois.aut_apply_eq_pm
#print axioms ArkLib.ProximityGap.A4CyclotomicGalois.sq_sum_eq_sum_sq_add_e2off
#print axioms ArkLib.ProximityGap.A4CyclotomicGalois.e2off_eq_zero_iff_sq_period
#print axioms ArkLib.ProximityGap.A4CyclotomicGalois.aut_fixes_powerSum_of_rootsActPM
#print axioms ArkLib.ProximityGap.A4CyclotomicGalois.aut_period_eq_pm_of_e2off_zero
#print axioms ArkLib.ProximityGap.A4CyclotomicGalois.aut_pow_eq_pm
#print axioms ArkLib.ProximityGap.A4CyclotomicGalois.rootsActPM_of_aut_neg_zeta
#print axioms ArkLib.ProximityGap.A4CyclotomicGalois.aut_period_eq_pm_of_e2off_zero_zeta
