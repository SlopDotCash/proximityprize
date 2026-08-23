/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Polynomial roots of monic graded polynomials: integrality + the sharp inner-degree bound

The elementary engine behind [BCIKS20] Claim 5.8 / Appendix A.2 (#304, #138): if a *polynomial*
`γ` (over the fraction field) is a root of a monic `T`-polynomial whose coefficients are graded,
then `γ` has integral coefficients of sharply bounded inner degree.  This replaces the
weighted-valuation / Newton-polygon argument of the paper ("γ solves R = 0, so γ has the same
weight as Y") by two pieces of completely elementary algebra:

* **Integrality** (`exists_map_eq_of_eval_monic_eq_zero`): a polynomial root over the fraction
  field of an integrally closed domain has integral coefficients.  Pure gluing of
  `IsIntegral.of_aeval_monic_of_isIntegral_coeff`, `IsIntegral.coeff`, and
  `IsIntegrallyClosed.isIntegral_iff`.  In the #304/#138 application this *replaces the entire
  `ξ`-order divisibility apparatus* (the `(A.4)` `+1`-bookkeeping): the Hensel coefficients are
  integral because they solve a monic equation, full stop.

* **The graded leading-term bound** (`natDegree_le_of_eval_monic_graded`, outer form;
  `coeff_natDegree_le_of_eval_monic_graded`, inner form): if `P` is monic in `T` of degree `d`
  and its `T^c`-coefficient has degree `≤ s·(d−c)` (the balanced grading; NOTE — audit F-1:
  no in-tree GS producer emits this monic+balanced pair yet: the flat/sloped producers give
  flat or slope-1 budgets on a merely-nonzero interpolant, and monicization costs slope.
  `SectionNewtonGradingSupply` records the open supply item), then any polynomial root `g`
  has degree `≤ s`.  Proof: if `deg g = m > s`, the coefficient of the sum `∑_c P_c·g^c = 0` in top degree
  `m·d` is `lc(g)^d ≠ 0` — every non-monic term has degree
  `≤ s(d−c) + cm < m(d−c) + cm = md`.  This is the Newton-polygon slope-uniqueness argument in
  its most elementary form.

The inner form is transported through `polySwap : R[X][Y] →+* R[X][Y]`, the variable-swap ring
homomorphism, whose entire interface is the single double-coefficient identity
`polySwap_coeff_coeff : ((polySwap g).coeff n).coeff i = (g.coeff i).coeff n`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claim 5.8), Appendix A.2/A.4.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate

namespace ArkLib

namespace PolyRootGradedBound

/-! ## The outer-degree leading-term bound -/

/-- **The graded leading-term bound** (outer form): a polynomial root of a monic graded
polynomial has degree at most the grading slope.  If `P` is monic of degree `d` in the outer
variable with `natDegree (P.coeff c) ≤ s·(d−c)` for `c < d`, then any root `g ∈ A[X]` of `P`
has `natDegree g ≤ s`. -/
theorem natDegree_le_of_eval_monic_graded {A : Type*} [CommRing A] [IsDomain A]
    {P : A[X][Y]} {g : A[X]} {s : ℕ}
    (hmonic : P.Monic)
    (hgrade : ∀ c < P.natDegree, (P.coeff c).natDegree ≤ s * (P.natDegree - c))
    (hroot : Polynomial.eval g P = 0) :
    g.natDegree ≤ s := by
  by_contra hle
  have hms : s < g.natDegree := by omega
  have hg : g ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hms
    omega
  set d := P.natDegree with hd_def
  set m := g.natDegree with hm_def
  have h0 : ∑ c ∈ Finset.range (d + 1), P.coeff c * g ^ c = 0 := by
    rw [← Polynomial.eval_eq_sum_range]
    exact hroot
  have hcoeff0 : ∑ c ∈ Finset.range (d + 1), (P.coeff c * g ^ c).coeff (m * d) = 0 := by
    rw [← Polynomial.finset_sum_coeff, h0, Polynomial.coeff_zero]
  have hzero : ∀ c ∈ Finset.range d, (P.coeff c * g ^ c).coeff (m * d) = 0 := by
    intro c hc
    rw [Finset.mem_range] at hc
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hmul : (P.coeff c * g ^ c).natDegree ≤ (P.coeff c).natDegree + (g ^ c).natDegree :=
      Polynomial.natDegree_mul_le
    have hpow : (g ^ c).natDegree = c * m := by
      rw [Polynomial.natDegree_pow]
    have h1 : (P.coeff c).natDegree ≤ s * (d - c) := hgrade c hc
    have h2 : s * (d - c) < m * (d - c) :=
      Nat.mul_lt_mul_of_pos_right hms (Nat.sub_pos_of_lt hc)
    have h3 : m * d = m * (d - c) + c * m := by
      rw [mul_comm c m, ← Nat.mul_add, Nat.sub_add_cancel hc.le]
    omega
  rw [Finset.sum_range_succ, Finset.sum_eq_zero hzero, zero_add,
    show P.coeff d = 1 from hmonic.coeff_natDegree, one_mul] at hcoeff0
  have hpowc : (g ^ d).coeff (m * d) = g.leadingCoeff ^ d := by
    rw [mul_comm m d, ← Polynomial.natDegree_pow g d, Polynomial.coeff_natDegree,
      Polynomial.leadingCoeff_pow]
  rw [hpowc] at hcoeff0
  exact pow_ne_zero d (Polynomial.leadingCoeff_ne_zero.mpr hg) hcoeff0

/-! ## The variable-swap ring homomorphism -/

section Swap

variable {R : Type*} [CommRing R]

/-- The variable-swap ring homomorphism on `R[X][Y]`: the outer variable goes to the (constant
embedding of the) inner one and vice versa.  Its entire downstream interface is
`polySwap_coeff_coeff`. -/
noncomputable def polySwap : R[X][Y] →+* R[X][Y] :=
  Polynomial.eval₂RingHom (Polynomial.mapRingHom (Polynomial.C : R →+* R[X]))
    (Polynomial.C Polynomial.X)

/-- **The double-coefficient identity for the swap**: coefficients transpose. -/
theorem polySwap_coeff_coeff (g : R[X][Y]) (n i : ℕ) :
    ((polySwap g).coeff n).coeff i = (g.coeff i).coeff n := by
  classical
  rw [polySwap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  rw [Polynomial.finset_sum_coeff]
  rw [Polynomial.finset_sum_coeff]
  have hterm : ∀ j ∈ g.support,
      (((Polynomial.mapRingHom (Polynomial.C : R →+* R[X])) (g.coeff j) *
        Polynomial.C Polynomial.X ^ j).coeff n).coeff i
      = if i = j then (g.coeff j).coeff n else 0 := by
    intro j _
    rw [← map_pow, Polynomial.coeff_mul_C, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_ite_eq g.support i (fun j => (g.coeff j).coeff n)]
  by_cases hi : i ∈ g.support
  · rw [if_pos hi]
  · rw [if_neg hi, Polynomial.notMem_support_iff.mp hi, Polynomial.coeff_zero]

/-- Outer degree of the swap is bounded by any uniform inner-degree bound. -/
theorem natDegree_polySwap_le (g : R[X][Y]) {N : ℕ}
    (h : ∀ i, (g.coeff i).natDegree ≤ N) : (polySwap g).natDegree ≤ N := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  ext i
  rw [polySwap_coeff_coeff, Polynomial.coeff_zero]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (h i) hn)

/-- Inner degrees are bounded by the outer degree of the swap. -/
theorem coeff_natDegree_le_natDegree_polySwap (g : R[X][Y]) (i : ℕ) :
    (g.coeff i).natDegree ≤ (polySwap g).natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have h := polySwap_coeff_coeff g n i
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn, Polynomial.coeff_zero] at h
  exact h.symm

end Swap

/-! ## The inner-degree graded root bound -/

/-- **The graded leading-term bound, inner form** (the [BCIKS20] Claim-5.8 shape): if
`P : (B[X][Y])[Y]` is monic of degree `d` in the outermost variable and every coefficient
satisfies the *inner* grading `natDegree ((P.coeff c).coeff j) ≤ s·(d−c)` (the balanced
Guruswami–Sudan grading with slope `s`), then every coefficient of a polynomial root
`g ∈ B[X][Y]` has inner degree at most `s`:  `natDegree (g.coeff j) ≤ s` for all `j`. -/
theorem coeff_natDegree_le_of_eval_monic_graded {B : Type*} [CommRing B] [IsDomain B]
    {P : Polynomial (B[X][Y])} {g : B[X][Y]} {s : ℕ}
    (hmonic : P.Monic)
    (hgrade : ∀ c < P.natDegree, ∀ j, ((P.coeff c).coeff j).natDegree ≤ s * (P.natDegree - c))
    (hroot : Polynomial.eval g P = 0) :
    ∀ j, (g.coeff j).natDegree ≤ s := by
  classical
  -- transport along the swap
  have hswaproot : Polynomial.eval (polySwap g) (P.map (polySwap : B[X][Y] →+* B[X][Y])) = 0 := by
    have h := Polynomial.hom_eval₂ P (RingHom.id _) (polySwap : B[X][Y] →+* B[X][Y]) g
    rw [RingHom.comp_id, Polynomial.eval₂_id, hroot, map_zero] at h
    rw [Polynomial.eval_map]
    exact h.symm
  have hswapmonic : (P.map (polySwap : B[X][Y] →+* B[X][Y])).Monic :=
    hmonic.map _
  have hswapdeg : (P.map (polySwap : B[X][Y] →+* B[X][Y])).natDegree = P.natDegree :=
    hmonic.natDegree_map _
  have hswapgrade : ∀ c < (P.map (polySwap : B[X][Y] →+* B[X][Y])).natDegree,
      ((P.map (polySwap : B[X][Y] →+* B[X][Y])).coeff c).natDegree
        ≤ s * ((P.map (polySwap : B[X][Y] →+* B[X][Y])).natDegree - c) := by
    intro c hc
    rw [hswapdeg] at hc ⊢
    rw [Polynomial.coeff_map]
    exact natDegree_polySwap_le _ (fun j => hgrade c hc j)
  have hbound : (polySwap g).natDegree ≤ s :=
    natDegree_le_of_eval_monic_graded hswapmonic hswapgrade hswaproot
  exact fun j => (coeff_natDegree_le_natDegree_polySwap g j).trans hbound

/-! ## Integrality of polynomial roots over an integrally closed domain -/

attribute [local instance] Polynomial.algebra

/-- **Integrality of polynomial roots** ([BCIKS20] Appendix A.4, the `ξ`-divisibility content,
for free): if `γ` is a polynomial over the fraction field `S` of an integrally closed domain
`R` and `γ` is a root of a monic `P ∈ R[X][Y]` (mapped to `S[X][Y]`), then `γ` is the image of a
polynomial over `R`. -/
theorem exists_map_eq_of_eval_monic_eq_zero {R S : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [Algebra R S] [IsFractionRing R S]
    {γ : Polynomial S} {P : R[X][Y]}
    (hmonic : P.Monic) (hd : P.natDegree ≠ 0)
    (hroot : Polynomial.eval γ
      (P.map (Polynomial.mapRingHom (algebraMap R S))) = 0) :
    ∃ g : R[X], g.map (algebraMap R S) = γ := by
  classical
  haveI : IsDomain S := IsFractionRing.isDomain R
  have hint : IsIntegral (Polynomial R) γ := by
    refine IsIntegral.of_aeval_monic_of_isIntegral_coeff
      (p := P.map (Polynomial.mapRingHom (algebraMap R S))) (hmonic.map _) ?_ ?_ ?_
    · rw [hmonic.natDegree_map]
      exact hd
    · rw [hroot]
      exact isIntegral_zero
    · intro i
      rw [Polynomial.coeff_map]
      exact isIntegral_algebraMap
  have hcoeff : ∀ i, IsIntegral R (γ.coeff i) := fun i => hint.coeff i
  have hlift : ∀ i, γ.coeff i ∈ Set.range (algebraMap R S) := fun i => by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hcoeff i)
    exact ⟨y, hy⟩
  obtain ⟨g, hg⟩ := (Polynomial.mem_lifts γ).mp ((Polynomial.lifts_iff_coeff_lifts γ).mpr hlift)
  exact ⟨g, hg⟩

/-! ## The grand capstone: integral coefficients of sharply bounded inner degree -/

/-- **The Claim-5.8 engine**: let `B` be an integrally closed domain (e.g. a field), `S` the
fraction field of `B[X]`, and `P` a monic polynomial over `B[X][Y]` of positive degree carrying
the balanced slope-`s` grading.  Then any polynomial root `γ ∈ S[X]` of `P` descends to
`g ∈ B[X][Y]` (integrality — the `ξ`-divisibility for free) with every coefficient of inner
degree at most `s` (the sharp Claim-5.8 degree bound). -/
theorem exists_graded_preimage_of_eval_monic_eq_zero {B S : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [CommRing S] [Algebra (Polynomial B) S]
    [IsFractionRing (Polynomial B) S]
    {γ : Polynomial S} {P : Polynomial (B[X][Y])} {s : ℕ}
    (hmonic : P.Monic) (hd : P.natDegree ≠ 0)
    (hgrade : ∀ c < P.natDegree, ∀ j, ((P.coeff c).coeff j).natDegree ≤ s * (P.natDegree - c))
    (hroot : Polynomial.eval γ
      (P.map (Polynomial.mapRingHom (algebraMap (Polynomial B) S))) = 0) :
    ∃ g : B[X][Y], g.map (algebraMap (Polynomial B) S) = γ ∧
      ∀ j, (g.coeff j).natDegree ≤ s := by
  classical
  obtain ⟨g, hg⟩ := exists_map_eq_of_eval_monic_eq_zero (R := Polynomial B) (S := S)
    hmonic hd hroot
  refine ⟨g, hg, ?_⟩
  -- descend the root identity to `B[X][Y]` along the injective coefficient map
  have hinj : Function.Injective (algebraMap (Polynomial B) S) :=
    IsFractionRing.injective _ _
  have hmapinj : Function.Injective
      (Polynomial.map (algebraMap (Polynomial B) S) : B[X][Y] → Polynomial S) :=
    Polynomial.map_injective _ hinj
  have hrootg : Polynomial.eval g P = 0 := by
    apply hmapinj
    rw [Polynomial.map_zero]
    calc (Polynomial.eval g P).map (algebraMap (Polynomial B) S)
        = Polynomial.eval₂ (Polynomial.mapRingHom (algebraMap (Polynomial B) S))
            (g.map (algebraMap (Polynomial B) S)) P := by
          rw [← Polynomial.eval₂_id,
            show (Polynomial.eval₂ (RingHom.id _) g P).map (algebraMap (Polynomial B) S)
              = (Polynomial.mapRingHom (algebraMap (Polynomial B) S))
                  (Polynomial.eval₂ (RingHom.id _) g P) from rfl,
            Polynomial.hom_eval₂, RingHom.comp_id]
          rfl
      _ = Polynomial.eval (g.map (algebraMap (Polynomial B) S))
            (P.map (Polynomial.mapRingHom (algebraMap (Polynomial B) S))) := by
          rw [Polynomial.eval_map]
      _ = 0 := by rw [hg]; exact hroot
  exact coeff_natDegree_le_of_eval_monic_graded hmonic hgrade hrootg

end PolyRootGradedBound

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.PolyRootGradedBound.natDegree_le_of_eval_monic_graded
#print axioms ArkLib.PolyRootGradedBound.polySwap_coeff_coeff
#print axioms ArkLib.PolyRootGradedBound.natDegree_polySwap_le
#print axioms ArkLib.PolyRootGradedBound.coeff_natDegree_le_natDegree_polySwap
#print axioms ArkLib.PolyRootGradedBound.coeff_natDegree_le_of_eval_monic_graded
#print axioms ArkLib.PolyRootGradedBound.exists_map_eq_of_eval_monic_eq_zero
#print axioms ArkLib.PolyRootGradedBound.exists_graded_preimage_of_eval_monic_eq_zero
