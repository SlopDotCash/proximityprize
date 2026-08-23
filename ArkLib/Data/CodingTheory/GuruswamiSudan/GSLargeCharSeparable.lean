/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.Hab25SeparableSupply
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Expand

/-!
# Large-characteristic separability: [BCIKS20] Appendix C is vacuous when `char F > deg_Y`

The characteristic-zero capstones of the Hab25 §3 / [BCIKS20] §5 separability layer
(`GSSeparabilityCharZero.lean`, `GSSquarefreePart.lean`, `Hab25SeparableSupply.lean`) used
`CharZero F` for exactly one thing: the fraction field `K(X)` (`K = F(Z)`) is then perfect,
so irreducible polynomials are separable. This file replaces that supply with the **degree
versus characteristic** case split: over *any* field `L`, an irreducible polynomial of
positive degree `< char L` is separable — inseparability forces `derivative = 0`, hence
membership in `L[Y^p]` (`Polynomial.expand_contract`), hence `p ∣ deg`, hence `deg ≥ p`.
Since every positive-`Y`-degree irreducible factor of the GS interpolant has
`deg_Y ≤ D/(k−1)`, **for `char F = 0` or `char F > D/(k−1)` every factor is separable in
`Y`** and the inseparable descent of [BCIKS20] Appendix C is vacuous.

## Main results

* `Irreducible.separable_of_natDegree_lt_charP` / `…_lt_ringChar` — over any field, an
  irreducible polynomial `f` with `0 < natDegree f < char` is separable (plus the `char = 0`
  branch). Crucially this holds over *imperfect* fields such as `K = F(Z)`.

* `Polynomial.discr_ne_zero_of_irreducible_of_natDegree_lt_ringChar` — the
  large-characteristic analogue of `discr_ne_zero_of_irreducible_of_perfectField_fractionRing`:
  over a domain `A`, an irreducible `f : A[X]` with `0 < natDegree f` and
  `natDegree f < ringChar (FractionRing A)` (or characteristic zero) has `discr f ≠ 0`.

* `irreducible_discr_ne_zero_of_natDegree_lt_ringChar` — the GS-chain form over
  `K = F(Z)`: irreducible `R ∈ K[X][Y]` with `0 < deg_Y R < char F` (or `char F = 0`) has
  nonzero `Y`-discriminant (`ringChar_fractionRing_eq_ringChar` transports the
  characteristic of `F` up to `Frac(K[X])`).

* `gs_interpolant_good_specialization_largeChar` — the mirror of
  `gs_interpolant_good_specialization_charZero` with `[CharZero F]` replaced by
  `D/(k−1) < ringChar F ∨ ringChar F = 0`: the fully residual-free Step S5.

* `separable_map_radical_of_natDegree_lt_ringChar` (+ `…_of_radical_natDegree_lt`,
  `discr_radical_ne_zero_of_natDegree_lt_ringChar`) — the global (squarefree-part) S5
  supply at large characteristic, mirrors of `separable_map_radical` /
  `discr_radical_ne_zero` without `[PerfectField]`.

* `gs_interpolant_squarefree_discr_largeChar` — mirror of
  `gs_interpolant_squarefree_discr_charZero`: the paper's global `disc_Y(Q̃) ≠ 0` holds
  whenever `D/(k−1) < char F` (or `char F = 0`).

* `radical_rep_good_specialization_largeChar` — mirror of
  `radical_rep_good_specialization_charZero` (the good-`z` supply for the S6→S8 weld) with
  `[CharZero F]` replaced by `deg_Y Q < ringChar F ∨ ringChar F = 0`.

All statements subsume their characteristic-zero ancestors via the `ringChar F = 0` branch.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654 — §5 Steps 5–7 and Appendix C (the inseparable descent made
  vacuous here at large characteristic).
* [Hab25] Habermehl, *…*, ePrint 2025/2110 — §3 Steps S5–S6.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate UniqueFactorizationMonoid

/-! ## Generic field-theory bricks: irreducible + small degree ⇒ separable -/

namespace Polynomial

/-- **Irreducible polynomials of degree below the characteristic are separable**, over any
field (perfect or not). If `f` were inseparable then `derivative f = 0`, so `f` lies in
`L[X^p]` (`expand_contract`), forcing `p ∣ natDegree f` and hence `natDegree f ≥ p`. -/
theorem _root_.Irreducible.separable_of_natDegree_lt_charP {L : Type*} [Field L]
    (p : ℕ) [CharP L p] {f : L[X]} (hirr : Irreducible f)
    (hdeg : 0 < f.natDegree) (hlt : f.natDegree < p) : f.Separable := by
  rw [Polynomial.separable_iff_derivative_ne_zero hirr]
  intro hder
  have hp0 : p ≠ 0 := by omega
  have hfc : Polynomial.expand L p (Polynomial.contract p f) = f :=
    Polynomial.expand_contract p hder hp0
  have hdeq : f.natDegree = (Polynomial.contract p f).natDegree * p := by
    conv_lhs => rw [← hfc]
    exact Polynomial.natDegree_expand p _
  rcases Nat.eq_zero_or_pos (Polynomial.contract p f).natDegree with h0 | hpos
  · rw [h0, zero_mul] at hdeq
    omega
  · have hge : p ≤ f.natDegree := by
      rw [hdeq]
      exact Nat.le_mul_of_pos_left p hpos
    omega

/-- **The `ringChar`-cased separability supply**: over any field `L`, an irreducible `f`
with `0 < natDegree f` and `natDegree f < ringChar L` *or* `ringChar L = 0` is separable.
This is the exact drop-in replacement for the `[CharZero L]`/`[PerfectField L]` supply
of `Irreducible.separable`, usable over imperfect fields such as `F(Z)(X)`. -/
theorem _root_.Irreducible.separable_of_natDegree_lt_ringChar {L : Type*} [Field L]
    {f : L[X]} (hirr : Irreducible f) (hdeg : 0 < f.natDegree)
    (hchar : f.natDegree < ringChar L ∨ ringChar L = 0) : f.Separable := by
  rcases hchar with hlt | hzero
  · exact hirr.separable_of_natDegree_lt_charP (ringChar L) hdeg hlt
  · haveI : CharZero L := (CharP.ringChar_zero_iff_CharZero L).mp hzero
    exact hirr.separable

/-- **Large-characteristic analogue of
`discr_ne_zero_of_irreducible_of_perfectField_fractionRing`.** Over a domain `A` (with
`NormalizedGCDMonoid` structure), every irreducible `f : A[X]` of positive degree below the
characteristic of `FractionRing A` (or in characteristic zero) has nonzero discriminant:
Gauss transports irreducibility to the fraction field, the degree-versus-characteristic
supply yields separability there, and the converse bridge pulls `discr ≠ 0` back to `A`. -/
theorem discr_ne_zero_of_irreducible_of_natDegree_lt_ringChar
    {A : Type*} [CommRing A] [IsDomain A] [NormalizedGCDMonoid A]
    {f : A[X]} (hirr : Irreducible f) (hdeg : 0 < f.natDegree)
    (hchar : f.natDegree < ringChar (FractionRing A) ∨ ringChar (FractionRing A) = 0) :
    f.discr ≠ 0 := by
  have hprim : f.IsPrimitive := hirr.isPrimitive hdeg.ne'
  have hirr' : Irreducible (f.map (algebraMap A (FractionRing A))) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hinj : Function.Injective (algebraMap A (FractionRing A)) :=
    IsFractionRing.injective A (FractionRing A)
  have hmapdeg : (f.map (algebraMap A (FractionRing A))).natDegree = f.natDegree :=
    natDegree_map_eq_of_injective hinj f
  have hsep : (f.map (algebraMap A (FractionRing A))).Separable :=
    hirr'.separable_of_natDegree_lt_ringChar (by rw [hmapdeg]; exact hdeg)
      (by rw [hmapdeg]; exact hchar)
  exact discr_ne_zero_of_separable_map hinj hdeg hsep

end Polynomial

/-! ## Generic squarefree-part bricks at large characteristic -/

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

section Generic

variable {A : Type*} [CommRing A] [IsDomain A] [NormalizedGCDMonoid A]
  [UniqueFactorizationMonoid A]

/-- **Per-factor separable image at large characteristic** (mirror of
`separable_map_of_mem_primeFactors` without `[PerfectField]`): a distinct normalized prime
factor of `Q : A[X]` of degree below the characteristic of `FractionRing A` (or in
characteristic zero) maps to a separable polynomial of `(FractionRing A)[X]`. -/
lemma separable_map_of_mem_primeFactors_of_natDegree_lt_ringChar
    {Q R : A[X]} (hQ0 : Q ≠ 0) (hR : R ∈ primeFactors Q)
    (hchar : R.natDegree < ringChar (FractionRing A) ∨ ringChar (FractionRing A) = 0) :
    (R.map (algebraMap A (FractionRing A))).Separable := by
  obtain ⟨hirr, -, -⟩ :=
    (mem_normalizedFactors_iff' hQ0).mp (mem_primeFactors.mp hR)
  by_cases hdeg : R.natDegree = 0
  · -- degree-zero prime factor: the image is a unit constant
    have hR0 : R ≠ 0 := hirr.ne_zero
    have hC : R = Polynomial.C (R.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hc0 : R.coeff 0 ≠ 0 := fun h => hR0 (by rw [hC, h, map_zero])
    rw [hC, Polynomial.map_C, Polynomial.separable_C]
    exact isUnit_iff_ne_zero.mpr fun h =>
      hc0 ((IsFractionRing.injective A (FractionRing A)) (by rw [h, map_zero]))
  · -- positive degree: Gauss + degree-versus-characteristic supply
    have hprim : R.IsPrimitive := hirr.isPrimitive hdeg
    have hirr' : Irreducible (R.map (algebraMap A (FractionRing A))) :=
      hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
    have hmapdeg : (R.map (algebraMap A (FractionRing A))).natDegree = R.natDegree :=
      Polynomial.natDegree_map_eq_of_injective
        (IsFractionRing.injective A (FractionRing A)) R
    exact hirr'.separable_of_natDegree_lt_ringChar
      (by rw [hmapdeg]; exact Nat.pos_of_ne_zero hdeg) (by rw [hmapdeg]; exact hchar)

/-- **Global separability of the squarefree part, per-factor characteristic bound**
(mirror of `separable_map_radical` without `[PerfectField]`): if every distinct prime
factor of `Q` has degree below the characteristic of `FractionRing A` (or characteristic
zero holds), the image of `radical Q` in `(FractionRing A)[X]` is separable. -/
theorem separable_map_radical_of_primeFactors_natDegree_lt (Q : A[X])
    (hchar : ∀ R ∈ primeFactors Q,
      R.natDegree < ringChar (FractionRing A) ∨ ringChar (FractionRing A) = 0) :
    ((radical Q).map (algebraMap A (FractionRing A))).Separable := by
  classical
  by_cases hQ0 : Q = 0
  · simp [hQ0]
  have hmap : (radical Q).map (algebraMap A (FractionRing A)) =
      ∏ R ∈ primeFactors Q, R.map (algebraMap A (FractionRing A)) := by
    rw [radical, ← Polynomial.coe_mapRingHom, map_prod]
    rfl
  rw [hmap]
  exact Polynomial.separable_prod'
    (fun R hR S hS hne => isCoprime_map_of_mem_primeFactors hQ0 hR hS hne)
    (fun R hR =>
      separable_map_of_mem_primeFactors_of_natDegree_lt_ringChar hQ0 hR (hchar R hR))

/-- Global separability of the squarefree part when `natDegree Q` is below the
characteristic of `FractionRing A` (each prime factor divides `Q`). -/
theorem separable_map_radical_of_natDegree_lt_ringChar {Q : A[X]} (hQ0 : Q ≠ 0)
    (hchar : Q.natDegree < ringChar (FractionRing A) ∨ ringChar (FractionRing A) = 0) :
    ((radical Q).map (algebraMap A (FractionRing A))).Separable := by
  refine separable_map_radical_of_primeFactors_natDegree_lt Q (fun R hR => ?_)
  obtain ⟨-, -, hdvd⟩ :=
    (mem_normalizedFactors_iff' hQ0).mp (mem_primeFactors.mp hR)
  exact hchar.imp
    (fun h => lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hdvd hQ0) h) id

/-- Global separability of the squarefree part when already `natDegree (radical Q)` is
below the characteristic (each prime factor divides the radical). -/
theorem separable_map_radical_of_radical_natDegree_lt (Q : A[X])
    (hchar : (radical Q).natDegree < ringChar (FractionRing A) ∨
      ringChar (FractionRing A) = 0) :
    ((radical Q).map (algebraMap A (FractionRing A))).Separable := by
  refine separable_map_radical_of_primeFactors_natDegree_lt Q (fun R hR => ?_)
  have hdvdrad : R ∣ radical Q := by
    rw [radical]
    exact Finset.dvd_prod_of_mem id hR
  exact hchar.imp
    (fun h => lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hdvdrad radical_ne_zero) h) id

/-- **Global discriminant non-vanishing of the squarefree part at large characteristic**
(mirror of `discr_radical_ne_zero` without `[PerfectField]`). -/
theorem discr_radical_ne_zero_of_natDegree_lt_ringChar {Q : A[X]} (hQ0 : Q ≠ 0)
    (hdeg : 0 < (radical Q).natDegree)
    (hchar : Q.natDegree < ringChar (FractionRing A) ∨ ringChar (FractionRing A) = 0) :
    (radical Q).discr ≠ 0 :=
  Polynomial.discr_ne_zero_of_separable_map
    (IsFractionRing.injective A (FractionRing A)) hdeg
    (separable_map_radical_of_natDegree_lt_ringChar hQ0 hchar)

/-- Global discriminant non-vanishing of the squarefree part, radical-degree form. -/
theorem discr_radical_ne_zero_of_radical_natDegree_lt {Q : A[X]}
    (hdeg : 0 < (radical Q).natDegree)
    (hchar : (radical Q).natDegree < ringChar (FractionRing A) ∨
      ringChar (FractionRing A) = 0) :
    (radical Q).discr ≠ 0 :=
  Polynomial.discr_ne_zero_of_separable_map
    (IsFractionRing.injective A (FractionRing A)) hdeg
    (separable_map_radical_of_radical_natDegree_lt Q hchar)

end Generic

/-! ## The GS chain over `K = F(Z)` -/

variable {F : Type} [Field F]

/-- The characteristic of `Frac(K[X])` (`K = F(Z)`) is the characteristic of `F`: the
composite `F → RatFunc F → (RatFunc F)[X] → FractionRing ((RatFunc F)[X])` is an injective
chain of ring maps, and characteristic transports along injections. -/
theorem ringChar_fractionRing_eq_ringChar (F : Type) [Field F] :
    ringChar (FractionRing ((RatFunc F)[X])) = ringChar F := by
  haveI h0 : CharP F (ringChar F) := ringChar.charP F
  haveI h1 : CharP (RatFunc F) (ringChar F) :=
    charP_of_injective_algebraMap (algebraMap F (RatFunc F)).injective (ringChar F)
  haveI h2 : CharP ((RatFunc F)[X]) (ringChar F) :=
    charP_of_injective_algebraMap
      (C_injective : Function.Injective (C (R := RatFunc F))) (ringChar F)
  haveI h3 : CharP (FractionRing ((RatFunc F)[X])) (ringChar F) :=
    charP_of_injective_algebraMap
      (IsFractionRing.injective ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X])))
      (ringChar F)
  exact ringChar.eq_iff.mpr h3

/-- **Large-characteristic separability of irreducible bivariate factors** (mirror of
`irreducible_discr_ne_zero_of_charZero`): an irreducible `R ∈ (RatFunc F)[X][Y]` with
`0 < deg_Y R < ringChar F` (or `ringChar F = 0`) has nonzero `Y`-discriminant. This is the
case split that makes the [BCIKS20] Appendix C inseparable descent vacuous: inseparable
irreducible factors live in `K[X][Y^p]` and hence have `Y`-degree `≥ char F`. -/
theorem irreducible_discr_ne_zero_of_natDegree_lt_ringChar
    {R : (RatFunc F)[X][Y]} (hirr : Irreducible R) (hdeg : 0 < R.natDegree)
    (hchar : R.natDegree < ringChar F ∨ ringChar F = 0) :
    R.discr ≠ 0 := by
  have hrc := ringChar_fractionRing_eq_ringChar F
  exact Polynomial.discr_ne_zero_of_irreducible_of_natDegree_lt_ringChar hirr hdeg
    (by rw [hrc]; exact hchar)

/-- **Hab25 §3, Step S5 at large characteristic — fully residual-free** (mirror of
`gs_interpolant_good_specialization_charZero` with `[CharZero F]` replaced by the
degree-versus-characteristic bound `D/(k−1) < ringChar F ∨ ringChar F = 0`).

There is a generic-fold GS interpolant `Q` over `K = F(Z)` (S2 `Conditions`) with the
[BCIKS20, Claim 5.4] degree data `degreeX Q ≤ D := gs_degree_bound k n m` and
`deg_Y Q ≤ D/(k−1)` (S3), factoring into irreducibles (S4a), such that for **any** finite
family `Rs` of positive-`Y`-degree members of `factors Q`, in the paper regime
`|Rs| · 2·(D/(k−1))·D < n` some lifted evaluation point `x₀` is simultaneously good for all
of `Rs`: every factor specializes along `X ↦ x₀` to a nonzero, degree-preserved,
**separable** polynomial in `K[Y]`. The per-factor separability is supplied by
`irreducible_discr_ne_zero_of_natDegree_lt_ringChar` via `deg_Y R ≤ deg_Y Q ≤ D/(k−1)`. -/
theorem gs_interpolant_good_specialization_largeChar
    {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hk1 : 1 < k) (hn0 : n ≠ 0) (hm : 1 ≤ m) (hk : 0 < k - 1)
    (hchar : gs_degree_bound k n m / (k - 1) < ringChar F ∨ ringChar F = 0) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain ωs) (genericFold f₀ f₁) Q ∧
      degreeX Q ≤ gs_degree_bound k n m ∧
      Q.natDegree ≤ gs_degree_bound k n m / (k - 1) ∧
      (∀ q ∈ UniqueFactorizationMonoid.factors Q, Irreducible q) ∧
      Associated (UniqueFactorizationMonoid.factors Q).prod Q ∧
      ∀ Rs : Finset (RatFunc F)[X][Y],
        (∀ R ∈ Rs, R ∈ UniqueFactorizationMonoid.factors Q) →
        (∀ R ∈ Rs, 0 < R.natDegree) →
        Rs.card * (2 * (gs_degree_bound k n m / (k - 1)) * gs_degree_bound k n m) < n →
        ∃ i₀ : Fin n, ∀ R ∈ Rs,
          (R.discr).eval (liftedDomain ωs i₀) ≠ 0 ∧
          (R.map (evalRingHom (liftedDomain ωs i₀))).natDegree = R.natDegree ∧
          R.map (evalRingHom (liftedDomain ωs i₀)) ≠ 0 ∧
          (R.map (evalRingHom (liftedDomain ωs i₀))).Separable := by
  obtain ⟨Q, hQ, hxdeg, hydeg, hirr, hprod, hmain⟩ :=
    gs_interpolant_good_specialization_of_dvd k m ωs f₀ f₁ hk1 hn0 hm hk
  refine ⟨Q, hQ, hxdeg, hydeg, hirr, hprod, ?_⟩
  intro Rs hmem hpos hcard
  refine hmain Rs (fun R hR => ?_) hpos (fun R hR => ?_) hcard
  · exact UniqueFactorizationMonoid.dvd_of_mem_factors (hmem R hR)
  · have hRdeg : R.natDegree ≤ gs_degree_bound k n m / (k - 1) :=
      le_trans (Polynomial.natDegree_le_of_dvd
        (UniqueFactorizationMonoid.dvd_of_mem_factors (hmem R hR)) hQ.Q_ne_0) hydeg
    exact irreducible_discr_ne_zero_of_natDegree_lt_ringChar
      (UniqueFactorizationMonoid.irreducible_of_factor R (hmem R hR)) (hpos R hR)
      (hchar.imp (fun h => lt_of_le_of_lt hRdeg h) id)

/-- **Hab25 §3 S5, global discriminant form, large characteristic** (mirror of
`gs_interpolant_squarefree_discr_charZero`): in the regime `D/(k−1) < char F` (or
characteristic zero) the paper's global S5 holds — `disc_Y(radical Q) ≠ 0` as soon as the
decoded list is nonempty. The "honest caveat" of the characteristic-`p` case disappears:
inseparable factors would need `Y`-degree `≥ char F > D/(k−1)`, which the S3 degree data
forbids. -/
theorem gs_interpolant_squarefree_discr_largeChar
    {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hk1 : 1 < k) (hn0 : n ≠ 0) (hm : 1 ≤ m) (hk : 0 < k - 1)
    (hchar : gs_degree_bound k n m / (k - 1) < ringChar F ∨ ringChar F = 0) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain ωs) (genericFold f₀ f₁) Q ∧
      Squarefree (radical Q) ∧
      (radical Q).natDegree ≤ gs_degree_bound k n m / (k - 1) ∧
      degreeX (radical Q) ≤ gs_degree_bound k n m ∧
      (∀ p : (RatFunc F)[X],
        (X - C p : (RatFunc F)[X][Y]) ∣ radical Q ↔ (X - C p : (RatFunc F)[X][Y]) ∣ Q) ∧
      (∀ p₀ : (RatFunc F)[X],
        (X - C p₀ : (RatFunc F)[X][Y]) ∣ Q → (radical Q).discr ≠ 0) := by
  have hrc := ringChar_fractionRing_eq_ringChar F
  obtain ⟨Q, hQ, _, hsf, hydeg, hxdeg, htransfer, _⟩ :=
    gs_interpolant_squarefree_part k m ωs f₀ f₁ hk1 hn0 hm hk
  have hQ0 : Q ≠ 0 := hQ.Q_ne_0
  refine ⟨Q, hQ, hsf, hydeg, hxdeg, htransfer, fun p₀ hdvd => ?_⟩
  exact discr_radical_ne_zero_of_radical_natDegree_lt
    (natDegree_radical_pos_of_linearFactor_dvd hQ0 hdvd)
    (by rw [hrc]; exact hchar.imp (fun h => lt_of_le_of_lt hydeg h) id)

/-- **The large-characteristic good-`z` supply for the squarefree part** (mirror of
`radical_rep_good_specialization_charZero`, residual (i) of the S6→S8 weld at large
characteristic). Let `Q` be a nonzero `K = F(Z)`-level interpolant with at least one
decoded linear factor and `deg_Y Q < ringChar F` (or `ringChar F = 0`), and let `(e, W₀)`
be any integer representative of `radical Q`. Then there is a nonzero `g ∈ F[Z]` such that
at every `z` with `g(z) ≠ 0` the specialization `W₀|_{Z:=z}` has no repeated linear
factor. -/
theorem radical_rep_good_specialization_largeChar
    {Q : (RatFunc F)[X][Y]} (hQ0 : Q ≠ 0)
    (hchar : Q.natDegree < ringChar F ∨ ringChar F = 0)
    {e : F[X]} {W₀ : (F[X])[X][Y]} (he : e ≠ 0)
    (hrep : W₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) e)) * radical Q)
    {p : (RatFunc F)[X]}
    (hdvd : (Polynomial.X - Polynomial.C p) ∣ Q) :
    ∃ g : F[X], g ≠ 0 ∧ ∀ z : F, g.eval z ≠ 0 →
      ∀ r : F[X], ¬ ((Polynomial.X - Polynomial.C r) ^ 2 ∣
        W₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) := by
  classical
  -- positive degree of the squarefree part, transferred to the integer representative
  have hWdeg : 0 < (radical Q : (RatFunc F)[X][Y]).natDegree :=
    natDegree_radical_pos_of_linearFactor_dvd hQ0 hdvd
  have hrad0 : (radical Q : (RatFunc F)[X][Y]) ≠ 0 := radical_ne_zero
  have hφinj : Function.Injective (algebraMap F[X] (RatFunc F)) :=
    RatFunc.algebraMap_injective F
  have hφe : algebraMap F[X] (RatFunc F) e ≠ 0 := fun h0 =>
    he ((map_eq_zero_iff _ hφinj).mp h0)
  have hcc : (Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) e)) :
      (RatFunc F)[X][Y]) ≠ 0 := by
    simpa using hφe
  have h2 : Function.Injective
      ⇑(Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) := by
    rw [Polynomial.coe_mapRingHom]
    exact Polynomial.map_injective _ hφinj
  have h1 : (W₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))).natDegree =
      W₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective h2 W₀
  have h3 : (W₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))).natDegree =
      (radical Q : (RatFunc F)[X][Y]).natDegree := by
    rw [hrep, Polynomial.natDegree_mul hcc hrad0, Polynomial.natDegree_C, zero_add]
  have hdeg : 0 < W₀.natDegree := by
    rw [← h1, h3]
    exact hWdeg
  -- separability of the squarefree part: degree-versus-characteristic supply
  have hrc := ringChar_fractionRing_eq_ringChar F
  have hsep : ((radical Q : (RatFunc F)[X][Y]).map
      (algebraMap (RatFunc F)[X] (FractionRing ((RatFunc F)[X])))).Separable :=
    separable_map_radical_of_natDegree_lt_ringChar hQ0 (by rw [hrc]; exact hchar)
  -- the integer representative has nonzero discriminant; conclude the cofinite good set
  exact exists_good_specialization_no_sq_linear hdeg
    (integer_rep_discr_ne_zero he hrep hdeg hsep)

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms Irreducible.separable_of_natDegree_lt_charP
#print axioms Irreducible.separable_of_natDegree_lt_ringChar
#print axioms Polynomial.discr_ne_zero_of_irreducible_of_natDegree_lt_ringChar
#print axioms GuruswamiSudan.OverRatFunc.ringChar_fractionRing_eq_ringChar
#print axioms GuruswamiSudan.OverRatFunc.irreducible_discr_ne_zero_of_natDegree_lt_ringChar
#print axioms GuruswamiSudan.OverRatFunc.separable_map_radical_of_natDegree_lt_ringChar
#print axioms GuruswamiSudan.OverRatFunc.discr_radical_ne_zero_of_natDegree_lt_ringChar
#print axioms GuruswamiSudan.OverRatFunc.gs_interpolant_good_specialization_largeChar
#print axioms GuruswamiSudan.OverRatFunc.gs_interpolant_squarefree_discr_largeChar
#print axioms GuruswamiSudan.OverRatFunc.radical_rep_good_specialization_largeChar
