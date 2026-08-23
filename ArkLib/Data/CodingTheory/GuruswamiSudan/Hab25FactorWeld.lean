/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorAssignment

/-!
# Hab25 §3 — the S6→S8 factor weld: per-good-`z` uniqueness and affine pinning

The remaining deep node of the Haböck §3 endgame
(`ArkLib/Data/CodingTheory/ProximityGap/Hab25Johnson.lean`,
`Hab25AffineCapture.lean`) is the **capture kernel**: every per-`z` decoded polynomial of a
scalar fold must arise as the `Z := z` specialization `a + z·b` of one of the `≤ ℓ` affine
pairs carried by the `K = F(Z)`-level decoded list. The in-tree S10 bridge already places
both objects in the factor structure of the *same* specialized interpolant `Q₀|_{Z:=z}`
(`scalar_fold_decoded_divides_specialization`, forward;
`decoded_affine_pair_divides_specialization`, converse), and
`exists_specialized_factor_assignment` assigns every per-`z` decode to *some* factor cell.
What was missing is the **weld**: at a good point `z`,

1. the claiming factor is **unique** — two distinct irreducible factors of `Q` cannot both
   claim the same per-`z` decoded root, because a doubly-claimed root is a repeated linear
   factor of `Q₀|_{Z:=z}`, which separability of the specialization forbids
   (root simplicity); and
2. if the claiming factor is **linear in `Y`** — i.e. it is one of the `K`-level decoded
   factors `Y − C p`, carrying the proven S6 affine pair `p = a + Z·b`
   (`GSAffinePair.affine_pair_of_hammingDist`) — then the per-`z` decoded root is **pinned**
   to that factor's affine pair: `q = a + z·b`. Consequently the per-`z` root assignment
   `z ↦ (its claiming factor)` is *constant* on the affine pencil: at every good `z` the
   specialized affine pair is claimed by its own `K`-level linear factor and by no other.

This file proves all of that, residual-free:

* `eq_of_linear_dvd_linear`, `not_sq_linear_dvd_of_separable_map`,
  `claiming_factor_unique` — the generic bricks: monic-linear divisibility pins the root;
  a separable image forbids `(Y − C q)²`-divisibility (`Polynomial.Separable.squarefree`);
  a prime claiming two distinct members of a product family dividing a square-linear-free
  polynomial is impossible.

* `exists_specialized_factor_assignment_sep` — the **sharpened S4 bridge**: the per-`z`
  factor assignment of `GSFactorAssignment.lean`, re-derived with an enlarged bad polynomial
  `bad = cn·d·D·cd` so that at every good `z` it additionally exposes
  (i) per-factor denominator nonvanishing `dR(z) ≠ 0` and
  (ii) **uniqueness of the claiming factor** whenever the specialization `Q₀|_{Z:=z}` has no
  repeated linear factor — the formal "two distinct factors can't both claim `(z, y_z)` at a
  good `z`".

* `rep_eq_of_linear_affine`, `rep_specialize_of_linear_affine` — the integer representative
  of a *linear* `K`-level factor with affine pair `(a, b)` is exactly
  `C (C dR) · (Y − C (a + Z·b))`, and it specializes at every `z` to
  `C (C dR(z)) · (Y − C (a + z·b))`.

* `decoded_root_eq_affine_of_linear_rep` — **the pinning**: at any `z` with `dR(z) ≠ 0`, a
  decoded root claimed by a linear factor equals that factor's affine specialization.

* `affine_specialization_dvd_rep`, `claiming_factor_of_affine_constant` — **the constancy
  weld**: the specialized affine pair is always claimed by its own linear factor, and (by
  uniqueness) by no other — the per-`z` assignment is constant on the affine pencil.

* `decoded_root_eq_affine_of_claiming_linear` — the consumer-shaped capstone: assignment +
  linearity of the claiming factor ⟹ the per-`z` decoded polynomial **is** an affine
  specialization `pa R + z·pb R` from the finite factor list — exactly the
  `AffineCaptured`/`hImprove` input surface of
  `Hab25AffineCapture.exists_algebraicData_of_affine_capture`.

## The honest remaining delta

Two precisely-named inputs are consumed, not proven, by the capstones:

* **separable specialization** (`hnosq`): `Q₀|_{Z:=z}` has no repeated linear factor at the
  good `z`. For the squarefree part `radical Q` (`GSSquarefreePart.lean`) in characteristic
  zero this holds at all but finitely many `z` (the discriminant
  `disc_Y (radical Q) ≠ 0` survives all but finitely many `Z := z` specializations via
  `discr_map_of_natDegree_preserved`); the cofinite-supply brick is mechanical but not yet
  in tree.
* **linearity of the claiming factor** (`hlin`): no per-`z` decoded root hides in a factor
  of `Y`-degree `≥ 2` — the genuinely deep BCIKS20 §5 Steps 5–7 / Hensel-rigidity content
  (Claims 5.8/5.9 and Appendix C in characteristic `p`).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

/-! ## Generic root-simplicity bricks -/

/-- **Monic-linear divisibility pins the root.** Over any commutative ring,
`(X − C q) ∣ (X − C r)` forces `q = r` (evaluate at `q`). -/
theorem eq_of_linear_dvd_linear {A : Type*} [CommRing A] {q r : A}
    (h : (Polynomial.X - Polynomial.C q) ∣ (Polynomial.X - Polynomial.C r)) : q = r := by
  obtain ⟨w, hw⟩ := h
  have h2 := congrArg (Polynomial.eval q) hw
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_C, sub_self, zero_mul] at h2
  exact sub_eq_zero.mp h2

/-- **Root simplicity from a separable image.** If the image of `W` under a coefficient
ring hom into a nontrivial commutative ring is separable, then `W` has no repeated linear
factor: `(X − C q)² ∤ W`. Separability of the image gives squarefreeness
(`Polynomial.Separable.squarefree`), and a repeated linear factor would map to a repeated
linear factor — a non-unit square divisor. -/
theorem not_sq_linear_dvd_of_separable_map {A L : Type*} [CommRing A] [CommRing L]
    [Nontrivial L] (φ : A →+* L) {W : A[X]} (hsep : (W.map φ).Separable) (q : A) :
    ¬ ((Polynomial.X - Polynomial.C q) ^ 2 ∣ W) := by
  intro h
  have hmap : (Polynomial.X - Polynomial.C (φ q)) ^ 2 ∣ W.map φ := by
    have h2 := Polynomial.map_dvd φ h
    simpa [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      using h2
  have hsf : Squarefree (W.map φ) := hsep.squarefree
  have hunit : IsUnit (Polynomial.X - Polynomial.C (φ q)) := by
    refine hsf _ ?_
    rw [← pow_two]
    exact hmap
  exact Polynomial.not_isUnit_X_sub_C _ hunit

/-- **Per-good-`z` uniqueness of the claiming factor (generic form).** If a product family
`∏ S R ^ e R` divides a polynomial `W` with no repeated linear factor, then the monic linear
prime `X − C q` cannot divide two *distinct* members of the family (with positive
multiplicities): otherwise `(X − C q)²` would divide `W`. This is the root-simplicity weld:
"two distinct factors can't both claim the same decoded root at a good point". -/
theorem claiming_factor_unique {A : Type*} [CommRing A] {ι : Type*} [DecidableEq ι]
    {Fs : Finset ι} {S : ι → A[X]} {e : ι → ℕ} {W : A[X]}
    (hdvd : (∏ R ∈ Fs, S R ^ e R) ∣ W)
    (hW : ∀ r : A, ¬ ((Polynomial.X - Polynomial.C r) ^ 2 ∣ W))
    {q : A} {R R' : ι} (hR : R ∈ Fs) (hR' : R' ∈ Fs) (hne : R ≠ R')
    (heR : e R ≠ 0) (heR' : e R' ≠ 0)
    (h1 : (Polynomial.X - Polynomial.C q) ∣ S R)
    (h2 : (Polynomial.X - Polynomial.C q) ∣ S R') : False := by
  have hR'e : R' ∈ Fs.erase R := Finset.mem_erase.mpr ⟨fun h => hne h.symm, hR'⟩
  have hprod1 : S R ^ e R * ∏ x ∈ Fs.erase R, S x ^ e x = ∏ x ∈ Fs, S x ^ e x :=
    Finset.mul_prod_erase Fs (fun x => S x ^ e x) hR
  have hprod2 : S R' ^ e R' * ∏ x ∈ (Fs.erase R).erase R', S x ^ e x =
      ∏ x ∈ Fs.erase R, S x ^ e x :=
    Finset.mul_prod_erase (Fs.erase R) (fun x => S x ^ e x) hR'e
  have hsq : (Polynomial.X - Polynomial.C q) ^ 2 ∣ ∏ x ∈ Fs, S x ^ e x := by
    rw [← hprod1, ← hprod2, pow_two, ← mul_assoc]
    exact Dvd.dvd.mul_right
      (mul_dvd_mul (h1.trans (dvd_pow_self _ heR)) (h2.trans (dvd_pow_self _ heR'))) _
  exact hW q (hsq.trans hdvd)

/-- A nonzero scalar constant `C (C c)` can be cancelled from a bivariate divisibility. -/
theorem dvd_of_dvd_C_C_mul {K : Type*} [Field K] {c : K} (hc : c ≠ 0)
    {x y : K[X][Y]} (h : x ∣ Polynomial.C (Polynomial.C c) * y) : x ∣ y := by
  have h2 := h.mul_left (Polynomial.C (Polynomial.C c⁻¹))
  rwa [← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul, inv_mul_cancel₀ hc,
    Polynomial.C_1, Polynomial.C_1, one_mul] at h2

variable {F : Type} [Field F]

/-! ## The sharpened per-`z` factor assignment: existence **and** uniqueness

This re-derives `exists_specialized_factor_assignment` (`GSFactorAssignment.lean`) with an
enlarged bad polynomial `bad = cn·d·D·cd` (also clearing the product of all representative
denominators `D` and the unit denominator `cd`), so that at every good `z` the bridge
additionally yields per-factor denominator nonvanishing and the **uniqueness of the
claiming factor** under the no-repeated-linear-factor (separable-specialization) condition. -/

set_option maxHeartbeats 800000 in
/-- **The sharpened per-`z` factor assignment (the S4→S6 weld bridge).**

There are integer representatives `rep R` of the irreducible factors of `Q` and a nonzero
polynomial `bad ∈ F[Z]` such that for every `z` with `bad(z) ≠ 0`:

1. (*representatives*) each factor's denominator survives: `dR ≠ 0`, the representative
   satisfies `Ψ (rep R) = C (C dR) · R` over `K = F(Z)`, and `dR(z) ≠ 0`;
2. (*assignment*) every decoded linear factor of the specialized integer interpolant
   divides the specialization of **some** factor's representative; and
3. (*uniqueness*) if `Q₀|_{Z:=z}` has no repeated linear factor (the separable-specialization
   condition, e.g. from the squarefree part in characteristic zero), the claiming factor is
   **unique**: no decoded root is claimed by two distinct factors. -/
theorem exists_specialized_factor_assignment_sep
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hd : d ≠ 0) (hQ0 : Q ≠ 0)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q) :
    ∃ (rep : (RatFunc F)[X][Y] → (F[X])[X][Y]) (bad : F[X]), bad ≠ 0 ∧
      (∀ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
        ∃ dR : F[X], dR ≠ 0 ∧
          (rep R).map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
            Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) dR)) * R ∧
          ∀ z : F, bad.eval z ≠ 0 → dR.eval z ≠ 0) ∧
      (∀ z : F, bad.eval z ≠ 0 → ∀ q : F[X],
        (Polynomial.X - Polynomial.C q) ∣
            Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
          ∃ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
            (Polynomial.X - Polynomial.C q) ∣
              (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) ∧
      (∀ z : F, bad.eval z ≠ 0 →
        (∀ r : F[X], ¬ ((Polynomial.X - Polynomial.C r) ^ 2 ∣
            Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))) →
        ∀ q : F[X], ∀ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
          ∀ R' ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
          (Polynomial.X - Polynomial.C q) ∣
            (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
          (Polynomial.X - Polynomial.C q) ∣
            (rep R').map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
          R = R') := by
  classical
  set φ := algebraMap F[X] (RatFunc F) with hφ
  set Ψ : (F[X])[X][Y] →+* (RatFunc F)[X][Y] :=
    Polynomial.mapRingHom (Polynomial.mapRingHom φ) with hΨ
  have hΨapp : ∀ p : (F[X])[X][Y], Ψ p = p.map (Polynomial.mapRingHom φ) := fun _ => rfl
  have hΨinj : Function.Injective Ψ := by
    rw [hΨ, Polynomial.coe_mapRingHom]
    exact Polynomial.map_injective _ (by
      rw [Polynomial.coe_mapRingHom]
      exact Polynomial.map_injective _ (RatFunc.algebraMap_injective F))
  -- the constant-embedding homs
  set h : F[X] →+* (RatFunc F)[X][Y] :=
    ((Polynomial.C : (RatFunc F)[X] →+* (RatFunc F)[X][Y]).comp
      (Polynomial.C : RatFunc F →+* (RatFunc F)[X])).comp φ with hh_def
  have hh : ∀ a : F[X], h a = Polynomial.C (Polynomial.C (φ a)) := fun _ => rfl
  set CCK : RatFunc F →+* (RatFunc F)[X][Y] :=
    (Polynomial.C : (RatFunc F)[X] →+* (RatFunc F)[X][Y]).comp
      (Polynomial.C : RatFunc F →+* (RatFunc F)[X]) with hCCK_def
  have hCCK : ∀ x : RatFunc F, CCK x = Polynomial.C (Polynomial.C x) := fun _ => rfl
  have hΨC : ∀ a : F[X],
      Ψ (Polynomial.C (Polynomial.C a)) = h a := by
    intro a
    rw [hΨapp, Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_C, hh]
  -- integer representatives of the factors, by choice
  have hex : ∀ R : (RatFunc F)[X][Y],
      ∃ dR : F[X], ∃ R₀ : (F[X])[X][Y], dR ≠ 0 ∧
        R₀.map (Polynomial.mapRingHom φ) =
          Polynomial.C (Polynomial.C (φ dR)) * R := by
    intro R
    obtain ⟨dR, R₀, h1, h2⟩ := exists_integer_representative R
    exact ⟨dR, R₀, h1, h2⟩
  choose dR repR hdR hrepR using hex
  set Fs : Finset (RatFunc F)[X][Y] :=
    (UniqueFactorizationMonoid.factors Q).toFinset with hFs
  set cnt : (RatFunc F)[X][Y] → ℕ :=
    fun R => (UniqueFactorizationMonoid.factors Q).count R with hcnt
  set P₀ : (F[X])[X][Y] := ∏ R ∈ Fs, (repR R) ^ (cnt R) with hP₀
  set D : F[X] := ∏ R ∈ Fs, (dR R) ^ (cnt R) with hD
  -- pushforward of the representative product
  have hmapP : Ψ P₀ = h D * (UniqueFactorizationMonoid.factors Q).prod := by
    have h1 : Ψ P₀ = ∏ R ∈ Fs, (h (dR R) * R) ^ (cnt R) := by
      rw [hP₀, map_prod Ψ (fun R => repR R ^ cnt R) Fs]
      refine Finset.prod_congr rfl fun R _ => ?_
      rw [map_pow Ψ (repR R) (cnt R), hΨapp, hrepR R, hh]
    have h2 : ∀ R ∈ Fs,
        (h (dR R) * R) ^ (cnt R) = h ((dR R) ^ (cnt R)) * R ^ (cnt R) := by
      intro R _
      rw [mul_pow, ← map_pow h (dR R) (cnt R)]
    rw [h1, Finset.prod_congr rfl h2, Finset.prod_mul_distrib, hD,
      ← map_prod h (fun R => dR R ^ cnt R) Fs]
    congr 1
    exact (Finset.prod_multiset_count (UniqueFactorizationMonoid.factors Q)).symm
  -- the unit of the factorization is a double constant
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hQ0
  obtain ⟨v, hvu, hv⟩ := Polynomial.isUnit_iff.mp u.isUnit
  obtain ⟨c₀, hcu, hc⟩ := Polynomial.isUnit_iff.mp hvu
  have hc₀0 : c₀ ≠ 0 := hcu.ne_zero
  have hQeq : (UniqueFactorizationMonoid.factors Q).prod * CCK c₀ = Q := by
    rw [hCCK, hc, hv]
    exact hu
  -- the unit's numerator/denominator
  set cn : F[X] := RatFunc.num c₀ with hcn_def
  set cd : F[X] := RatFunc.denom c₀ with hcd_def
  have hcn0 : cn ≠ 0 := RatFunc.num_ne_zero hc₀0
  have hcdK : φ cd ≠ 0 := fun h0 =>
    RatFunc.denom_ne_zero c₀
      ((map_eq_zero_iff φ (RatFunc.algebraMap_injective F)).mp h0)
  have hnum_eq : φ cn = c₀ * φ cd := by
    conv_rhs => rw [← RatFunc.num_div_denom c₀]
    rw [div_mul_cancel₀ _ hcdK]
  -- the pushforward of `Q₀`, with the unit-resolved form of `Q`
  have hΨQ₀ : Ψ Q₀ = h d * Q := by
    rw [hΨapp, hrep, hh]
  have hΨQ₀' : Ψ Q₀ =
      h d * ((UniqueFactorizationMonoid.factors Q).prod * CCK c₀) := by
    rw [hΨQ₀, hQeq]
  -- **the unit-clearing identity over `F[Z]`**
  have hkey : Polynomial.C (Polynomial.C (cn * d)) * P₀ =
      Polynomial.C (Polynomial.C (D * cd)) * Q₀ := by
    apply hΨinj
    rw [map_mul Ψ (Polynomial.C (Polynomial.C (cn * d))) P₀,
      map_mul Ψ (Polynomial.C (Polynomial.C (D * cd))) Q₀,
      hΨC, hΨC, hmapP, hΨQ₀']
    have hcn_split : h cn = CCK c₀ * h cd := by
      rw [hh, hnum_eq, hCCK, hh, Polynomial.C_mul, Polynomial.C_mul]
    rw [map_mul h cn d, map_mul h D cd, hcn_split]
    ring
  -- nonvanishing data for the enlarged bad polynomial
  have hD0 : D ≠ 0 := by
    rw [hD]
    exact Finset.prod_ne_zero_iff.mpr fun R _ => pow_ne_zero _ (hdR R)
  have hcd0 : cd ≠ 0 := by
    rw [hcd_def]
    exact RatFunc.denom_ne_zero c₀
  have hcnt0 : ∀ R ∈ Fs, cnt R ≠ 0 := by
    intro R hR
    rw [hFs] at hR
    simp only [hcnt]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hR)).ne'
  -- conclude, with `bad := cn · d · D · cd`
  refine ⟨repR, cn * d * (D * cd),
    mul_ne_zero (mul_ne_zero hcn0 hd) (mul_ne_zero hD0 hcd0), ?_, ?_, ?_⟩
  · -- per-factor representatives and denominator nonvanishing
    intro R hR
    refine ⟨dR R, hdR R, hrepR R, ?_⟩
    intro z hz h0
    have hdvdD : dR R ∣ D := by
      rw [hD]
      exact dvd_trans (dvd_pow_self _ (hcnt0 R hR)) (Finset.dvd_prod_of_mem _ hR)
    obtain ⟨s, hs⟩ : dR R ∣ cn * d * (D * cd) :=
      hdvdD.trans ((dvd_mul_right D cd).trans (dvd_mul_left _ _))
    exact hz (by rw [hs, Polynomial.eval_mul, h0, zero_mul])
  · -- the factor assignment
    intro z hz q hq
    have hz1 : (cn * d).eval z ≠ 0 := by
      obtain ⟨s, hs⟩ : cn * d ∣ cn * d * (D * cd) := dvd_mul_right _ _
      intro h0
      exact hz (by rw [hs, Polynomial.eval_mul, h0, zero_mul])
    set σ : Polynomial (Polynomial (Polynomial F)) →+* Polynomial (Polynomial F) :=
      Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.evalRingHom z)) with hσ
    have hσapp : ∀ p : (F[X])[X][Y],
        σ p = p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := fun _ => rfl
    have hσC : ∀ a : F[X],
        σ (Polynomial.C (Polynomial.C a)) =
          Polynomial.C (Polynomial.C (a.eval z)) := by
      intro a
      rw [hσapp, Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.coe_evalRingHom]
    have hkeyz := congrArg σ hkey
    rw [map_mul σ (Polynomial.C (Polynomial.C (cn * d))) P₀,
      map_mul σ (Polynomial.C (Polynomial.C (D * cd))) Q₀, hσC, hσC] at hkeyz
    have hprime : Prime (Polynomial.X - Polynomial.C q : F[X][Y]) :=
      Polynomial.prime_X_sub_C q
    have hq' : (Polynomial.X - Polynomial.C q) ∣ σ Q₀ := hq
    have h1 : (Polynomial.X - Polynomial.C q) ∣
        Polynomial.C (Polynomial.C ((cn * d).eval z)) * σ P₀ := by
      rw [hkeyz]
      exact hq'.mul_left _
    rcases hprime.dvd_or_dvd h1 with hC | hP
    · exact absurd hC (not_linear_dvd_C (by simpa using hz1))
    · have hσP : σ P₀ = ∏ R ∈ Fs, (σ (repR R)) ^ (cnt R) := by
        rw [hP₀, map_prod σ (fun R => repR R ^ cnt R) Fs]
        exact Finset.prod_congr rfl fun R _ => map_pow σ _ _
      rw [hσP] at hP
      obtain ⟨R, hRmem, hdvd⟩ := hprime.exists_mem_finset_dvd hP
      exact ⟨R, hRmem, hprime.dvd_of_dvd_pow hdvd⟩
  · -- uniqueness of the claiming factor at a separable specialization
    intro z hz hnosq q R hR R' hR' h1 h2
    by_contra hne
    have hz2 : (D * cd).eval z ≠ 0 := by
      obtain ⟨s, hs⟩ : D * cd ∣ cn * d * (D * cd) := dvd_mul_left _ _
      intro h0
      exact hz (by rw [hs, Polynomial.eval_mul, h0, zero_mul])
    set σ : Polynomial (Polynomial (Polynomial F)) →+* Polynomial (Polynomial F) :=
      Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.evalRingHom z)) with hσ
    have hσapp : ∀ p : (F[X])[X][Y],
        σ p = p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := fun _ => rfl
    have hσC : ∀ a : F[X],
        σ (Polynomial.C (Polynomial.C a)) =
          Polynomial.C (Polynomial.C (a.eval z)) := by
      intro a
      rw [hσapp, Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.coe_evalRingHom]
    have hkeyz := congrArg σ hkey
    rw [map_mul σ (Polynomial.C (Polynomial.C (cn * d))) P₀,
      map_mul σ (Polynomial.C (Polynomial.C (D * cd))) Q₀, hσC, hσC] at hkeyz
    have hσP : σ P₀ = ∏ R'' ∈ Fs, (σ (repR R'')) ^ (cnt R'') := by
      rw [hP₀, map_prod σ (fun R'' => repR R'' ^ cnt R'') Fs]
      exact Finset.prod_congr rfl fun R'' _ => map_pow σ _ _
    have hnosqP : ∀ r : F[X],
        ¬ ((Polynomial.X - Polynomial.C r) ^ 2 ∣ σ P₀) := by
      intro r hsq
      have hsq2 : (Polynomial.X - Polynomial.C r) ^ 2 ∣
          Polynomial.C (Polynomial.C ((D * cd).eval z)) * σ Q₀ := by
        rw [← hkeyz]
        exact hsq.mul_left _
      exact hnosq r (dvd_of_dvd_C_C_mul hz2 hsq2)
    exact claiming_factor_unique (S := fun R'' => σ (repR R'')) (e := cnt)
      hσP.symm.dvd hnosqP hR hR' hne (hcnt0 R hR) (hcnt0 R' hR') h1 h2

/-! ## The linear-factor representative: identification, specialization, pinning -/

/-- **Identification of the integer representative of a linear `K`-level factor.** If the
factor is `Y − C p` with affine pair `p = a + Z·b` (the proven S6 output), its integer
representative with denominator `dR` is exactly `C (C dR) · (Y − C (a + Z·b))` (with the
affine pair lifted integrally by `affinePairLift`). -/
theorem rep_eq_of_linear_affine
    {rep : (F[X])[X][Y]} {dR : F[X]} {p : (RatFunc F)[X]} {a b : F[X]}
    (hrepR : rep.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) dR)) *
        (Polynomial.X - Polynomial.C p))
    (haffine : p = a.map (algebraMap F (RatFunc F)) +
      Polynomial.C RatFunc.X * b.map (algebraMap F (RatFunc F))) :
    rep = Polynomial.C (Polynomial.C dR) *
      (Polynomial.X - Polynomial.C (affinePairLift a b)) := by
  have hinj1 : Function.Injective
      ⇑(Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) := by
    rw [Polynomial.coe_mapRingHom]
    exact Polynomial.map_injective _ (RatFunc.algebraMap_injective F)
  have hinj : Function.Injective (fun t : (F[X])[X][Y] =>
      t.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))) :=
    fun s t hst => Polynomial.map_injective _ hinj1 hst
  apply hinj
  show rep.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
    (Polynomial.C (Polynomial.C dR) *
      (Polynomial.X - Polynomial.C (affinePairLift a b))).map
        (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))
  rw [hrepR]
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.coe_mapRingHom]
  rw [affinePairLift_map, ← haffine]

/-- **Specialization of a linear factor's representative.** At every `z ∈ F`, the integer
representative of the linear factor `Y − C (a + Z·b)` specializes to
`C (C dR(z)) · (Y − C (a + z·b))`. -/
theorem rep_specialize_of_linear_affine
    {rep : (F[X])[X][Y]} {dR : F[X]} {p : (RatFunc F)[X]} {a b : F[X]}
    (hrepR : rep.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) dR)) *
        (Polynomial.X - Polynomial.C p))
    (haffine : p = a.map (algebraMap F (RatFunc F)) +
      Polynomial.C RatFunc.X * b.map (algebraMap F (RatFunc F)))
    (z : F) :
    rep.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) =
      Polynomial.C (Polynomial.C (dR.eval z)) *
        (Polynomial.X - Polynomial.C (a + Polynomial.C z * b)) := by
  rw [rep_eq_of_linear_affine hrepR haffine]
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom]
  rw [affinePairLift_specialize]

/-- **The pinning (the S6→S8 weld at a linear factor).** At any `z` where the factor's
denominator survives (`dR(z) ≠ 0`), a decoded root claimed by a linear `K`-level factor
with affine pair `(a, b)` **equals** that factor's affine specialization: `q = a + z·b`.
This is the Hensel-uniqueness consequence for the linear (separable, branch-separated)
factors — no lift needed, the affine pair is rigid under specialization. -/
theorem decoded_root_eq_affine_of_linear_rep
    {rep : (F[X])[X][Y]} {dR : F[X]} {p : (RatFunc F)[X]} {a b : F[X]}
    (hrepR : rep.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) dR)) *
        (Polynomial.X - Polynomial.C p))
    (haffine : p = a.map (algebraMap F (RatFunc F)) +
      Polynomial.C RatFunc.X * b.map (algebraMap F (RatFunc F)))
    {z : F} (hz : dR.eval z ≠ 0) {q : F[X]}
    (hdvd : (Polynomial.X - Polynomial.C q) ∣
      rep.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) :
    q = a + Polynomial.C z * b := by
  rw [rep_specialize_of_linear_affine hrepR haffine z] at hdvd
  have hprime : Prime (Polynomial.X - Polynomial.C q : F[X][Y]) :=
    Polynomial.prime_X_sub_C q
  rcases hprime.dvd_or_dvd hdvd with hC | hlin
  · exact absurd hC (not_linear_dvd_C (by simpa using hz))
  · exact eq_of_linear_dvd_linear hlin

/-- **The affine pencil claims its own factor at every `z`** (no goodness needed): the
specialized affine pair `Y − C (a + z·b)` always divides the specialization of its own
linear factor's representative. -/
theorem affine_specialization_dvd_rep
    {rep : (F[X])[X][Y]} {dR : F[X]} {p : (RatFunc F)[X]} {a b : F[X]}
    (hrepR : rep.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) dR)) *
        (Polynomial.X - Polynomial.C p))
    (haffine : p = a.map (algebraMap F (RatFunc F)) +
      Polynomial.C RatFunc.X * b.map (algebraMap F (RatFunc F)))
    (z : F) :
    (Polynomial.X - Polynomial.C (a + Polynomial.C z * b)) ∣
      rep.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
  rw [rep_specialize_of_linear_affine hrepR haffine z]
  exact dvd_mul_left _ _

/-! ## The weld capstones -/

/-- **Constancy of the per-`z` root assignment on the affine pencil.** Given the uniqueness
clause of the sharpened assignment at a good `z`, the specialized affine pair
`a + z·b` of a linear factor `R` is claimed by **no factor other than `R` itself**: the map
`z ↦ (claiming factor of a + z·b)` is constant `≡ R` on the good set. This is the formal
"the per-`z` root assignment is constant on large agreement sets" weld statement. -/
theorem claiming_factor_of_affine_constant
    {Fs : Finset (RatFunc F)[X][Y]} {rep : (RatFunc F)[X][Y] → (F[X])[X][Y]} {z : F}
    (huniq : ∀ q : F[X], ∀ R ∈ Fs, ∀ R' ∈ Fs,
      (Polynomial.X - Polynomial.C q) ∣
        (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
      (Polynomial.X - Polynomial.C q) ∣
        (rep R').map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
      R = R')
    {R : (RatFunc F)[X][Y]} (hR : R ∈ Fs)
    {dR : F[X]} {p : (RatFunc F)[X]} {a b : F[X]}
    (hrepR : (rep R).map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) dR)) *
        (Polynomial.X - Polynomial.C p))
    (haffine : p = a.map (algebraMap F (RatFunc F)) +
      Polynomial.C RatFunc.X * b.map (algebraMap F (RatFunc F)))
    {R' : (RatFunc F)[X][Y]} (hR' : R' ∈ Fs)
    (hclaim : (Polynomial.X - Polynomial.C (a + Polynomial.C z * b)) ∣
      (rep R').map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) :
    R' = R :=
  huniq _ R' hR' R hR hclaim (affine_specialization_dvd_rep hrepR haffine z)

/-- **The consumer-shaped weld capstone.** At a `z` where the factor assignment holds, if
every factor claiming the decoded root `q` is **linear with an affine pair** (the named
Hensel residual: no per-`z` codeword hides in a `Y`-degree `≥ 2` factor), then `q` *is* an
affine specialization from the finite factor list:

  `∃ R ∈ Fs, q = pa R + z · pb R`.

This is exactly the per-`z` input surface of the Hab25 capture bundle
(`Hab25AffineCapture.exists_algebraicData_of_affine_capture` /
`Hab25CaptureKernel.McaDecode.affineCaptured`): the pair list is the image of the `≤ ℓ`
factors under `(pa, pb)`, and the resulting `AffineCaptured` membership feeds the **proven**
`hImprove` obligation (`affineCaptured_improve`). -/
theorem decoded_root_eq_affine_of_claiming_linear
    {Fs : Finset (RatFunc F)[X][Y]} {rep : (RatFunc F)[X][Y] → (F[X])[X][Y]}
    (pd pa pb : (RatFunc F)[X][Y] → F[X]) (pK : (RatFunc F)[X][Y] → (RatFunc F)[X])
    {z : F} {q : F[X]}
    (hassign : ∃ R ∈ Fs, (Polynomial.X - Polynomial.C q) ∣
      (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hlin : ∀ R ∈ Fs, (Polynomial.X - Polynomial.C q) ∣
        (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
      (rep R).map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
          Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) (pd R))) *
            (Polynomial.X - Polynomial.C (pK R)) ∧
        pK R = (pa R).map (algebraMap F (RatFunc F)) +
          Polynomial.C RatFunc.X * (pb R).map (algebraMap F (RatFunc F)) ∧
        (pd R).eval z ≠ 0) :
    ∃ R ∈ Fs, q = pa R + Polynomial.C z * pb R := by
  obtain ⟨R, hR, hclaim⟩ := hassign
  obtain ⟨hrepR, haffine, hz⟩ := hlin R hR hclaim
  exact ⟨R, hR, decoded_root_eq_affine_of_linear_rep hrepR haffine hz hclaim⟩

/-- **Fixed linear claiming factor gives cellwise affine pinning.** This packages
`decoded_root_eq_affine_of_linear_rep` in the exact family shape consumed downstream by the
Hab25/WHIR capture kernel: if every decoded root `P z` in a cell is claimed by one fixed
linear `K`-level factor whose affine pair is `(a, b)`, and the factor denominator survives
throughout the cell, then the whole decoded-polynomial family is pinned as
`P z = a + z·b` with the supplied degree bounds. -/
theorem decoded_family_affine_pinning_of_fixed_linear_rep
    {rep : (F[X])[X][Y]} {dR : F[X]} {p : (RatFunc F)[X]} {a b : F[X]}
    {Ecell : Finset F} {P : F → F[X]} {k : ℕ}
    (ha : a.natDegree < k) (hb : b.natDegree < k)
    (hrepR : rep.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) dR)) *
        (Polynomial.X - Polynomial.C p))
    (haffine : p = a.map (algebraMap F (RatFunc F)) +
      Polynomial.C RatFunc.X * b.map (algebraMap F (RatFunc F)))
    (hden : ∀ z ∈ Ecell, dR.eval z ≠ 0)
    (hclaim : ∀ z ∈ Ecell,
      (Polynomial.X - Polynomial.C (P z)) ∣
        rep.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < k ∧ v₁.natDegree < k ∧
      ∀ z ∈ Ecell, P z = v₀ + Polynomial.C z * v₁ := by
  refine ⟨a, b, ha, hb, fun z hz => ?_⟩
  exact decoded_root_eq_affine_of_linear_rep hrepR haffine (hden z hz) (hclaim z hz)

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.eq_of_linear_dvd_linear
#print axioms GuruswamiSudan.OverRatFunc.not_sq_linear_dvd_of_separable_map
#print axioms GuruswamiSudan.OverRatFunc.claiming_factor_unique
#print axioms GuruswamiSudan.OverRatFunc.dvd_of_dvd_C_C_mul
#print axioms GuruswamiSudan.OverRatFunc.exists_specialized_factor_assignment_sep
#print axioms GuruswamiSudan.OverRatFunc.rep_eq_of_linear_affine
#print axioms GuruswamiSudan.OverRatFunc.rep_specialize_of_linear_affine
#print axioms GuruswamiSudan.OverRatFunc.decoded_root_eq_affine_of_linear_rep
#print axioms GuruswamiSudan.OverRatFunc.affine_specialization_dvd_rep
#print axioms GuruswamiSudan.OverRatFunc.claiming_factor_of_affine_constant
#print axioms GuruswamiSudan.OverRatFunc.decoded_root_eq_affine_of_claiming_linear
#print axioms GuruswamiSudan.OverRatFunc.decoded_family_affine_pinning_of_fixed_linear_rep
