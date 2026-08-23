/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSIntegerRepresentative
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorizationOverRatFunc

/-!
# BCIKS20 Claim 5.7, algebraic half — the per-`z` factor assignment

[BCI⁺20, ePrint 2020/654] Claim 5.7 begins: *"For any `z ∈ S`, the polynomial `P_z(X)`
satisfies `Q(X, P_z(X), z) = 0`, i.e. `Y − P_z(X) ∣ Q(X,Y,z)`, thus there is some `i` such
that `Y − P_z(X) ∣ Rᵢ(X,Y,z)`."* This file proves that assignment step over the integer
model, completing the algebraic half of Claim 5.7 (the remaining half is the pigeonhole and
the `x₀`-fiber refinement):

* every irreducible factor `R` of the `K = F(Z)`-level interpolant `Q` gets an integer
  representative `rep R ∈ F[Z][X][Y]` (`exists_integer_representative`, applied by choice);
* the **unit-clearing identity** (`hkey` in the proof): writing `Q = (∏ factors)·C(C c)`
  with `c = cn/cd ∈ K^×` (UFD product + the shape of units of `K[X][Y]`), and collecting
  the representatives' denominators `D = ∏ d_R^{count R}`, one gets the *integral* identity

    `C(C(cn·d)) · ∏ (rep R)^{count R} = C(C(D·cd)) · Q₀`  in `F[Z][X][Y]`;

* **`exists_specialized_factor_assignment`** — specializing at any `z` outside the roots of
  `bad := cn·d` (a nonzero polynomial, so a cofinite set): every decoded linear factor
  `(Y − C q) ∣ Q₀|_{Z:=z}` divides the specialization of **some** factor's integer
  representative, `(Y − C q) ∣ (rep R)|_{Z:=z}` — primality of `Y − C q` over the domain
  `F[X]` routes it through the product and the powers.

Combined with the proven per-`z` divisibility (`scalar_fold_decoded_divides_specialization`)
this yields the Claim-5.7 cell structure: each bad scalar is assigned to a factor cell.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-- A monic linear polynomial does not divide a nonzero constant (degree count over a
domain). -/
lemma not_linear_dvd_C {A : Type*} [CommRing A] [IsDomain A] {q e : A} (he : e ≠ 0) :
    ¬ (Polynomial.X - Polynomial.C q ∣ (Polynomial.C e : A[X])) := by
  rintro ⟨w, hw⟩
  have hCe : (Polynomial.C e : A[X]) ≠ 0 := by
    simpa using he
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hw
    exact hCe hw
  have hX0 : (Polynomial.X - Polynomial.C q : A[X]) ≠ 0 :=
    (Polynomial.monic_X_sub_C q).ne_zero
  have hdeg := congrArg Polynomial.natDegree hw
  rw [Polynomial.natDegree_C, Polynomial.natDegree_mul hX0 hw0,
    Polynomial.natDegree_X_sub_C] at hdeg
  omega

/-- **The per-`z` factor assignment (algebraic half of BCIKS20 Claim 5.7).**

There are integer representatives `rep R` of the irreducible factors of `Q` and a nonzero
polynomial `bad ∈ F[Z]` such that for every `z` with `bad(z) ≠ 0`: every decoded linear
factor of the specialized integer interpolant divides the specialization of some factor's
representative. -/
theorem exists_specialized_factor_assignment
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hd : d ≠ 0) (hQ0 : Q ≠ 0)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q) :
    ∃ (rep : (RatFunc F)[X][Y] → (F[X])[X][Y]) (bad : F[X]), bad ≠ 0 ∧
      (∀ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
        ∃ dR : F[X], dR ≠ 0 ∧
          (rep R).map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
            Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) dR)) * R) ∧
      ∀ z : F, bad.eval z ≠ 0 → ∀ q : F[X],
        (Polynomial.X - Polynomial.C q) ∣
            Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
          ∃ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
            (Polynomial.X - Polynomial.C q) ∣
              (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
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
  -- conclude, with `bad := cn · d`
  refine ⟨repR, cn * d, mul_ne_zero hcn0 hd,
    fun R _ => ⟨dR R, hdR R, hrepR R⟩, ?_⟩
  intro z hz q hq
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
  -- specialize the identity at `z`
  have hkeyz := congrArg σ hkey
  rw [map_mul σ (Polynomial.C (Polynomial.C (cn * d))) P₀,
    map_mul σ (Polynomial.C (Polynomial.C (D * cd))) Q₀, hσC, hσC] at hkeyz
  -- divisibility chase through the prime `Y − C q`
  have hprime : Prime (Polynomial.X - Polynomial.C q : F[X][Y]) :=
    Polynomial.prime_X_sub_C q
  have hq' : (Polynomial.X - Polynomial.C q) ∣ σ Q₀ := hq
  have h1 : (Polynomial.X - Polynomial.C q) ∣
      Polynomial.C (Polynomial.C ((cn * d).eval z)) * σ P₀ := by
    rw [hkeyz]
    exact hq'.mul_left _
  rcases hprime.dvd_or_dvd h1 with hC | hP
  · exact absurd hC (not_linear_dvd_C (by
      simpa using hz))
  · have hσP : σ P₀ = ∏ R ∈ Fs, (σ (repR R)) ^ (cnt R) := by
      rw [hP₀, map_prod σ (fun R => repR R ^ cnt R) Fs]
      exact Finset.prod_congr rfl fun R _ => map_pow σ _ _
    rw [hσP] at hP
    obtain ⟨R, hRmem, hdvd⟩ := hprime.exists_mem_finset_dvd hP
    exact ⟨R, hRmem, hprime.dvd_of_dvd_pow hdvd⟩

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.not_linear_dvd_C
#print axioms GuruswamiSudan.OverRatFunc.exists_specialized_factor_assignment
