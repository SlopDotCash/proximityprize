/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSListSizeOverRatFunc
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Hab25 §3 Step S4 — factorization of the GS interpolant over `K = F(Z)` (index structure)

This file proves the tractable core of **Step S4** of the Haböck §3 endgame
(`ArkLib/Data/CodingTheory/ProximityGap/Hab25Johnson.lean`), building directly on the
discharged S2 (`gs_existence_over_ratfunc`, `gs_divisibility_over_ratfunc`) and S3
(`genericInterpolant_yDegree_le`) steps:

* **S4(a) — UFD factorization.** `(RatFunc F)[X][Y]` is a UFD (polynomial ring over the UFD
  `(RatFunc F)[X]`, itself a polynomial ring over the field `K = F(Z)`), so the nonzero GS
  interpolant `Q` factors into irreducibles with multiplicity:
  `Associated (UniqueFactorizationMonoid.factors Q).prod Q`, every member irreducible
  (`gs_interpolant_factorization`).

* **S4(b) — decoded linear factors are irreducible factors.** Each linear-in-`Y` factor
  `Y - C p` is irreducible (and prime) in `K[X][Y]` (`irreducible_linearFactor`,
  `prime_linearFactor`), so the per-codeword divisibility from S1/S2
  (`gs_divisibility_over_ratfunc`) upgrades to: the decoded codeword's linear factor is an
  **associate of a member of the irreducible factorization** of `Q`
  (`decoded_linearFactor_mem_factors`).

* **S4(c) — index structure / factor count.** Associated monic linear factors are *equal*
  (`linearFactor_associated_iff`), so distinct decoded messages index **distinct** irreducible
  factors of `Q`: any finite family `Ps` of messages whose linear factors divide `Q` injects
  into `(factors Q).toFinset`, giving `Ps.card ≤ (factors Q).toFinset.card`
  (`card_le_card_distinct_factors`) — alongside the S3 `Y`-degree cap
  `Ps.card ≤ gs_degree_bound k n m / (k - 1)`.

The capstone `gs_factorization_index_structure` packages all of S4(a)–(c) for the generic-fold
GS interpolant over `K = F(Z)`. The remaining deep S4→S6 content (the factors being exactly
`(Y - (a(X) + Z·b(X)))^{p^f}` for affine pairs, via discriminant non-vanishing S5 and the Hensel
lift S6) is *not* claimed here.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

/-! ## Linear-in-`Y` factors in `K[X][Y]`: irreducibility and rigidity -/

section LinearFactors

variable {K : Type} [Field K]

/-- **The linear factor `Y - C p` is irreducible in `K[X][Y]`.** Since `K[X]` is an integral
domain, the monic linear polynomial `X - C p` of the outer variable (i.e. `Y - p(X)`) is
irreducible. This is the input that places each decoded codeword's factor among the
*irreducible* factors of the GS interpolant. -/
theorem irreducible_linearFactor (p : K[X]) :
    Irreducible (X - C p : K[X][Y]) :=
  Polynomial.irreducible_X_sub_C p

/-- The linear factor `Y - C p` is moreover *prime* in `K[X][Y]`. -/
theorem prime_linearFactor (p : K[X]) :
    Prime (X - C p : K[X][Y]) :=
  Polynomial.prime_X_sub_C p

/-- **Rigidity of linear factors.** Two linear factors `Y - C p`, `Y - C p'` are associated in
`K[X][Y]` iff `p = p'`: both are monic, and associated monic polynomials are equal. This is the
*index structure* of S4 — the assignment {decoded message} → {irreducible factor of `Q`} cannot
collide. -/
theorem linearFactor_associated_iff (p p' : K[X]) :
    Associated (X - C p : K[X][Y]) (X - C p') ↔ p = p' := by
  constructor
  · intro h
    have heq : (X - C p : K[X][Y]) = X - C p' :=
      Polynomial.eq_of_monic_of_associated (monic_X_sub_C p) (monic_X_sub_C p') h
    exact Polynomial.C_injective (sub_right_inj.mp heq)
  · rintro rfl
    exact Associated.refl _

/-- **A dividing linear factor is an associate of an irreducible factor.** If `Y - C p` divides
the nonzero `Q : K[X][Y]`, then some member `q` of the UFD factorization
`UniqueFactorizationMonoid.factors Q` is an associate of `Y - C p`. -/
theorem linearFactor_mem_factors_of_dvd {Q : K[X][Y]} (hQ : Q ≠ 0) {p : K[X]}
    (hdvd : (X - C p : K[X][Y]) ∣ Q) :
    ∃ q ∈ UniqueFactorizationMonoid.factors Q, Associated (X - C p : K[X][Y]) q :=
  UniqueFactorizationMonoid.exists_mem_factors_of_dvd hQ (irreducible_linearFactor p) hdvd

/-- **Distinct linear factors index distinct irreducible factors.** Any finite family
`Ps : Finset K[X]` of messages whose linear factors `Y - C p` all divide the nonzero `Q` injects
into the finset of distinct irreducible factors of `Q`; in particular
`Ps.card ≤ (factors Q).toFinset.card`. The injection sends `p` to a chosen factor associated to
`Y - C p`; collisions are impossible by `linearFactor_associated_iff`. -/
theorem card_le_card_distinct_factors
    (Q : K[X][Y]) (hQ : Q ≠ 0) (Ps : Finset K[X])
    (hdvd : ∀ p ∈ Ps, (X - C p : K[X][Y]) ∣ Q) :
    Ps.card ≤ (UniqueFactorizationMonoid.factors Q).toFinset.card := by
  classical
  -- the chosen-factor assignment
  set f : K[X] → K[X][Y] := fun p =>
    if h : (X - C p : K[X][Y]) ∣ Q then (linearFactor_mem_factors_of_dvd hQ h).choose
    else 0 with hf
  apply Finset.card_le_card_of_injOn f
  · -- maps into the distinct factors
    intro p hp
    have h := hdvd p hp
    have hfp : f p = (linearFactor_mem_factors_of_dvd hQ h).choose := by
      simp only [hf]
      exact dif_pos h
    rw [Finset.mem_coe, hfp, Multiset.mem_toFinset]
    exact (linearFactor_mem_factors_of_dvd hQ h).choose_spec.1
  · -- injective on `Ps`
    intro p hp p' hp' hfeq
    have h := hdvd p (Finset.mem_coe.mp hp)
    have h' := hdvd p' (Finset.mem_coe.mp hp')
    have hfp : f p = (linearFactor_mem_factors_of_dvd hQ h).choose := by
      simp only [hf]
      exact dif_pos h
    have hfp' : f p' = (linearFactor_mem_factors_of_dvd hQ h').choose := by
      simp only [hf]
      exact dif_pos h'
    have hchoose :
        (linearFactor_mem_factors_of_dvd hQ h).choose =
          (linearFactor_mem_factors_of_dvd hQ h').choose := by
      rw [← hfp, ← hfp', hfeq]
    have hassoc : Associated (X - C p : K[X][Y]) (X - C p') := by
      have h1 := (linearFactor_mem_factors_of_dvd hQ h).choose_spec.2
      have h2 := (linearFactor_mem_factors_of_dvd hQ h').choose_spec.2
      rw [hchoose] at h1
      exact h1.trans h2.symm
    exact (linearFactor_associated_iff p p').mp hassoc

end LinearFactors

/-! ## S4 for the generic-fold GS interpolant over `K = F(Z)` -/

variable {F : Type} [Field F]

/-- **Hab25 §3, Step S4(a) — UFD factorization of the GS interpolant over `K = F(Z)`.**

The S2 interpolant `Q ∈ (RatFunc F)[X][Y]` of the generic fold factors, in the UFD
`(RatFunc F)[X][Y]`, into a multiset of irreducible factors whose product is an associate
of `Q`. -/
theorem gs_interpolant_factorization {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain ωs) (genericFold f₀ f₁) Q ∧
      (∀ q ∈ UniqueFactorizationMonoid.factors Q, Irreducible q) ∧
      Associated (UniqueFactorizationMonoid.factors Q).prod Q := by
  obtain ⟨Q, hQ⟩ := gs_existence_over_ratfunc k m ωs f₀ f₁ hk hn hm
  exact ⟨Q, hQ, fun q hq => UniqueFactorizationMonoid.irreducible_of_factor q hq,
    UniqueFactorizationMonoid.factors_prod hQ.Q_ne_0⟩

/-- **Hab25 §3, Step S4(b) — decoded codewords give irreducible factors of `Q`.**

If a degree-`< k` codeword polynomial `p` over `K = F(Z)` lies within the Guruswami–Sudan
Johnson radius of the generic fold, then its linear factor `Y - C p` is an associate of a
member of the irreducible factorization of the interpolant `Q`. This upgrades the S1/S2
divisibility `(Y - C p) ∣ Q` to membership in the S4 factor index set. -/
theorem decoded_linearFactor_mem_factors {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (hk : k + 1 ≤ n) (hm : 1 ≤ m)
    (p : ReedSolomon.code (liftedDomain ωs) k)
    {Q : (RatFunc F)[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain ωs) (genericFold f₀ f₁) Q)
    (h_dist :
      (hammingDist (genericFold f₀ f₁)
          (fun i => (ReedSolomon.codewordToPoly p).eval ((liftedDomain ωs) i)) : ℝ) / n <
        gs_johnson k n m) :
    ∃ q ∈ UniqueFactorizationMonoid.factors Q,
      Associated (X - C (ReedSolomon.codewordToPoly p)) q :=
  linearFactor_mem_factors_of_dvd hQ.Q_ne_0
    (gs_divisibility_over_ratfunc k m ωs f₀ f₁ hk hm p hQ h_dist)

/-- **Hab25 §3, Step S4 — factorization of the GS interpolant with index structure, packaged.**

There is a generic-fold GS interpolant `Q ∈ (RatFunc F)[X][Y]` satisfying the S2 `Conditions`
such that:

1. *(S3)* its `Y`-degree obeys `Q.natDegree ≤ gs_degree_bound k n m / (k - 1)`;
2. *(S4a)* `Q` factors into irreducibles: every member of
   `UniqueFactorizationMonoid.factors Q` is irreducible and their product is an associate
   of `Q`;
3. *(S4b)* every codeword within the GS Johnson radius of the generic fold contributes a linear
   factor `Y - C p` that is an associate of a member of `factors Q`;
4. *(S4c)* any finite family of messages whose linear factors divide `Q` is bounded **both** by
   the number of distinct irreducible factors of `Q` and by the S3 `Y`-degree cap
   `gs_degree_bound k n m / (k - 1)`.

This is the affine-pair *index structure* of S4: decoded codewords inject into the irreducible
factors of `Q`, whose count the S3 bound caps. The remaining deep content (each factor being
`(Y - (a(X) + Z·b(X)))^{p^f}`, S5/S6) is not claimed. -/
theorem gs_factorization_index_structure {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (hk1 : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) (hk : 0 < k - 1)
    (hkn : k + 1 ≤ n) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain ωs) (genericFold f₀ f₁) Q ∧
      Q.natDegree ≤ gs_degree_bound k n m / (k - 1) ∧
      (∀ q ∈ UniqueFactorizationMonoid.factors Q, Irreducible q) ∧
      Associated (UniqueFactorizationMonoid.factors Q).prod Q ∧
      (∀ p : ReedSolomon.code (liftedDomain ωs) k,
        (hammingDist (genericFold f₀ f₁)
            (fun i => (ReedSolomon.codewordToPoly p).eval ((liftedDomain ωs) i)) : ℝ) / n <
          gs_johnson k n m →
        ∃ q ∈ UniqueFactorizationMonoid.factors Q,
          Associated (X - C (ReedSolomon.codewordToPoly p)) q) ∧
      (∀ Ps : Finset (RatFunc F)[X], (∀ p ∈ Ps, (X - C p) ∣ Q) →
        Ps.card ≤ (UniqueFactorizationMonoid.factors Q).toFinset.card ∧
        Ps.card ≤ gs_degree_bound k n m / (k - 1)) := by
  obtain ⟨Q, hQ, hdeg⟩ := genericInterpolant_yDegree_le k m ωs f₀ f₁ hk1 hn hm hk
  refine ⟨Q, hQ, hdeg,
    fun q hq => UniqueFactorizationMonoid.irreducible_of_factor q hq,
    UniqueFactorizationMonoid.factors_prod hQ.Q_ne_0,
    fun p hdist => ?_, fun Ps hdvd => ?_⟩
  · exact linearFactor_mem_factors_of_dvd hQ.Q_ne_0
      (gs_divisibility_over_ratfunc k m ωs f₀ f₁ hkn hm p hQ hdist)
  · exact ⟨card_le_card_distinct_factors Q hQ.Q_ne_0 Ps hdvd,
      le_trans (GSFactorExtract.gs_list_size_le Q hQ.Q_ne_0 Ps hdvd) hdeg⟩

end GuruswamiSudan.OverRatFunc

#print axioms GuruswamiSudan.OverRatFunc.irreducible_linearFactor
#print axioms GuruswamiSudan.OverRatFunc.prime_linearFactor
#print axioms GuruswamiSudan.OverRatFunc.linearFactor_associated_iff
#print axioms GuruswamiSudan.OverRatFunc.linearFactor_mem_factors_of_dvd
#print axioms GuruswamiSudan.OverRatFunc.card_le_card_distinct_factors
#print axioms GuruswamiSudan.OverRatFunc.gs_interpolant_factorization
#print axioms GuruswamiSudan.OverRatFunc.decoded_linearFactor_mem_factors
#print axioms GuruswamiSudan.OverRatFunc.gs_factorization_index_structure
