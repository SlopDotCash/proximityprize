/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Factorization
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Cardinality
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic

/-!
# `R_q^H` is a Field Isomorphic to `F_{q^k}` (Hachi §3, Lemma 5)

This is the one piece of Hachi [NOZ26, §3] not yet covered by the rest of `Subfield/`: upgrading
the fixed subring `R_q^H` from "a `Subring` of cardinality `q^k`" (`card_fixedSubring_eq`) to "a
field isomorphic to `F_{q^k}`".

The route (blueprint `blueprint/src/lattices/hachi_subfield.tex`, Phases 4–5):

1. `X^{2^α}+1 = p₁·p₂` (coprime irreducibles, `exists_irreducible_factorization`), and `σ_{-1}`
   (`= X ↦ X⁻¹`) relates to polynomial reversal by `mk(reverse p) = σ_{-1}(mk p)·(mk X)^{deg p}`
   (`mk_reverse_eq_galoisAutₛ_mul`); with `p₁.reverse ~ p₂` (`no_selfReciprocal_factor`) this makes
   `σ_{-1}` swap the two factors.
2. Hence in `S = Z_q[X]/(X^{2^α}+1)` every nonzero `σ_{-1}`-fixed element is a unit
   (`galoisAutₛ_fixed_isUnit`): if `p₁ ∣ g` then `σ_{-1}`-fixedness forces `p₂ ∣ g` too, so
   `X^{2^α}+1 ∣ g` and the element is `0`. Transporting to `R_q` gives `conjFixedSubring_isField`.
3. `R_q^H ⊆ R_q^{σ_{-1}}` (`fixedSubring_le_conjFixedSubring`) is then a finite integral domain,
   hence a field (`fixedSubring_isField`).
4. A finite field of cardinality `q^k` (`card_fixedSubring_eq`) is `≃+* GaloisField q k`
   (`fixedSubringEquivGaloisField`).

## Status

`no_selfReciprocal_factor` (blueprint Lemma 4.5) is proved. Reversal swaps the two irreducible
factors of `X^{2^α}+1`: a root in `AdjoinRoot p₁` has Frobenius orbit of size `deg p₁`, and that
orbit cannot contain the inverse root, because `neg_one_notMem_powers_q` says `−1 ∉ ⟨q⟩`. The
reverse identity, factor existence, the core unit lemma, and the assembly
(`conjFixedSubring_isField`, `fixedSubring_isField`, `fixedSubringEquivGaloisField`) then go
through with no residual axiom.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

open Polynomial

namespace ArkLib.Lattices.CyclotomicModulus

variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]

/-! ## Phase 4a: the `σ_{-1} ↔ reverse` correspondence -/

open Polynomial in
omit [NeZero q] in
/-- **The reverse identity.** In `S = Z_q[X]/(X^{2^α}+1)`, the conjugation `σ_{-1}` (here the
semantic automorphism `galoisAutₛ` of exponent `conjExp = 2^{α+1}-1`) and the polynomial reversal
are related by `mk(reverse p) = σ_{-1}(mk p) · (mk X)^{deg p}`.

This is the concrete handle behind "`σ_{-1}` swaps the two factors": since `(mk X)^{deg p}` is a
unit, `σ_{-1}` carries the principal ideal `(mk p)` onto `(mk (reverse p))`. The proof routes
through Mathlib's `Polynomial.eval₂_reverse_mul_pow` with the evaluation point `⅟(mk X) = (mk X)^c`
(as `(mk X)^{2^{α+1}} = 1`), avoiding any coefficient-sum manipulation. -/
theorem mk_reverse_eq_galoisAutₛ_mul (α : ℕ) (p : (ZMod q)[X]) :
    Ideal.Quotient.mk (powTwoCyclotomic (R := ZMod q) α).modIdeal p.reverse
      = galoisAutₛ α (conjExp α) (conjExp_odd α)
          (Ideal.Quotient.mk (powTwoCyclotomic (R := ZMod q) α).modIdeal p)
        * (Ideal.Quotient.mk (powTwoCyclotomic (R := ZMod q) α).modIdeal X) ^ p.natDegree := by
  set mk := Ideal.Quotient.mk (powTwoCyclotomic (R := ZMod q) α).modIdeal with hmkdef
  set x : (powTwoCyclotomic (R := ZMod q) α).CyclotomicRing := mk X with hxdef
  have hx2d : x ^ (2 ^ (α + 1)) = 1 := by rw [hxdef, ← map_pow]; exact mk_X_pow_conductor_eq_one α
  have hcx : x ^ (conjExp α) * x = 1 := by
    rw [← pow_succ, conjExp, Nat.sub_add_cancel Nat.one_le_two_pow, hx2d]
  letI invx : Invertible x := ⟨x ^ (conjExp α), hcx, by rw [mul_comm]; exact hcx⟩
  set i : ZMod q →+* (powTwoCyclotomic (R := ZMod q) α).CyclotomicRing := mk.comp C with hidef
  have heval_mk : ∀ r : (ZMod q)[X], eval₂ i x r = mk r := by
    have hext : (Polynomial.eval₂RingHom i x) = mk := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [Polynomial.coe_eval₂RingHom, eval₂_C, hidef, RingHom.comp_apply]
      · simp only [Polynomial.coe_eval₂RingHom, eval₂_X, hxdef]
    intro r; rw [← hext]; rfl
  have hxc : mk (X ^ (conjExp α)) = ⅟x := by rw [map_pow]; rfl
  have hsigma : galoisAutₛ α (conjExp α) (conjExp_odd α) (mk p) = eval₂ i (⅟x) p := by
    rw [galoisAutₛ_mk, Polynomial.aeval_def, Polynomial.algebraMap_eq, Polynomial.hom_eval₂,
      ← hidef, hxc]
  have hrev := Polynomial.eval₂_reverse_mul_pow i (⅟x) p
  rw [invOf_invOf, heval_mk, ← hsigma] at hrev
  rw [← hrev, mul_assoc, ← mul_pow, invOf_mul_self, one_pow, mul_one]

/-! ## Phase 4b: factorization into two coprime irreducibles -/

omit [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **Factor existence.** For `q ≡ 5 (mod 8)`, `X^{2^α}+1` factors over `Z_q` as a product of two
coprime irreducible polynomials. Extracted from `cyclotomic_card_normalizedFactors` (the
two normalized factors), with coprimality from `Irreducible.coprime_iff_not_dvd`. -/
theorem exists_irreducible_factorization (hq5 : q % 8 = 5) {α : ℕ} (hα : 1 ≤ α) :
    ∃ p₁ p₂ : (ZMod q)[X], Irreducible p₁ ∧ Irreducible p₂ ∧ IsCoprime p₁ p₂ ∧
      (X ^ (2 ^ α) + 1 : (ZMod q)[X]) = p₁ * p₂ := by
  classical
  have hqcop : ¬ (q ∣ 2 ^ (α + 1)) := by
    intro h
    have hq2 : q ∣ 2 := Nat.Prime.dvd_of_dvd_pow Fact.out h
    have := Nat.le_of_dvd (by norm_num) hq2; omega
  haveI : NeZero ((2 ^ (α + 1) : ℕ) : ZMod q) :=
    ⟨by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqcop⟩
  set f : (ZMod q)[X] := cyclotomic (2 ^ (α + 1)) (ZMod q) with hf
  have hfne : f ≠ 0 := cyclotomic_ne_zero _ _
  have hf_monic : f.Monic := cyclotomic.monic _ _
  have hsqf : Squarefree f := squarefree_cyclotomic _ _
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hfne).mp hsqf
  have hcard : Multiset.card (UniqueFactorizationMonoid.normalizedFactors f) = 2 := by
    have h2 := cyclotomic_card_normalizedFactors q hq5 hα
    rw [← hf] at h2
    rwa [← Multiset.toFinset_card_of_nodup hnodup]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  have ha_mem : a ∈ UniqueFactorizationMonoid.normalizedFactors f := by rw [hab]; simp
  have hb_mem : b ∈ UniqueFactorizationMonoid.normalizedFactors f := by rw [hab]; simp
  have ha_irr := UniqueFactorizationMonoid.irreducible_of_normalized_factor a ha_mem
  have hb_irr := UniqueFactorizationMonoid.irreducible_of_normalized_factor b hb_mem
  have ha_monic : a.Monic := by
    have h := UniqueFactorizationMonoid.normalize_normalized_factor a ha_mem
    rw [← h]; exact monic_normalize ha_irr.ne_zero
  have hb_monic : b.Monic := by
    have h := UniqueFactorizationMonoid.normalize_normalized_factor b hb_mem
    rw [← h]; exact monic_normalize hb_irr.ne_zero
  have hne : a ≠ b := by have := hnodup; rw [hab] at this; simpa using this
  have hprod : a * b = f := by
    have hassoc : Associated (a * b) f := by
      have := UniqueFactorizationMonoid.prod_normalizedFactors hfne
      rwa [hab, Multiset.prod_pair] at this
    calc a * b = normalize (a * b) := ((ha_monic.mul hb_monic).normalize_eq_self).symm
      _ = normalize f := normalize_eq_normalize_iff.mpr ⟨hassoc.dvd, hassoc.symm.dvd⟩
      _ = f := hf_monic.normalize_eq_self
  have hcop : IsCoprime a b := by
    rw [ha_irr.coprime_iff_not_dvd]
    intro hdvd
    have hassoc : Associated a b := ha_irr.associated_of_dvd hb_irr hdvd
    refine hne ?_
    calc a = normalize a := (ha_monic.normalize_eq_self).symm
      _ = normalize b := normalize_eq_normalize_iff.mpr ⟨hassoc.dvd, hassoc.symm.dvd⟩
      _ = b := hb_monic.normalize_eq_self
  exact ⟨a, b, ha_irr, hb_irr, hcop, by rw [Xpow_add_one_eq_cyclotomic q α, ← hf, ← hprod]⟩

/-! ## Phase 4: the swap -/

omit [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- `X^n + 1` is fixed by reversal for `n > 0`. -/
private theorem reverse_X_pow_add_one {R : Type*} [CommRing R] [Nontrivial R]
    (n : ℕ) (_hn : 0 < n) : (X ^ n + 1 : R[X]).reverse = X ^ n + 1 := by
  have hdeg : (X ^ n : R[X]).natDegree = n := natDegree_X_pow _
  rw [← C_1, reverse_add_C, hdeg]
  have hrevX : (X ^ n : R[X]).reverse = 1 := by
    rw [show (X ^ n : R[X]) = C (1 : R) * X ^ n by simp, reverse_mul_X_pow, reverse_C, map_one]
  rw [hrevX, map_one, one_mul, add_comm]

omit [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- Reversal preserves irreducibility when the constant term is nonzero.

Over a field, `reverse` is an involution on that locus (`natTrailingDegree = 0`). A nontrivial
trailing gap in a factor would kill the constant term of the reverse, which is the original
leading coefficient. -/
private theorem irreducible_reverse_of_natTrailingDegree_eq_zero {p : (ZMod q)[X]}
    (hp : Irreducible p) (htr : p.natTrailingDegree = 0) : Irreducible p.reverse := by
  have hrevdeg : p.reverse.natDegree = p.natDegree := by rw [reverse_natDegree, htr, Nat.sub_zero]
  have hinv : p.reverse.reverse = p := by
    rw [reverse, hrevdeg, reverse, reflect_reflect]
  have hpos : 0 < p.natDegree := by
    apply Nat.pos_of_ne_zero
    intro h0
    have hdeg : p.degree = 0 := by rw [degree_eq_natDegree hp.ne_zero, h0]; rfl
    exact hp.not_isUnit ((isUnit_iff_degree_eq_zero).mpr hdeg)
  refine ⟨?_, fun a b hab => ?_⟩
  · intro hunit
    have hdeg0 : p.reverse.natDegree = 0 := by
      rw [natDegree_eq_zero_iff_degree_le_zero]
      exact le_of_eq ((isUnit_iff_degree_eq_zero).mp hunit)
    exact absurd (hrevdeg.symm.trans hdeg0) (Nat.ne_of_gt hpos)
  · have hpr : p = a.reverse * b.reverse := by rw [← hinv, hab, reverse_mul_of_domain]
    have unit_factor {c d : (ZMod q)[X]} (hcd : p.reverse = c * d) (hu : IsUnit c.reverse) :
        IsUnit c := by
      have hnat0 : c.reverse.natDegree = 0 := by
        rw [natDegree_eq_zero_iff_degree_le_zero]
        exact le_of_eq ((isUnit_iff_degree_eq_zero).mp hu)
      have htrdeg : c.natDegree = c.natTrailingDegree :=
        le_antisymm (Nat.sub_eq_zero_iff_le.mp (by simpa [reverse_natDegree] using hnat0))
          (natTrailingDegree_le_natDegree c)
      have hk : c.natDegree = 0 := by
        by_contra hk
        have hcoeff : c.coeff 0 = 0 :=
          coeff_eq_zero_of_lt_natTrailingDegree (by rwa [← htrdeg, Nat.pos_iff_ne_zero])
        have hconst : (p.reverse).coeff 0 = 0 := by rw [hcd, mul_coeff_zero, hcoeff, zero_mul]
        exact (leadingCoeff_ne_zero.mpr hp.ne_zero) (coeff_zero_reverse p ▸ hconst)
      have hcC : c = C (c.coeff 0) :=
        eq_C_of_degree_le_zero ((natDegree_eq_zero_iff_degree_le_zero).mp hk)
      rw [hcC, reverse_C, ← hcC] at hu
      exact hu
    rcases hp.isUnit_or_isUnit hpr with hA | hB
    · exact Or.inl (unit_factor hab hA)
    · exact Or.inr (unit_factor (by rw [hab, mul_comm]) hB)

omit [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- Frobenius commutes with evaluation of a polynomial defined over `ZMod q`. -/
private theorem aeval_pow_char {K : Type*} [Field K] [Algebra (ZMod q) K] [CharP K q]
    (poly : (ZMod q)[X]) (x : K) : aeval (x ^ q) poly = (aeval x poly) ^ q := by
  induction poly using Polynomial.induction_on with
  | C a =>
    rw [aeval_C, aeval_C, ← map_pow, ZMod.pow_card]
  | add poly r ihp ihr =>
    rw [aeval_add, aeval_add, ihp, ihr, add_pow_char (aeval x poly) (aeval x r) q]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, aeval_mul, aeval_X]
    rw [aeval_mul (p := C a * X ^ n), aeval_X, mul_pow, ih]

omit [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- A nonzero polynomial over `ZMod q` has at most `natDegree` roots in any extension field. -/
private theorem card_le_natDegree_of_aeval_eq_zero {K : Type*} [Field K] [Algebra (ZMod q) K]
    {p : (ZMod q)[X]} {s : Finset K} (hp : p ≠ 0) (hs : ∀ x ∈ s, aeval x p = 0) :
    s.card ≤ p.natDegree := by
  classical
  have hmap : Function.Injective (algebraMap (ZMod q) K) := by
    refine (injective_iff_map_eq_zero (algebraMap (ZMod q) K)).mpr ?_
    intro a ha
    by_contra hne
    have hunit : IsUnit (algebraMap (ZMod q) K a) := (isUnit_iff_ne_zero.mpr hne).map _
    rw [ha] at hunit
    exact not_isUnit_zero hunit
  let P : K[X] := p.map (algebraMap (ZMod q) K)
  have hP0 : P ≠ 0 := (Polynomial.map_eq_zero_iff hmap).not.mpr hp
  have hdiv : ∀ t : Finset K, (∀ x ∈ t, aeval x p = 0) → (∏ x ∈ t, (X - C x)) ∣ P := by
    intro t
    induction t using Finset.induction with
    | empty =>
      intro _
      simp
    | insert a t ha ih =>
      intro ht
      obtain ⟨g, hg⟩ := ih (fun x hx => ht x (Finset.mem_insert_of_mem hx))
      have hPeval : P.eval a = 0 := by
        change (p.map (algebraMap (ZMod q) K)).eval a = 0
        rw [eval_map, ← aeval_def]
        exact ht a (Finset.mem_insert_self a t)
      have heval : (∏ x ∈ t, (X - C x)).eval a ≠ 0 := by
        rw [eval_prod, Finset.prod_ne_zero_iff]
        intro x hx
        rw [eval_sub, eval_X, eval_C]
        exact sub_ne_zero.mpr fun hax => ha (hax ▸ hx)
      have hg0 : g.eval a = 0 := by
        rw [hg, eval_mul, mul_eq_zero] at hPeval
        exact hPeval.resolve_left heval
      obtain ⟨g', hg'⟩ := (dvd_iff_isRoot).mpr hg0
      refine ⟨g', ?_⟩
      rw [Finset.prod_insert ha, hg, hg']
      ring
  have hprod := hdiv s hs
  have hdegprod : (∏ x ∈ s, (X - C x)).natDegree = s.card := by
    rw [natDegree_prod_of_monic (s := s) (f := fun x => X - C x) (fun _ _ => monic_X_sub_C _)]
    simp [Finset.sum_const]
  have hPdeg : P.natDegree = p.natDegree := natDegree_map_eq_of_injective hmap p
  have hle := natDegree_le_of_dvd hprod hP0
  rwa [hdegprod, hPdeg] at hle

/-- **(Phase 4, blueprint Lemma 4.5, `lem:no_selfReciprocal`)** For `q ≡ 5 (mod 8)`, reversal
*swaps* the two irreducible factors of `X^{2^α}+1`: if `X^{2^α}+1 = p₁ · p₂` with `p₁, p₂`
irreducible, then `p₁.reverse` is associated to `p₂`.

`X^{2^α}+1 = Φ_{2^{α+1}}` is self-reciprocal, so reversal permutes its irreducible factors. The
permutation is the swap: the roots of `p₁` in `AdjoinRoot p₁` are the Frobenius orbit of the
adjoined root `ζ`, a coset of `⟨q⟩` in `(Z/2^{α+1})ˣ`, while `ζ⁻¹` is a root of `p₁.reverse`.
Closing the orbit under inversion would force `−1 ∈ ⟨q⟩`, contradicting `neg_one_notMem_powers_q`.
Each irreducible factor has degree `orderOf q = 2^{α-1}` by
`natDegree_of_dvd_cyclotomic_of_irreducible`, so the orbit exhausts the roots. -/
theorem no_selfReciprocal_factor (hq5 : q % 8 = 5) {α : ℕ} (hα : 1 ≤ α)
    {p₁ p₂ : (ZMod q)[X]} (hp₁ : Irreducible p₁) (hp₂ : Irreducible p₂)
    (hf : (X ^ (2 ^ α) + 1 : (ZMod q)[X]) = p₁ * p₂) :
    Associated p₁.reverse p₂ := by
  classical
  set f : (ZMod q)[X] := X ^ (2 ^ α) + 1
  have hcoeff0 : p₁.coeff 0 ≠ 0 := by
    intro h0
    have hroot0 : p₁.eval 0 = 0 := by simpa [coeff_zero_eq_eval_zero] using h0
    have hf0 : f.eval 0 = 0 :=
      eval_eq_zero_of_dvd_of_eval_eq_zero (by rw [hf]; exact dvd_mul_right _ _) hroot0
    simp [f, eval_pow, eval_X, eval_one, eval_add] at hf0
  have htr : p₁.natTrailingDegree = 0 :=
    Nat.eq_zero_of_le_zero (natTrailingDegree_le_of_ne_zero (n := 0) (by simpa using hcoeff0))
  have hrev : Irreducible p₁.reverse := irreducible_reverse_of_natTrailingDegree_eq_zero q hp₁ htr
  have hdvd : p₁.reverse ∣ p₁ * p₂ := by
    have hfrev : f.reverse = f :=
      reverse_X_pow_add_one (2 ^ α) (pow_pos (by decide : (0 : ℕ) < 2) α)
    have hmul : f.reverse = p₁.reverse * p₂.reverse := by rw [hf, reverse_mul_of_domain]
    rw [hfrev] at hmul
    refine ⟨p₂.reverse, ?_⟩
    rw [← hf]
    exact hmul
  have hdeg : p₁.natDegree = 2 ^ (α - 1) := by
    have hcard : Fintype.card (ZMod q) = q ^ 1 := by rw [pow_one]; exact ZMod.card q
    have hcop : Nat.Coprime q (2 ^ (α + 1)) :=
      Nat.Coprime.pow_right _
        ((Nat.coprime_primes (Fact.out : q.Prime) Nat.prime_two).mpr (by omega))
    have hdiv : p₁ ∣ cyclotomic (2 ^ (α + 1)) (ZMod q) := by
      rw [← Xpow_add_one_eq_cyclotomic q α]
      change p₁ ∣ f
      rw [hf]
      exact dvd_mul_right _ _
    rw [Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible hcard hcop hdiv hp₁, ← orderOf_units,
      ZMod.coe_unitOfCoprime, pow_one]
    exact orderOf_q_eq q hq5 hα
  have hself : ¬ Associated p₁.reverse p₁ := by
    intro hassoc
    haveI : Fact (Irreducible p₁) := ⟨hp₁⟩
    let K := AdjoinRoot p₁
    have hmap : Function.Injective (algebraMap (ZMod q) K) := by
      refine (injective_iff_map_eq_zero (algebraMap (ZMod q) K)).mpr ?_
      intro a ha
      by_contra hne
      have hunit : IsUnit (algebraMap (ZMod q) K a) := (isUnit_iff_ne_zero.mpr hne).map _
      rw [ha] at hunit
      exact not_isUnit_zero hunit
    haveI : CharP K q := charP_of_injective_algebraMap hmap q
    let ζ : K := AdjoinRoot.root p₁
    have hζeval : aeval ζ p₁ = 0 := by
      unfold ζ
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have hζpow : ζ ^ (2 ^ α) = -1 := by
      have h0 : aeval ζ f = 0 := by rw [hf, aeval_mul, hζeval, zero_mul]
      have hsum : ζ ^ (2 ^ α) + 1 = 0 := by simpa [f, aeval_add, aeval_X_pow, aeval_one] using h0
      exact eq_neg_of_add_eq_zero_left hsum
    have hone : ζ ^ (2 ^ (α + 1)) = 1 := by
      rw [show 2 ^ (α + 1) = 2 ^ α * 2 by rw [pow_succ, mul_comm], pow_mul, hζpow]
      norm_num
    have hζ0 : ζ ≠ 0 := by
      intro h
      rw [h, zero_pow (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0))] at hone
      exact one_ne_zero hone.symm
    have htwo : (2 : K) ≠ 0 := by
      intro h
      have h2q : (2 : ZMod q) = 0 := by
        apply hmap
        simpa [map_ofNat] using h
      have hdvd2 : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using h2q)
      have hqle : q ≤ 2 := Nat.le_of_dvd (by decide) hdvd2
      have hqge : 5 ≤ q := by omega
      omega
    have hord : orderOf ζ = 2 ^ (α + 1) := by
      have hdvd := orderOf_dvd_of_pow_eq_one hone
      obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hk_eq : k = α + 1 := by
        refine le_antisymm hk ?_
        by_contra hlt
        have hdivα : orderOf ζ ∣ 2 ^ α := by
          rw [heq]
          exact pow_dvd_pow 2 (by omega)
        have h1 : ζ ^ (2 ^ α) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdivα
        rw [hζpow] at h1
        apply htwo
        calc (2 : K) = 1 + 1 := by norm_num
          _ = -1 + 1 := by nth_rw 1 [← h1]
          _ = 0 := by ring
      rw [heq, hk_eq]
    have horbit_root : ∀ i, aeval (ζ ^ (q ^ i)) p₁ = 0 := by
      intro i
      induction i with
      | zero => simpa using hζeval
      | succ i ih =>
        have hstep := aeval_pow_char q p₁ (ζ ^ (q ^ i))
        rw [ih, zero_pow (by omega : q ≠ 0)] at hstep
        have hpow : (ζ ^ (q ^ i)) ^ q = ζ ^ (q ^ (i + 1)) := by
          rw [← pow_mul, ← pow_succ]
        simpa [hpow] using hstep
    have horbit_inj : ∀ i j, i < 2 ^ (α - 1) → j < 2 ^ (α - 1) →
        ζ ^ (q ^ i) = ζ ^ (q ^ j) → i = j := by
      intro i j hi hj heq
      wlog hij : i ≤ j generalizing i j
      · exact (this j i hj hi heq.symm (le_of_not_ge hij)).symm
      have hle : q ^ i ≤ q ^ j := Nat.pow_le_pow_right (by omega) hij
      have hdiff : ζ ^ (q ^ j - q ^ i) = 1 := by
        have hmul : ζ ^ (q ^ i) * ζ ^ (q ^ j - q ^ i) = ζ ^ (q ^ j) := by
          rw [← pow_add, Nat.add_sub_cancel' hle]
        rw [heq] at hmul
        exact mul_left_cancel₀ (pow_ne_zero _ hζ0) (by simpa [mul_one] using hmul)
      have hN : 2 ^ (α + 1) ∣ q ^ j - q ^ i := by
        rw [← hord]
        exact orderOf_dvd_of_pow_eq_one hdiff
      have hfac : q ^ j - q ^ i = q ^ i * (q ^ (j - i) - 1) := by
        calc
          q ^ j - q ^ i = q ^ (i + (j - i)) - q ^ i := by rw [Nat.add_sub_of_le hij]
          _ = q ^ i * q ^ (j - i) - q ^ i * 1 := by rw [pow_add, mul_one]
          _ = q ^ i * (q ^ (j - i) - 1) := by rw [← Nat.mul_sub_left_distrib]
      rw [hfac] at hN
      have hcop : Nat.Coprime (2 ^ (α + 1)) (q ^ i) := by
        have hodd : Nat.Coprime 2 q :=
          (Nat.coprime_primes Nat.prime_two (Fact.out : q.Prime)).mpr (by omega)
        exact (hodd.pow_right i).pow_left (α + 1)
      have hsubdv : 2 ^ (α + 1) ∣ q ^ (j - i) - 1 := hcop.dvd_of_dvd_mul_left hN
      have hpow1 : (q : ZMod (2 ^ (α + 1))) ^ (j - i) = 1 := by
        have hge : 1 ≤ q ^ (j - i) := Nat.one_le_pow _ _ (by omega)
        have hcast : ((q ^ (j - i) - 1 : ℕ) : ZMod (2 ^ (α + 1))) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).mpr hsubdv
        rw [Nat.cast_sub hge, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at hcast
        exact hcast
      have hdiv_ord : 2 ^ (α - 1) ∣ j - i := by
        rw [← orderOf_q_eq q hq5 hα]
        exact orderOf_dvd_of_pow_eq_one hpow1
      have hji0 : j - i = 0 := by
        by_contra hne
        have hposd : 0 < j - i := Nat.pos_of_ne_zero hne
        have hle_ord := Nat.le_of_dvd hposd hdiv_ord
        omega
      omega
    let d : ℕ := 2 ^ (α - 1)
    let s : Finset K := (Finset.range d).image (fun i => ζ ^ (q ^ i))
    have hsroot : ∀ x ∈ s, aeval x p₁ = 0 := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact horbit_root i
    have hscard : s.card = d := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj heq
      exact horbit_inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) heq
    obtain ⟨u, hu⟩ := hassoc
    haveI : Invertible ζ := invertibleOfNonzero hζ0
    have hrev_root : aeval ζ⁻¹ p₁.reverse = 0 := by
      rw [aeval_def, ← invOf_eq_inv]
      exact (eval₂_reverse_eq_zero_iff (algebraMap (ZMod q) K) ζ p₁).mpr
        (by rw [← aeval_def]; exact hζeval)
    have hinv_root : aeval ζ⁻¹ p₁ = 0 := by
      have hprod : aeval ζ⁻¹ (p₁.reverse * (u : (ZMod q)[X])) = 0 := by
        rw [aeval_mul, hrev_root, zero_mul]
      simpa [hu] using hprod
    have hmem : ∃ i, i < d ∧ ζ⁻¹ = ζ ^ (q ^ i) := by
      by_contra hnot
      push Not at hnot
      have hnotmem : ζ⁻¹ ∉ s := by
        intro hs
        obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hs
        exact hnot i (Finset.mem_range.mp hi) he.symm
      have htroot : ∀ x ∈ insert ζ⁻¹ s, aeval x p₁ = 0 := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hinv_root
        · exact hsroot x hx
      have hcard := card_le_natDegree_of_aeval_eq_zero q hp₁.ne_zero htroot
      rw [Finset.card_insert_of_notMem hnotmem, hscard, hdeg] at hcard
      omega
    obtain ⟨i, _hi, hiζ⟩ := hmem
    have hpowi : ζ ^ (q ^ i + 1) = 1 := by
      rw [pow_succ, ← hiζ, inv_mul_cancel₀ hζ0]
    have hdvdN : 2 ^ (α + 1) ∣ q ^ i + 1 := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hpowi
    have hmod : (q : ZMod (2 ^ (α + 1))) ^ i = -1 := by
      have h0 : ((q ^ i + 1 : ℕ) : ZMod (2 ^ (α + 1))) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hdvdN
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, add_eq_zero_iff_eq_neg] at h0
      exact h0
    exact neg_one_notMem_powers_q q hq5 hα i hmod
  have hprime : Prime p₁.reverse := UniqueFactorizationMonoid.irreducible_iff_prime.mp hrev
  rcases hprime.dvd_mul.mp hdvd with h | h
  · exact absurd (hrev.associated_of_dvd hp₁ h) hself
  · exact hrev.associated_of_dvd hp₂ h

open Polynomial in
/-- **Core unit lemma.** In `S = Z_q[X]/(X^{2^α}+1)`, every nonzero `σ_{-1}`-fixed element is a
unit. If `b = mk g` is not a unit then `g` shares a factor `p_i` with `X^{2^α}+1 = p₁p₂`; the
reverse identity plus the swap `p₁.reverse ~ p₂` force `g` to be divisible by *both* `p₁` and `p₂`,
hence by `X^{2^α}+1`, so `b = 0`. -/
theorem galoisAutₛ_fixed_isUnit (hq5 : q % 8 = 5) {α : ℕ} (hα : 1 ≤ α)
    {b : (powTwoCyclotomic (R := ZMod q) α).CyclotomicRing}
    (hbfix : galoisAutₛ α (conjExp α) (conjExp_odd α) b = b) (hb0 : b ≠ 0) :
    IsUnit b := by
  classical
  obtain ⟨p₁, p₂, hp₁, hp₂, hcop, hf⟩ := exists_irreducible_factorization q hq5 hα
  have hswap12 : Associated p₁.reverse p₂ := no_selfReciprocal_factor q hq5 hα hp₁ hp₂ hf
  have hswap21 : Associated p₂.reverse p₁ :=
    no_selfReciprocal_factor q hq5 hα hp₂ hp₁ (by rw [hf]; ring)
  set mk := Ideal.Quotient.mk (powTwoCyclotomic (R := ZMod q) α).modIdeal with hmkdef
  have hmk_zero : ∀ z : (ZMod q)[X], mk z = 0 ↔ (X ^ (2 ^ α) + 1 : (ZMod q)[X]) ∣ z := fun z => by
    rw [hmkdef, Ideal.Quotient.eq_zero_iff_mem, modIdeal, powTwoCyclotomic_toPoly,
      Ideal.mem_span_singleton]
  -- `mk X` is a unit (`(mk X)^{2^{α+1}} = 1`)
  have hmkX_unit : IsUnit (mk X) :=
    IsUnit.of_mul_eq_one ((mk X) ^ (conjExp α)) (by
      rw [mul_comm, ← pow_succ, conjExp, Nat.sub_add_cancel Nat.one_le_two_pow, ← map_pow,
        mk_X_pow_conductor_eq_one α])
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
  by_contra hbnu
  have hncop : ¬ IsCoprime g (X ^ (2 ^ α) + 1 : (ZMod q)[X]) := by
    rintro ⟨u, v, huv⟩
    refine hbnu (IsUnit.of_mul_eq_one (mk u) ?_)
    have := congrArg mk huv
    rwa [map_add, map_mul, map_mul, (hmk_zero _).mpr (dvd_refl _), mul_zero, add_zero, map_one,
      mul_comm] at this
  -- the key step: a factor `p` of `g` forces its "reverse partner" `p'` to divide `g` too
  have keystep : ∀ (p p' : (ZMod q)[X]), Associated p.reverse p' →
      p' ∣ (X ^ (2 ^ α) + 1 : (ZMod q)[X]) → p ∣ g → p' ∣ g := by
    intro p p' hpp' hp'f hpg
    have hd1 : mk p' ∣ mk p.reverse := map_dvd mk hpp'.symm.dvd
    rw [mk_reverse_eq_galoisAutₛ_mul q α p] at hd1
    have hd2 : mk p' ∣ galoisAutₛ α (conjExp α) (conjExp_odd α) (mk p) :=
      ((hmkX_unit.pow p.natDegree).dvd_mul_right).mp hd1
    have hd3 : galoisAutₛ α (conjExp α) (conjExp_odd α) (mk p) ∣ mk g := by
      obtain ⟨h, hh⟩ := hpg
      refine ⟨galoisAutₛ α (conjExp α) (conjExp_odd α) (mk h), ?_⟩
      rw [← map_mul, ← hbfix, hh, map_mul]
    obtain ⟨c, hc⟩ := hd2.trans hd3
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have hz : (X ^ (2 ^ α) + 1 : (ZMod q)[X]) ∣ (g - p' * c') := by
      rw [← hmk_zero, map_sub, map_mul, ← hc, sub_self]
    have : p' ∣ (g - p' * c') := hp'f.trans hz
    simpa using dvd_add this (Dvd.intro c' rfl)
  rw [hf, IsCoprime.mul_right_iff, not_and_or] at hncop
  have hfg : (X ^ (2 ^ α) + 1 : (ZMod q)[X]) ∣ g := by
    rw [hf]
    rcases hncop with h1 | h2
    · have hp1g : p₁ ∣ g := by
        by_contra hnd
        exact h1 (isCoprime_comm.mp ((hp₁.coprime_iff_not_dvd).mpr hnd))
      exact hcop.mul_dvd hp1g (keystep p₁ p₂ hswap12 (hf ▸ dvd_mul_left p₂ p₁) hp1g)
    · have hp2g : p₂ ∣ g := by
        by_contra hnd
        exact h2 (isCoprime_comm.mp ((hp₂.coprime_iff_not_dvd).mpr hnd))
      exact hcop.mul_dvd (keystep p₂ p₁ hswap21 (hf ▸ dvd_mul_right p₁ p₂) hp2g) hp2g
  exact hb0 ((hmk_zero g).mpr hfg)

/-! ## Phase 5: assembling the field structure and the isomorphism -/

/-- **`R_q^{σ_{-1}}` is a field** (blueprint Theorem, Phase 5). For `q ≡ 5 (mod 8)`, every nonzero
`σ_{-1}`-fixed element is a unit: if `p₁ ∣ g` then the reverse identity plus the swap
`p₁.reverse ~ p₂` force `p₂ ∣ g` too, so `X^{2^α}+1 ∣ g` and the element vanishes.

The swap `no_selfReciprocal_factor` supplies the factor interchange: transport to
`S = Z_q[X]/(X^{2^α}+1)` via `Rq.equivQuotient`, where `conjAut` becomes `galoisAutₛ`
(`galoisAut_toQuotient`), and apply the core unit lemma `galoisAutₛ_fixed_isUnit`. The inverse of
a `σ_{-1}`-fixed unit is again fixed (apply `σ_{-1}` to `a·a⁻¹ = 1` and cancel the unit). -/
theorem conjFixedSubring_isField (hq5 : q % 8 = 5) {α : ℕ} (hα : 1 ≤ α) :
    IsField (conjFixedSubring (R := ZMod q) α) := by
  haveI hntC : Nontrivial (powTwoCyclotomic (R := ZMod q) α).CyclotomicRing := by
    refine ⟨0, 1, fun h => ?_⟩
    rw [show (1 : (powTwoCyclotomic (R := ZMod q) α).CyclotomicRing)
          = Ideal.Quotient.mk _ 1 from (map_one _).symm, eq_comm,
        Ideal.Quotient.eq_zero_iff_mem, modIdeal, powTwoCyclotomic_toPoly,
        Ideal.mem_span_singleton] at h
    have hdeg := Polynomial.natDegree_le_of_dvd h one_ne_zero
    rw [Polynomial.natDegree_one, show (X ^ (2 ^ α) + 1 : (ZMod q)[X]) = X ^ (2 ^ α) + C 1 by
      rw [map_one], Polynomial.natDegree_X_pow_add_C] at hdeg
    exact absurd hdeg (Nat.not_le.mpr (by positivity))
  haveI : Nontrivial (Rq (powTwoCyclotomic (R := ZMod q) α)) := by
    refine ⟨0, 1, fun h => ?_⟩
    have h2 := congrArg (Rq.equivQuotient (powTwoCyclotomic (R := ZMod q) α)) h
    rw [map_zero, map_one] at h2
    exact zero_ne_one h2
  haveI : Nontrivial (conjFixedSubring (R := ZMod q) α) := inferInstance
  refine ⟨exists_pair_ne _, mul_comm, ?_⟩
  intro a ha
  set Ψ := Rq.equivQuotient (powTwoCyclotomic (R := ZMod q) α) with hΨ
  have haval_fix : conjAut α (a : Rq (powTwoCyclotomic (R := ZMod q) α)) = a :=
    (mem_conjFixedSubring_iff α _).mp a.property
  have haval0 : (a : Rq (powTwoCyclotomic (R := ZMod q) α)) ≠ 0 :=
    fun h => ha (Subtype.ext (by rw [h]; rfl))
  have hbfix : galoisAutₛ α (conjExp α) (conjExp_odd α) (Ψ a) = Ψ a := by
    have h1 := (galoisAut_toQuotient α (conjExp α) (conjExp_odd α)
      (a : Rq (powTwoCyclotomic (R := ZMod q) α))).symm
    have h2 : galoisAut (powTwoCyclotomic α) (conjExp α)
        (a : Rq (powTwoCyclotomic (R := ZMod q) α)) = a := by
      have h := haval_fix; rwa [conjAut, galoisRingHom_apply] at h
    rw [show Ψ (a : Rq (powTwoCyclotomic (R := ZMod q) α))
        = Rq.toQuotient _ a from rfl, h1, h2]
  have hb0 : Ψ (a : Rq (powTwoCyclotomic (R := ZMod q) α)) ≠ 0 := by
    rw [Ne, ← map_zero Ψ]; exact fun h => haval0 (Ψ.injective h)
  have hunitC := galoisAutₛ_fixed_isUnit q hq5 hα hbfix hb0
  have hunitRq : IsUnit (a : Rq (powTwoCyclotomic (R := ZMod q) α)) := by
    have := hunitC.map Ψ.symm
    rwa [Ψ.symm_apply_apply] at this
  obtain ⟨u, hu⟩ := hunitRq
  set c : Rq (powTwoCyclotomic (R := ZMod q) α) := ↑u⁻¹ with hcdef
  have hac : (a : Rq (powTwoCyclotomic (R := ZMod q) α)) * c = 1 := by
    rw [hcdef, ← hu]; exact u.mul_inv
  have hcfix : conjAut α c = c := by
    have h1 : conjAut α ((a : Rq (powTwoCyclotomic (R := ZMod q) α)) * c) = 1 := by
      rw [hac, map_one]
    rw [map_mul, haval_fix] at h1
    have h2 : (a : Rq (powTwoCyclotomic (R := ZMod q) α)) * conjAut α c
        = (a : Rq (powTwoCyclotomic (R := ZMod q) α)) * c := by rw [h1, hac]
    rw [← hu] at h2
    exact (Units.mul_right_inj u).mp h2
  exact ⟨⟨c, (mem_conjFixedSubring_iff α _).mpr hcfix⟩, Subtype.ext (by
    rw [MulMemClass.coe_mul, OneMemClass.coe_one]; exact hac)⟩

/-- **`R_q^H` is a field** (Hachi [NOZ26, §3, Lemma 5], field part). Since
`R_q^H ⊆ R_q^{σ_{-1}}` (`fixedSubring_le_conjFixedSubring`) and the latter is a field
(`conjFixedSubring_isField`), `R_q^H` is a finite integral domain, hence a field.

The inclusion `R_q^H ↪ R_q^{σ_{-1}}` is an injective
ring hom into a field, so `R_q^H` is an integral domain (`Function.Injective.isDomain`); being
finite (`fixedSubring.fintype`) it is therefore a field (`Finite.isField_of_domain`). -/
theorem fixedSubring_isField (hq5 : q % 8 = 5) {α κ : ℕ} (hα : 1 ≤ α) :
    IsField (fixedSubring (R := ZMod q) α (2 ^ κ)) := by
  have hconjF := conjFixedSubring_isField q hq5 hα
  have hle := fixedSubring_le_conjFixedSubring (R := ZMod q) α (2 ^ κ)
  -- Derive `Nontrivial`/`NoZeroDivisors` on `R_q^{σ_{-1}}` from the `IsField` *Prop* directly,
  -- avoiding the instance diamond that `IsField.toField` would create on the subring carrier.
  haveI : Nontrivial (conjFixedSubring (R := ZMod q) α) := ⟨hconjF.exists_pair_ne⟩
  haveI : NoZeroDivisors (conjFixedSubring (R := ZMod q) α) := by
    refine ⟨fun {a b} hab => ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · obtain ⟨a', haa'⟩ := hconjF.mul_inv_cancel ha
      refine Or.inr ?_
      have h0 : a' * (a * b) = 0 := by rw [hab, mul_zero]
      rwa [← mul_assoc, mul_comm a' a, haa', one_mul] at h0
  -- Pull the domain structure back along the injective inclusion `R_q^H ↪ R_q^{σ_{-1}}`.
  haveI : Nontrivial (fixedSubring (R := ZMod q) α (2 ^ κ)) :=
    (Subring.inclusion hle).domain_nontrivial
  haveI : NoZeroDivisors (fixedSubring (R := ZMod q) α (2 ^ κ)) :=
    Function.Injective.noZeroDivisors (Subring.inclusion hle) (Subring.inclusion_injective hle)
      (Subring.inclusion hle).map_zero (fun x y => (Subring.inclusion hle).map_mul x y)
  haveI : IsDomain (fixedSubring (R := ZMod q) α (2 ^ κ)) := NoZeroDivisors.to_isDomain _
  exact Finite.isField_of_domain _

/-- **Hachi [NOZ26, §3, Lemma 5]: `R_q^H ≅ F_{q^k}`.** For `q ≡ 5 (mod 8)` and `2·2^κ ∣ 2^α`,
the fixed subring is ring-isomorphic to `GaloisField q (2^κ)` (`= F_{q^{2^κ}}`). Combines
`fixedSubring_isField` with `card_fixedSubring_eq` (`|R_q^H| = q^{2^κ}`) and the classification of
finite fields by cardinality.

Equip `R_q^H` with the
field structure from `fixedSubring_isField`, compute both cardinalities as `q^{2^κ}`
(`card_fixedSubring_eq` and `GaloisField.card`), and invoke the uniqueness of finite fields
(`FiniteField.ringEquivOfCardEq`). -/
theorem fixedSubringEquivGaloisField (hq5 : q % 8 = 5) {α κ : ℕ} (hα : 1 ≤ α)
    (hk : 2 * 2 ^ κ ∣ 2 ^ α) :
    Nonempty (fixedSubring (R := ZMod q) α (2 ^ κ) ≃+* GaloisField q (2 ^ κ)) := by
  have hq2 : ¬ (q ∣ 2) := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h2 : (2 : ZMod q) ≠ 0 := by
    have h2' : ((2 : ℕ) : ZMod q) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hq2
    simpa using h2'
  letI : Field (fixedSubring (R := ZMod q) α (2 ^ κ)) := (fixedSubring_isField q hq5 hα).toField
  haveI : Fintype (GaloisField q (2 ^ κ)) := Fintype.ofFinite _
  have hcardK : Fintype.card (fixedSubring (R := ZMod q) α (2 ^ κ)) = q ^ 2 ^ κ := by
    rw [card_fixedSubring_eq q α κ h2 hk, ZMod.card q]
  have hcardG : Fintype.card (GaloisField q (2 ^ κ)) = q ^ 2 ^ κ := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card q (2 ^ κ) (by positivity)]
  exact ⟨FiniteField.ringEquivOfCardEq (hcardK.trans hcardG.symm)⟩

end ArkLib.Lattices.CyclotomicModulus
