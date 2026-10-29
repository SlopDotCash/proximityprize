/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.ProximityGap.Folding

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import ProximityPrize.Extensions.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.ToMathlib.KeystoneStrictResidual
import ArkLib.Data.Probability.Notation
import ProximityPrize.Compatibility.UniformProbability

/-!
# Folding preservation at arbitrary divisible message degrees

The canonical folding module owns the split/fold primitives and dyadic coefficient helpers.
The compatibility theorem below retains the downstream soundness statement for every positive
message degree `d` divisible by `2 ^ k`, including `k = 0`, with the original strict-coefficient
residual and finite uniform probability. The canonical theorem instead uses a message degree
`2 ^ d` and a `FoldingContext`.

Only the private interpolation geometry needed for the broader degree statement is retained.
Its block arity follows the canonical logarithmic convention; there is no raw-arity copy of
`foldWordAux` or its coefficient helpers. The public `betaRec` wrapper retains its original
statement and supplies the residual to this compatibility theorem.

The stronger canonical curve capstone now proves the strict positive-radius branch directly.
The residual parameter remains in the public compatibility interface and is no longer needed
by the soundness proof.
-/

namespace ProximityGap

open NNReal Finset Function
open scoped ProbabilityTheory BigOperators LinearCode
open Code Affine ReedSolomon Domain
open Polynomial

variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}

namespace Compatibility
section
variable {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))}
variable {k : ℕ} {x : F}

omit [DecidableEq F] in
/-- Evaluation in either order gives the same value for a bivariate polynomial. -/
private lemma eval_comm {f : Polynomial (Polynomial F)} {a x : F} :
  (f.eval (Polynomial.C a)).eval x = (Polynomial.map (evalRingHom x) f).eval a := by
  simp only [Polynomial.eval_map]
  have h_eval : Polynomial.eval (Polynomial.C a) f =
    ∑ i ∈ f.support, f.coeff i * (Polynomial.C a) ^ i := by
    aesop (add simp [Polynomial.eval_eq_sum])
  simp [h_eval, Polynomial.eval_finsetSum,
        Polynomial.eval₂_eq_sum, Polynomial.sum_def]


private lemma roots_in_domain_card_eq_if_x_in_domain
    (hk : k ≤ n) (hx : x ∈ domain.subdomain k) :
    Finset.card {i | domain i ^ 2 ^ k = x} = 2 ^ k := by
  change (CosetFftDomainClass.blockIdx domain k x).card = 2 ^ k
  rw [CosetFftDomainClass.card_blockIdx]
  exact CosetFftDomainClass.card_block_of_mem_subdomain' hk hx

private noncomputable def indicatedPolynomial
  (domain : SmoothCosetFftDomain n F) (f : Word F (Fin (2 ^ n))) (k : ℕ) (s' : Finset F) :
  Polynomial (Polynomial F) := ∑ x ∈ s',
    Polynomial.C (singletonIndicator x s') *
      (Polynomial.map Polynomial.C <| foldWordAux domain f k x)

section IndicatedPolynomial

variable {s' : Finset F}

omit [Field F] [DecidableEq F] in
private theorem card_ne_zero (hs' : s'.Nonempty) : NeZero (Finset.card s') where
  out := by aesop

private lemma indicated_polynomial_degree_x_lt (hs' : s'.Nonempty) :
  Bivariate.degreeX (indicatedPolynomial domain f k s') < s'.card := by
  simp only [Bivariate.degreeX, indicatedPolynomial, finsetSum_coeff, coeff_C_mul, coeff_map]
  rw [Finset.sup_lt_iff (by simp [hs'])]
  intro b hb
  exact natDegree_sum_lt_of_forall_lt (inst := card_ne_zero hs') _ _ <|
    fun i hi ↦ lt_of_le_of_lt natDegree_mul_le <| by
      aesop
        (add simp [singleton_indicator_natDegree_lt_of_mem])

private lemma indicated_polynomial_degree_y_lt :
  Bivariate.natDegreeY (indicatedPolynomial domain f k s') < 2 ^ k := by
  simp only [Bivariate.natDegreeY, indicatedPolynomial]
  exact natDegree_sum_lt_of_forall_lt _ _ <| fun i hi ↦
    lt_of_le_of_lt natDegree_mul_le <| by
      aesop
        (add simp [foldWordAux_natDegree])
        (add safe (by omega))

private lemma indicated_polynomial_eq_foldAux {α : F} (hx : x ∈ s') :
  ((indicatedPolynomial domain f k s').eval (Polynomial.C α)).eval x =
    (foldWordAux domain f k x).eval α := by
  aesop
    (add simp [indicatedPolynomial, eval_finsetSum])
    (add safe
      [(by rw [singleton_indicator_eval_eq_zero_of_mem_sdiff]),
        (by rw [Finset.sum_eq_ite x])])

private lemma indicated_polynomial_eval_eq_combination_of_correlated
  {u : Fin (2 ^ k) → Polynomial F}
  {α : F}
  (hu : ∀ i x, x ∈ s' → (u i).eval x = foldWordAuxCoeff domain f k i x)
  (hx : x ∈ s') :
  ((indicatedPolynomial domain f k s').eval (Polynomial.C α)).eval x =
    ∑ i, (u i).eval x * α ^ i.val := by
  aesop
    (add safe (by rw [←foldValue_def]))
    (add simp
      [indicated_polynomial_eq_foldAux,
        foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha])

private lemma indicated_polynomial_eq_combination_of_correlated
  (hs' : s'.Nonempty)
  {u : Fin (2 ^ k) → Polynomial F}
  {α : F}
  (hu : ∀ i x, x ∈ s' → (u i).eval x = (foldWordAuxCoeff domain f k i x))
  (hu_deg : ∀ i, (u i).natDegree < s'.card) :
  ((indicatedPolynomial domain f k s').eval (Polynomial.C α)) =
    ∑ i, (u i) * Polynomial.C (α ^ i.val) := by
  apply Polynomial.eq_of_eval_eq_natDegree (s := s') (n := #s')
    <;> try rfl
  · simp only [indicatedPolynomial,
      eval_finsetSum, eval_mul, eval_C, eval_map_apply]
    exact natDegree_sum_lt_of_forall_lt (inst := card_ne_zero hs') _ _ <|
      fun i _ ↦ lt_of_le_of_lt natDegree_mul_le <| by
        aesop
          (add simp [singleton_indicator_natDegree_lt_of_mem])
  · exact natDegree_sum_lt_of_forall_lt (inst := card_ne_zero hs') _ _ <|
      fun i _ ↦ lt_of_le_of_lt natDegree_mul_le <| by simp [hu_deg]
  · aesop
      (add safe forward
        [indicated_polynomial_eval_eq_combination_of_correlated])
      (add simp [eval_finsetSum])

private lemma indicated_polynomial_eq_foldAux'
  [Fintype F]
  {s' : Finset F}
  {u : Fin (2 ^ k) → Polynomial F}
  (hx : ∀ i, (u i).eval x = (foldWordAuxCoeff domain f k i x))
  (hu : ∀ i x, x ∈ s' → (u i).eval x = (foldWordAuxCoeff domain f k i x))
  (hu_deg : ∀ i, (u i).natDegree < s'.card)
  (h_s' : s'.Nonempty)
  (h_card : 2 ^ k ≤ Fintype.card F) :
  (Polynomial.map
    (Polynomial.evalRingHom x)
    (indicatedPolynomial domain f k s')) =
    foldWordAux domain f k x := by
  refine Polynomial.eq_of_eval_eq_natDegree (s := Finset.univ) (n := 2 ^ k) ?_ ?_ ?_ ?_
  · simp only
      [indicatedPolynomial, Polynomial.map_sum,
        Polynomial.map_mul, map_C, coe_evalRingHom]
    exact natDegree_sum_lt_of_forall_lt _ _ <| fun i hi ↦
      lt_of_le_of_lt natDegree_mul_le <| by
        aesop
          (add simp [Polynomial.map_map])
          (add safe [foldWordAux_natDegree])
  · exact foldWordAux_natDegree
  · simpa using h_card
  · intro α _
    rw [←eval_comm,
      indicated_polynomial_eq_combination_of_correlated h_s' hu hu_deg,
      eval_finsetSum, ←foldValue_def,
      foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha]
    simp only [eval_mul, eval_C, hx]

private lemma foldWordAux_poly_sum {a : F} :
  ((foldWordAux domain f k a).sum fun e a ↦ Polynomial.C a * Polynomial.X ^ e) =
  foldWordAux domain f k a := by
  aesop (add safe
    [(by rw [←Polynomial.sum_monomial_eq]),
     (by rw [Polynomial.sum])])

private lemma indicated_polynomial_comp_x_k_natDegree
  (hs' : s'.Nonempty) :
  ((Polynomial.map (Polynomial.compRingHom (Polynomial.X ^ 2 ^ k)) <|
    indicatedPolynomial domain f k s').eval Polynomial.X).natDegree < (2 ^ k) * s'.card := by
  by_cases h_card : 1 < s'.card
  · simp only [indicatedPolynomial,
      Polynomial.eval_map, eval₂_finsetSum,
      eval₂_mul, eval₂_C, coe_compRingHom]
    exact natDegree_sum_lt_of_forall_lt
      (inst := instNeZeroNatHMul (hm := card_ne_zero hs')) _ _ <|
      fun i hi ↦ lt_of_le_of_lt natDegree_mul_le <| by
      simp only [natDegree_comp, natDegree_pow, natDegree_X, mul_one, eval₂_map,
        eval₂, RingHom.coe_comp, coe_compRingHom, comp_apply, C_comp, foldWordAux_poly_sum]
      have h_ind :=
        Nat.le_sub_one_of_lt (singleton_indicator_natDegree_lt_of_mem hi)
      exact lt_of_le_of_lt
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ h_ind) _) <|
          lt_of_lt_of_le
            (Nat.add_lt_add_left foldWordAux_natDegree _) <| by
            rw [Nat.mul_comm, ←Nat.mul_add_one]
            grind +ring
  · have h_card : #s' = 1 := by grind
    aesop
      (add unsafe [(by rw [Polynomial.eval_map, Polynomial.eval₂_map, eval₂])])
      (add simp [Finset.card_eq_one, indicatedPolynomial,
        singletonIndicator, indicator,
        foldWordAux_poly_sum])
      (add safe [foldWordAux_natDegree])

end IndicatedPolynomial

omit [DecidableEq F] in
private lemma eval_comp_x_pow_map_eq {f : Polynomial (Polynomial F)} {x : F}
  {k : ℕ} :
  Polynomial.eval x
    (Polynomial.eval
        Polynomial.X
        (Polynomial.map (Polynomial.X ^ k).compRingHom f)) =
             (Polynomial.eval
               x
               (Polynomial.map
                (Polynomial.evalRingHom (x ^ k))
                f)) := by
  induction f using Polynomial.induction_on <;> aesop (add simp pow_succ)


private noncomputable def hammingDistComplementBound
  {n : ℕ} (k : ℕ) (domain : SmoothCosetFftDomain n F) (s : Finset F) : ℕ :=
  Finset.card { i ∈
    Finset.product
      Finset.univ
      (Finset.preimage s (domain.subdomain k) (by simp)) |
    (domain i.1) ^ (2 ^ k) = domain.subdomain k i.2 }

private noncomputable def hammingDistBound
  {n : ℕ} (k : ℕ) (domain : SmoothCosetFftDomain n F) (s : Finset F) : ℕ :=
  Fintype.card (Fin (2 ^ n)) - hammingDistComplementBound k domain s

@[simp]
private lemma contradictory_hamming_dist_zero :
  hammingDistBound k domain ∅ = 2 ^ n := by
  simp [hammingDistBound, hammingDistComplementBound]

@[simp]
private lemma contradictory_hamming_dist_formula {s : Finset F}
  {d : ℕ}
  (h_s : s ⊆ (domain.subdomain k).toFinset)
  (h_k_d : 2 ^ k ≤ d)
  (h_d : d ≤ 2 ^ n) :
  hammingDistBound k domain s =
    2 ^ n - 2 ^ k * (Finset.card s) := by
    unfold hammingDistBound hammingDistComplementBound
    simp only [Fintype.card_fin, product_eq_sprod]
    congr
    rw [show @filter _ _ _ _ =
        (Finset.preimage s (domain.subdomain k) (by simp)).biUnion
          (fun i ↦ {j | domain j.1 ^ 2 ^ k = domain.subdomain k i ∧ j.2 = i} ) by aesop,
        Finset.card_biUnion (fun x hx y hy hxy a ha₁ ha₂ ↦ by
          by_contra contra
          obtain ⟨c, hc⟩ : ∃ c, c ∈ a := by
            aesop
              (add simp [le_eq_subset])
              (add safe (by grind))
          specialize (ha₁ hc)
          specialize (ha₂ hc)
          aesop
        )]
    conv =>
      lhs
      congr
      rfl
      ext u
      rw [show (Finset.card _) = #{j | domain j ^ 2 ^ k =
        (CosetFftDomain.subdomain domain k) u} by
        aesop (add safe (by apply Finset.card_bij (fun a _ ↦ a.1)))
      ]
    rw [Finset.sum_bij (t := s)
      (g := fun x ↦ Finset.card {j | domain j ^ (2 ^ k) = x})
      (i := fun i _ ↦ domain.subdomain k i)
      (by aesop)
      CosetFftDomain.injOn
      (by {
        intro b hb
        obtain ⟨a, ha⟩ : ∃ i, b = (CosetFftDomain.subdomain domain k) i := by
          have hbmem := CosetFftDomain.mem_toFinset_iff_mem.mp (h_s hb)
          obtain ⟨i, hi⟩ := CosetFftDomainClass.mem_def.mp hbmem
          exact ⟨i, hi.symm⟩
        exists a
        aesop
      })
      (by simp)]
    rw [Finset.sum_bij (t := s)
      (g := fun i ↦ 2 ^ k) (fun i _ ↦ i)
      (by aesop)
      (by aesop)
      (by aesop)
      (fun a ha ↦ by
        rw [roots_in_domain_card_eq_if_x_in_domain
          (by {
            rw [←Nat.pow_le_pow_iff_right (a := 2) (by simp)]
            omega
        }) (by {
          rw [←CosetFftDomain.mem_toFinset_iff_mem]
          exact h_s ha
        })]
      )]
    aesop (add safe (by grind))

private lemma correlated_agreement_implies_contradictory_hamm_dist
  [Fintype F]
  {s : Finset F}
  (h_s : s ⊆ (domain.subdomain k).toFinset)
  {u : Fin (2 ^ k) → Polynomial F}
  (h_u : ∀ i, ∀ x ∈ s, (u i).eval x =
    foldWordAuxCoeff domain f k i x)
  {d : ℕ}
  (h_d : 2 ^ k ≤ d)
  (h_k_card : (2 ^ k) ≤ Fintype.card F)
  (h_u_deg : ∀ i, (u i).natDegree < d / (2 ^ k)) :
  ∃ f' : Polynomial F,
    f'.natDegree < d ∧
      hammingDist f (fun x => f'.eval (domain x)) ≤
        hammingDistBound k domain s := by
  by_cases h_empty : s = ∅
  · exists (C <| f 0)
    aesop
      (add safe (by grind))
      (add unsafe (by rw [←Finset.compl_filter, Finset.card_compl]))
      (add simp [hammingDist, Finset.card_sdiff])
  · let s' := s.pickSubset (d / (2 ^ k))
    have h_nonempty : s.Nonempty := by grind
    have h_s'_card : s'.card = min s.card (d / (2 ^ k)) := by simp [s']
    have h_s'_non_empty : s'.Nonempty := by
      simp_all only [card_pick_subset, ne_eq,
        Nat.div_eq_zero_iff, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and,
        false_or, not_lt, nonempty_pick_subset_of_nonempty_of_ne, s']
    exists ((Polynomial.map (Polynomial.compRingHom (Polynomial.X ^ (2 ^ k))) <|
      indicatedPolynomial domain f k s').eval Polynomial.X)
    constructor
    · exact lt_of_lt_of_le
        (indicated_polynomial_comp_x_k_natDegree h_s'_non_empty)
        (le_trans
          (Nat.mul_le_mul_left (m := d / (2 ^ k)) _ (by omega))
          (Nat.mul_div_le _ _))
    · simp only [hammingDist, ne_eq, hammingDistBound, Fintype.card_fin]
      rw [←Finset.compl_filter, Finset.card_compl, Fintype.card_fin]
      apply Nat.sub_le_sub_left
      apply Finset.card_le_card_of_injOn Prod.fst
        (f_inj := fun _ _ _ _ h ↦ by
          aesop
            (add unsafe [(by apply CosetFftDomain.injective (ω := domain.subdomain k))])
)
      rintro ⟨a₁, a₂⟩ ha
      simp_all only [product_eq_sprod, coe_filter, mem_product, mem_univ, mem_preimage, true_and,
        Set.mem_setOf_eq]
      rcases ha with ⟨h_a_s, h_eq⟩
      rw [eval_comp_x_pow_map_eq, h_eq]
      by_cases h_s'_s : s' = s
      · rw [h_s'_s,
            ←eval_comm,
            indicated_polynomial_eq_foldAux (by simp [h_a_s]),
            ←h_eq,
            ←foldValue_def,
            foldValue_pow_x_k]
      · rw [indicated_polynomial_eq_foldAux' (u := u) (by aesop)] <;> try assumption
        · rw [←foldValue_def, ←h_eq, foldValue_pow_x_k]
        · intro i x hx
          have hx := (pick_subset_subset : s' ⊆ s) hx
          rw [h_u _ _ hx]
        · intro i
          exact lt_of_lt_of_le
            (h_u_deg i)
            (by rw [pick_subset_card_eq_of_ne h_s'_s])

set_option linter.unusedFintypeInType false in -- false alert
private lemma dist_from_code_bound_of_correlated_agreement
  [Fintype F]
  {s : Finset F}
  (h_s : s ⊆ (domain.subdomain k).toFinset)
  {u : Fin (2 ^ k) → Polynomial F}
  (h_u : ∀ i, ∀ x ∈ s, (u i).eval x =
      foldWordAuxCoeff domain f k i x)
  {d : ℕ}
  (h_k_d : 2 ^ k ≤ d)
  (h_d : d ≤ 2 ^ n)
  (h_u_deg : ∀ i, (u i).natDegree < d / (2 ^ k)) :
  Δ₀(f, ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) d)
        ≤ 2 ^ n -
          2 ^ k * (Finset.card s) := by
  simp only [distFromCode, SetLike.mem_coe]
  exact sInf_le_of_le
    (b := ↑(hammingDistBound k domain s))
    (h := by
      aesop
        (add safe
          (by rw [contradictory_hamming_dist_formula]))
    ) <| by
    obtain ⟨f', h_f'_deg, hdist⟩ :=
      correlated_agreement_implies_contradictory_hamm_dist h_s h_u h_k_d (by {
    exact le_trans h_k_d <| by
      exact le_trans h_d <| by
        simpa only [Fintype.card_fin] using
          Fintype.card_le_of_injective domain domain.injective
  }) h_u_deg
    aesop (add safe [mem_code_of_polynomial_of_natDegree_lt_of_eval])

private lemma folded_rate_div_eq_helper {d : ℕ}
  (hkn : k ≤ n) (hkd : 2 ^ k ∣ d) :
  (↑(d / 2 ^ k) : ℚ≥0) / 2 ^ (n - k) = (↑d : ℚ≥0) / 2 ^ n := by
  obtain ⟨m, rfl⟩ := hkd
  simp +zetaDelta only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true,
    mul_div_cancel_left₀, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at *
  rw [←Nat.add_sub_cancel' hkn,
      pow_add,
      mul_div_mul_left _ _ (by positivity)]
  norm_num


omit [DecidableEq F] in
/-- Folding by a divisor of an arbitrary message degree preserves its rate. -/
lemma folded_rate_eq {d : ℕ} (hkn : k ≤ n) (hkd : 2 ^ k ∣ d) :
    LinearCode.rate
      (ReedSolomon.code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) (d / (2 ^ k))) =
    LinearCode.rate (ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) d) := by
  simp only [rateOfLinearCode_eq_min_div, Fintype.card_fin, min_def, Nat.cast_ite, Nat.cast_pow,
    Nat.cast_ofNat]
  by_cases hif : d ≤ 2 ^ n
  · simp only [hif, ↓reduceIte]
    have hif : d / 2 ^ k ≤ 2 ^ (n - k) := by
      rw [Nat.div_le_iff_le_mul (by simp)]
      exact le_trans hif <| by
        rw [←pow_add, Nat.sub_add_cancel hkn]
        grind
    aesop (add safe forward [folded_rate_div_eq_helper])
  · simp only [hif, ↓reduceIte, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
    not_false_eq_true, div_self]
    have hif := Nat.div_le_div_right (c := 2 ^ k) (Nat.le_of_lt (not_le.mp hif))
    rw [show 2 ^ n / 2 ^ k = 2 ^ (n - k) by
      aesop (add safe
        [(by rw [Nat.div_eq_iff]),
          (by rw [←pow_add]),
          (by grind)])
    ] at hif
    rcases (Nat.lt_or_eq_of_le hif) with hif | hif
    · aesop (add safe (by omega))
    · aesop
        (add safe forward [div_eq_one_iff_eq])
        (add safe [(by norm_cast)])

omit [DecidableEq F] in
/-- The square root of the rate of the folded RS-code is the same. -/
lemma folded_sqrtRate_eq {d : ℕ} (hkn : k ≤ n) (hkd : 2 ^ k ∣ d) :
    ReedSolomon.sqrtRate
     (d / (2 ^ k))
     (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) =
    ReedSolomon.sqrtRate d (domain : Fin (2 ^ n) ↪ F) := by
  simp only [ReedSolomon.sqrtRate, folded_rate_eq hkn hkd]




/-- Soundness for arbitrary positive divisible message degrees, retaining the strict
coefficient-polynomial residual and finite uniform sampling. -/
theorem folding_preserves_distance
    [Fintype F]
  {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))} {d k : ℕ}
  {δ : ℝ≥0}
  (k_div_d : 2 ^ k ∣ d)
  (hd0 : 0 < d)
  (h_d_n : d ≤ 2 ^ n)
  (hStrictCoeff : StrictCoeffPolysResidual
    (k := 2 ^ k - 1) (deg := d / (2 ^ k))
    (domain := (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F)) (δ := δ))
  (δ_gt_0 : 0 < δ)
  (δ_lt : δ < min (δᵣ(f, ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) d))
    (1 - (ReedSolomon.sqrtRate d (domain : Fin (2 ^ n) ↪ F)))) :
    Pr_{ let r ←$ᵖ F}[δᵣ(foldWord domain f k r,
      ReedSolomon.code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F)
      (d / (2 ^ k))) ≤ δ] ≤
        ((2 ^ k) - 1) * ProximityGap.errorBound δ (d / (2 ^ k))
        (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) := by
    have h_k_d : 2 ^ k ≤ d := by
      by_cases hδ0 : δ = 0
      · exact (ne_of_gt δ_gt_0 hδ0).elim
      · exact Nat.le_of_dvd (by omega) k_div_d
    have h_k_le_n : k ≤ n := by
      rw [←Nat.pow_le_pow_iff_right (a := 2) (by simp)]
      omega
    have bound_tighter :
      δ < 1 - ReedSolomon.sqrtRate (d / (2 ^ k))
        (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) := by
        aesop
          (add safe [(by rw [folded_sqrtRate_eq])])
          (add safe [(by grind)])
          (add safe (by norm_cast at *))
    letI : NeZero (d / 2 ^ k) := ⟨by rw [Nat.div_ne_zero_iff]; omega⟩
    let : SampleableType F := SampleableType.ofFintype F
    have correlated_agreement :=
      correlatedAgreement_affine_curves
        (k := 2 ^ k - 1) (deg := d / (2 ^ k))
        (domain := (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F))
        (δ := δ) (Nat.div_pos h_k_d (by positivity)) δ_gt_0 bound_tighter
    unfold foldWord δ_ε_correlatedAgreementCurves at *
    simp_rw [← ProximityPrize.Compatibility.pmf_uniform_probability_eq_native]
      at correlated_agreement
    by_contra contra
    simp only [not_le, foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha, bind_pure_comp, Functor.map,
      PMF.bind_apply,
      ProximityPrize.Compatibility.uniformOfFintype_apply,
      comp_apply, PMF.pure_apply, eq_iff_iff, true_iff,
      mul_ite, mul_one, mul_zero, tsum_fintype] at contra correlated_agreement
    let cast (x : Fin (2 ^ k - 1 + 1)) : Fin (2 ^ k) :=
      Fin.cast (by rw [Nat.sub_add_cancel (by omega)]) x
    let cast' (x : Fin (2 ^ k)) : Fin (2 ^ k - 1 + 1) :=
      Fin.cast (by rw [Nat.sub_add_cancel (by omega)]) x
    have bijective_cast : Bijective cast := by
      rw [bijective_iff_has_inverse]
      exists cast'
      simp [LeftInverse, RightInverse, cast, cast']
    specialize correlated_agreement
      (Matrix.of (fun i j ↦ foldWordAuxCoeff domain f k
        (cast i)
        (domain.subdomain k j)))
    have correlated_curve_eq_sum_of_foldWord_coeffs {a : F} :
      ∑ i : Fin (2 ^ k - 1 + 1), a ^ (↑i : ℕ) •
        Matrix.of (fun i j ↦
          foldWordAuxCoeff domain f k (cast i) (domain.subdomain k j)) i =
      (fun x ↦
        ∑ j, foldWordAuxCoeff domain f k j
          (domain.subdomain k x) * a ^ (↑j : ℕ)) := by
      ext x
      simp only [Finset.sum_apply]
      exact Fintype.sum_bijective cast bijective_cast _ _ <|
        fun i ↦ by simp [cast, mul_comm]
    specialize correlated_agreement (by {
      conv_lhs =>
        rhs
        ext a
        rw [correlated_curve_eq_sum_of_foldWord_coeffs]
      norm_cast at contra
    })
    simp only [jointAgreement, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, ge_iff_le,
      SetLike.mem_coe, Matrix.of_apply] at correlated_agreement
    obtain ⟨S, h_card, v, h'⟩ := correlated_agreement
    rw [forall_and] at h'
    rcases h' with ⟨h_rs, h'⟩
    have h_rs := fun x ↦ (mem_code_iff_exists_polynomial_of_ne_zero
        (ne := ⟨by rw [Nat.div_ne_zero_iff]; omega⟩)).mp (h_rs x)
    let u : Fin (2 ^ k - 1 + 1) → Polynomial F :=
      fun i => Classical.choose (h_rs i)
    have contradiction := dist_from_code_bound_of_correlated_agreement (domain := domain) (f := f)
      (s := Finset.image
        (domain.subdomain k) S)
      (fun x hx ↦ by
        rw [CosetFftDomain.mem_toFinset_iff_mem]
        simp only [mem_image] at hx
        obtain ⟨x', _, hx'⟩ := hx
        aesop
      )
      (u := u ∘ cast')
      (fun i j hj ↦ by
        let i' := cast' i
        obtain ⟨j', hjS, hjEq⟩ := Finset.mem_image.mp hj
        subst j
        have hagree := (Finset.mem_filter.mp (h' i' hjS)).2
        have h_spec := congrFun (a := j') <| Classical.choose_spec (h_rs i') |>.2
        change v i' j' = (u i').eval (domain.subdomain k j') at h_spec
        change (u i').eval (domain.subdomain k j') = _
        rw [← h_spec]
        simpa only [i', cast', cast, Fin.cast_cast, Fin.cast_eq_self] using hagree
      )
      (d := d)
      h_k_d
      h_d_n
      (fun i ↦
        And.left <| Classical.choose_spec (h_rs (cast' i)))
    rw [Finset.card_image_of_injective _ (by simp)] at contradiction
    have contradiction : (Δ₀(f, code (domain : Fin (2 ^ n) ↪ F) d) : ENNReal)
      ≤ (↑(2 ^ n) : ℚ≥0) * δ :=
      le_trans (ENat.toENNReal_le.mpr contradiction) <| by
        apply le_trans
          (b := (2 ^ n : ENNReal) - 2 ^ k * (1 - ↑δ) * 2 ^ (n - k))
        · rw [ENat.toENNReal_sub,
              show ENat.toENNReal (2 ^ n) = (2 ^ n : ENNReal) by simp,
              ENNReal.sub_le_sub_iff_left (h' := by simp)
                (h := swap (le_trans (b := 2 ^ n * 1)) (by simp) <| by
                  rw [mul_comm,
                      ←mul_assoc,
                      ←pow_add,
                      Nat.sub_add_cancel h_k_le_n,
                      ENNReal.mul_le_mul_iff_right (by simp) (by simp)]
                  simp
          )]
          apply le_trans (b := 2 ^ k * ↑↑(#S))
          · rw [mul_assoc,
                ENNReal.mul_le_mul_iff_right (by simp) (by simp)]
            have h_card := ENNReal.coe_le_coe_of_le h_card
            exact (swap le_trans h_card) (by norm_cast)
          · norm_cast
        · rw [mul_comm,
              ←mul_assoc,
              ←pow_add,
              Nat.sub_add_cancel h_k_le_n]
          conv_lhs =>
            lhs
            rw [←mul_one (2 ^ n)]
          rw [←ENNReal.mul_sub (by simp),
              ENNReal.sub_sub_cancel (by simp)
                (by {
                  simp only [lt_inf_iff] at δ_lt
                  exact le_trans (le_of_lt δ_lt.2) (by simp)
                })]
          norm_cast
    have contradiction : δᵣ(f, code (domain : Fin (2 ^ n) ↪ F) d) ≤ (δ : NNReal) := by
      rw [relDistFromCode_le_iff_distFromCode_toENNReal_le]
      exact le_trans contradiction <| by
        simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
        rw [mul_comm]
        norm_cast
    simp only [lt_inf_iff] at δ_lt
    simpa using lt_of_lt_of_le δ_lt.1 contradiction


end
end Compatibility

/--
Folding preservation with the strict Johnson coefficient-polynomial residual supplied by the
verified `betaRec` capsule for the folded Reed-Solomon domain.
-/
theorem folding_preserves_distance_johnson_of_betaRec
    [Fintype F]
  {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))} {d k : ℕ}
  {δ : ℝ≥0}
  (k_div_d : 2 ^ k ∣ d)
  (hd0 : 0 < d)
  (h_d_n : d ≤ 2 ^ n)
  (hInput : ∀ (_hk : 0 < 2 ^ k - 1)
    (u : WordStack F (Fin ((2 ^ k - 1) + 1)) (Fin (2 ^ (n - k)))),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin ((2 ^ k - 1) + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code
            (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) (d / (2 ^ k))) ≤ δ] >
          (((2 ^ k - 1) : ℕ) : ENNReal) *
            (ProximityGap.errorBound δ (d / (2 ^ k))
              (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) : ENNReal) →
      (1 -
          (LinearCode.rate
            (ReedSolomon.code
              (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) (d / (2 ^ k))) :
            ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate (d / (2 ^ k))
        (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) →
      ArkLib.KeystoneStrictResidual.BetaCurveInput
        (k := 2 ^ k - 1) (deg := d / (2 ^ k))
        (domain := (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F))
        (δ := δ) u)
  (δ_gt_0 : 0 < δ)
  (δ_lt : δ < min (δᵣ(f, ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) d))
    (1 - (ReedSolomon.sqrtRate d (domain : Fin (2 ^ n) ↪ F)))) :
    Pr_{ let r ←$ᵖ F}[δᵣ(foldWord domain f k r,
      ReedSolomon.code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F)
      (d / (2 ^ k))) ≤ δ] ≤
        ((2 ^ k) - 1) * ProximityGap.errorBound δ (d / (2 ^ k))
        (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) :=
  Compatibility.folding_preserves_distance (domain := domain) (f := f) (d := d) (k := k)
    (δ := δ) k_div_d hd0 h_d_n
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec
      (k := 2 ^ k - 1) (deg := d / (2 ^ k))
      (domain := (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F))
      (δ := δ) hInput)
    δ_gt_0 δ_lt


end ProximityGap
