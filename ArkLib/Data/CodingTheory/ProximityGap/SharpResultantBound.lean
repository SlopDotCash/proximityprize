/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# The Landau ℓ²-sharpening of the cyclotomic resultant bound (#371)

The in-tree archimedean bound `natAbs_resultant_cyclotomic_le` estimates every value
`|R(ζ)|` at a primitive `2^m`-th root by `‖R‖₁`, giving `|Res| ≤ ‖R‖₁^{2^{m−1}}` and the
doubly-exponential bad-side threshold `(2^μ)^{2^{μ−1}} < p`.  **This file sharpens it via
the Mahler measure**: factoring the resultant over the roots of `R` instead,

  `|Res_ℤ(R, Φ_{2^m})| = |lc R|^h · ∏_{R(β)=0} |β^h + 1| ≤ 2^{deg R} · M(R)^h`

(`h = 2^{m−1}`; `|β^h + 1| ≤ 2·max(1,|β|)^h`; Jensen's factorization
`M(R) = |lc R|·∏ max(1,|β|)` from the multiplicativity of the Mahler measure), and then
**Landau's inequality** (`Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff`, in Mathlib)
bounds `M(R) ≤ ‖R‖₂`.  In squared (ℕ-friendly) form:

> **`natAbs_resultant_cyclotomic_sq_le`** —
> `|Res_ℤ(R, Φ_{2^m})|² ≤ 4^{deg R} · (∑_i |R_i|²)^{2^{m−1}}`.

For the KKH26 collision polynomials (coefficients in `{−2..2}`, window `< h`) this gives
`|Res|² ≤ 4^{h−1}·(4h)^h` — at `μ = 6`: `≤ 2^{286}`, against the old route's
`(2^{192})² = 2^{384}` — **below `P²` for every μ = 6 literal-budget prime**: the gap that
upgrades the conditional `n = 64` pins of `Mu6ConditionalPin.lean` to unconditional
(consumer wiring follows in a separate file).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false

open Polynomial Finset Real

namespace ArkLib.ProximityGap.SharpResultantBound

/-! ## Multiset product helpers over `ℝ` -/

private theorem norm_multiset_prod_eq (s : Multiset ℂ) : ‖s.prod‖ = (s.map norm).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [ih]

private theorem multiset_prod_map_le {α : Type} (s : Multiset α) (f g : α → ℝ)
    (h0 : ∀ a ∈ s, 0 ≤ f a) (h : ∀ a ∈ s, f a ≤ g a) :
    (s.map f).prod ≤ (s.map g).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    have h0a : 0 ≤ f a := h0 a (Multiset.mem_cons_self a s)
    have h0s : (0 : ℝ) ≤ (s.map f).prod := by
      refine Multiset.prod_nonneg fun x hx => ?_
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hx
      exact h0 b (Multiset.mem_cons_of_mem hb)
    have hga : 0 ≤ g a := le_trans h0a (h a (Multiset.mem_cons_self a s))
    refine mul_le_mul (h a (Multiset.mem_cons_self a s))
      (ih (fun b hb => h0 b (Multiset.mem_cons_of_mem hb))
        (fun b hb => h b (Multiset.mem_cons_of_mem hb))) h0s hga

/-! ## Jensen's factorization of the Mahler measure over `ℂ` -/

/-- Jensen's product formula: over `ℂ`, the Mahler measure is the absolute value of the
leading coefficient times the product of `max 1 ‖root‖` (multiplicativity of the Mahler
measure applied to the splitting). -/
theorem mahlerMeasure_eq_prod_roots (p : Polynomial ℂ) :
    p.mahlerMeasure = ‖p.leadingCoeff‖ * (p.roots.map (fun z => max 1 ‖z‖)).prod := by
  conv_lhs => rw [(IsAlgClosed.splits p).eq_prod_roots]
  rw [Polynomial.mahlerMeasure_mul, Polynomial.mahlerMeasure_const,
    Polynomial.prod_mahlerMeasure_eq_mahlerMeasure_prod, Multiset.map_map]
  congr 1
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun z _ => by
    simp [Function.comp, Polynomial.mahlerMeasure_X_sub_C])

/-! ## The per-root estimate for `Φ_{2^m}` -/

/-- Over `ℂ`, the `2^m`-th cyclotomic polynomial is `X^{2^{m−1}} + 1`. -/
theorem cyclotomic_two_pow_complex {m : ℕ} (hm : 1 ≤ m) :
    cyclotomic (2 ^ m) ℂ = X ^ 2 ^ (m - 1) + 1 := by
  have h : 2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1; omega
  rw [h, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [add_comm]

/-- The evaluation estimate: `‖Φ_{2^m}(β)‖ = ‖β^h + 1‖ ≤ 2 · max 1 ‖β‖ ^ h`. -/
theorem norm_eval_cyclotomic_le {m : ℕ} (hm : 1 ≤ m) (β : ℂ) :
    ‖(cyclotomic (2 ^ m) ℂ).eval β‖ ≤ 2 * max 1 ‖β‖ ^ 2 ^ (m - 1) := by
  rw [cyclotomic_two_pow_complex hm]
  simp only [eval_add, eval_pow, eval_X, eval_one]
  calc ‖β ^ 2 ^ (m - 1) + 1‖ ≤ ‖β ^ 2 ^ (m - 1)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
  _ = ‖β‖ ^ 2 ^ (m - 1) + 1 := by rw [norm_pow, norm_one]
  _ ≤ max 1 ‖β‖ ^ 2 ^ (m - 1) + max 1 ‖β‖ ^ 2 ^ (m - 1) := by
      gcongr
      · exact le_max_right 1 ‖β‖
      · exact one_le_pow₀ (le_max_left 1 ‖β‖)
  _ = 2 * max 1 ‖β‖ ^ 2 ^ (m - 1) := by ring

/-! ## The sharp resultant bound -/

set_option maxHeartbeats 1600000 in
-- The Mahler-measure proof expands resultants, roots, and coefficient norms;
-- the default heartbeat limit is too low after those normal forms unfold.
/-- The Landau `l2`-sharpening: `|Res_Z(R, Phi_{2^m})|^2` is at most
`4^{deg R} * (sum_i |R_i|^2)^{2^{m-1}}`. -/
theorem natAbs_resultant_cyclotomic_sq_le {m : ℕ} (hm : 1 ≤ m) (R : Polynomial ℤ) :
    (Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)).natAbs ^ 2
      ≤ 4 ^ R.natDegree
        * (∑ i ∈ R.support, (R.coeff i).natAbs ^ 2) ^ 2 ^ (m - 1) := by
  classical
  have hdegΦ : (cyclotomic (2 ^ m) ℤ).natDegree = 2 ^ (m - 1) := by
    rw [natDegree_cyclotomic]
    rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < m)]
    omega
  rcases eq_or_ne R 0 with rfl | hR0
  · rw [show ((0 : Polynomial ℤ).resultant (cyclotomic (2 ^ m) ℤ)) = 0 by
      rw [Polynomial.resultant_zero_left, hdegΦ]
      simp [zero_pow (show (2:ℕ) ^ (m - 1) ≠ 0 by positivity)]]
    simp
  set ι : ℤ →+* ℂ := Int.castRingHom ℂ with hι
  have hinj : Function.Injective ι := Int.cast_injective
  set Φ : Polynomial ℤ := cyclotomic (2 ^ m) ℤ with hΦdef
  set h : ℕ := 2 ^ (m - 1) with hhdef
  -- degree bookkeeping
  have hdegRC : (R.map ι).natDegree = R.natDegree :=
    natDegree_map_eq_of_injective hinj _
  have hdegΦC : (Φ.map ι).natDegree = h := by
    rw [natDegree_map_eq_of_injective hinj, hΦdef, hdegΦ]
  have hRC0 : R.map ι ≠ 0 := fun hc => hR0 (Polynomial.map_injective ι hinj
    (by rw [hc, Polynomial.map_zero]))
  -- transport the resultant to ℂ
  have hmap : Polynomial.resultant (R.map ι) (Φ.map ι) = ι (Polynomial.resultant R Φ) := by
    rw [show Polynomial.resultant (R.map ι) (Φ.map ι)
          = Polynomial.resultant (R.map ι) (Φ.map ι) R.natDegree Φ.natDegree by
        rw [hdegRC, hdegΦC, hdegΦ],
      Polynomial.resultant_map_map]
  -- the product formula over the roots of R
  have hsplits : (R.map ι).Splits := IsAlgClosed.splits _
  have hprod : Polynomial.resultant (R.map ι) (Φ.map ι)
      = (R.map ι).leadingCoeff ^ h * ((R.map ι).roots.map (Φ.map ι).eval).prod := by
    have hres := Polynomial.resultant_eq_prod_eval (R.map ι) (Φ.map ι) h
      (le_of_eq hdegΦC) hsplits
    rw [show Polynomial.resultant (R.map ι) (Φ.map ι)
          = Polynomial.resultant (R.map ι) (Φ.map ι) ((R.map ι).natDegree) h by
        rw [hdegΦC]]
    exact hres
  -- root count
  have hcard : Multiset.card (R.map ι).roots = R.natDegree := by
    rw [← hdegRC]
    exact hsplits.natDegree_eq_card_roots.symm
  -- the norm bound over the roots
  have hΦeval : ∀ β ∈ (R.map ι).roots,
      ‖(Φ.map ι).eval β‖ ≤ 2 * max 1 ‖β‖ ^ h := by
    intro β _
    have hΦC : Φ.map ι = cyclotomic (2 ^ m) ℂ := map_cyclotomic_int _ ℂ
    rw [hΦC, hhdef]
    exact norm_eval_cyclotomic_le hm β
  have hstep : ‖((R.map ι).roots.map (Φ.map ι).eval).prod‖
      ≤ ((R.map ι).roots.map (fun β => 2 * max 1 ‖β‖ ^ h)).prod := by
    rw [norm_multiset_prod_eq, Multiset.map_map]
    exact multiset_prod_map_le _ _ _
      (fun β _ => norm_nonneg _) (fun β hβ => hΦeval β hβ)
  have hnorm : ‖ι (Polynomial.resultant R Φ)‖
      ≤ ‖(R.map ι).leadingCoeff‖ ^ h
        * ((R.map ι).roots.map (fun β => 2 * max 1 ‖β‖ ^ h)).prod := by
    rw [← hmap, hprod, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left hstep (pow_nonneg (norm_nonneg _) h)
  -- pull out the 2s
  have hsplit2 : ((R.map ι).roots.map (fun β => 2 * max 1 ‖β‖ ^ h)).prod
      = 2 ^ R.natDegree * ((R.map ι).roots.map (fun β => max 1 ‖β‖ ^ h)).prod := by
    rw [show (fun β : ℂ => 2 * max 1 ‖β‖ ^ h)
        = fun β : ℂ => (fun _ => (2 : ℝ)) β * (fun β : ℂ => max 1 ‖β‖ ^ h) β from rfl]
    rw [Multiset.prod_map_mul]
    congr 1
    rw [Multiset.map_const', Multiset.prod_replicate, hcard]
  have hMpow : ((R.map ι).roots.map (fun β => max 1 ‖β‖ ^ h)).prod
      = (((R.map ι).roots.map (fun β => max 1 ‖β‖)).prod) ^ h := by
    rw [← Multiset.prod_map_pow]
  -- the combined real bound through the Mahler measure
  have hM : (R.map ι).mahlerMeasure
      = ‖(R.map ι).leadingCoeff‖
        * ((R.map ι).roots.map (fun z => max 1 ‖z‖)).prod :=
    mahlerMeasure_eq_prod_roots _
  have hprodnn : (0:ℝ) ≤ ((R.map ι).roots.map (fun z => max 1 ‖z‖)).prod := by
    refine Multiset.prod_nonneg fun x hx => ?_
    obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx
    positivity
  have hcomb : ‖ι (Polynomial.resultant R Φ)‖
      ≤ 2 ^ R.natDegree * (R.map ι).mahlerMeasure ^ h := by
    calc ‖ι (Polynomial.resultant R Φ)‖
        ≤ ‖(R.map ι).leadingCoeff‖ ^ h
          * (2 ^ R.natDegree
            * (((R.map ι).roots.map (fun β => max 1 ‖β‖)).prod) ^ h) := by
          rw [← hMpow, ← hsplit2]
          exact hnorm
    _ = 2 ^ R.natDegree * (‖(R.map ι).leadingCoeff‖
          * ((R.map ι).roots.map (fun β => max 1 ‖β‖)).prod) ^ h := by
        rw [mul_pow]
        ring
    _ = 2 ^ R.natDegree * (R.map ι).mahlerMeasure ^ h := by rw [← hM]
  -- Landau
  have hlandau : (R.map ι).mahlerMeasure ^ 2
      ≤ ∑ i ∈ (R.map ι).support, ‖(R.map ι).coeff i‖ ^ 2 := by
    have hl := Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff (R.map ι)
    have hnn : (0 : ℝ) ≤ ∑ i ∈ (R.map ι).support, ‖(R.map ι).coeff i‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    calc (R.map ι).mahlerMeasure ^ 2
        ≤ (√(∑ i ∈ (R.map ι).support, ‖(R.map ι).coeff i‖ ^ 2)) ^ 2 := by
          gcongr
          exact Polynomial.mahlerMeasure_nonneg _
    _ = _ := Real.sq_sqrt hnn
  -- identify the coefficient sum with the ℕ quantity
  have hcoeffsum : (∑ i ∈ (R.map ι).support, ‖(R.map ι).coeff i‖ ^ 2)
      = ((∑ i ∈ R.support, (R.coeff i).natAbs ^ 2 : ℕ) : ℝ) := by
    rw [Polynomial.support_map_of_injective _ hinj]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.coeff_map]
    change ‖((R.coeff i : ℤ) : ℂ)‖ ^ 2 = ((R.coeff i).natAbs : ℝ) ^ 2
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
  -- square the combined bound and finish over ℝ
  have hres_norm : ‖ι (Polynomial.resultant R Φ)‖
      = (((Polynomial.resultant R Φ).natAbs : ℝ)) := by
    change ‖((Polynomial.resultant R Φ : ℤ) : ℂ)‖ = _
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
  have hsq : ‖ι (Polynomial.resultant R Φ)‖ ^ 2
      ≤ (2 ^ R.natDegree * (R.map ι).mahlerMeasure ^ h) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hcomb 2
  have hexp1 : ((2 : ℝ) ^ R.natDegree) ^ 2 = 4 ^ R.natDegree := by
    rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 from by norm_num, ← pow_mul, mul_comm]
  have hexp2 : (((R.map ι).mahlerMeasure ^ h)) ^ 2
      = ((R.map ι).mahlerMeasure ^ 2) ^ h := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hle : ((R.map ι).mahlerMeasure ^ 2) ^ h
      ≤ (((∑ i ∈ R.support, (R.coeff i).natAbs ^ 2 : ℕ) : ℝ)) ^ h := by
    refine pow_le_pow_left₀ (pow_nonneg (Polynomial.mahlerMeasure_nonneg _) 2) ?_ h
    rw [← hcoeffsum]
    exact hlandau
  have hchain : (((Polynomial.resultant R Φ).natAbs : ℝ)) ^ 2
      ≤ (4 : ℝ) ^ R.natDegree
        * ((∑ i ∈ R.support, (R.coeff i).natAbs ^ 2 : ℕ) : ℝ) ^ h := by
    rw [← hres_norm]
    calc ‖ι (Polynomial.resultant R Φ)‖ ^ 2
        ≤ (2 ^ R.natDegree * (R.map ι).mahlerMeasure ^ h) ^ 2 := hsq
    _ = 4 ^ R.natDegree * ((R.map ι).mahlerMeasure ^ 2) ^ h := by
        rw [mul_pow, hexp1, hexp2]
    _ ≤ (4 : ℝ) ^ R.natDegree
        * ((∑ i ∈ R.support, (R.coeff i).natAbs ^ 2 : ℕ) : ℝ) ^ h :=
        mul_le_mul_of_nonneg_left hle (by positivity)
  exact_mod_cast hchain

end ArkLib.ProximityGap.SharpResultantBound

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.SharpResultantBound.mahlerMeasure_eq_prod_roots
#print axioms ArkLib.ProximityGap.SharpResultantBound.natAbs_resultant_cyclotomic_sq_le
