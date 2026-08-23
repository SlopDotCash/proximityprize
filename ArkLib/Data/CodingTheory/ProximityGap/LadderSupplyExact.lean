/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LadderExactList

/-!
# THE LADDER SUPPLY HALF → THE EXACT LIST COUNT (#389)

`LadderExactList` proved the *rigidity* half of the subset-sum fibre law at `m = 2`
ladder words: every codeword agreeing `≥ 2r` with `w = x^{2r} + λx^{2r−2}` differs
from it by `∏_{t∈T}(x² − t)` for an `r`-subset `T ⊆ μ_{n/2}` with `Σ T = −λ`.  This
file proves the *supply* half and assembles the two into an exact count.

* `ladderFibreCodeword T` — the fibre codeword `i ↦ w_i − ∏_{t∈T}(dom_i² − t)`.
* `ladderFibreCodeword_mem` — it lies in `rsCode dom k` for `k ≥ 2r − 3`: the two
  top coefficients of `W − G_T(X²)` cancel (`X^{2r}` and, since `Σ T = −λ`, also
  `X^{2r−2}`); all coefficients are even-indexed, so the next nonzero one is at
  `2r − 4 < k`.
* `ladderFibreCodeword_agree_iff` — `c_T i = w_i ⟺ dom_i² ∈ T`: the agreement set
  is exactly the squaring-preimage of `T`.
* `ladder_fibre_agreement_card` — when the domain is all of `μ_n` (`n = 2^ν`), that
  preimage has size `2r` (the squaring map is 2-to-1 onto `μ_{n/2}`).

Together with `ladder_explainer_fiber` (rigidity) these pin the single-word list at
agreement `≥ 2r` to the subset-sum fibre exactly.  Issue #389.
-/

open Finset Polynomial

namespace ProximityGap.LadderList

open ProximityGap.SpikeFloor ProximityGap.Ownership

variable {L : Type} [Field L]
variable {ν n r k : ℕ} {ζ lam : L} {dom : Fin n ↪ L}

/-- Odd coefficients of an `X²`-composition vanish. -/
theorem coeff_comp_X_sq_odd (G : L[X]) (d : ℕ) :
    (G.comp (X ^ 2)).coeff (2 * d + 1) = 0 := by
  classical
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum, Polynomial.finset_sum_coeff]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [← pow_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have : ¬ (2 * d + 1 = 2 * e) := by omega
  simp [this]

/-- The fibre codeword attached to an `r`-subset `T ⊆ μ_{n/2}`. -/
def ladderFibreCodeword (dom : Fin n ↪ L) (r : ℕ) (lam : L) (T : Finset L) :
    Fin n → L :=
  fun i => ladderWord dom r lam i - ∏ t ∈ T, ((dom i) ^ 2 - t)

/-- **The supply half, membership**: for `k ≥ 2r − 3` and `Σ T = −λ`, the fibre
codeword lies in `rsCode dom k`. -/
theorem ladderFibreCodeword_mem (hr : 1 ≤ r) (hk1 : 1 ≤ k) (hk : 2 * r - 3 ≤ k)
    {T : Finset L} (hTcard : T.card = r) (hsumT : ∑ t ∈ T, t = -lam) :
    ladderFibreCodeword dom r lam T
      ∈ (rsCode dom k : Submodule L (Fin n → L)) := by
  classical
  set G : L[X] := ∏ t ∈ T, (X - C t) with hG
  set W : L[X] := X ^ (2 * r) + C lam * X ^ (2 * r - 2) with hW
  set Gc : L[X] := G.comp (X ^ 2) with hGc
  set D : L[X] := W - Gc with hD
  -- the fibre codeword is `D` evaluated on the domain
  have hpoint : ∀ i, ladderFibreCodeword dom r lam T i = D.eval (dom i) := by
    intro i
    have hGceval : Gc.eval (dom i) = ∏ t ∈ T, ((dom i) ^ 2 - t) := by
      rw [hGc, eval_comp, hG, eval_prod]
      simp
    rw [ladderFibreCodeword, hD, eval_sub, hGceval, hW, eval_add, eval_mul, eval_pow,
      eval_pow, eval_X, eval_C, ladderWord]
  -- structural facts about `G`, `Gc`, `W`
  have hGnat : G.natDegree = r := by
    rw [hG, natDegree_prod_of_monic _ _ fun t _ => monic_X_sub_C t]
    simp [hTcard]
  have hGccomp : Gc = ∏ t ∈ T, ((X : L[X]) ^ 2 - C t) := by
    rw [hGc, hG, Polynomial.prod_comp]
    exact Finset.prod_congr rfl fun t _ => by rw [sub_comp, X_comp, C_comp]
  have hGcnat : Gc.natDegree = 2 * r := by
    rw [hGccomp, natDegree_prod_of_monic _ _ (fun t _ => monic_X_pow_sub_C t (by norm_num))]
    have hdd : ∀ t ∈ T, ((X : L[X]) ^ 2 - C t).natDegree = 2 := fun t _ =>
      natDegree_X_pow_sub_C
    rw [Finset.sum_congr rfl hdd, Finset.sum_const, smul_eq_mul, hTcard]; ring
  have hGcmon : Gc.Monic := by
    rw [hGccomp]; exact monic_prod_of_monic _ _ fun t _ => monic_X_pow_sub_C t (by norm_num)
  have hWnat : W.natDegree = 2 * r := by
    rw [hW, natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · rw [natDegree_X_pow]
      exact lt_of_le_of_lt (natDegree_C_mul_le _ _) (by rw [natDegree_X_pow]; omega)
  -- coefficient agreement at `2r` and `2r − 2`; all coeffs even-indexed
  have hGc_top : Gc.coeff (2 * r) = 1 := by rw [← hGcnat]; exact hGcmon.leadingCoeff
  have hW_top : W.coeff (2 * r) = 1 := by
    rw [hW, coeff_add, coeff_X_pow, if_pos rfl, coeff_C_mul, coeff_X_pow,
      if_neg (by omega), mul_zero, add_zero]
  have hGc_sub : Gc.coeff (2 * r - 2) = lam := by
    have hidx : 2 * r - 2 = 2 * (r - 1) := by omega
    rw [hidx, hGc, coeff_comp_X_sq]
    have hco : G.coeff (r - 1) = -∑ t ∈ T, t := by
      have h1 : G.nextCoeff = -∑ t ∈ T, t := by rw [hG]; exact prod_X_sub_C_nextCoeff _
      rw [nextCoeff_of_natDegree_pos (by rw [hGnat]; omega), hGnat] at h1
      exact h1
    rw [hco, hsumT, neg_neg]
  have hW_sub : W.coeff (2 * r - 2) = lam := by
    rw [hW, coeff_add, coeff_X_pow, if_neg (by omega), coeff_C_mul, coeff_X_pow,
      if_pos rfl, mul_one, zero_add]
  -- `W` has only even coefficients
  have hW_odd : ∀ d, W.coeff (2 * d + 1) = 0 := by
    intro d
    rw [hW, coeff_add, coeff_X_pow, if_neg (by omega), coeff_C_mul, coeff_X_pow,
      if_neg (by omega), mul_zero, add_zero]
  -- the difference `D` has degree `< k`
  have hDdeg : D.degree < (k : WithBot ℕ) := by
    have hcoeff0 : ∀ m, 2 * r - 4 < m → D.coeff m = 0 := by
      intro m hm
      rw [hD, coeff_sub]
      rcases Nat.even_or_odd m with ⟨d, hd⟩ | ⟨d, hd⟩
      · -- even `m = 2d`, `m ≥ 2r − 2`
        have hm2 : m = 2 * d := by omega
        by_cases hmtop : m = 2 * r
        · rw [hmtop, hW_top, hGc_top, sub_self]
        · by_cases hmsub : m = 2 * r - 2
          · rw [hmsub, hW_sub, hGc_sub, sub_self]
          · -- `m > 2r` ⟹ both zero by degree
            have hmgt : 2 * r < m := by omega
            rw [coeff_eq_zero_of_natDegree_lt (by rw [hWnat]; omega),
              coeff_eq_zero_of_natDegree_lt (by rw [hGcnat]; omega), sub_zero]
      · -- odd `m = 2d + 1`: both `W` and `Gc` vanish
        rw [hd, hW_odd d, hGc, coeff_comp_X_sq_odd, sub_zero]
    have hDnat : D.natDegree ≤ 2 * r - 4 :=
      Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hcoeff0
    by_cases h0 : D = 0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe k
    · calc D.degree ≤ (2 * r - 4 : ℕ) := degree_le_of_natDegree_le hDnat
        _ < (k : WithBot ℕ) := by exact_mod_cast (by omega : 2 * r - 4 < k)
  refine ⟨D, hDdeg, ?_⟩
  funext i; exact hpoint i

/-- **The agreement set is the squaring-preimage of `T`**: the fibre codeword agrees
with the ladder word at `i` iff `dom_i² ∈ T`. -/
theorem ladderFibreCodeword_agree_iff {T : Finset L} (i : Fin n) :
    ladderFibreCodeword dom r lam T i = ladderWord dom r lam i ↔ (dom i) ^ 2 ∈ T := by
  classical
  rw [ladderFibreCodeword, sub_eq_self]
  constructor
  · intro hprod
    by_contra hmem
    exact absurd hprod (Finset.prod_ne_zero_iff.mpr fun t ht =>
      sub_ne_zero.mpr fun h => hmem (h ▸ ht))
  · intro hmem
    exact Finset.prod_eq_zero hmem (by rw [sub_self])

/-- **Square roots in `μ_n`**: every element of `μ_{n/2}` is a square of an element of
`μ_n` (the squaring map `μ_n → μ_{n/2}` is surjective). -/
theorem exists_sqrt_in_mu (hν : 1 ≤ ν) (hζ : IsPrimitiveRoot ζ (2 ^ ν))
    (hn : n = 2 ^ ν) {t : L} (ht : t ^ (n / 2) = 1) :
    ∃ s : L, s ^ n = 1 ∧ s ^ 2 = t := by
  haveI : NeZero (2 ^ ν) := ⟨(Nat.two_pow_pos ν).ne'⟩
  have hhalf : 2 * (n / 2) = n := by
    rw [hn]
    have : (2 : ℕ) ^ ν = 2 * 2 ^ (ν - 1) := by
      conv_lhs => rw [show ν = (ν - 1) + 1 by omega]
      rw [pow_succ']
    omega
  have htn : t ^ n = 1 := by
    rw [← hhalf, mul_comm, pow_mul, ht, one_pow]
  haveI : NeZero n := ⟨by rw [hn]; exact (Nat.two_pow_pos ν).ne'⟩
  rw [← hn] at hζ
  obtain ⟨j, hj, hjt⟩ := hζ.eq_pow_of_pow_eq_one htn
  -- `j` is even from `t^{n/2} = 1`
  have hjeven : 2 ∣ j := by
    have h1 : ζ ^ (j * (n / 2)) = 1 := by
      rw [pow_mul, hjt, ht]
    rw [hζ.pow_eq_one_iff_dvd] at h1
    -- `n ∣ j·(n/2)` with `n = 2·(n/2)` ⟹ `2 ∣ j`
    obtain ⟨c, hc⟩ := h1
    have hn0 : 0 < n / 2 := by
      rcases Nat.eq_zero_or_pos (n / 2) with h | h
      · rw [h] at hhalf; simp at hhalf; omega
      · exact h
    refine ⟨c, ?_⟩
    have : 2 * (n / 2) * c = j * (n / 2) := by rw [hhalf]; exact hc.symm
    have h2 : (n / 2) * (2 * c) = (n / 2) * j := by ring_nf; ring_nf at this; omega
    exact (Nat.eq_of_mul_eq_mul_left hn0 h2).symm
  obtain ⟨a, rfl⟩ := hjeven
  refine ⟨ζ ^ a, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · rw [← pow_mul, mul_comm a 2, hjt]

open Classical in
/-- **THE AGREEMENT COUNT**: over the full domain `μ_n` (`n = 2^ν`), the fibre
codeword's agreement set with the ladder word has size exactly `2·|T|` — the
squaring map is 2-to-1 onto `μ_{n/2}`. -/
theorem ladder_fibre_agreement_card (hν : 1 ≤ ν) (hζ : IsPrimitiveRoot ζ (2 ^ ν))
    (hn : n = 2 ^ ν) (h2 : (2 : L) ≠ 0) (hroot : ∀ i, (dom i) ^ n = 1)
    {T : Finset L} (hT : ∀ t ∈ T, t ^ (n / 2) = 1) :
    (Finset.univ.filter (fun i => (dom i) ^ 2 ∈ T)).card = 2 * T.card := by
  classical
  have hn1 : 1 ≤ n := by rw [hn]; exact Nat.one_le_two_pow
  set S : Finset (Fin n) := Finset.univ.filter (fun i => (dom i) ^ 2 ∈ T) with hS
  -- fibrewise over `i ↦ dom_i²`
  have hmaps : ∀ i ∈ S, (dom i) ^ 2 ∈ T := fun i hi => (Finset.mem_filter.mp hi).2
  have hneven : Even n := by
    rw [hn]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hfiber : ∀ t ∈ T, (S.filter (fun i => (dom i) ^ 2 = t)).card = 2 := by
    intro t ht
    obtain ⟨s, hsn, hst⟩ := exists_sqrt_in_mu hν hζ hn (hT t ht)
    have hnegn : (-s) ^ n = 1 := by rw [hneven.neg_pow, hsn]
    obtain ⟨i0, hi0⟩ := exists_dom_eq_of_root hn1 hroot hsn
    obtain ⟨i1, hi1⟩ := exists_dom_eq_of_root hn1 hroot hnegn
    have hs0 : s ≠ 0 := by
      intro h; rw [h, zero_pow (by omega : n ≠ 0)] at hsn; exact one_ne_zero hsn.symm
    have hsneg : s ≠ -s := by
      intro h
      apply hs0
      have : (2 : L) * s = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h2' | h2'
      · exact absurd h2' h2
      · exact h2'
    have hi01 : i0 ≠ i1 := by
      intro h
      apply hsneg
      have hcong := congrArg dom h
      rwa [hi0, hi1] at hcong
    have hfeq : S.filter (fun i => (dom i) ^ 2 = t) = {i0, i1} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, hS,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hsq⟩
        have hfac : (dom i - s) * (dom i + s) = 0 := by
          have h0 : (dom i) ^ 2 - s ^ 2 = 0 := by rw [hsq, hst]; ring
          linear_combination h0
        rcases mul_eq_zero.mp hfac with h | h
        · left; exact dom.injective (by rw [hi0, sub_eq_zero.mp h])
        · right; exact dom.injective (by rw [hi1, eq_neg_of_add_eq_zero_left h])
      · rintro (rfl | rfl)
        · exact ⟨by rw [hi0, hst]; exact ht, by rw [hi0, hst]⟩
        · exact ⟨by rw [hi1, neg_sq, hst]; exact ht, by rw [hi1, neg_sq, hst]⟩
    rw [hfeq, Finset.card_insert_of_notMem (by simp [hi01]), Finset.card_singleton]
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hfiber,
    Finset.sum_const, smul_eq_mul, mul_comm]

end ProximityGap.LadderList

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.LadderList.coeff_comp_X_sq_odd
#print axioms ProximityGap.LadderList.ladderFibreCodeword_mem
#print axioms ProximityGap.LadderList.ladderFibreCodeword_agree_iff
#print axioms ProximityGap.LadderList.exists_sqrt_in_mu
#print axioms ProximityGap.LadderList.ladder_fibre_agreement_card
