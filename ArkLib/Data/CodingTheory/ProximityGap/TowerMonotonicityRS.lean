/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TowerMonotonicity
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS

/-!
# Tower monotonicity for Reed–Solomon: the hypothesis-free instantiation (#357, item 23)

`TowerMonotonicity.lean` proved `ε_mca(C′, δ) ≤ ε_mca(C, δ)` under two structural
hypotheses.  This file discharges both for the smooth Reed–Solomon tower: with `g`
of order `2m`, upstairs domain `gⁱ` (`i < 2m`), downstairs domain `g^{2j}` (`j < m`),
and dimensions `K = 2K′ − 1`:

* `rs_hlift` — a downstairs codeword `eval P′` lifts to `eval (P′.comp X²)`, of
  degree `≤ 2(K′−1) < K`, since both fiber points square to the same downstairs
  point;
* `rs_heven` — the even part of an upstairs codeword `eval Q` is `eval (evenComp Q)`
  of the even-coefficient compression: `g^{j+m} = −g^j` (because `g^m = −1`), so the
  fiber average is `(Q(x) + Q(−x))/2`, and the parity split of the evaluation sum
  kills odd monomials and doubles even ones (`eval_add_eval_neg`).

**`epsMCA_rs_tower`**:

  `ε_mca(RS[F, g^{2j}, K′], δ) ≤ ε_mca(RS[F, gⁱ, 2K′−1], δ)`  for every `δ` —

every exact value, floor bound, or supply instance at scale `m` transports to scale
`2m`, hence to every dyadic scale above, with no side conditions beyond `orderOf g`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Tower

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m]
variable {g : F} (hg : orderOf g = 2 * m)

include hg

theorem g_pow_2m : g ^ (2 * m) = 1 := by
  rw [← hg]
  exact pow_orderOf_eq_one g

/-- `g^m = −1`: its square is `1` and it is not `1`. -/
theorem g_pow_m : g ^ m = -1 := by
  have hsq : g ^ m * g ^ m = 1 := by
    rw [← pow_add, show m + m = 2 * m by ring]
    exact g_pow_2m hg
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exfalso
    have hd : orderOf g ∣ m := orderOf_dvd_of_pow_eq_one h
    rw [hg] at hd
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have := Nat.le_of_dvd hm hd
    omega
  · exact h

/-- Odd characteristic, from the existence of an order-`2m` element. -/
theorem two_ne_zero' : (2 : F) ≠ 0 := by
  intro h2
  have hm1 : (-1 : F) = 1 := by linear_combination -h2
  have hgm := g_pow_m hg
  rw [hm1] at hgm
  have hd : orderOf g ∣ m := orderOf_dvd_of_pow_eq_one hgm
  rw [hg] at hd
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have := Nat.le_of_dvd hm hd
  omega

theorem g_ne_zero : g ≠ 0 := by
  intro h
  have h1 := g_pow_2m hg
  rw [h, zero_pow (by
    have := Nat.pos_of_ne_zero (NeZero.ne m)
    omega : 2 * m ≠ 0)] at h1
  exact zero_ne_one h1

/-- Power equality below the order, routed through the unit group (fields are not
left-cancellative at zero). -/
theorem g_pow_inj {a b : ℕ} (ha : a < 2 * m) (hb : b < 2 * m)
    (hab : g ^ a = g ^ b) : a = b := by
  set gu : Fˣ := Units.mk0 g (g_ne_zero hg) with hgu
  have hval : ∀ k : ℕ, ((gu ^ k : Fˣ) : F) = g ^ k := by
    intro k
    rw [Units.val_pow_eq_pow_val]
    rfl
  have habu : gu ^ a = gu ^ b :=
    Units.ext (by rw [hval, hval]; exact hab)
  have hord : orderOf gu = 2 * m := by
    rw [← orderOf_units]
    show orderOf ((Units.mk0 g (g_ne_zero hg) : Fˣ) : F) = 2 * m
    rw [Units.val_mk0]
    exact hg
  have h := pow_eq_pow_iff_modEq.mp habu
  rw [hord] at h
  exact Nat.ModEq.eq_of_lt_of_lt h ha hb

theorem upDom_injective :
    Function.Injective (fun i : Fin (2 * m) => g ^ (i : ℕ)) := by
  intro a b hab
  exact Fin.val_injective (g_pow_inj hg a.2 b.2 hab)

theorem downDom_injective :
    Function.Injective (fun j : Fin m => g ^ (2 * (j : ℕ))) := by
  intro a b hab
  have ha := a.2
  have hb := b.2
  have h2 : 2 * (a : ℕ) = 2 * (b : ℕ) :=
    g_pow_inj hg (by omega) (by omega) hab
  exact Fin.val_injective (by omega)

/-- The upstairs domain embedding `i ↦ gⁱ`. -/
noncomputable def upDom : Fin (2 * m) ↪ F :=
  ⟨fun i => g ^ (i : ℕ), upDom_injective hg⟩

/-- The downstairs domain embedding `j ↦ g^{2j}`. -/
noncomputable def downDom : Fin m ↪ F :=
  ⟨fun j => g ^ (2 * (j : ℕ)), downDom_injective hg⟩

theorem upDom_inl_sq (j : Fin m) : (upDom hg) (inl j) ^ 2 = (downDom hg) j := by
  simp only [upDom, downDom, Function.Embedding.coeFn_mk, inl]
  rw [← pow_mul]
  congr 1
  ring

theorem upDom_inr_sq (j : Fin m) : (upDom hg) (inr j) ^ 2 = (downDom hg) j := by
  simp only [upDom, downDom, Function.Embedding.coeFn_mk, inr]
  rw [← pow_mul, show ((j : ℕ) + m) * 2 = 2 * (j : ℕ) + 2 * m by ring, pow_add,
    g_pow_2m hg, mul_one]

theorem upDom_inr_eq_neg (j : Fin m) :
    (upDom hg) (inr j) = -((upDom hg) (inl j)) := by
  simp only [upDom, Function.Embedding.coeFn_mk, inl, inr]
  rw [pow_add, g_pow_m hg]
  ring

/-! ### The structural hypotheses for Reed–Solomon -/

/-- **Lifts of downstairs codewords are upstairs codewords** (`P′ ↦ P′.comp X²`). -/
theorem rs_hlift {K' : ℕ} (hK' : 1 ≤ K') :
    ∀ c' ∈ rsCode (downDom hg) K',
      lift c' ∈ rsCode (upDom hg) (2 * K' - 1) := by
  rintro c' ⟨P', hP', rfl⟩
  refine ⟨P'.comp (X ^ 2), ?_, ?_⟩
  · by_cases hP0 : P' = 0
    · rw [hP0]
      simp only [Polynomial.zero_comp, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · have hnd : P'.natDegree < K' :=
        (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hP'
      refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
      rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_pow]
      exact_mod_cast (by omega : P'.natDegree * 2 < 2 * K' - 1)
  · funext i
    simp only [lift, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
    congr 1
    rcases (by omega : (i : ℕ) < m ∨ m ≤ (i : ℕ)) with h | h
    · have hi : i = inl (cls i) := by
        simp only [inl, cls]
        exact Fin.val_injective (by simp [Nat.mod_eq_of_lt h])
      rw [hi, cls_inl, ← upDom_inl_sq hg]
    · have hmod : (i : ℕ) % m = (i : ℕ) - m := by
        rw [Nat.mod_eq_sub_mod h]
        exact Nat.mod_eq_of_lt (by have := i.2; omega)
      have hi : i = inr (cls i) := by
        simp only [inr, cls]
        refine Fin.val_injective ?_
        simp only [hmod]
        have hi2 := i.2
        omega
      rw [hi, cls_inr, ← upDom_inr_sq hg]

omit hg in
/-- The even-coefficient compression of a polynomial. -/
noncomputable def evenComp (Q : Polynomial F) (K' : ℕ) : Polynomial F :=
  ∑ i ∈ Finset.range K', Polynomial.C (Q.coeff (2 * i)) * X ^ i

omit hg in
theorem evenComp_degree_lt (Q : Polynomial F) {K' : ℕ} (hK' : 1 ≤ K') :
    (evenComp Q K').degree < (K' : ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe K')]
  intro i hi
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast Finset.mem_range.mp hi

omit hg in
/-- **The parity-split evaluation identity:** for `deg Q < 2K′−1`,
`Q(x) + Q(−x) = 2·(evenComp Q K′)(x²)`. -/
theorem eval_add_eval_neg {K' : ℕ} (hK' : 1 ≤ K') {Q : Polynomial F}
    (hQ : Q.degree < ((2 * K' - 1 : ℕ) : WithBot ℕ)) (x : F) :
    Q.eval x + Q.eval (-x) = 2 * (evenComp Q K').eval (x ^ 2) := by
  have hnd : Q.natDegree < 2 * K' - 1 := by
    by_cases hQ0 : Q = 0
    · rw [hQ0]
      simp only [Polynomial.natDegree_zero]
      omega
    · exact (Polynomial.natDegree_lt_iff_degree_lt hQ0).mpr hQ
  have heval : ∀ y : F,
      Q.eval y = ∑ e ∈ Finset.range (2 * K' - 1), Q.coeff e * y ^ e := fun y =>
    Polynomial.eval_eq_sum_range' hnd y
  -- split the exponent range by parity
  have hsplit : Finset.range (2 * K' - 1)
      = (Finset.range K').image (fun i => 2 * i)
        ∪ (Finset.range (K' - 1)).image (fun i => 2 * i + 1) := by
    ext e
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
    constructor
    · intro he
      rcases Nat.even_or_odd e with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact Or.inl ⟨i, by omega, show 2 * i = e by omega⟩
      · exact Or.inr ⟨i, by omega, show 2 * i + 1 = e by omega⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · show 2 * i < 2 * K' - 1
        omega
      · show 2 * i + 1 < 2 * K' - 1
        omega
  have hdisj : Disjoint ((Finset.range K').image (fun i => 2 * i))
      ((Finset.range (K' - 1)).image (fun i => 2 * i + 1)) := by
    rw [Finset.disjoint_left]
    rintro a ha hb
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ha
    obtain ⟨i', -, hi'⟩ := Finset.mem_image.mp hb
    have h1 : 2 * i = a := hi
    have h2 : 2 * i' + 1 = a := hi'
    omega
  have hinj2 : Set.InjOn (fun i => 2 * i) ↑(Finset.range K') := by
    intro a _ b _ h
    have h' : 2 * a = 2 * b := h
    omega
  have hinj21 : Set.InjOn (fun i => 2 * i + 1) ↑(Finset.range (K' - 1)) := by
    intro a _ b _ h
    have h' : 2 * a + 1 = 2 * b + 1 := h
    omega
  calc Q.eval x + Q.eval (-x)
      = ∑ e ∈ Finset.range (2 * K' - 1), Q.coeff e * (x ^ e + (-x) ^ e) := by
        rw [heval x, heval (-x), ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun e _ => by ring
    _ = (∑ e ∈ (Finset.range K').image (fun i => 2 * i),
          Q.coeff e * (x ^ e + (-x) ^ e))
        + ∑ e ∈ (Finset.range (K' - 1)).image (fun i => 2 * i + 1),
          Q.coeff e * (x ^ e + (-x) ^ e) := by
        rw [← Finset.sum_union hdisj, ← hsplit]
    _ = (∑ i ∈ Finset.range K', Q.coeff (2 * i) * (2 * (x ^ 2) ^ i)) + 0 := by
        congr 1
        · rw [Finset.sum_image hinj2]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hev : (-x) ^ (2 * i) = x ^ (2 * i) := (even_two_mul i).neg_pow x
          rw [hev, pow_mul]
          ring
        · rw [Finset.sum_image hinj21]
          refine Finset.sum_eq_zero fun i _ => ?_
          have hodd : (-x) ^ (2 * i + 1) = -(x ^ (2 * i + 1)) :=
            (odd_two_mul_add_one i).neg_pow x
          rw [hodd]
          ring
    _ = 2 * (evenComp Q K').eval (x ^ 2) := by
        rw [add_zero, evenComp, Polynomial.eval_finset_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X]
        ring

/-- **Even parts of upstairs codewords are downstairs codewords.** -/
theorem rs_heven {K' : ℕ} (hK' : 1 ≤ K') :
    ∀ v ∈ rsCode (upDom hg) (2 * K' - 1),
      evenPart v ∈ rsCode (downDom hg) K' := by
  rintro v ⟨Q, hQ, rfl⟩
  refine ⟨evenComp Q K', evenComp_degree_lt Q hK', ?_⟩
  funext j
  show ((fun i => Q.eval ((upDom hg) i)) (inl j)
      + (fun i => Q.eval ((upDom hg) i)) (inr j)) / 2
    = (evenComp Q K').eval ((downDom hg) j)
  simp only
  rw [upDom_inr_eq_neg hg, eval_add_eval_neg hK' hQ ((upDom hg) (inl j)),
    upDom_inl_sq hg]
  rw [mul_comm, mul_div_assoc, div_self (two_ne_zero' hg), mul_one]

/-- **Tower monotonicity for Reed–Solomon, hypothesis-free:**
`ε_mca(RS[g^{2j}, K′], δ) ≤ ε_mca(RS[gⁱ, 2K′−1], δ)` for every `δ`. -/
theorem epsMCA_rs_tower {K' : ℕ} (hK' : 1 ≤ K') (δ : ℝ≥0) :
    epsMCA (F := F) (A := F)
      ((rsCode (downDom hg) K' : Submodule F (Fin m → F)) : Set (Fin m → F)) δ
      ≤ epsMCA (F := F) (A := F)
        ((rsCode (upDom hg) (2 * K' - 1) :
          Submodule F (Fin (2 * m) → F)) : Set (Fin (2 * m) → F)) δ :=
  epsMCA_le_of_tower _ _ (two_ne_zero' hg) (rs_hlift hg hK') (rs_heven hg hK') δ

end ProximityGap.Tower

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Tower.eval_add_eval_neg
#print axioms ProximityGap.Tower.epsMCA_rs_tower
