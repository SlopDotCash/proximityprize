/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.MultiplicityInterpolation
import ArkLib.Data.CodingTheory.GuruswamiSudan.MonomialCount
open Finset

/-! # ROUTE 4: Trivariate (curve) Guruswami–Sudan dimension count & kernel existence

X = evaluation point, Y = codeword value, Z = curve parameter. Weights `(1, k, ρ)`.
Mirrors the in-tree bivariate `GSMultInterp` development. -/

namespace GS3

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Index sets and their cardinalities -/

/-- Trivariate monomial index set: triples `(a,b,c)` (X,Y,Z-exponents) of `(1,k,ρ)`-weighted
degree `< D`: `a + k*b + ρ*c < D`. -/
def monoIdx3 (k ρ D : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range D) ×ˢ (Finset.range D) ×ˢ (Finset.range D)).filter
    (fun abc => abc.1 + k * abc.2.1 + ρ * abc.2.2 < D)

/-- Trivariate multiplicity-`m` constraint index set at a single point: triples `(a,b,c)`
with `a + b + c < m`. -/
def multIdx3 (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range m) ×ˢ (Finset.range m) ×ˢ (Finset.range m)).filter
    (fun abc => abc.1 + abc.2.1 + abc.2.2 < m)

lemma mem_monoIdx3 {k ρ D : ℕ} {abc : ℕ × ℕ × ℕ} :
    abc ∈ monoIdx3 k ρ D ↔
      abc.1 < D ∧ abc.2.1 < D ∧ abc.2.2 < D ∧ abc.1 + k * abc.2.1 + ρ * abc.2.2 < D := by
  classical
  simp only [monoIdx3, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; tauto

lemma mem_multIdx3 {m : ℕ} {abc : ℕ × ℕ × ℕ} :
    abc ∈ multIdx3 m ↔ abc.1 + abc.2.1 + abc.2.2 < m := by
  classical
  simp only [multIdx3, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨⟨by omega, by omega, by omega⟩, h⟩

/-- Fiber of `multIdx3 m` over the Z-exponent `c` is in bijection with the bivariate
`multIdx (m - c)`. -/
theorem card_fiber_multIdx3 (m c : ℕ) (hc : c < m) :
    ((multIdx3 m).filter (fun abc => abc.2.2 = c)).card = (GSMultInterp.multIdx (m - c)).card := by
  classical
  apply Finset.card_bij (fun abc _ => (abc.1, abc.2.1))
  · intro abc hmem
    rw [Finset.mem_filter, mem_multIdx3] at hmem
    rw [GSMultInterp.mem_multIdx]
    obtain ⟨hlt, heq⟩ := hmem; omega
  · intro a ha b hb hab
    rw [Finset.mem_filter, mem_multIdx3] at ha hb
    obtain ⟨_, hac⟩ := ha; obtain ⟨_, hbc⟩ := hb
    simp only [Prod.mk.injEq] at hab
    ext
    · exact hab.1
    · exact hab.2
    · rw [hac, hbc]
  · intro ab hab
    rw [GSMultInterp.mem_multIdx] at hab
    refine ⟨(ab.1, ab.2, c), ?_, rfl⟩
    rw [Finset.mem_filter, mem_multIdx3]
    refine ⟨?_, rfl⟩; dsimp only; omega

theorem card_multIdx3_eq_sum (m : ℕ) :
    (multIdx3 m).card = ∑ c ∈ Finset.range m, (GSMultInterp.multIdx (m - c)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun abc : ℕ × ℕ × ℕ => abc.2.2)
        (t := Finset.range m) (s := multIdx3 m) ?_]
  · refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [Finset.mem_range] at hc
    exact card_fiber_multIdx3 m c hc
  · intro abc hmem
    rw [Finset.mem_coe, mem_multIdx3] at hmem
    rw [Finset.mem_coe, Finset.mem_range]; dsimp only; omega

private theorem six_mul_sum_tri (m : ℕ) :
    6 * (∑ j ∈ Finset.range m, (j + 1) * ((j + 1) + 1) / 2) = m * (m + 1) * (m + 2) := by
  induction m with
  | zero => decide
  | succ p ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    have hdvd : 2 ∣ (p + 1) * ((p + 1) + 1) := by
      simpa using (Nat.even_mul_succ_self (p + 1)).two_dvd
    obtain ⟨t, ht⟩ := hdvd
    rw [ht, Nat.mul_div_cancel_left _ (by norm_num)]
    nlinarith [ht]

/-- **The number of trivariate multiplicity-`m` constraints per point is the tetrahedral
number `m(m+1)(m+2)/6`** (the 3D analogue of the bivariate `m(m+1)/2`). -/
theorem card_multIdx3 (m : ℕ) :
    6 * (multIdx3 m).card = m * (m + 1) * (m + 2) := by
  rw [card_multIdx3_eq_sum]
  have hreindex : (∑ c ∈ Finset.range m, (GSMultInterp.multIdx (m - c)).card)
      = ∑ j ∈ Finset.range m, (j + 1) * ((j + 1) + 1) / 2 := by
    rw [← Finset.sum_range_reflect (fun c => (GSMultInterp.multIdx (m - c)).card) m]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hmc : m - (m - 1 - j) = j + 1 := by omega
    rw [hmc, GSMultInterp.card_multIdx]
  rw [hreindex, six_mul_sum_tri]

theorem card_fiber_monoIdx3 (k ρ D c : ℕ) (hk : 0 < k) (hcD : c < D) :
    ((monoIdx3 k ρ D).filter (fun abc => abc.2.2 = c)).card
      = (GSMultInterp.monoIdx k (D - ρ * c)).card := by
  classical
  apply Finset.card_bij (fun abc _ => (abc.1, abc.2.1))
  · intro abc hmem
    rw [Finset.mem_filter, mem_monoIdx3] at hmem
    obtain ⟨⟨_, _, _, hwd⟩, heq⟩ := hmem
    rw [GSMultInterp.mem_monoIdx_of_pos hk]
    dsimp only; subst heq; omega
  · intro a ha b hb hab
    rw [Finset.mem_filter, mem_monoIdx3] at ha hb
    obtain ⟨_, hac⟩ := ha; obtain ⟨_, hbc⟩ := hb
    simp only [Prod.mk.injEq] at hab
    ext
    · exact hab.1
    · exact hab.2
    · rw [hac, hbc]
  · intro ab hab
    rw [GSMultInterp.mem_monoIdx_of_pos hk] at hab
    refine ⟨(ab.1, ab.2, c), ?_, rfl⟩
    rw [Finset.mem_filter, mem_monoIdx3]
    dsimp only
    have hkb : ab.2 ≤ k * ab.2 := Nat.le_mul_of_pos_left ab.2 hk
    have hsub : D - ρ * c ≤ D := Nat.sub_le _ _
    refine ⟨⟨?_, ?_, hcD, ?_⟩, rfl⟩ <;> omega

theorem card_monoIdx3_eq_sum (k ρ D : ℕ) (hk : 0 < k) :
    (monoIdx3 k ρ D).card = ∑ c ∈ Finset.range D, (GSMultInterp.monoIdx k (D - ρ * c)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun abc : ℕ × ℕ × ℕ => abc.2.2)
        (t := Finset.range D) (s := monoIdx3 k ρ D) ?_]
  · refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [Finset.mem_range] at hc
    exact card_fiber_monoIdx3 k ρ D c hk hc
  · intro abc hmem
    rw [Finset.mem_coe, mem_monoIdx3] at hmem
    rw [Finset.mem_coe, Finset.mem_range]; dsimp only; omega

/-! ## Lower bounds for the trivariate monomial count (feasibility input) -/

/-- **Partial-window lower bound.** Keeping the first `t₃ ≤ D` Z-exponents:
`∑_{c<t₃} card(monoIdx k (D-ρ*c)) ≤ card(monoIdx3 k ρ D)`. -/
theorem card_monoIdx3_ge_partial (k ρ D t₃ : ℕ) (hk : 0 < k) (ht : t₃ ≤ D) :
    ∑ c ∈ Finset.range t₃, (GSMultInterp.monoIdx k (D - ρ * c)).card
      ≤ (monoIdx3 k ρ D).card := by
  rw [card_monoIdx3_eq_sum k ρ D hk]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono ht) (fun _ _ _ => Nat.zero_le _)

/-- **Explicit cubic (double-triangle) lower bound.** With outer Z-window `t₃` and inner
Y-window `t`, both valid at the worst (smallest) slice `D - ρ*(t₃-1)`,

  `t₃ · (t·(D - ρ*(t₃-1)) − k·t(t-1)/2) ≤ card(monoIdx3 k ρ D)`.

Choosing `t ≈ (D-ρt₃)/k` and `t₃ ≈ D/ρ` makes the RHS `≈ D³/(6kρ)`, the GS staircase
volume that beats the constraint count `n·m(m+1)(m+2)/6`. -/
theorem card_monoIdx3_ge_cubic (k ρ D t t₃ : ℕ) (hk : 0 < k) (ht3 : t₃ ≤ D)
    (hval1 : k * (t - 1) ≤ D - ρ * (t₃ - 1))
    (hval2 : t ≤ D - ρ * (t₃ - 1)) :
    t₃ * (t * (D - ρ * (t₃ - 1)) - k * (t * (t - 1) / 2)) ≤ (monoIdx3 k ρ D).card := by
  refine le_trans ?_ (card_monoIdx3_ge_partial k ρ D t₃ hk ht3)
  have hterm : ∀ c ∈ Finset.range t₃,
      t * (D - ρ * (t₃ - 1)) - k * (t * (t - 1) / 2)
        ≤ (GSMultInterp.monoIdx k (D - ρ * c)).card := by
    intro c hc
    rw [Finset.mem_range] at hc
    have hmono : ρ * c ≤ ρ * (t₃ - 1) := Nat.mul_le_mul_left ρ (by omega)
    have hslice : D - ρ * (t₃ - 1) ≤ D - ρ * c := Nat.sub_le_sub_left hmono D
    calc t * (D - ρ * (t₃ - 1)) - k * (t * (t - 1) / 2)
        ≤ t * (D - ρ * c) - k * (t * (t - 1) / 2) := by
          apply Nat.sub_le_sub_right; exact Nat.mul_le_mul_left t hslice
      _ ≤ (GSMultInterp.monoIdx k (D - ρ * c)).card :=
          GSMultInterp.card_monoIdx_ge_triangle k (D - ρ * c) t
            (le_trans hval1 hslice) (le_trans hval2 hslice)
  calc t₃ * (t * (D - ρ * (t₃ - 1)) - k * (t * (t - 1) / 2))
      = ∑ _c ∈ Finset.range t₃, (t * (D - ρ * (t₃ - 1)) - k * (t * (t - 1) / 2)) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ ∑ c ∈ Finset.range t₃, (GSMultInterp.monoIdx k (D - ρ * c)).card :=
        Finset.sum_le_sum hterm

/-! ## Coefficient / constraint spaces and the trivariate Hasse conditions -/

abbrev CoeffSpace3 (k ρ D : ℕ) := {abc : ℕ × ℕ × ℕ // abc ∈ monoIdx3 k ρ D} → F
abbrev ConstrSpace3 (n m : ℕ) := (Fin n × {abc : ℕ × ℕ × ℕ // abc ∈ multIdx3 m}) → F

/-- Order-`(a,b,c)` trivariate Hasse coefficient of `Q = ∑ coeff·X^s·Y^t·Z^u` evaluated at
`(x₀,y₀,z₀)`. F-linear in the coefficient vector. -/
def hasseCoeff3 (k ρ D : ℕ) (cf : CoeffSpace3 (F := F) k ρ D) (a b c : ℕ) (x₀ y₀ z₀ : F) : F :=
  ∑ stu : {abc : ℕ × ℕ × ℕ // abc ∈ monoIdx3 k ρ D},
    (Nat.choose stu.1.1 a : F) * (Nat.choose stu.1.2.1 b : F) * (Nat.choose stu.1.2.2 c : F)
      * cf stu * x₀ ^ (stu.1.1 - a) * y₀ ^ (stu.1.2.1 - b) * z₀ ^ (stu.1.2.2 - c)

/-- `Q` vanishes to order `m` at `(x₀,y₀,z₀)`: every order-`(a,b,c)` Hasse coefficient with
`a+b+c < m` vanishes. -/
def vanishesToOrder3 (k ρ D m : ℕ) (cf : CoeffSpace3 (F := F) k ρ D) (x₀ y₀ z₀ : F) : Prop :=
  ∀ a b c : ℕ, a + b + c < m → hasseCoeff3 k ρ D cf a b c x₀ y₀ z₀ = 0

/-- The trivariate interpolation constraint matrix. -/
noncomputable def constrMatrix3 (k ρ D m n : ℕ) (xs ys zs : Fin n → F) :
    Matrix (Fin n × {abc : ℕ × ℕ × ℕ // abc ∈ multIdx3 m})
           {abc : ℕ × ℕ × ℕ // abc ∈ monoIdx3 k ρ D} F :=
  fun row stu =>
    (Nat.choose stu.1.1 row.2.1.1 : F) * (Nat.choose stu.1.2.1 row.2.1.2.1 : F)
      * (Nat.choose stu.1.2.2 row.2.1.2.2 : F)
      * xs row.1 ^ (stu.1.1 - row.2.1.1) * ys row.1 ^ (stu.1.2.1 - row.2.1.2.1)
      * zs row.1 ^ (stu.1.2.2 - row.2.1.2.2)

omit [DecidableEq F] in
lemma constrMatrix3_mulVec (k ρ D m n : ℕ) (xs ys zs : Fin n → F)
    (cf : CoeffSpace3 (F := F) k ρ D) (i : Fin n)
    (abc : {abc : ℕ × ℕ × ℕ // abc ∈ multIdx3 m}) :
    Matrix.mulVec (constrMatrix3 k ρ D m n xs ys zs) cf (i, abc)
      = hasseCoeff3 k ρ D cf abc.1.1 abc.1.2.1 abc.1.2.2 (xs i) (ys i) (zs i) := by
  simp only [Matrix.mulVec, dotProduct, constrMatrix3, hasseCoeff3]
  apply Finset.sum_congr rfl
  intro stu _; ring

omit [DecidableEq F] in
lemma mulVec3_eq_zero_iff (k ρ D m n : ℕ) (xs ys zs : Fin n → F)
    (cf : CoeffSpace3 (F := F) k ρ D) :
    Matrix.mulVec (constrMatrix3 k ρ D m n xs ys zs) cf = 0
      ↔ ∀ i : Fin n, vanishesToOrder3 k ρ D m cf (xs i) (ys i) (zs i) := by
  classical
  constructor
  · intro hker i a b c hab
    have h := congrFun hker (i, ⟨(a, b, c), mem_multIdx3.mpr (by simpa using hab)⟩)
    rw [constrMatrix3_mulVec] at h
    simpa using h
  · intro hv
    funext row
    obtain ⟨i, abc⟩ := row
    rw [constrMatrix3_mulVec]
    exact hv i abc.1.1 abc.1.2.1 abc.1.2.2 (mem_multIdx3.mp abc.2)

/-! ## Kernel existence via the dimension count -/

omit [DecidableEq F] in
/-- **Trivariate (curve) Guruswami–Sudan multiplicity interpolation — EXISTENCE.**
Given `n` interpolation points `(xs i, ys i, zs i)`, multiplicity `m`, weights `(1,k,ρ)`,
degree bound `D`, if the number of vanishing constraints is strictly below the number of
available trivariate monomials, `n · card(multIdx3 m) < card(monoIdx3 k ρ D)`, then there
is a **nonzero** trivariate `Q` (coefficient vector `cf`) of `(1,k,ρ)`-weighted degree `< D`
vanishing to order `m` at every point. -/
theorem exists_ne_zero_vanishesToOrder3 (k ρ D m n : ℕ) (xs ys zs : Fin n → F)
    (hcount : n * (multIdx3 m).card < (monoIdx3 k ρ D).card) :
    ∃ cf : CoeffSpace3 (F := F) k ρ D, cf ≠ 0 ∧
      ∀ i : Fin n, vanishesToOrder3 k ρ D m cf (xs i) (ys i) (zs i) := by
  classical
  have hfr : Module.finrank F (ConstrSpace3 (F := F) n m)
      < Module.finrank F (CoeffSpace3 (F := F) k ρ D) := by
    simp only [ConstrSpace3, CoeffSpace3, Module.finrank_pi, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe]
    exact hcount
  obtain ⟨cf, hc0, hker⟩ :=
    GSMultInterp.exists_ne_zero_map_eq_zero
      (Matrix.mulVecLin (constrMatrix3 k ρ D m n xs ys zs)) hfr
  refine ⟨cf, hc0, ?_⟩
  rw [← mulVec3_eq_zero_iff]
  simpa [Matrix.mulVecLin_apply] using hker

omit [DecidableEq F] in
/-- **Directly-checkable trivariate GS feasibility.** If the explicit cubic monomial lower
bound `t₃·(t·(D-ρ(t₃-1)) − k·t(t-1)/2)` already exceeds the constraint count
`6 | … ` form `6·(n·card(multIdx3 m)) = n·m(m+1)(m+2)` (passed via the directly-checkable
`hbeat`), a nonzero vanishing trivariate `Q` exists. Removes the abstract
`card(monoIdx3 …)` hypothesis in favour of an arithmetic side condition (no √). -/
theorem exists_ne_zero_vanishesToOrder3_of_cubic
    (k ρ D t t₃ m n : ℕ) (xs ys zs : Fin n → F) (hk : 0 < k) (ht3 : t₃ ≤ D)
    (hval1 : k * (t - 1) ≤ D - ρ * (t₃ - 1)) (hval2 : t ≤ D - ρ * (t₃ - 1))
    (hbeat : n * (multIdx3 m).card < t₃ * (t * (D - ρ * (t₃ - 1)) - k * (t * (t - 1) / 2))) :
    ∃ cf : CoeffSpace3 (F := F) k ρ D, cf ≠ 0 ∧
      ∀ i : Fin n, vanishesToOrder3 k ρ D m cf (xs i) (ys i) (zs i) :=
  exists_ne_zero_vanishesToOrder3 k ρ D m n xs ys zs
    (lt_of_lt_of_le hbeat (card_monoIdx3_ge_cubic k ρ D t t₃ hk ht3 hval1 hval2))

end GS3

#print axioms GS3.card_multIdx3
#print axioms GS3.card_monoIdx3_eq_sum
#print axioms GS3.card_monoIdx3_ge_cubic
#print axioms GS3.exists_ne_zero_vanishesToOrder3
#print axioms GS3.exists_ne_zero_vanishesToOrder3_of_cubic
