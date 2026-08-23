/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSInterpolantSloped
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSInterpolantZDegreeCurve

/-!
# The sloped (Y,Z)-degree GS interpolant for the `L`-ary curve fold

`GSInterpolantSloped.lean` produced the **sloped** Z-budget for the *pair* generic fold
`f₀ + Z·f₁`: a nonzero integer interpolant with `deg_Z((Q₀.coeff b).coeff a) ≤ D_YZ − b`,
the `(Z,Y)`-joint budget the balanced grading of the engine wants.
`GSInterpolantZDegreeCurve.lean` produced the **flat** budget for the `L`-ary *curve* fold
`∑ⱼ Zʲ·fⱼ` (Y-point `intPointYCurve`, entry Z-degree `≤ (L−1)·b` per column).  This file is
the missing corner of the square: the **sloped curve** producer.

Sloping with the curve slope `L − 1` (entry degree in the `Yᵇ`-column is `≤ (L−1)·b`, so the
unknown block in that column is capped at `W − (L−1)·b`) costs exactly
`∑_{(a,b) ∈ wBI} (L−1)·b` unknowns relative to the flat count, while every constraint row
stays uniformly of degree `≤ W`.  Hence the **tight, unconditional** budget is

  `W := slopedBudgetCurve L k D = ∑_{p ∈ wBI} (L−1)·p.2 = (L−1)·slopedBudget k D`,

and the in-tree surplus `numVars > numConstraints` closes the dimension count with room
`+1` — no numeric side conditions, exactly as in the pair case.

* `slopedBudgetCurve` — `∑_{p ∈ wBI} (L−1)·p.2`, with the pointwise bound
  `slope_le_slopedBudgetCurve` and the closed forms `slopedBudgetCurve_eq_mul`
  and `slopedBudgetCurve_le`;
* `zVecSlopedCurve` — the sloped unknown blocks, `natDegree ≤ W − (L−1)·b`;
* `sloped_count_curve` — the tight dimension count;
* **`gs_existence_sloped_curve`** — nonzero integer interpolant, GS `Conditions` for the
  `L`-ary curve fold over `K = F(Z)`, and the sloped budget
  `∀ b a, deg_Z((Q₀.coeff b).coeff a) ≤ W − (L−1)·b`;
* `gs_existence_sloped_curve_card` — the degenerate-set corollary (`≤ W`).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurve

open Polynomial Polynomial.Bivariate Finset GuruswamiSudan
open GuruswamiSudan.OverRatFunc.ZDegree.Graded
open GuruswamiSudan.OverRatFunc.ZDegree.Sloped
open GuruswamiSudan.OverRatFunc.ZDegree.Curve

variable {F : Type} [Field F]

attribute [local instance] Classical.propDecidable

local notation "K" => RatFunc F

/-- The tight sloped curve budget: the `(L−1)`-weighted sum of all `Y`-exponents in the GS
monomial support — the curve-slope mirror of `slopedBudget`. -/
def slopedBudgetCurve (L k D : ℕ) : ℕ := ∑ p ∈ weigthBoundIndices k D, (L - 1) * p.2

/-- The sloped curve budget is the pair sloped budget scaled by the curve slope `L − 1`. -/
lemma slopedBudgetCurve_eq_mul (L k D : ℕ) :
    slopedBudgetCurve L k D = (L - 1) * slopedBudget k D := by
  unfold slopedBudgetCurve slopedBudget
  rw [Finset.mul_sum]

/-- Each sloped column cost `(L−1)·b` is at most the sloped curve budget. -/
lemma slope_le_slopedBudgetCurve {L k D : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ weigthBoundIndices k D) :
    (L - 1) * p.2 ≤ slopedBudgetCurve L k D := by
  unfold slopedBudgetCurve
  exact Finset.single_le_sum (f := fun q => (L - 1) * q.2) (fun _ _ => Nat.zero_le _) hp

/-- Closed-form cap on the sloped curve budget: `∑ (L−1)·b ≤ |wBI|·((L−1)·(D/(k−1)))`. -/
lemma slopedBudgetCurve_le (L k D : ℕ) (hk : 1 < k) :
    slopedBudgetCurve L k D ≤
      (weigthBoundIndices k D).card * ((L - 1) * (D / (k - 1))) := by
  unfold slopedBudgetCurve
  calc ∑ p ∈ weigthBoundIndices k D, (L - 1) * p.2
      ≤ ∑ _p ∈ weigthBoundIndices k D, (L - 1) * (D / (k - 1)) :=
        Finset.sum_le_sum fun p hp =>
          Nat.mul_le_mul_left _ (snd_le_div_of_mem_weigthBoundIndices hk hp)
    _ = (weigthBoundIndices k D).card * ((L - 1) * (D / (k - 1))) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- The sloped curve unknown block: in the `Yᵇ`-column the `Z`-cap is `W − (L−1)·b`. -/
noncomputable def zVecSlopedCurve (L k D : ℕ)
    (x : (Σ p : weigthBoundIndices k D,
      Fin (slopedBudgetCurve L k D - (L - 1) * p.1.2 + 1)) → F) :
    weigthBoundIndices k D → F[X] :=
  fun p => ∑ c : Fin (slopedBudgetCurve L k D - (L - 1) * p.1.2 + 1),
    Polynomial.monomial (c : ℕ) (x ⟨p, c⟩)

theorem zVecSlopedCurve_coeff_fin {L k D : ℕ}
    (x : (Σ p : weigthBoundIndices k D,
      Fin (slopedBudgetCurve L k D - (L - 1) * p.1.2 + 1)) → F)
    (p : weigthBoundIndices k D)
    (c : Fin (slopedBudgetCurve L k D - (L - 1) * p.1.2 + 1)) :
    (zVecSlopedCurve L k D x p).coeff (c : ℕ) = x ⟨p, c⟩ := by
  unfold zVecSlopedCurve
  rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single c]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro b _ hne
    rw [Polynomial.coeff_monomial, if_neg fun hc => hne (Fin.ext hc)]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

/-- The sloped curve block obeys the sloped degree cap. -/
theorem zVecSlopedCurve_natDegree_le (L k D : ℕ)
    (x : (Σ p : weigthBoundIndices k D,
      Fin (slopedBudgetCurve L k D - (L - 1) * p.1.2 + 1)) → F)
    (p : weigthBoundIndices k D) :
    (zVecSlopedCurve L k D x p).natDegree ≤ slopedBudgetCurve L k D - (L - 1) * p.1.2 := by
  unfold zVecSlopedCurve
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun c _ => ?_
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp c.isLt)

/-- The sloped GS system for the `L`-ary curve fold as an `F`-linear map. -/
noncomputable def slopedMapCurve (k n m : ℕ) (ωs : Fin n ↪ F) {L : ℕ}
    (f : Fin L → Fin n → F) (D : ℕ) :
    ((Σ p : weigthBoundIndices k D,
      Fin (slopedBudgetCurve L k D - (L - 1) * p.1.2 + 1)) → F) →ₗ[F]
      ((Fin n × constraintIndices m) × Fin (slopedBudgetCurve L k D + 1) → F) where
  toFun x rc :=
    ((gsMatrixZCurve k n m ωs f D).mulVec (zVecSlopedCurve L k D x) rc.1).coeff (rc.2 : ℕ)
  map_add' x y := by
    have hv : zVecSlopedCurve L k D (x + y) =
        zVecSlopedCurve L k D x + zVecSlopedCurve L k D y := by
      funext p
      unfold zVecSlopedCurve
      simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
    funext rc
    simp [hv, Matrix.mulVec_add]
  map_smul' a x := by
    have hv : zVecSlopedCurve L k D (a • x) = a • zVecSlopedCurve L k D x := by
      funext p
      unfold zVecSlopedCurve
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, Polynomial.smul_monomial]
    funext rc
    simp [hv, Matrix.mulVec_smul, Polynomial.coeff_smul]

/-- **The tight sloped curve dimension count**: sloping with slope `L − 1` costs exactly
`∑ (L−1)·b = W` unknowns, and the in-tree surplus `NC < |wBI|` absorbs it with room `+1`. -/
theorem sloped_count_curve {L k D NC : ℕ} (h : NC < (weigthBoundIndices k D).card) :
    NC * (slopedBudgetCurve L k D + 1) <
      ∑ p ∈ (weigthBoundIndices k D).attach,
        (slopedBudgetCurve L k D - (L - 1) * p.1.2 + 1) := by
  classical
  set W := slopedBudgetCurve L k D with hW
  -- the sloped unknown count is `|wBI|·(W+1) − W`, exactly
  have hsplit : (∑ p ∈ (weigthBoundIndices k D).attach, (W - (L - 1) * p.1.2 + 1)) + W =
      (weigthBoundIndices k D).card * (W + 1) := by
    have hterm : ∀ p ∈ (weigthBoundIndices k D).attach,
        (W - (L - 1) * p.1.2 + 1) + (L - 1) * p.1.2 = W + 1 := by
      intro p _
      have hle : (L - 1) * p.1.2 ≤ W := slope_le_slopedBudgetCurve p.2
      omega
    have hWattach : W = ∑ p ∈ (weigthBoundIndices k D).attach, (L - 1) * p.1.2 := by
      rw [hW]
      unfold slopedBudgetCurve
      rw [← Finset.sum_attach (weigthBoundIndices k D) (fun q => (L - 1) * q.2)]
    have hjoin : (∑ p ∈ (weigthBoundIndices k D).attach, (W - (L - 1) * p.1.2 + 1)) +
        ∑ p ∈ (weigthBoundIndices k D).attach, (L - 1) * p.1.2 =
        ∑ p ∈ (weigthBoundIndices k D).attach,
          ((W - (L - 1) * p.1.2 + 1) + (L - 1) * p.1.2) :=
      (Finset.sum_add_distrib).symm
    calc (∑ p ∈ (weigthBoundIndices k D).attach, (W - (L - 1) * p.1.2 + 1)) + W
        = ∑ p ∈ (weigthBoundIndices k D).attach,
            ((W - (L - 1) * p.1.2 + 1) + (L - 1) * p.1.2) := by
          rw [hWattach] at *
          exact hjoin
      _ = ∑ _p ∈ (weigthBoundIndices k D).attach, (W + 1) :=
          Finset.sum_congr rfl hterm
      _ = (weigthBoundIndices k D).card * (W + 1) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_attach]
  have hcard : NC + 1 ≤ (weigthBoundIndices k D).card := h
  nlinarith [hsplit, hcard]

/-- Rank-nullity for the sloped curve system. -/
theorem exists_nonzero_sloped_kernel_curve {k n m L : ℕ} (ωs : Fin n ↪ F)
    (f : Fin L → Fin n → F) (D : ℕ)
    (hcard : n * (constraintIndices m).card < (weigthBoundIndices k D).card) :
    ∃ x : (Σ p : weigthBoundIndices k D,
        Fin (slopedBudgetCurve L k D - (L - 1) * p.1.2 + 1)) → F,
      x ≠ 0 ∧ slopedMapCurve k n m ωs f D x = 0 := by
  classical
  have h_kernel_nontrivial :
      Module.finrank F
        ((Σ p : weigthBoundIndices k D,
          Fin (slopedBudgetCurve L k D - (L - 1) * p.1.2 + 1)) → F) >
        Module.finrank F
          ((Fin n × constraintIndices m) × Fin (slopedBudgetCurve L k D + 1) → F) := by
    rw [Module.finrank_pi F, Module.finrank_pi F]
    have hSig : Fintype.card
        (Σ p : weigthBoundIndices k D,
          Fin (slopedBudgetCurve L k D - (L - 1) * p.1.2 + 1)) =
        ∑ p ∈ (weigthBoundIndices k D).attach,
          (slopedBudgetCurve L k D - (L - 1) * p.1.2 + 1) := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      rfl
    have hcount := sloped_count_curve (L := L) (k := k) (D := D)
      (NC := n * (constraintIndices m).card) hcard
    rw [hSig]
    simpa [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using hcount
  have h_inj : ¬ Function.Injective (slopedMapCurve k n m ωs f D) := by
    intro h_inj
    exact h_kernel_nontrivial.not_ge
      (LinearMap.finrank_range_of_inj h_inj ▸ Submodule.finrank_le _)
  contrapose! h_inj
  exact LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr fun x hx ↦
    by_contra fun hx' ↦ h_inj x hx' <| by simpa using hx)

/-- Constraint rows are uniformly `Z`-bounded by `W`: the column entry contributes
`≤ (L−1)·b`, the sloped block `≤ W − (L−1)·b`. -/
theorem mulVec_zVecSlopedCurve_natDegree_le {k n m L : ℕ} (ωs : Fin n ↪ F)
    (f : Fin L → Fin n → F) (D : ℕ)
    (x : (Σ p : weigthBoundIndices k D,
      Fin (slopedBudgetCurve L k D - (L - 1) * p.1.2 + 1)) → F)
    (ist : Fin n × constraintIndices m) :
    ((gsMatrixZCurve k n m ωs f D).mulVec (zVecSlopedCurve L k D x) ist).natDegree ≤
      slopedBudgetCurve L k D := by
  simp only [Matrix.mulVec, dotProduct]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun p _ => ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  have h1 := gsMatrixZCurve_natDegree_le_col ωs f D ist p
  have h2 := zVecSlopedCurve_natDegree_le L k D x p
  have h3 : (L - 1) * p.1.2 ≤ slopedBudgetCurve L k D := slope_le_slopedBudgetCurve p.2
  omega

/-- **The sloped (Y,Z)-degree GS interpolant for the `L`-ary curve fold.**

A nonzero integer interpolant for the curve fold `∑ⱼ Zʲ·fⱼ` satisfying the GS `Conditions`
over `K = F(Z)` whose `Z`-degrees obey the curve **slope**: the `Yᵇ`-coefficient has
`deg_Z ≤ W − (L−1)·b` for the tight budget `W = slopedBudgetCurve L k (gs_degree_bound k n m)`
— the `L`-ary mirror of `gs_existence_sloped`, with the affine slope `1` replaced by the
curve slope `L − 1` from `gsMatrixZCurve_natDegree_le_col`. -/
theorem gs_existence_sloped_curve {n L : ℕ} (k m : ℕ) (ωs : Fin n ↪ F)
    (f : Fin L → Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (curveFold f)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      ∀ b a : ℕ, ((Q₀.coeff b).coeff a).natDegree ≤
        slopedBudgetCurve L k (gs_degree_bound k n m) - (L - 1) * b := by
  classical
  set D := gs_degree_bound k n m with hD
  set W := slopedBudgetCurve L k D with hW
  -- 1. the dimension count
  have hcount : numConstraints n m < numVars k D :=
    gs_numVars_gt_numConstraints_of_gt_one hn hk hm
  have hcard : n * (constraintIndices m).card < (weigthBoundIndices k D).card := by
    simpa [numVars, numConstraints] using hcount
  -- 2. a nonzero kernel vector of the sloped F-linear system
  obtain ⟨x, hx0, hxker⟩ := exists_nonzero_sloped_kernel_curve ωs f D hcard
  set c' : weigthBoundIndices k D → F[X] := zVecSlopedCurve L k D x with hc'
  have hc'0 : c' ≠ 0 := by
    intro habs
    apply hx0
    funext pc
    have h1 : (c' pc.1).coeff (pc.2 : ℕ) = x ⟨pc.1, pc.2⟩ := by
      rw [hc']; exact zVecSlopedCurve_coeff_fin x pc.1 pc.2
    rw [habs] at h1
    simpa using h1.symm
  have hdegW : ∀ ist : Fin n × constraintIndices m,
      ((gsMatrixZCurve k n m ωs f D).mulVec c' ist).natDegree ≤ W := by
    intro ist
    rw [hc', hW]
    exact mulVec_zVecSlopedCurve_natDegree_le ωs f D x ist
  have hc'ker : (gsMatrixZCurve k n m ωs f D).mulVec c' = 0 := by
    funext ist
    rw [Pi.zero_apply]
    refine Polynomial.ext fun j => ?_
    rw [Polynomial.coeff_zero]
    by_cases hj : j < W + 1
    · have h0 := congr_fun hxker (ist, (⟨j, hj⟩ : Fin (W + 1)))
      simp only [slopedMapCurve, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
      rw [hc']
      exact h0
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hdegW ist) (by omega))
  -- 3. the integer interpolant, coefficient extraction, and the Conditions legs
  set Q₀ : (F[X])[X][Y] := ∑ p : weigthBoundIndices k D,
      Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p)) with hQ₀
  have hcoeff : ∀ a b : ℕ, ((Q₀.coeff b).coeff a) =
      if h : (a, b) ∈ weigthBoundIndices k D then c' ⟨(a, b), h⟩ else 0 := by
    intro a b
    rw [hQ₀, Polynomial.finset_sum_coeff]
    have hterm : ∀ p : weigthBoundIndices k D,
        ((Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p))).coeff b).coeff a =
          if p.1 = (a, b) then c' p else 0 := by
      intro p
      rw [Polynomial.coeff_monomial]
      by_cases h2 : p.1.2 = b
      · rw [if_pos h2, Polynomial.coeff_monomial]
        by_cases h1 : p.1.1 = a
        · rw [if_pos h1, if_pos (Prod.ext h1 h2)]
        · rw [if_neg h1, if_neg (fun h => h1 (by rw [h]))]
      · rw [if_neg h2, Polynomial.coeff_zero, if_neg (fun h => h2 (by rw [h]))]
    calc (∑ p : weigthBoundIndices k D,
            ((Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p))).coeff b)).coeff
              a
        = ∑ p : weigthBoundIndices k D,
            ((Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p))).coeff
              b).coeff a := by
          rw [Polynomial.finset_sum_coeff]
      _ = ∑ p : weigthBoundIndices k D, if p.1 = (a, b) then c' p else 0 :=
          Finset.sum_congr rfl fun p _ => hterm p
      _ = if h : (a, b) ∈ weigthBoundIndices k D then c' ⟨(a, b), h⟩ else 0 := by
          by_cases h : (a, b) ∈ weigthBoundIndices k D
          · rw [dif_pos h, Finset.sum_eq_single (⟨(a, b), h⟩ : weigthBoundIndices k D)]
            · rw [if_pos rfl]
            · intro p _ hne
              rw [if_neg (fun hp => hne (Subtype.ext hp))]
            · intro habs; exact absurd (Finset.mem_univ _) habs
          · rw [dif_neg h, Finset.sum_eq_zero]
            intro p _
            rw [if_neg (fun hp => h (by rw [← hp]; exact p.2))]
  -- the mapped interpolant is `coeffsToPoly` of the mapped kernel vector
  set c'' : weigthBoundIndices k D → K := fun p => algebraMap F[X] K (c' p) with hc''
  have hmap : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K)) =
      coeffsToPoly k D c'' := by
    rw [coeffsToPoly_eq_sum, hQ₀, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Polynomial.map_monomial]
    simp only [Polynomial.mapRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [Polynomial.map_monomial]
    rw [GuruswamiSudan.monomial, Polynomial.smul_monomial, Polynomial.smul_monomial,
      smul_eq_mul, mul_one]
  -- the mapped kernel vector is nonzero and in the kernel of `constraintMap`
  have hc''0 : c'' ≠ 0 := by
    intro habs
    apply hc'0
    funext p
    simpa [hc''] using (IsFractionRing.injective F[X] K)
      (by simpa [hc''] using congr_fun habs p)
  have hck'' : constraintMap k n m (liftedDomain ωs) (curveFold f) D c'' = 0 := by
    funext i st
    have hrep := constraintMapCurve_eq_mulVec (k := k) (m := m) ωs f D c'' (i, st)
    rw [show constraintMap k n m (liftedDomain ωs) (curveFold f) D c'' i st =
        constraintMap k n m (liftedDomain ωs) (curveFold f) D c''
          ((i, st) : Fin n × constraintIndices m).1
          ((i, st) : Fin n × constraintIndices m).2
      from rfl, hrep]
    show (((gsMatrixZCurve k n m ωs f D).map (algebraMap F[X] K)).mulVec c'') (i, st) = 0
    have : ((gsMatrixZCurve k n m ωs f D).map (algebraMap F[X] K)).mulVec c'' (i, st) =
        algebraMap F[X] K ((gsMatrixZCurve k n m ωs f D).mulVec c' (i, st)) := by
      simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, hc'', map_sum, map_mul]
    rw [this, hc'ker]
    simp
  -- injectivity of `coeffsToPoly` over K (for the nonzero leg)
  have h_inj : Function.Injective (coeffsToPoly (F := K) k D) := by
    have : Function.Injective (Finsupp.linearCombination K
        (fun p : weigthBoundIndices k D ↦ GuruswamiSudan.monomial (F := K) p.1.1 p.1.2)) :=
      linearIndependent_monomials.comp _ (fun p q h ↦ by aesop)
    exact this.comp (LinearEquiv.injective _)
  refine ⟨Q₀, ?_, ?_, ?_⟩
  · -- Q₀ ≠ 0 via coefficient extraction
    obtain ⟨p₀, hp₀⟩ := Function.ne_iff.mp hc'0
    intro habs
    apply hp₀
    have := hcoeff p₀.1.1 p₀.1.2
    rw [habs] at this
    simp only [Polynomial.coeff_zero] at this
    rw [dif_pos (by exact (Prod.mk.eta (p := p₀.1)) ▸ p₀.2)] at this
    rw [show (⟨(p₀.1.1, p₀.1.2), _⟩ : weigthBoundIndices k D) = p₀ from
      Subtype.ext (Prod.mk.eta)] at this
    exact this.symm
  · -- Conditions: the four legs at K, with kernel vector c''
    rw [hmap]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun h ↦ hc''0 <| h_inj <| by simpa using h
    · convert Option.some_le_some.mpr (natWeightedDegree_coeffsToPoly_le k D c'') using 1
      exact weightedDegree_eq_natWeightedDegree
    · intro i
      exact eval_eq_zero_of_constraint_zero hm fun s t hst ↦ by
        simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk] at hck''
        have := congr_fun (congr_fun hck'' i) ⟨(s, t), Finset.mem_filter.2
          ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by linarith),
            Finset.mem_range.mpr (by linarith)⟩, by linarith⟩⟩
        aesop
    · intro i
      apply rootMultiplicity_ge_of_shift_zero
      · exact fun h ↦ hc''0 <| h_inj <| by simpa using h
      · intro s t hst
        simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk] at hck''
        have := congr_fun (congr_fun hck'' i) ⟨(s, t), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by linarith),
            Finset.mem_range.mpr (by linarith)⟩, by linarith⟩⟩
        aesop
  · -- the sloped curve budget
    intro b a
    rw [hcoeff a b]
    by_cases h : (a, b) ∈ weigthBoundIndices k D
    · rw [dif_pos h, hc']
      exact zVecSlopedCurve_natDegree_le L k D x ⟨(a, b), h⟩
    · rw [dif_neg h]
      simp

/-- **The sloped curve degenerate-set corollary**: the sloped curve interpolant's degenerate
scalars number at most `W` (the slope at `b = 0`). -/
theorem gs_existence_sloped_curve_card [Fintype F] {n L : ℕ} (k m : ℕ)
    (ωs : Fin n ↪ F) (f : Fin L → Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (curveFold f)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      (∀ b a : ℕ, ((Q₀.coeff b).coeff a).natDegree ≤
        slopedBudgetCurve L k (gs_degree_bound k n m) - (L - 1) * b) ∧
      (Finset.univ.filter (fun z : F =>
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0)).card ≤
        slopedBudgetCurve L k (gs_degree_bound k n m) := by
  obtain ⟨Q₀, h0, hcond, hdeg⟩ := gs_existence_sloped_curve k m ωs f hk hn hm
  refine ⟨Q₀, h0, hcond, hdeg, ?_⟩
  exact card_specialization_collapse_le h0
    (fun b a => le_trans (hdeg b a) (Nat.sub_le _ _))

end GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurve

/-! ## Axiom audit — all kernel-clean. -/
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurve in
#print axioms slopedBudgetCurve_eq_mul
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurve in
#print axioms slopedBudgetCurve_le
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurve in
#print axioms sloped_count_curve
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurve in
#print axioms exists_nonzero_sloped_kernel_curve
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurve in
#print axioms mulVec_zVecSlopedCurve_natDegree_le
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurve in
#print axioms gs_existence_sloped_curve
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurve in
#print axioms gs_existence_sloped_curve_card
