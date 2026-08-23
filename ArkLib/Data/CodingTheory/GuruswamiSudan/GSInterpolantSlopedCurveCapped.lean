/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSInterpolantSlopedCurve

/-!
# The capped sloped GS interpolant — the `Θ(n)` repair of the matching-count numerics (#304)

**Finding F16 (matching-count numerics).**  The sloped curve producer
`gs_existence_sloped_curve` fixes the lazy cap `W = slopedBudgetCurve L k D = Σ_{wBI} (L−1)·b`
(the FULL sloping cost), which at Guruswami–Sudan parameters is `Θ(n)`
(`≈ (L−1)·(m+½)³·n/(6√ρ)`).  Feeding that flat `Z`-budget `DZ = W` into the sharp window
budget `sharpBudget … T ≈ 4·DZ·T²` (`SectionNewtonClearedSharp`) with tail horizon
`T = DX + d·(k−1) ≤ 2D = Θ(n)` gives a matching-count threshold `Θ(n³)` — but the §6
good-set count is only `|good| > (L−1)·errorBound·|F| = (L−1)·k²/(2·m_J)⁷ = Θ(n²)`
(the `|F|` cancels in the Johnson branch of `errorBound`).  The in-tree producer therefore
makes the section-Newton window **vacuous in the genuine regime**, short by a factor `Θ(n)`
that no choice of `|F|` repairs.

**The repair is the rank–nullity slack.**  The GS dimension margin
`numVars − numConstraints ≈ n/8` is itself `Θ(n)`, so the sloped linear system stays
solvable at ANY cap `W` satisfying

* `(L−1)·b ≤ W` for every column `(a, b) ∈ wBI`            (slope admissibility), and
* `slopedBudgetCurve < (numVars − numConstraints)·(W + 1)`  (margin count),

i.e. down to `W* ≈ slopedBudgetCurve/(numVars − numConstraints)`,
`≈ (4/3)·(L−1)·(m+½)³/√ρ` — **constant in `n`**.  Then `sharpBudget ≈ 4·W*·T² = Θ(n²)`, and the good-set count covers
the window iff `ρ^{3/2} ≳ (m+½)⁵·(2·m_J)⁷`, which holds at the BCIKS20 parameter coupling
`m ≈ √ρ/(2η)`, `m_J = min(η, √ρ/20)`, for every rate, with room to spare.

This file is `GSInterpolantSlopedCurve.lean` with the cap as a parameter (and the target
degree `D` generalized away from `gs_degree_bound`, which only the count ever used):

* `capped_count_of_margin` — the dimension count from the margin inequality;
* `gs_existence_sloped_curve_capped` — the producer at any admissible cap `W`;
* `cappedZBudgetCurve` — the canonical near-optimal cap
  `max ((L−1)·(D/(k−1))) (slopedBudgetCurve/(numVars − NC))`, with both admissibility
  lemmas (`slope_le_cappedZBudgetCurve`, `margin_cappedZBudgetCurve`);
* `gs_existence_sloped_curve_margin` / `gs_existence_sloped_curve_margin_card` — the
  front-door instantiation at the canonical cap and `D = gs_degree_bound k n m`, including
  the `≤ W` degenerate-set count.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurveCapped

open Polynomial Polynomial.Bivariate Finset GuruswamiSudan
open GuruswamiSudan.OverRatFunc.ZDegree.Graded
open GuruswamiSudan.OverRatFunc.ZDegree.Sloped
open GuruswamiSudan.OverRatFunc.ZDegree.Curve
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurve

variable {F : Type} [Field F]

attribute [local instance] Classical.propDecidable

local notation "K" => RatFunc F

/-! ## §1 — the capped unknown blocks -/

/-- The capped sloped unknown block: in the `Yᵇ`-column the `Z`-cap is `W − (L−1)·b`. -/
noncomputable def zVecCapped (L k D W : ℕ)
    (x : (Σ p : weigthBoundIndices k D, Fin (W - (L - 1) * p.1.2 + 1)) → F) :
    weigthBoundIndices k D → F[X] :=
  fun p => ∑ c : Fin (W - (L - 1) * p.1.2 + 1), Polynomial.monomial (c : ℕ) (x ⟨p, c⟩)

theorem zVecCapped_coeff_fin {L k D W : ℕ}
    (x : (Σ p : weigthBoundIndices k D, Fin (W - (L - 1) * p.1.2 + 1)) → F)
    (p : weigthBoundIndices k D) (c : Fin (W - (L - 1) * p.1.2 + 1)) :
    (zVecCapped L k D W x p).coeff (c : ℕ) = x ⟨p, c⟩ := by
  unfold zVecCapped
  rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single c]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro b _ hne
    rw [Polynomial.coeff_monomial, if_neg fun hc => hne (Fin.ext hc)]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

/-- The capped block obeys the capped degree bound. -/
theorem zVecCapped_natDegree_le (L k D W : ℕ)
    (x : (Σ p : weigthBoundIndices k D, Fin (W - (L - 1) * p.1.2 + 1)) → F)
    (p : weigthBoundIndices k D) :
    (zVecCapped L k D W x p).natDegree ≤ W - (L - 1) * p.1.2 := by
  unfold zVecCapped
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun c _ => ?_
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp c.isLt)

/-- The capped sloped GS system for the `L`-ary curve fold as an `F`-linear map. -/
noncomputable def slopedMapCapped (k n m : ℕ) (ωs : Fin n ↪ F) {L : ℕ}
    (f : Fin L → Fin n → F) (D W : ℕ) :
    ((Σ p : weigthBoundIndices k D, Fin (W - (L - 1) * p.1.2 + 1)) → F) →ₗ[F]
      ((Fin n × constraintIndices m) × Fin (W + 1) → F) where
  toFun x rc :=
    ((gsMatrixZCurve k n m ωs f D).mulVec (zVecCapped L k D W x) rc.1).coeff (rc.2 : ℕ)
  map_add' x y := by
    have hv : zVecCapped L k D W (x + y) =
        zVecCapped L k D W x + zVecCapped L k D W y := by
      funext p
      unfold zVecCapped
      simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
    funext rc
    simp [hv, Matrix.mulVec_add]
  map_smul' a x := by
    have hv : zVecCapped L k D W (a • x) = a • zVecCapped L k D W x := by
      funext p
      unfold zVecCapped
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, Polynomial.smul_monomial]
    funext rc
    simp [hv, Matrix.mulVec_smul, Polynomial.coeff_smul]

/-! ## §2 — the margin dimension count -/

/-- **The margin dimension count**: at any slope-admissible cap `W`, the capped unknown
count is exactly `numVars·(W+1) − slopedBudgetCurve`, so the system has a surplus as soon
as the margin pays the sloping cost: `slopedBudgetCurve < (numVars − NC)·(W+1)`. -/
theorem capped_count_of_margin {L k D W NC : ℕ}
    (hslope : ∀ p ∈ weigthBoundIndices k D, (L - 1) * p.2 ≤ W)
    (hmargin : slopedBudgetCurve L k D <
      ((weigthBoundIndices k D).card - NC) * (W + 1)) :
    NC * (W + 1) <
      ∑ p ∈ (weigthBoundIndices k D).attach, (W - (L - 1) * p.1.2 + 1) := by
  classical
  set S := slopedBudgetCurve L k D with hS
  set NV := (weigthBoundIndices k D).card with hNV
  -- the margin forces a genuine surplus `NC < NV`
  have hNC : NC < NV := by
    rcases Nat.lt_or_ge NC NV with h | h
    · exact h
    · rw [Nat.sub_eq_zero_of_le h, zero_mul] at hmargin
      omega
  -- the capped unknown count is `NV·(W+1) − S`, exactly
  have hsplit : (∑ p ∈ (weigthBoundIndices k D).attach, (W - (L - 1) * p.1.2 + 1)) + S =
      NV * (W + 1) := by
    have hterm : ∀ p ∈ (weigthBoundIndices k D).attach,
        (W - (L - 1) * p.1.2 + 1) + (L - 1) * p.1.2 = W + 1 := by
      intro p _
      have hle : (L - 1) * p.1.2 ≤ W := hslope p.1 p.2
      omega
    have hSattach : S = ∑ p ∈ (weigthBoundIndices k D).attach, (L - 1) * p.1.2 := by
      rw [hS]
      unfold slopedBudgetCurve
      rw [← Finset.sum_attach (weigthBoundIndices k D) (fun q => (L - 1) * q.2)]
    calc (∑ p ∈ (weigthBoundIndices k D).attach, (W - (L - 1) * p.1.2 + 1)) + S
        = ∑ p ∈ (weigthBoundIndices k D).attach,
            ((W - (L - 1) * p.1.2 + 1) + (L - 1) * p.1.2) := by
          rw [hSattach, ← Finset.sum_add_distrib]
      _ = ∑ _p ∈ (weigthBoundIndices k D).attach, (W + 1) :=
          Finset.sum_congr rfl hterm
      _ = NV * (W + 1) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_attach]
  have hsubmul : (NV - NC) * (W + 1) = NV * (W + 1) - NC * (W + 1) :=
    Nat.sub_mul NV NC (W + 1)
  have hmul_le : NC * (W + 1) ≤ NV * (W + 1) :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt hNC)
  omega

/-- Rank–nullity for the capped sloped curve system, from the margin count. -/
theorem exists_nonzero_capped_kernel {k n m L : ℕ} (ωs : Fin n ↪ F)
    (f : Fin L → Fin n → F) (D W : ℕ)
    (hcount : n * (constraintIndices m).card * (W + 1) <
      ∑ p ∈ (weigthBoundIndices k D).attach, (W - (L - 1) * p.1.2 + 1)) :
    ∃ x : (Σ p : weigthBoundIndices k D, Fin (W - (L - 1) * p.1.2 + 1)) → F,
      x ≠ 0 ∧ slopedMapCapped k n m ωs f D W x = 0 := by
  classical
  have h_kernel_nontrivial :
      Module.finrank F
        ((Σ p : weigthBoundIndices k D, Fin (W - (L - 1) * p.1.2 + 1)) → F) >
        Module.finrank F
          ((Fin n × constraintIndices m) × Fin (W + 1) → F) := by
    rw [Module.finrank_pi F, Module.finrank_pi F]
    have hSig : Fintype.card
        (Σ p : weigthBoundIndices k D, Fin (W - (L - 1) * p.1.2 + 1)) =
        ∑ p ∈ (weigthBoundIndices k D).attach, (W - (L - 1) * p.1.2 + 1) := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      rfl
    rw [hSig]
    simpa [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, mul_assoc]
      using hcount
  have h_inj : ¬ Function.Injective (slopedMapCapped k n m ωs f D W) := by
    intro h_inj
    exact h_kernel_nontrivial.not_ge
      (LinearMap.finrank_range_of_inj h_inj ▸ Submodule.finrank_le _)
  contrapose! h_inj
  exact LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr fun x hx ↦
    by_contra fun hx' ↦ h_inj x hx' <| by simpa using hx)

/-- Constraint rows are uniformly `Z`-bounded by `W` at any slope-admissible cap: the
column entry contributes `≤ (L−1)·b`, the capped block `≤ W − (L−1)·b`. -/
theorem mulVec_zVecCapped_natDegree_le {k n m L : ℕ} (ωs : Fin n ↪ F)
    (f : Fin L → Fin n → F) (D W : ℕ)
    (hslope : ∀ p ∈ weigthBoundIndices k D, (L - 1) * p.2 ≤ W)
    (x : (Σ p : weigthBoundIndices k D, Fin (W - (L - 1) * p.1.2 + 1)) → F)
    (ist : Fin n × constraintIndices m) :
    ((gsMatrixZCurve k n m ωs f D).mulVec (zVecCapped L k D W x) ist).natDegree ≤ W := by
  simp only [Matrix.mulVec, dotProduct]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun p _ => ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  have h1 := gsMatrixZCurve_natDegree_le_col ωs f D ist p
  have h2 := zVecCapped_natDegree_le L k D W x p
  have h3 : (L - 1) * p.1.2 ≤ W := hslope p.1 p.2
  omega

/-! ## §3 — the capped existence theorem -/

/-- **The capped sloped (Y,Z)-degree GS interpolant for the `L`-ary curve fold.**

A nonzero integer interpolant for the curve fold `∑ⱼ Zʲ·fⱼ` satisfying the GS `Conditions`
over `K = F(Z)` with the **capped** sloped budget: the `Yᵇ`-coefficient has
`deg_Z ≤ W − (L−1)·b` for ANY cap `W` that is slope-admissible and pays the sloping cost
out of the dimension margin.  `gs_existence_sloped_curve` is the special (lazy) case
`W = slopedBudgetCurve L k D`; at GS parameters the margin is `Θ(n)`, admitting
`W = Θ(slopedBudgetCurve/n)` — constant in `n` — which is what the section-Newton
matching-count numerics need. -/
theorem gs_existence_sloped_curve_capped {n L : ℕ} (k m D W : ℕ) (ωs : Fin n ↪ F)
    (f : Fin L → Fin n → F) (hm : 1 ≤ m)
    (hslope : ∀ p ∈ weigthBoundIndices k D, (L - 1) * p.2 ≤ W)
    (hmargin : slopedBudgetCurve L k D <
      ((weigthBoundIndices k D).card - n * (constraintIndices m).card) * (W + 1)) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m D (liftedDomain ωs) (curveFold f)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      ∀ b a : ℕ, ((Q₀.coeff b).coeff a).natDegree ≤ W - (L - 1) * b := by
  classical
  -- 1. the margin dimension count
  have hcount : n * (constraintIndices m).card * (W + 1) <
      ∑ p ∈ (weigthBoundIndices k D).attach, (W - (L - 1) * p.1.2 + 1) :=
    capped_count_of_margin hslope hmargin
  -- 2. a nonzero kernel vector of the capped F-linear system
  obtain ⟨x, hx0, hxker⟩ := exists_nonzero_capped_kernel ωs f D W hcount
  set c' : weigthBoundIndices k D → F[X] := zVecCapped L k D W x with hc'
  have hc'0 : c' ≠ 0 := by
    intro habs
    apply hx0
    funext pc
    have h1 : (c' pc.1).coeff (pc.2 : ℕ) = x ⟨pc.1, pc.2⟩ := by
      rw [hc']; exact zVecCapped_coeff_fin x pc.1 pc.2
    rw [habs] at h1
    simpa using h1.symm
  have hdegW : ∀ ist : Fin n × constraintIndices m,
      ((gsMatrixZCurve k n m ωs f D).mulVec c' ist).natDegree ≤ W := by
    intro ist
    rw [hc']
    exact mulVec_zVecCapped_natDegree_le ωs f D W hslope x ist
  have hc'ker : (gsMatrixZCurve k n m ωs f D).mulVec c' = 0 := by
    funext ist
    rw [Pi.zero_apply]
    refine Polynomial.ext fun j => ?_
    rw [Polynomial.coeff_zero]
    by_cases hj : j < W + 1
    · have h0 := congr_fun hxker (ist, (⟨j, hj⟩ : Fin (W + 1)))
      simp only [slopedMapCapped, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
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
  · -- the capped sloped budget
    intro b a
    rw [hcoeff a b]
    by_cases h : (a, b) ∈ weigthBoundIndices k D
    · rw [dif_pos h, hc']
      exact zVecCapped_natDegree_le L k D W x ⟨(a, b), h⟩
    · rw [dif_neg h]
      simp

/-! ## §4 — the canonical near-optimal cap -/

/-- **The canonical capped Z-budget**: large enough for every column slope, and one
division above the margin-optimal value `slopedBudgetCurve/(numVars − NC)`.  At GS
parameters (`NC = numConstraints n m`, `D = gs_degree_bound k n m`) the margin is `Θ(n)`
and this cap is `Θ_n(1)`: `≈ max((L−1)·(m+½)/√ρ, (4/3)·(L−1)·(m+½)³/√ρ)`. -/
def cappedZBudgetCurve (L k D NC : ℕ) : ℕ :=
  max ((L - 1) * (D / (k - 1)))
    (slopedBudgetCurve L k D / ((weigthBoundIndices k D).card - NC))

/-- The canonical cap is slope-admissible. -/
theorem slope_le_cappedZBudgetCurve {L k D NC : ℕ} (hk : 1 < k) {p : ℕ × ℕ}
    (hp : p ∈ weigthBoundIndices k D) :
    (L - 1) * p.2 ≤ cappedZBudgetCurve L k D NC :=
  le_trans (Nat.mul_le_mul_left _ (snd_le_div_of_mem_weigthBoundIndices hk hp))
    (le_max_left _ _)

/-- The canonical cap pays the sloping cost out of the margin. -/
theorem margin_cappedZBudgetCurve {L k D NC : ℕ}
    (hNC : NC < (weigthBoundIndices k D).card) :
    slopedBudgetCurve L k D <
      ((weigthBoundIndices k D).card - NC) * (cappedZBudgetCurve L k D NC + 1) := by
  set g := (weigthBoundIndices k D).card - NC with hg
  set S := slopedBudgetCurve L k D with hS
  have hg0 : 0 < g := by omega
  have hdivlt : S < g * (S / g + 1) := by
    nlinarith [Nat.div_add_mod S g, Nat.mod_lt S hg0]
  have hcap : S / g ≤ cappedZBudgetCurve L k D NC := le_max_right _ _
  calc S < g * (S / g + 1) := hdivlt
    _ ≤ g * (cappedZBudgetCurve L k D NC + 1) := by
        exact Nat.mul_le_mul_left _ (by omega)

/-- **The margin front door**: the capped sloped curve interpolant at the canonical cap
and the standard GS degree bound — `gs_existence_sloped_curve` with the `Z`-budget reduced
from `Θ(n)` to `Θ_n(1)`. -/
theorem gs_existence_sloped_curve_margin {n L : ℕ} (k m : ℕ) (ωs : Fin n ↪ F)
    (f : Fin L → Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (curveFold f)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      ∀ b a : ℕ, ((Q₀.coeff b).coeff a).natDegree ≤
        cappedZBudgetCurve L k (gs_degree_bound k n m) (numConstraints n m)
          - (L - 1) * b := by
  have hcard : numConstraints n m < numVars k (gs_degree_bound k n m) :=
    gs_numVars_gt_numConstraints_of_gt_one hn hk hm
  have hcard' : n * (constraintIndices m).card <
      (weigthBoundIndices k (gs_degree_bound k n m)).card := by
    simpa [numVars, numConstraints] using hcard
  refine gs_existence_sloped_curve_capped k m (gs_degree_bound k n m)
    (cappedZBudgetCurve L k (gs_degree_bound k n m) (numConstraints n m)) ωs f hm
    (fun p hp => slope_le_cappedZBudgetCurve hk hp) ?_
  have := margin_cappedZBudgetCurve
    (L := L) (k := k) (D := gs_degree_bound k n m) (NC := numConstraints n m)
    (by simpa [numVars] using hcard)
  simpa [numConstraints] using this

/-- **The margin front door with the degenerate-set count**: the canonical-cap interpolant
has at most `cappedZBudgetCurve` degenerate scalars — `Θ_n(1)` instead of the in-tree
`Θ(n)`, so the exceptional budget `b` of the §6 consumer stays constant as well. -/
theorem gs_existence_sloped_curve_margin_card [Fintype F] {n L : ℕ} (k m : ℕ)
    (ωs : Fin n ↪ F) (f : Fin L → Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (curveFold f)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      (∀ b a : ℕ, ((Q₀.coeff b).coeff a).natDegree ≤
        cappedZBudgetCurve L k (gs_degree_bound k n m) (numConstraints n m)
          - (L - 1) * b) ∧
      (Finset.univ.filter (fun z : F =>
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0)).card ≤
        cappedZBudgetCurve L k (gs_degree_bound k n m) (numConstraints n m) := by
  obtain ⟨Q₀, h0, hcond, hdeg⟩ := gs_existence_sloped_curve_margin k m ωs f hk hn hm
  refine ⟨Q₀, h0, hcond, hdeg, ?_⟩
  exact card_specialization_collapse_le h0
    (fun b a => le_trans (hdeg b a) (Nat.sub_le _ _))

/-- Sanity (non-regression): the lazy cap `W = slopedBudgetCurve` is always admissible —
the in-tree `gs_existence_sloped_curve` budget is the trivial-margin special case. -/
theorem slopedBudgetCurve_margin_admissible {L k D NC : ℕ}
    (hNC : NC < (weigthBoundIndices k D).card) :
    slopedBudgetCurve L k D <
      ((weigthBoundIndices k D).card - NC) * (slopedBudgetCurve L k D + 1) := by
  have h1 : 1 ≤ (weigthBoundIndices k D).card - NC := by omega
  calc slopedBudgetCurve L k D < slopedBudgetCurve L k D + 1 := Nat.lt_succ_self _
    _ = 1 * (slopedBudgetCurve L k D + 1) := (one_mul _).symm
    _ ≤ ((weigthBoundIndices k D).card - NC) * (slopedBudgetCurve L k D + 1) :=
        Nat.mul_le_mul_right _ h1

end GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurveCapped

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurveCapped in
#print axioms zVecCapped_coeff_fin
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurveCapped in
#print axioms zVecCapped_natDegree_le
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurveCapped in
#print axioms capped_count_of_margin
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurveCapped in
#print axioms exists_nonzero_capped_kernel
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurveCapped in
#print axioms mulVec_zVecCapped_natDegree_le
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurveCapped in
#print axioms gs_existence_sloped_curve_capped
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurveCapped in
#print axioms slope_le_cappedZBudgetCurve
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurveCapped in
#print axioms margin_cappedZBudgetCurve
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurveCapped in
#print axioms gs_existence_sloped_curve_margin
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurveCapped in
#print axioms gs_existence_sloped_curve_margin_card
open GuruswamiSudan.OverRatFunc.ZDegree.SlopedCurveCapped in
#print axioms slopedBudgetCurve_margin_admissible
