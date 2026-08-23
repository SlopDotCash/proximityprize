/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSInterpolantZDegreeGraded

/-!
# The sloped (Y,Z)-degree GS interpolant — BCIKS20 Claim 5.4, inequality (5.7)

The graded producer (`GSInterpolantZDegreeGraded.lean`) bounds every `F[Z]`-coefficient
of the integer interpolant by one flat budget. The P2 route to the Λ-weight kernel of
#302 (`Λ(α_t) ≤ 1` from the root equation) needs more: the **sloped** budget

  `deg_Z (Q₀.coeff_Y b) ≤ D_YZ − b`,

i.e. the total `(Y,Z)`-degree bound `deg_{Y,Z} Q ≤ D_YZ` of [BCIKS20] Claim 5.4 (5.7) —
without the slope, the interpolant's Λ-weight is unbounded and the per-order budget of
the P2 lane is unprovable. This file produces it, with the **tight, unconditional**
choice of budget

  `D_YZ := slopedBudget k D = ∑_{(a,b) ∈ wBI} b`:

sloping the unknown blocks (`Z`-cap `D_YZ − b` in the `Yᵇ`-column) costs exactly
`∑ b = D_YZ` unknowns relative to the flat count, while the constraint side stays at
`n·|cI|·(D_YZ+1)` (the column-wise entry bound `deg_Z ≤ b` makes every constraint row
uniform of degree `≤ D_YZ`). The in-tree surplus `numVars > numConstraints` then closes
the dimension count with room `+1` — no numeric side conditions at all.

* `slopedBudget` — `∑_{p ∈ wBI} p.2`, with `p.2 ≤ slopedBudget` pointwise and the
  closed-form cap `slopedBudget ≤ numVars·(D/(k−1))`;
* `zVecSloped` — the sloped unknown blocks, `natDegree ≤ D_YZ − b`;
* `sloped_count` — the tight dimension count;
* **`gs_existence_sloped`** — nonzero integer interpolant, GS `Conditions` over
  `K = F(Z)`, and the sloped budget `∀ b a, deg_Z((Q₀.coeff b).coeff a) ≤ D_YZ − b`;
* `gs_existence_sloped_card` — the degenerate-set corollary (`≤ D_YZ`).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

namespace GuruswamiSudan.OverRatFunc.ZDegree.Sloped

open Polynomial Polynomial.Bivariate Finset GuruswamiSudan
open GuruswamiSudan.OverRatFunc.ZDegree.Graded

variable {F : Type} [Field F]

attribute [local instance] Classical.propDecidable

local notation "K" => RatFunc F

/-- The tight sloped budget: the sum of all `Y`-exponents in the GS monomial support. -/
def slopedBudget (k D : ℕ) : ℕ := ∑ p ∈ weigthBoundIndices k D, p.2

/-- Each `Y`-exponent is at most the sloped budget. -/
lemma snd_le_slopedBudget {k D : ℕ} {p : ℕ × ℕ} (hp : p ∈ weigthBoundIndices k D) :
    p.2 ≤ slopedBudget k D :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp

/-- Closed-form cap on the sloped budget: `∑ b ≤ |wBI|·(D/(k−1))`. -/
lemma slopedBudget_le (k D : ℕ) (hk : 1 < k) :
    slopedBudget k D ≤ (weigthBoundIndices k D).card * (D / (k - 1)) := by
  unfold slopedBudget
  calc ∑ p ∈ weigthBoundIndices k D, p.2
      ≤ ∑ _p ∈ weigthBoundIndices k D, D / (k - 1) :=
        Finset.sum_le_sum fun p hp => snd_le_div_of_mem_weigthBoundIndices hk hp
    _ = (weigthBoundIndices k D).card * (D / (k - 1)) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- The sloped unknown block: in the `Yᵇ`-column the `Z`-cap is `D_YZ − b`. -/
noncomputable def zVecSloped (k D : ℕ)
    (x : (Σ p : weigthBoundIndices k D, Fin (slopedBudget k D - p.1.2 + 1)) → F) :
    weigthBoundIndices k D → F[X] :=
  fun p => ∑ c : Fin (slopedBudget k D - p.1.2 + 1), Polynomial.monomial (c : ℕ) (x ⟨p, c⟩)

theorem zVecSloped_coeff_fin {k D : ℕ}
    (x : (Σ p : weigthBoundIndices k D, Fin (slopedBudget k D - p.1.2 + 1)) → F)
    (p : weigthBoundIndices k D) (c : Fin (slopedBudget k D - p.1.2 + 1)) :
    (zVecSloped k D x p).coeff (c : ℕ) = x ⟨p, c⟩ := by
  unfold zVecSloped
  rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single c]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro b _ hne
    rw [Polynomial.coeff_monomial, if_neg fun hc => hne (Fin.ext hc)]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

/-- The sloped block obeys the sloped degree cap. -/
theorem zVecSloped_natDegree_le (k D : ℕ)
    (x : (Σ p : weigthBoundIndices k D, Fin (slopedBudget k D - p.1.2 + 1)) → F)
    (p : weigthBoundIndices k D) :
    (zVecSloped k D x p).natDegree ≤ slopedBudget k D - p.1.2 := by
  unfold zVecSloped
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun c _ => ?_
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp c.isLt)

/-- The sloped GS system as an `F`-linear map. -/
noncomputable def slopedMap (k n m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F) (D : ℕ) :
    ((Σ p : weigthBoundIndices k D, Fin (slopedBudget k D - p.1.2 + 1)) → F) →ₗ[F]
      ((Fin n × constraintIndices m) × Fin (slopedBudget k D + 1) → F) where
  toFun x rc :=
    ((gsMatrixZ k n m ωs f₀ f₁ D).mulVec (zVecSloped k D x) rc.1).coeff (rc.2 : ℕ)
  map_add' x y := by
    have hv : zVecSloped k D (x + y) = zVecSloped k D x + zVecSloped k D y := by
      funext p
      unfold zVecSloped
      simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
    funext rc
    simp [hv, Matrix.mulVec_add]
  map_smul' a x := by
    have hv : zVecSloped k D (a • x) = a • zVecSloped k D x := by
      funext p
      unfold zVecSloped
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, Polynomial.smul_monomial]
    funext rc
    simp [hv, Matrix.mulVec_smul, Polynomial.coeff_smul]

/-- **The tight sloped dimension count**: sloping costs exactly `∑ b = D_YZ` unknowns,
and the in-tree surplus `NC < |wBI|` absorbs it with room `+1`. -/
theorem sloped_count {k D NC : ℕ} (h : NC < (weigthBoundIndices k D).card) :
    NC * (slopedBudget k D + 1) <
      ∑ p ∈ (weigthBoundIndices k D).attach, (slopedBudget k D - p.1.2 + 1) := by
  classical
  set DYZ := slopedBudget k D with hDYZ
  -- the sloped unknown count is `|wBI|·(DYZ+1) − DYZ`, exactly
  have hsplit : (∑ p ∈ (weigthBoundIndices k D).attach, (DYZ - p.1.2 + 1)) + DYZ =
      (weigthBoundIndices k D).card * (DYZ + 1) := by
    have hterm : ∀ p ∈ (weigthBoundIndices k D).attach,
        (DYZ - p.1.2 + 1) + p.1.2 = DYZ + 1 := by
      intro p _
      have hle : p.1.2 ≤ DYZ := snd_le_slopedBudget p.2
      omega
    have hDYZattach : DYZ = ∑ p ∈ (weigthBoundIndices k D).attach, p.1.2 := by
      rw [hDYZ]
      unfold slopedBudget
      rw [← Finset.sum_attach (weigthBoundIndices k D) (fun q => q.2)]
    have hjoin : (∑ p ∈ (weigthBoundIndices k D).attach, (DYZ - p.1.2 + 1)) +
        ∑ p ∈ (weigthBoundIndices k D).attach, p.1.2 =
        ∑ p ∈ (weigthBoundIndices k D).attach, ((DYZ - p.1.2 + 1) + p.1.2) :=
      (Finset.sum_add_distrib).symm
    calc (∑ p ∈ (weigthBoundIndices k D).attach, (DYZ - p.1.2 + 1)) + DYZ
        = ∑ p ∈ (weigthBoundIndices k D).attach, ((DYZ - p.1.2 + 1) + p.1.2) := by
          rw [hDYZattach] at *
          exact hjoin
      _ = ∑ _p ∈ (weigthBoundIndices k D).attach, (DYZ + 1) :=
          Finset.sum_congr rfl hterm
      _ = (weigthBoundIndices k D).card * (DYZ + 1) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_attach]
  have hcard : NC + 1 ≤ (weigthBoundIndices k D).card := h
  nlinarith [hsplit, hcard]

/-- Rank-nullity for the sloped system. -/
theorem exists_nonzero_sloped_kernel {k n m : ℕ} (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (D : ℕ)
    (hcard : n * (constraintIndices m).card < (weigthBoundIndices k D).card) :
    ∃ x : (Σ p : weigthBoundIndices k D, Fin (slopedBudget k D - p.1.2 + 1)) → F,
      x ≠ 0 ∧ slopedMap k n m ωs f₀ f₁ D x = 0 := by
  classical
  have h_kernel_nontrivial :
      Module.finrank F
        ((Σ p : weigthBoundIndices k D, Fin (slopedBudget k D - p.1.2 + 1)) → F) >
        Module.finrank F
          ((Fin n × constraintIndices m) × Fin (slopedBudget k D + 1) → F) := by
    rw [Module.finrank_pi F, Module.finrank_pi F]
    have hSig : Fintype.card
        (Σ p : weigthBoundIndices k D, Fin (slopedBudget k D - p.1.2 + 1)) =
        ∑ p ∈ (weigthBoundIndices k D).attach, (slopedBudget k D - p.1.2 + 1) := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      rfl
    have hcount := sloped_count (k := k) (D := D)
      (NC := n * (constraintIndices m).card) hcard
    rw [hSig]
    simpa [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using hcount
  have h_inj : ¬ Function.Injective (slopedMap k n m ωs f₀ f₁ D) := by
    intro h_inj
    exact h_kernel_nontrivial.not_ge
      (LinearMap.finrank_range_of_inj h_inj ▸ Submodule.finrank_le _)
  contrapose! h_inj
  exact LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr fun x hx ↦
    by_contra fun hx' ↦ h_inj x hx' <| by simpa using hx)

/-- Constraint rows are uniformly `Z`-bounded by `D_YZ`: the column entry contributes
`≤ b`, the sloped block `≤ D_YZ − b`. -/
theorem mulVec_zVecSloped_natDegree_le {k n m : ℕ} (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (D : ℕ)
    (x : (Σ p : weigthBoundIndices k D, Fin (slopedBudget k D - p.1.2 + 1)) → F)
    (ist : Fin n × constraintIndices m) :
    ((gsMatrixZ k n m ωs f₀ f₁ D).mulVec (zVecSloped k D x) ist).natDegree ≤
      slopedBudget k D := by
  simp only [Matrix.mulVec, dotProduct]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun p _ => ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  have h1 := gsMatrixZ_natDegree_le_col ωs f₀ f₁ D ist p
  have h2 := zVecSloped_natDegree_le k D x p
  have h3 : p.1.2 ≤ slopedBudget k D := snd_le_slopedBudget p.2
  omega

/-- **The sloped (Y,Z)-degree GS interpolant ([BCIKS20] Claim 5.4, inequality (5.7)).**

A nonzero integer interpolant for the generic fold satisfying the GS `Conditions` over
`K = F(Z)` whose `Z`-degrees obey the **slope**: the `Yᵇ`-coefficient has
`deg_Z ≤ D_YZ − b` for the tight budget `D_YZ = slopedBudget k D` — i.e. the total
`(Y,Z)`-degree of the interpolant is at most `D_YZ`. This is the Λ-weight input of the
P2 lane. -/
theorem gs_existence_sloped {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (genericFold f₀ f₁)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      ∀ b a : ℕ, ((Q₀.coeff b).coeff a).natDegree ≤
        slopedBudget k (gs_degree_bound k n m) - b := by
  classical
  set D := gs_degree_bound k n m with hD
  set DYZ := slopedBudget k D with hDYZ
  -- 1. the dimension count
  have hcount : numConstraints n m < numVars k D :=
    gs_numVars_gt_numConstraints_of_gt_one hn hk hm
  have hcard : n * (constraintIndices m).card < (weigthBoundIndices k D).card := by
    simpa [numVars, numConstraints] using hcount
  -- 2. a nonzero kernel vector of the sloped F-linear system
  obtain ⟨x, hx0, hxker⟩ := exists_nonzero_sloped_kernel ωs f₀ f₁ D hcard
  set c' : weigthBoundIndices k D → F[X] := zVecSloped k D x with hc'
  have hc'0 : c' ≠ 0 := by
    intro habs
    apply hx0
    funext pc
    have h1 : (c' pc.1).coeff (pc.2 : ℕ) = x ⟨pc.1, pc.2⟩ := by
      rw [hc']; exact zVecSloped_coeff_fin x pc.1 pc.2
    rw [habs] at h1
    simpa using h1.symm
  have hdegW : ∀ ist : Fin n × constraintIndices m,
      ((gsMatrixZ k n m ωs f₀ f₁ D).mulVec c' ist).natDegree ≤ DYZ := by
    intro ist
    rw [hc', hDYZ]
    exact mulVec_zVecSloped_natDegree_le ωs f₀ f₁ D x ist
  have hc'ker : (gsMatrixZ k n m ωs f₀ f₁ D).mulVec c' = 0 := by
    funext ist
    rw [Pi.zero_apply]
    refine Polynomial.ext fun j => ?_
    rw [Polynomial.coeff_zero]
    by_cases hj : j < DYZ + 1
    · have h0 := congr_fun hxker (ist, (⟨j, hj⟩ : Fin (DYZ + 1)))
      simp only [slopedMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
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
  have hc''0 : c'' ≠ 0 := by
    intro habs
    apply hc'0
    funext p
    simpa [hc''] using (IsFractionRing.injective F[X] K)
      (by simpa [hc''] using congr_fun habs p)
  have hck'' : constraintMap k n m (liftedDomain ωs) (genericFold f₀ f₁) D c'' = 0 := by
    funext i st
    have hrep := constraintMap_eq_mulVec (k := k) (m := m) ωs f₀ f₁ D c'' (i, st)
    rw [show constraintMap k n m (liftedDomain ωs) (genericFold f₀ f₁) D c'' i st =
        constraintMap k n m (liftedDomain ωs) (genericFold f₀ f₁) D c''
          ((i, st) : Fin n × constraintIndices m).1
          ((i, st) : Fin n × constraintIndices m).2
      from rfl, hrep]
    show (((gsMatrixZ k n m ωs f₀ f₁ D).map (algebraMap F[X] K)).mulVec c'') (i, st) = 0
    have : ((gsMatrixZ k n m ωs f₀ f₁ D).map (algebraMap F[X] K)).mulVec c'' (i, st) =
        algebraMap F[X] K ((gsMatrixZ k n m ωs f₀ f₁ D).mulVec c' (i, st)) := by
      simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, hc'', map_sum, map_mul]
    rw [this, hc'ker]
    simp
  have h_inj : Function.Injective (coeffsToPoly (F := K) k D) := by
    have : Function.Injective (Finsupp.linearCombination K
        (fun p : weigthBoundIndices k D ↦ GuruswamiSudan.monomial (F := K) p.1.1 p.1.2)) :=
      linearIndependent_monomials.comp _ (fun p q h ↦ by aesop)
    exact this.comp (LinearEquiv.injective _)
  refine ⟨Q₀, ?_, ?_, ?_⟩
  · obtain ⟨p₀, hp₀⟩ := Function.ne_iff.mp hc'0
    intro habs
    apply hp₀
    have := hcoeff p₀.1.1 p₀.1.2
    rw [habs] at this
    simp only [Polynomial.coeff_zero] at this
    rw [dif_pos (by exact (Prod.mk.eta (p := p₀.1)) ▸ p₀.2)] at this
    rw [show (⟨(p₀.1.1, p₀.1.2), _⟩ : weigthBoundIndices k D) = p₀ from
      Subtype.ext (Prod.mk.eta)] at this
    exact this.symm
  · rw [hmap]
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
  · -- the sloped budget
    intro b a
    rw [hcoeff a b]
    by_cases h : (a, b) ∈ weigthBoundIndices k D
    · rw [dif_pos h, hc']
      exact zVecSloped_natDegree_le k D x ⟨(a, b), h⟩
    · rw [dif_neg h]
      simp

/-- **The sloped degenerate-set corollary**: the sloped interpolant's degenerate scalars
number at most `D_YZ` (the slope at `b = 0`). -/
theorem gs_existence_sloped_card [Fintype F] {n : ℕ} (k m : ℕ)
    (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (genericFold f₀ f₁)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      (∀ b a : ℕ, ((Q₀.coeff b).coeff a).natDegree ≤
        slopedBudget k (gs_degree_bound k n m) - b) ∧
      (Finset.univ.filter (fun z : F =>
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0)).card ≤
        slopedBudget k (gs_degree_bound k n m) := by
  obtain ⟨Q₀, h0, hcond, hdeg⟩ := gs_existence_sloped k m ωs f₀ f₁ hk hn hm
  refine ⟨Q₀, h0, hcond, hdeg, ?_⟩
  exact card_specialization_collapse_le h0
    (fun b a => le_trans (hdeg b a) (Nat.sub_le _ _))

end GuruswamiSudan.OverRatFunc.ZDegree.Sloped

/-! ## Axiom audit — all kernel-clean. -/
open GuruswamiSudan.OverRatFunc.ZDegree.Sloped in
#print axioms sloped_count
open GuruswamiSudan.OverRatFunc.ZDegree.Sloped in
#print axioms exists_nonzero_sloped_kernel
open GuruswamiSudan.OverRatFunc.ZDegree.Sloped in
#print axioms gs_existence_sloped
open GuruswamiSudan.OverRatFunc.ZDegree.Sloped in
#print axioms gs_existence_sloped_card
