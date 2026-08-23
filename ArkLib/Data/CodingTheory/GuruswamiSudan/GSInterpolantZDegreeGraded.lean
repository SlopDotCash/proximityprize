/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSInterpolantZDegree

/-!
# Issue #302 — graded Z-degree GS interpolant (budget linear in `n`)

`GSInterpolantZDegree.lean` produced the integer Guruswami–Sudan interpolant for the generic
fold `f₀ + Z·f₁` by the Cramer route, with per-coefficient `Z`-degree budget
`n·|constraintIndices m|·gs_degree_bound k n m` — *quadratic* in `n` (since `gs_degree_bound`
itself grows like `m·n`). This file refines the budget to one **linear in `n`** by solving the
GS system gradedly over `F` instead of over `F(Z)` ([BCIKS20] §5.2.1 dimension count):

* unknowns are the `Z`-coefficients `x(p, c)` (`c ≤ DZ`) of each monomial coefficient, with
  `DZ := n·|constraintIndices m|·(D/(k-1))` and `D := gs_degree_bound k n m`;
* each Hasse constraint, an `F[Z]`-polynomial equation, has `Z`-degree `≤ DZ + D/(k-1)`,
  because the `gsMatrixZ` entry in column `(a, b)` has `Z`-degree `≤ b ≤ D/(k-1)`
  (`gsMatrixZ_natDegree_le_col`, the column-wise strengthening of `gsMatrixZ_natDegree_le`);
* the dimension count `(NC+1)·(DZ+1) = NC·(DZ+DY+1) + 1` (`graded_count`) certifies a nonzero
  kernel over `F` by rank-nullity (`exists_nonzero_graded_kernel`);
* assembling the kernel block into `F[Z]`-coefficients (`zVec`) yields a *polynomial* kernel
  vector of the `F[Z]`-matrix directly — no Cramer determinant blow-up — and the interpolant
  assembly of `GSInterpolantZDegree.lean` then applies verbatim.

**Headline** (`gs_existence_zDegree_graded`): a nonzero integer interpolant
`Q₀ : F[Z][X][Y]` satisfying the GS `Conditions` over `K = F(Z)` whose every
`F[Z]`-coefficient has `natDegree ≤ n·|constraintIndices m|·(gs_degree_bound k n m/(k-1))`.
Combined with `card_specialization_collapse_le` this yields the linear-in-`n` degenerate-set
bound (`gs_existence_zDegree_graded_card`).
-/

namespace GuruswamiSudan.OverRatFunc.ZDegree.Graded

open Polynomial Polynomial.Bivariate Finset GuruswamiSudan

variable {F : Type} [Field F]

attribute [local instance] Classical.propDecidable

local notation "K" => RatFunc F

/-- The graded dimension count: with unknown blocks of size `NC·DY + 1` and constraint blocks
of size `NC·DY + DY + 1`, the strict column surplus `NC < cW` gives strictly more unknowns
than equations: `(NC+1)·(NC·DY+1) = NC·(NC·DY+DY+1) + 1`. -/
theorem graded_count {NC DY cW : ℕ} (h : NC < cW) :
    NC * (NC * DY + DY + 1) < cW * (NC * DY + 1) := by
  have hkey : (NC + 1) * (NC * DY + 1) = NC * (NC * DY + DY + 1) + 1 := by ring
  calc NC * (NC * DY + DY + 1) < NC * (NC * DY + DY + 1) + 1 := Nat.lt_succ_self _
    _ = (NC + 1) * (NC * DY + 1) := hkey.symm
    _ ≤ cW * (NC * DY + 1) := Nat.mul_le_mul (Nat.succ_le_of_lt h) le_rfl

/-- Membership in `weigthBoundIndices k D` bounds the `Y`-exponent by `D / (k-1)` when
`1 < k`: from `a + (k-1)·b ≤ D` we get `(k-1)·b ≤ D`, i.e. `b ≤ D/(k-1)`. -/
theorem snd_le_div_of_mem_weigthBoundIndices {k D : ℕ} (hk : 1 < k) {p : ℕ × ℕ}
    (hp : p ∈ weigthBoundIndices k D) : p.2 ≤ D / (k - 1) := by
  simp only [weigthBoundIndices, mem_filter] at hp
  refine (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hk)).mpr ?_
  calc p.2 * (k - 1) = (k - 1) * p.2 := Nat.mul_comm _ _
    _ ≤ p.1 + (k - 1) * p.2 := Nat.le_add_left _ _
    _ ≤ D := hp.2

/-- **Column-wise Z-degree bound** for `gsMatrixZ`: the entry in column `(a, b)` has
`natDegree ≤ b` — the entry is a constant times `(f₀ᵢ + Z·f₁ᵢ)^(b-t)` and the base is linear
in `Z`. This is the strengthening of `gsMatrixZ_natDegree_le` driving the linear-in-`n`
budget. -/
theorem gsMatrixZ_natDegree_le_col {k n m : ℕ} (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (D : ℕ) (ist : Fin n × constraintIndices m)
    (p : weigthBoundIndices k D) :
    (gsMatrixZ k n m ωs f₀ f₁ D ist p).natDegree ≤ p.1.2 := by
  calc (gsMatrixZ k n m ωs f₀ f₁ D ist p).natDegree
      ≤ (C ((p.1.1.choose ist.2.1.1 : F) * (ωs ist.1) ^ (p.1.1 - ist.2.1.1) *
            (p.1.2.choose ist.2.1.2 : F))).natDegree +
        ((C (f₀ ist.1) + X * C (f₁ ist.1)) ^ (p.1.2 - ist.2.1.2)).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 0 + (p.1.2 - ist.2.1.2) * 1 := by
        gcongr
        · exact le_of_eq (Polynomial.natDegree_C _)
        · refine Polynomial.natDegree_pow_le.trans ?_
          gcongr
          refine (Polynomial.natDegree_add_le _ _).trans ?_
          refine max_le (by simp) ?_
          exact (Polynomial.natDegree_mul_le).trans (by simp [Polynomial.natDegree_C])
    _ ≤ p.1.2 := by omega

/-- The `F[Z]`-vector assembled from a graded block of scalar unknowns: component `p` is the
polynomial `∑_{c ≤ DZ} x(p,c)·Z^c`, of `natDegree ≤ DZ`. -/
noncomputable def zVec (k D DZ : ℕ) (x : weigthBoundIndices k D × Fin (DZ + 1) → F) :
    weigthBoundIndices k D → F[X] :=
  fun p => ∑ c : Fin (DZ + 1), Polynomial.monomial (c : ℕ) (x (p, c))

/-- Coefficient extraction for `zVec`. -/
theorem zVec_coeff {k D DZ : ℕ} (x : weigthBoundIndices k D × Fin (DZ + 1) → F)
    (p : weigthBoundIndices k D) (j : ℕ) :
    (zVec k D DZ x p).coeff j = if h : j < DZ + 1 then x (p, ⟨j, h⟩) else 0 := by
  unfold zVec
  rw [Polynomial.finset_sum_coeff]
  by_cases h : j < DZ + 1
  · rw [dif_pos h, Finset.sum_eq_single (⟨j, h⟩ : Fin (DZ + 1))]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro c _ hne
      rw [Polynomial.coeff_monomial, if_neg fun hc => hne (Fin.ext hc)]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · rw [dif_neg h, Finset.sum_eq_zero]
    intro c _
    rw [Polynomial.coeff_monomial, if_neg (fun hc : (c : ℕ) = j => h (hc ▸ c.isLt))]

/-- `Fin`-indexed form of `zVec_coeff`. -/
theorem zVec_coeff_fin {k D DZ : ℕ} (x : weigthBoundIndices k D × Fin (DZ + 1) → F)
    (p : weigthBoundIndices k D) (c : Fin (DZ + 1)) :
    (zVec k D DZ x p).coeff (c : ℕ) = x (p, c) := by
  rw [zVec_coeff, dif_pos c.isLt]

/-- Each component of `zVec` has `natDegree ≤ DZ`. -/
theorem zVec_natDegree_le (k D DZ : ℕ) (x : weigthBoundIndices k D × Fin (DZ + 1) → F)
    (p : weigthBoundIndices k D) : (zVec k D DZ x p).natDegree ≤ DZ := by
  unfold zVec
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun c _ => ?_
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp c.isLt)

/-- The graded GS system as an `F`-linear map: unknown blocks `x(p, ·)` are sent to the
`Z`-coefficients (orders `0..DW`) of every `F[Z]`-valued Hasse constraint of the generic
fold. -/
noncomputable def gradedMap (k n m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (D DZ DW : ℕ) :
    (weigthBoundIndices k D × Fin (DZ + 1) → F) →ₗ[F]
      ((Fin n × constraintIndices m) × Fin (DW + 1) → F) where
  toFun x rc :=
    ((gsMatrixZ k n m ωs f₀ f₁ D).mulVec (zVec k D DZ x) rc.1).coeff (rc.2 : ℕ)
  map_add' x y := by
    have hv : zVec k D DZ (x + y) = zVec k D DZ x + zVec k D DZ y := by
      funext p
      unfold zVec
      simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
    funext rc
    simp [hv, Matrix.mulVec_add]
  map_smul' a x := by
    have hv : zVec k D DZ (a • x) = a • zVec k D DZ x := by
      funext p
      unfold zVec
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, Polynomial.smul_monomial]
    funext rc
    simp [hv, Matrix.mulVec_smul, Polynomial.coeff_smul]

/-- Rank-nullity for the graded system: when the unknown count `|wBI|·(DZ+1)` exceeds the
equation count `n·|cI|·(DW+1)`, the graded map has a nonzero kernel vector. -/
theorem exists_nonzero_graded_kernel {k n m : ℕ} (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (D DZ DW : ℕ)
    (hcard : n * (constraintIndices m).card * (DW + 1) <
      (weigthBoundIndices k D).card * (DZ + 1)) :
    ∃ x : weigthBoundIndices k D × Fin (DZ + 1) → F,
      x ≠ 0 ∧ gradedMap k n m ωs f₀ f₁ D DZ DW x = 0 := by
  have h_kernel_nontrivial :
      Module.finrank F (weigthBoundIndices k D × Fin (DZ + 1) → F) >
        Module.finrank F ((Fin n × constraintIndices m) × Fin (DW + 1) → F) := by
    rw [Module.finrank_pi F, Module.finrank_pi F]
    simpa [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using hcard
  have h_inj : ¬ Function.Injective (gradedMap k n m ωs f₀ f₁ D DZ DW) := by
    intro h_inj
    exact h_kernel_nontrivial.not_ge
      (LinearMap.finrank_range_of_inj h_inj ▸ Submodule.finrank_le _)
  contrapose! h_inj
  exact LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr fun x hx ↦
    by_contra fun hx' ↦ h_inj x hx' <| by simpa using hx)

/-- Each `F[Z]`-valued Hasse constraint applied to a graded vector has `Z`-degree at most
`DZ + D/(k-1)`: column entries have degree `≤ b ≤ D/(k-1)` and the vector has degree
`≤ DZ`. -/
theorem mulVec_zVec_natDegree_le {k n m : ℕ} (hk : 1 < k) (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (D DZ : ℕ)
    (x : weigthBoundIndices k D × Fin (DZ + 1) → F) (ist : Fin n × constraintIndices m) :
    ((gsMatrixZ k n m ωs f₀ f₁ D).mulVec (zVec k D DZ x) ist).natDegree ≤
      DZ + D / (k - 1) := by
  simp only [Matrix.mulVec, dotProduct]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun p _ => ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  have h1 := gsMatrixZ_natDegree_le_col ωs f₀ f₁ D ist p
  have h2 := snd_le_div_of_mem_weigthBoundIndices hk p.2
  have h3 := zVec_natDegree_le k D DZ x p
  omega

/-- **The graded Z-degree GS interpolant (#302): budget linear in `n`.**

For the generic fold `f₀ + Z·f₁` with `1 < k`, `n ≠ 0`, `1 ≤ m`, there is a *nonzero integer*
interpolant `Q₀ ∈ F[Z][X][Y]` whose image over `K = F(Z)` satisfies the Guruswami–Sudan
`Conditions` at the `gs_degree_bound`, and whose every `F[Z]`-coefficient has
`natDegree ≤ n·|constraintIndices m|·(gs_degree_bound k n m / (k-1))`. Since
`gs_degree_bound k n m / (k-1)` is `O(m/√ρ)` — independent of `n` at fixed rate — this budget
is **linear in `n`**, one factor of `n` sharper than the Cramer-route budget of
`gs_existence_over_ratfunc_zDegree`. -/
theorem gs_existence_zDegree_graded {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (genericFold f₀ f₁)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      ∀ b a : ℕ, ((Q₀.coeff b).coeff a).natDegree ≤
        n * (constraintIndices m).card * (gs_degree_bound k n m / (k - 1)) := by
  classical
  set D := gs_degree_bound k n m with hD
  set DY := D / (k - 1) with hDY
  set DZ := n * (constraintIndices m).card * DY with hDZ
  set DW := DZ + DY with hDW
  -- 1. the graded dimension count
  have hcount : numConstraints n m < numVars k D :=
    gs_numVars_gt_numConstraints_of_gt_one hn hk hm
  have hcard : n * (constraintIndices m).card * (DW + 1) <
      (weigthBoundIndices k D).card * (DZ + 1) := by
    rw [hDW, hDZ]
    exact graded_count (by simpa [numVars, numConstraints] using hcount)
  -- 2. a nonzero kernel vector of the graded F-linear system
  obtain ⟨x, hx0, hxker⟩ := exists_nonzero_graded_kernel ωs f₀ f₁ D DZ DW hcard
  set c' : weigthBoundIndices k D → F[X] := zVec k D DZ x with hc'
  -- 3. it assembles to a nonzero polynomial kernel vector of the F[Z]-matrix
  have hc'0 : c' ≠ 0 := by
    intro habs
    apply hx0
    funext pc
    have h1 : (c' pc.1).coeff (pc.2 : ℕ) = x (pc.1, pc.2) := by
      rw [hc']; exact zVec_coeff_fin x pc.1 pc.2
    rw [habs] at h1
    simpa using h1.symm
  have hdegW : ∀ ist : Fin n × constraintIndices m,
      ((gsMatrixZ k n m ωs f₀ f₁ D).mulVec c' ist).natDegree ≤ DW := by
    intro ist
    rw [hc', hDW, hDY]
    exact mulVec_zVec_natDegree_le hk ωs f₀ f₁ D DZ x ist
  have hc'ker : (gsMatrixZ k n m ωs f₀ f₁ D).mulVec c' = 0 := by
    funext ist
    rw [Pi.zero_apply]
    refine Polynomial.ext fun j => ?_
    rw [Polynomial.coeff_zero]
    by_cases hj : j < DW + 1
    · have h0 := congr_fun hxker (ist, (⟨j, hj⟩ : Fin (DW + 1)))
      simp only [gradedMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
      rw [hc']
      exact h0
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hdegW ist) (by omega))
  -- 4. the integer interpolant and its coefficient extraction
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
            ((Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p))).coeff b)).coeff a
        = ∑ p : weigthBoundIndices k D,
            ((Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p))).coeff b).coeff a := by
          rw [Polynomial.finset_sum_coeff]
      _ = ∑ p : weigthBoundIndices k D, if p.1 = (a, b) then c' p else 0 := by
          exact Finset.sum_congr rfl fun p _ => hterm p
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
  have hmap : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K)) = coeffsToPoly k D c'' := by
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
    have := congr_fun habs p
    simpa [hc''] using (IsFractionRing.injective F[X] K)
      (by simpa [hc''] using congr_fun habs p)
  have hck'' : constraintMap k n m (liftedDomain ωs) (genericFold f₀ f₁) D c'' = 0 := by
    funext i st
    have hrep := constraintMap_eq_mulVec (k := k) (m := m) ωs f₀ f₁ D c'' (i, st)
    rw [show constraintMap k n m (liftedDomain ωs) (genericFold f₀ f₁) D c'' i st =
        constraintMap k n m (liftedDomain ωs) (genericFold f₀ f₁) D c''
          ((i, st) : Fin n × constraintIndices m).1 ((i, st) : Fin n × constraintIndices m).2
      from rfl, hrep]
    show (((gsMatrixZ k n m ωs f₀ f₁ D).map (algebraMap F[X] K)).mulVec c'') (i, st) = 0
    have : ((gsMatrixZ k n m ωs f₀ f₁ D).map (algebraMap F[X] K)).mulVec c'' (i, st) =
        algebraMap F[X] K ((gsMatrixZ k n m ωs f₀ f₁ D).mulVec c' (i, st)) := by
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
  · -- Conditions: the four legs at K, mirroring `gs_existence` with kernel vector c''
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
  · -- the graded Z-degree budget
    intro b a
    rw [hcoeff a b]
    by_cases h : (a, b) ∈ weigthBoundIndices k D
    · rw [dif_pos h, hc']
      exact zVec_natDegree_le k D DZ x ⟨(a, b), h⟩
    · rw [dif_neg h]
      simp

/-- **The graded `hbadz` producer (#302).** The graded integer GS interpolant has a degenerate
set of cardinality at most `n·|constraintIndices m|·(gs_degree_bound k n m/(k-1))` — the
linear-in-`n` refinement of `gs_existence_over_ratfunc_zDegree_card`, via
`card_specialization_collapse_le`. -/
theorem gs_existence_zDegree_graded_card [Fintype F] {n : ℕ} (k m : ℕ)
    (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (genericFold f₀ f₁)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      (Finset.univ.filter (fun z : F =>
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0)).card ≤
        n * (constraintIndices m).card * (gs_degree_bound k n m / (k - 1)) := by
  obtain ⟨Q₀, h0, hcond, hdeg⟩ := gs_existence_zDegree_graded k m ωs f₀ f₁ hk hn hm
  exact ⟨Q₀, h0, hcond, card_specialization_collapse_le h0 hdeg⟩

end GuruswamiSudan.OverRatFunc.ZDegree.Graded

-- Axiom audit anchors: every result is axiom-clean `[propext, Classical.choice, Quot.sound]`.
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.Graded.graded_count
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.Graded.snd_le_div_of_mem_weigthBoundIndices
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.Graded.gsMatrixZ_natDegree_le_col
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.Graded.zVec_coeff
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.Graded.zVec_natDegree_le
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.Graded.exists_nonzero_graded_kernel
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.Graded.mulVec_zVec_natDegree_le
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.Graded.gs_existence_zDegree_graded
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.Graded.gs_existence_zDegree_graded_card
