/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude

Ported from mitschabaude-bot/ArkLib:reduced-rate (commit 93fd4833b88fb0b964a29d9ca8cbbcd7ca781ba4).
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.GoodCoeffs
import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots

/-!
# Correlated agreement for Reed–Solomon curves in the unique-decoding range

[BCHKS25, Theorem 1.3] for curves, with proximity loss. Let `C` be the Reed–Solomon code of
degree `< k` on `n` points, `ρ = k / n`, and `u₀, …, u_M` words with curve points
`u_z = ∑ⱼ zʲ uⱼ` (`Curve.polynomialCurveEval`). If `0 < δ_fld ≤ (1 - ρ) / 2 - 1 / n`,
`δ_fld < δ_int`, and the `uⱼ` are not jointly `δ_int`-close to `C`, then the number `a` of `z`
with `u_z` `δ_fld`-close to `C` is (`card_goodCoeffs_le`)

  `a ≤ M · max(T₁, T₂)`,  `T₁ = (1 - ρ - δ_fld) / (δ_fld (1 - ρ - 2 δ_fld))`,
  `T₂ = δ_int / (δ_int - δ_fld)`,

so a uniform `z` is bad with probability at most `M · max(T₁, T₂) / q`. The case `M = 1`, lines,
is `rs_epsCa_le_in_unique_decoding_range`.

## Derivation

Let `e = ⌊δ_fld n⌋`, `u(x, Z) = ∑ⱼ uⱼ(x) Zʲ`, and `G` the set of good `z`, `a = |G|`. Suppose
`a > M T₁` and `a > M T₂`; we show the `uⱼ` are jointly `δ_int`-close.

1. *Interpolation* (`exists_interpolant`). Take `a_x = n - k - e`, `b_x = n - e - 1`,
   `g = n - k - 2e + 1 > 0` and `d_A = ⌊M e / g⌋`, and solve for `A` of degrees
   `(a_x, d_A)` and `B` of degrees `(b_x, d_A + M)` in `(X, Z)` with
   `B(xᵢ, Z) = u(xᵢ, Z) A(xᵢ, Z)` for all `i`. These are `n (d_A + M + 1)` equations in
   `(d_A + 1)(a_x + 1) + (d_A + M + 1)(b_x + 1)` unknowns; as `a_x + b_x + 2 = n + g` and
   `b_x + 1 = n - e`, the surplus is `(d_A + 1) g - M e > 0`. `A ≠ 0`, as otherwise every
   `Z`-coefficient of `B`, of `X`-degree `< n`, vanishes on the domain.
2. *Rows* (`row_identity`). For `z ∈ G` with `P_z` of degree `< k` within `e` of `u_z`,
   `B(X, z) - P_z(X) A(X, z)` has degree `≤ b_x < n - e` and vanishes where `u_z = P_z`.
3. *Polishchuk–Spielman* (`exists_codewords_of_ratio`). With `a_y = d_A`, `b_y = d_A + M`, the
   condition `b_x / n + (d_A + M) / a < 1` holds: `b_x / n < 1 - δ_fld`, and since `g ≥
   n (1 - ρ - 2δ_fld)` and `e ≤ δ_fld n`, `d_A + M ≤ M (1 - ρ - δ_fld) / (1 - ρ - 2δ_fld)`,
   i.e. `(d_A + M) / δ_fld ≤ M T₁ < a` (`params_spec`). So `B = P A` with `deg_X P ≤ k - 1`,
   `deg_Z P ≤ M`, and `P(xᵢ, Z) = u(xᵢ, Z)` on at least `n - a_x` points. The coefficients
   `pⱼ` of `Zʲ` in `P` are codewords differing from `u` on a set `D`, `|D| ≤ a_x`
   (`exists_codewords_of_quotient`).
4. *Co-curvilinearity* (`polynomialCurveEval_close`). For `z ∈ G`, `P_z` and `p_z = ∑ⱼ zʲ pⱼ`
   are codewords at distance `≤ e + a_x = n - k`, below the minimum distance, so `P_z = p_z` and
   `u_z` is within `e` of `p_z`.
5. *Collinearity for curves* (`double_count`). For `i ∈ D`, `∑ⱼ zʲ (uⱼ(i) - pⱼ(i))` is a
   nonzero polynomial of degree `≤ M`, so at most `M` good `z` agree at `i`; counting
   disagreements, `(a - M) |D| ≤ a e ≤ a δ_fld n`. As `a > M T₂` means
   `a δ_fld < (a - M) δ_int`, `|D| < δ_int n`, and `p` witnesses joint `δ_int`-closeness.

For `k = 0` the code is `{0}`; step 5 applies directly with `p = 0`.

Steps 1–5 are `exists_jointCodewords`: the codewords `p`, co-curvilinearity, and
`|D| ≤ δ_int n`, without the joint-closeness hypothesis.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S., *On Proximity Gaps for
  Reed–Solomon Codes*][BCHKS25]
-/


-- Elaborate ArkLib's `Matrix`-based proximity API as ArkLib does under Lean 4.33+.
set_option backward.isDefEq.respectTransparency false

namespace CodingTheory.UniqueDecoding

open NNReal Finset Function Code ProximityGap CoreDefinitions Curve
open scoped BigOperators LinearCode ProbabilityTheory

section Words

variable {ι : Type} {F : Type} [Field F]

/-- Coordinates of a point of a polynomial curve. -/
theorem polynomialCurveEval_apply {M : ℕ} (u : Fin (M + 1) → ι → F) (z : F) (i : ι) :
    polynomialCurveEval u z i = ∑ j : Fin (M + 1), z ^ (j : ℕ) * u j i := by
  simp only [polynomialCurveEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

variable [DecidableEq F]

/-- The column polynomial `∑ⱼ uⱼ(i) Zʲ` of the coordinate `i`. -/
noncomputable def colPoly {M : ℕ} (u : Fin (M + 1) → ι → F) (i : ι) : Polynomial F :=
  Polynomial.ofFn (M + 1) (fun j => u j i)

/-- A column polynomial has degree at most `M`. -/
theorem colPoly_natDegree_le {M : ℕ} (u : Fin (M + 1) → ι → F) (i : ι) :
    (colPoly u i).natDegree ≤ M :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos M) _)

/-- The `Zʲ` coefficient of the column polynomial of `i` is `uⱼ(i)`. -/
theorem colPoly_coeff {M : ℕ} (u : Fin (M + 1) → ι → F) (i : ι) (j : Fin (M + 1)) :
    (colPoly u i).coeff j = u j i :=
  Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt

/-- The column polynomial of `i` at `z` is the `i`-th coordinate of the curve point. -/
theorem colPoly_eval {M : ℕ} (u : Fin (M + 1) → ι → F) (i : ι) (z : F) :
    (colPoly u i).eval z = polynomialCurveEval u z i := by
  rw [polynomialCurveEval_apply, colPoly, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_monomial, mul_comm]

end Words

/-! ## The interpolant -/

section Interpolation

open Polynomial Polynomial.Bivariate

variable {F : Type} [Field F] [DecidableEq F]

/-- The bivariate polynomial `∑ₛ Zˢ ∑ₜ a s t Xᵗ` with coefficient matrix `a`. -/
noncomputable def polyOf (dy dx : ℕ) (a : Matrix (Fin dy) (Fin dx) F) :
    Polynomial (Polynomial F) :=
  ofFn dy (fun s => ofFn dx (a s))

/-- `polyOf` is additive. -/
theorem polyOf_add (dy dx : ℕ) (a b : Matrix (Fin dy) (Fin dx) F) :
    polyOf dy dx (a + b) = polyOf dy dx a + polyOf dy dx b := by
  unfold polyOf
  rw [← map_add]
  congr 1
  funext s
  exact map_add (ofFn dx) (a s) (b s)

/-- `polyOf` commutes with scalars. -/
theorem polyOf_smul (dy dx : ℕ) (c : F) (a : Matrix (Fin dy) (Fin dx) F) :
    polyOf dy dx (c • a) = C (C c) * polyOf dy dx a := by
  unfold polyOf
  rw [← smul_eq_C_mul, ← map_smul]
  congr 1
  funext s
  change ofFn dx (c • a s) = C c * ofFn dx (a s)
  rw [map_smul, smul_eq_C_mul]

/-- The `Zˢ` coefficient of `polyOf`. -/
theorem polyOf_coeff (dy dx : ℕ) (a : Matrix (Fin dy) (Fin dx) F) (s : ℕ) :
    (polyOf dy dx a).coeff s = if hs : s < dy then ofFn dx (a ⟨s, hs⟩) else 0 := by
  unfold polyOf
  split_ifs with hs
  · exact ofFn_coeff_eq_val_of_lt _ hs
  · exact ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hs)

/-- `polyOf` is injective. -/
theorem polyOf_injective (dy dx : ℕ) : Function.Injective (polyOf (F := F) dy dx) := by
  intro a b hab
  funext s
  apply injective_ofFn dx
  have hs := congrArg (fun p : Polynomial (Polynomial F) => p.coeff (s : ℕ)) hab
  simpa only [polyOf_coeff, s.isLt, ↓reduceDIte] using hs

/-- `X`-degree bound of `polyOf`. -/
theorem polyOf_degreeX_le (dy dx : ℕ) (a : Matrix (Fin dy) (Fin (dx + 1)) F) :
    degreeX (polyOf dy (dx + 1) a) ≤ dx := by
  unfold degreeX
  refine Finset.sup_le_iff.2 fun s _ => ?_
  rw [polyOf_coeff]
  split_ifs with hs
  · exact Nat.le_of_lt_succ (ofFn_natDegree_lt (Nat.succ_pos dx) _)
  · exact (natDegree_zero (R := F)).trans_le (Nat.zero_le _)

/-- `Z`-degree bound of `polyOf`. -/
theorem polyOf_natDegreeY_le (dy dx : ℕ) (a : Matrix (Fin (dy + 1)) (Fin dx) F) :
    natDegreeY (polyOf (dy + 1) dx a) ≤ dy :=
  Nat.le_of_lt_succ (ofFn_natDegree_lt (Nat.succ_pos dy) _)

/-- `polyOf` at `X = x` has degree below its number of rows. -/
theorem evalX_polyOf_natDegree_le (dy dx : ℕ) (a : Matrix (Fin (dy + 1)) (Fin dx) F) (x : F) :
    (evalX x (polyOf (dy + 1) dx a)).natDegree ≤ dy := by
  rw [evalX_eq_map]
  exact natDegree_map_le.trans (polyOf_natDegreeY_le dy dx a)

/-- Coefficients of `polyOf` at `X = x`. -/
theorem evalX_polyOf_coeff (dy dx : ℕ) (a : Matrix (Fin dy) (Fin dx) F) (x : F) (s : ℕ) :
    (evalX x (polyOf dy dx a)).coeff s =
      if hs : s < dy then (ofFn dx (a ⟨s, hs⟩)).eval x else 0 := by
  rw [evalX_eq_map, coeff_map, polyOf_coeff]
  split_ifs <;> simp only [coe_evalRingHom, eval_zero]

variable {ι : Type}

/-- The interpolation constraints `B(xᵢ, Z) = u(xᵢ, Z) A(xᵢ, Z)`, coefficientwise in `Z`. -/
noncomputable def constraintMap (domain : ι → F) {M : ℕ} (u : Fin (M + 1) → ι → F)
    (ax bx dA : ℕ) :
    (Matrix (Fin (dA + 1)) (Fin (ax + 1)) F ×
        Matrix (Fin (dA + M + 1)) (Fin (bx + 1)) F) →ₗ[F]
      Matrix ι (Fin (dA + M + 1)) F where
  toFun ab i s :=
    (evalX (domain i) (polyOf _ _ ab.2) -
      colPoly u i * evalX (domain i) (polyOf _ _ ab.1)).coeff s
  map_add' x y := by
    ext i s
    simp only [Prod.fst_add, Prod.snd_add, polyOf_add, evalX_eq_map, Polynomial.map_add,
      mul_add, Matrix.add_apply, coeff_add, coeff_sub]
    ring
  map_smul' c x := by
    ext i s
    simp only [Prod.smul_fst, Prod.smul_snd, polyOf_smul, evalX_eq_map, Polynomial.map_mul,
      Polynomial.map_C, coe_evalRingHom, eval_C, Matrix.smul_apply, RingHom.id_apply,
      smul_eq_mul]
    rw [show ∀ p q : Polynomial F, C c * p - colPoly u i * (C c * q) =
      C c * (p - colPoly u i * q) from fun p q => by ring, coeff_C_mul]

/-- A kernel element gives the column identities `B(xᵢ, Z) = u(xᵢ, Z) A(xᵢ, Z)`. -/
theorem identity_of_mem_ker (domain : ι → F) {M : ℕ} (u : Fin (M + 1) → ι → F)
    (ax bx dA : ℕ) (ab : Matrix (Fin (dA + 1)) (Fin (ax + 1)) F ×
        Matrix (Fin (dA + M + 1)) (Fin (bx + 1)) F)
    (hab : ab ∈ LinearMap.ker (constraintMap domain u ax bx dA)) (i : ι) :
    evalX (domain i) (polyOf _ _ ab.2) = colPoly u i * evalX (domain i) (polyOf _ _ ab.1) := by
  apply Polynomial.ext
  intro s
  by_cases hs : s < dA + M + 1
  · have h := congrFun (congrFun (LinearMap.mem_ker.mp hab) i) ⟨s, hs⟩
    change (evalX (domain i) (polyOf _ _ ab.2) -
      colPoly u i * evalX (domain i) (polyOf _ _ ab.1)).coeff s = 0 at h
    rw [coeff_sub] at h
    exact sub_eq_zero.mp h
  · have hB := evalX_polyOf_natDegree_le (dA + M) (bx + 1) ab.2 (domain i)
    have hA := evalX_polyOf_natDegree_le dA (ax + 1) ab.1 (domain i)
    have hprod : (colPoly u i * evalX (domain i) (polyOf _ _ ab.1)).natDegree ≤ dA + M :=
      natDegree_mul_le.trans (by have := colPoly_natDegree_le u i; omega)
    rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

variable [Fintype ι]

/-- A nonzero kernel element has `A ≠ 0`, as `B` of `X`-degree `< n` cannot vanish on `n` points. -/
theorem polyOf_fst_ne_zero (domain : ι ↪ F) {M : ℕ} (u : Fin (M + 1) → ι → F)
    (ax bx dA : ℕ) (ab : Matrix (Fin (dA + 1)) (Fin (ax + 1)) F ×
        Matrix (Fin (dA + M + 1)) (Fin (bx + 1)) F)
    (hab0 : ab ≠ 0) (hab : ab ∈ LinearMap.ker (constraintMap domain u ax bx dA))
    (hbx : bx < Fintype.card ι) :
    polyOf _ _ ab.1 ≠ 0 := by
  intro hA
  have hrow : ∀ s, ofFn (bx + 1) (ab.2 s) = 0 := by
    intro s
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ domain.injective (fun i => ?_)
      ((ofFn_natDegree_lt (by omega) _).trans_le (by omega))
    have h := congrArg (fun q : Polynomial F => q.coeff s)
      (identity_of_mem_ker domain u ax bx dA ab hab i)
    simp only [hA, evalX_eq_map, Polynomial.map_zero, mul_zero, coeff_zero] at h
    rw [← evalX_eq_map, evalX_polyOf_coeff] at h
    simpa only [s.isLt, ↓reduceDIte] using h
  apply hab0
  refine Prod.ext (polyOf_injective _ _ (hA.trans ?_)) (funext fun s => ?_)
  · unfold polyOf
    exact (map_zero _).symm.trans (congrArg _ (funext fun s => (map_zero _).symm))
  · exact injective_ofFn _ ((hrow s).trans (map_zero _).symm)

/-- **Interpolation.** With more unknowns than constraints there is a nonzero `A` and a `B`
with `B(xᵢ, Z) = u(xᵢ, Z) A(xᵢ, Z)` for all `i`, `deg_X A ≤ a_x`, `deg_Z A ≤ d_A`,
`deg_X B ≤ b_x`, `deg_Z B ≤ d_A + M`. -/
theorem exists_interpolant (domain : ι ↪ F) {M : ℕ} (u : Fin (M + 1) → ι → F)
    (ax bx dA : ℕ) (hbx : bx < Fintype.card ι)
    (hdim : Fintype.card ι * (dA + M + 1) < (dA + 1) * (ax + 1) + (dA + M + 1) * (bx + 1)) :
    ∃ A B : Polynomial (Polynomial F), A ≠ 0 ∧ degreeX A ≤ ax ∧ natDegreeY A ≤ dA ∧
      degreeX B ≤ bx ∧ natDegreeY B ≤ dA + M ∧
      ∀ i, evalX (domain i) B = colPoly u i * evalX (domain i) A := by
  have hfin : Module.finrank F (Matrix ι (Fin (dA + M + 1)) F) <
      Module.finrank F (Matrix (Fin (dA + 1)) (Fin (ax + 1)) F ×
        Matrix (Fin (dA + M + 1)) (Fin (bx + 1)) F) := by
    simp only [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self,
      Fintype.card_fin, mul_one]
    exact hdim
  obtain ⟨ab, hab, hab0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt hfin)
  exact ⟨_, _, polyOf_fst_ne_zero domain u ax bx dA ab hab0 hab hbx,
    polyOf_degreeX_le _ _ _, polyOf_natDegreeY_le _ _ _, polyOf_degreeX_le _ _ _,
    polyOf_natDegreeY_le _ _ _, identity_of_mem_ker (⇑domain) u ax bx dA ab hab⟩

end Interpolation

/-! ## Decoding the interpolant -/

section Decoding

open Polynomial Polynomial.Bivariate

variable {ι : Type} [Fintype ι] {F : Type}

/-- The coordinates at which the words `u` and `p` differ in some row. -/
noncomputable def disagree [DecidableEq F] {M : ℕ} (u p : Fin (M + 1) → ι → F) : Finset ι :=
  Finset.univ.filter fun i => ∃ j, u j i ≠ p j i

/-- Codewords `p` within `⌊δ n⌋` disagreements make `u` jointly `δ`-close. -/
theorem jointProximity_of_disagree_card_le [DecidableEq F] [Nonempty ι] (C : Set (ι → F)) {M : ℕ}
    (u p : Fin (M + 1) → ι → F) (δ : ℝ≥0) (hp : ∀ j, p j ∈ C)
    (hD : (disagree u p).card ≤ Nat.floor (δ * Fintype.card ι)) :
    Code.jointProximity (C := C) (u := u) δ := by
  classical
  rw [← Code.jointAgreement_iff_jointProximity]
  refine ⟨(disagree u p)ᶜ, (Code.relDist_floor_bound_iff_complement_bound _ _ _).mp ?_, p,
    fun j => ⟨hp j, fun i hi => ?_⟩⟩
  · rw [Finset.card_compl]
    exact Nat.sub_le_sub_left hD _
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra h
    exact Finset.mem_compl.mp hi
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, Ne.symm h⟩)

variable [Field F]

/-- Evaluating in `X` then `Z` is evaluating in `Z` then `X`. -/
theorem evalX_eval_eq_evalY_eval (x z : F) (f : Polynomial (Polynomial F)) :
    (evalX x f).eval z = (evalY z f).eval x := by
  have h := eval₂_at_apply (p := f) (evalRingHom x) (C z)
  rw [coe_evalRingHom, eval_C] at h
  rw [evalX_eq_map, eval_map, h]
  rfl

/-- Fixing `Z` keeps the `X`-degree. -/
theorem evalY_natDegree_le (z : F) (f : Polynomial (Polynomial F)) :
    (evalY z f).natDegree ≤ degreeX f := by
  rw [evalY, eval_eq_sum, sum_def]
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  rw [← C_pow]
  exact le_trans (natDegree_mul_C_le _ _) (coeff_natDegree_le_degreeX f j)

variable [DecidableEq F]

/-- **Rows.** At a good parameter `z`, with `Pz` the codeword close to the curve point,
`B(X, z) = Pz(X) A(X, z)`. -/
theorem row_identity (domain : ι ↪ F) {M : ℕ} (u : Fin (M + 1) → ι → F)
    (A B : Polynomial (Polynomial F)) {k e ax bx : ℕ} (hax : ax + (k - 1) = bx)
    (hbx : bx < Fintype.card ι - e) (hAX : degreeX A ≤ ax) (hBX : degreeX B ≤ bx)
    (hAB : ∀ i, evalX (domain i) B = colPoly u i * evalX (domain i) A)
    (z : F) (P : Polynomial F) (hP : P.natDegree < k)
    (hclose : Δ₀(polynomialCurveEval u z, P.eval ∘ domain) ≤ e) :
    evalY z B = P * evalY z A := by
  obtain ⟨T, hTcard, hT⟩ := (Code.closeToWord_iff_exists_agreementCols _ _ e).1 hclose
  refine sub_eq_zero.1 (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (s := T.image domain)
    (fun x hx => ?_) ?_)
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi : polynomialCurveEval u z i = P.eval (domain i) := (hT i).1 hi
    rw [eval_sub, eval_mul, ← evalX_eval_eq_evalY_eval, ← evalX_eval_eq_evalY_eval, hAB i,
      eval_mul, colPoly_eval, hi, sub_self]
  · rw [Finset.card_image_of_injective _ domain.injective]
    have hprod : (P * evalY z A).natDegree ≤ bx :=
      natDegree_mul_le.trans (by have := evalY_natDegree_le z A; omega)
    have := evalY_natDegree_le z B
    exact (natDegree_sub_le _ _).trans_lt (by omega)

/-- Curve points of `u` and `p` differ only on `disagree u p`. -/
theorem hammingDist_polynomialCurveEval_le {M : ℕ} (u p : Fin (M + 1) → ι → F) (z : F) :
    Δ₀(polynomialCurveEval u z, polynomialCurveEval p z) ≤ (disagree u p).card := by
  rw [Code.hammingDist_eq_disagreementCols_card]
  refine Finset.card_le_card fun i hi => ?_
  rw [Code.mem_disagreementCols] at hi
  simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra h
  push Not at h
  exact hi (by simp only [polynomialCurveEval_apply, h])

/-- **Seed.** The `Z`-coefficients of a quotient `P` that matches the column polynomials on
`n - a_x` points are codewords that differ from `u` on at most `a_x` coordinates. -/
theorem exists_codewords_of_quotient {k : ℕ} [NeZero k] (domain : ι ↪ F) {M : ℕ}
    (u : Fin (M + 1) → ι → F) (P : Polynomial (Polynomial F)) (Qx : Finset F) {ax : ℕ}
    (hPX : degreeX P ≤ k - 1) (hQcard : Fintype.card ι - ax ≤ Qx.card)
    (hQsub : Qx ⊆ Finset.univ.map domain)
    (hQ : ∀ i, domain i ∈ Qx → evalX (domain i) P = colPoly u i) :
    ∃ p : Fin (M + 1) → ι → F, (∀ j, p j ∈ ReedSolomon.code domain k) ∧
      (disagree u p).card ≤ ax := by
  classical
  let S : Finset ι := Finset.univ.filter fun i => domain i ∈ Qx
  have hS : Qx.card ≤ S.card := by
    calc Qx.card ≤ (S.map domain).card := Finset.card_le_card fun x hx => by
          obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp (hQsub hx)
          exact Finset.mem_map_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
      _ = S.card := Finset.card_map _
  refine ⟨fun j => (P.coeff j).eval ∘ domain, fun j => ?_, ?_⟩
  · exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval _
      ((coeff_natDegree_le_degreeX P j).trans hPX |>.trans_lt
        (Nat.pred_lt (NeZero.ne k))) (fun _ => rfl)
  · have hsub : disagree u (fun j => (P.coeff j).eval ∘ domain) ⊆ Sᶜ := by
      intro i hi
      simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨j, hj⟩ := hi
      simp only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hiQ
      apply hj
      have h := congrArg (fun q : Polynomial F => q.coeff j) (hQ i hiQ)
      simp only [evalX_eq_map, coeff_map, coe_evalRingHom, colPoly_coeff] at h
      exact h.symm
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_compl]
    omega

/-- **Curves through the good points.** If the words `p` are codewords within `a_x` of `u`,
and `e + a_x` is below the minimum distance, every good curve point decodes to the curve
point of `p`, so is within `e` of it. -/
theorem polynomialCurveEval_close {k : ℕ} [NeZero k] (domain : ι ↪ F) {M : ℕ}
    (u p : Fin (M + 1) → ι → F) (hp : ∀ j, p j ∈ ReedSolomon.code domain k) {e ax : ℕ}
    (hk : k ≤ Fintype.card ι) (hmin : e + ax ≤ Fintype.card ι - k)
    (hD : (disagree u p).card ≤ ax) (z : F) (P : Polynomial F) (hP : P.natDegree < k)
    (hclose : Δ₀(polynomialCurveEval u z, P.eval ∘ domain) ≤ e) :
    Δ₀(polynomialCurveEval u z, polynomialCurveEval p z) ≤ e := by
  have hPmem : P.eval ∘ domain ∈ ReedSolomon.code domain k :=
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval P hP (fun _ => rfl)
  have hcmem : polynomialCurveEval p z ∈ ReedSolomon.code domain k :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hp j)
  have heq : P.eval ∘ domain = polynomialCurveEval p z := by
    by_contra hne
    have hmd := Code.minDist_le_dist hPmem hcmem hne
    rw [ReedSolomon.minDist_of_le hk] at hmd
    have htri := hammingDist_triangle (P.eval ∘ domain) (polynomialCurveEval u z)
      (polynomialCurveEval p z)
    have := hammingDist_comm (P.eval ∘ domain) (polynomialCurveEval u z)
    have := hammingDist_polynomialCurveEval_le u p z
    omega
  rwa [← heq]

/-- At a disagreement coordinate at most `M` parameters make the curve points agree. -/
theorem card_filter_agree_le {M : ℕ} (u p : Fin (M + 1) → ι → F) {i : ι}
    (hi : i ∈ disagree u p) (good : Finset F) :
    (good.filter fun z => polynomialCurveEval u z i = polynomialCurveEval p z i).card ≤ M := by
  obtain ⟨j, hj⟩ : ∃ j, u j i ≠ p j i := by
    simpa only [disagree, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  have hq : colPoly u i - colPoly p i ≠ 0 := by
    intro h
    apply hj
    have h' := congrArg (fun r : Polynomial F => r.coeff j) h
    simp only [coeff_sub, colPoly_coeff, coeff_zero] at h'
    exact sub_eq_zero.mp h'
  have hsub : (good.filter fun z => polynomialCurveEval u z i = polynomialCurveEval p z i) ⊆
      (colPoly u i - colPoly p i).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots hq, IsRoot, eval_sub, colPoly_eval, colPoly_eval,
      (Finset.mem_filter.mp hz).2, sub_self]
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Multiset.toFinset_card_le _
    _ ≤ _ := card_roots' _
    _ ≤ M := (natDegree_sub_le _ _).trans
      (max_le (colPoly_natDegree_le _ _) (colPoly_natDegree_le _ _))

/-- **Collinearity for curves.** Each disagreement coordinate is fixed by at most `M` curve
parameters, and each good parameter leaves at most `e` disagreements, so
`(a - M) |D| ≤ a e`. -/
theorem double_count (good : Finset F) {M : ℕ} (u p : Fin (M + 1) → ι → F) (e : ℕ)
    (hclose : ∀ z ∈ good, Δ₀(polynomialCurveEval u z, polynomialCurveEval p z) ≤ e) :
    (good.card - M) * (disagree u p).card ≤ good.card * e := by
  classical
  let count : ι → ℕ := fun i =>
    (good.filter fun z => polynomialCurveEval u z i ≠ polynomialCurveEval p z i).card
  have hsum : ∑ z ∈ good, Δ₀(polynomialCurveEval u z, polynomialCurveEval p z) = ∑ i, count i := by
    simp only [hammingDist, count, Finset.card_filter]
    exact Finset.sum_comm
  have hlow : ∀ i ∈ disagree u p, good.card - M ≤ count i := fun i hi => by
    have h1 := Finset.card_filter_add_card_filter_not (s := good)
      (fun z => polynomialCurveEval u z i = polynomialCurveEval p z i)
    have h2 := card_filter_agree_le u p hi good
    simp only [count, ne_eq]
    omega
  calc (good.card - M) * (disagree u p).card = ∑ _i ∈ disagree u p, (good.card - M) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ disagree u p, count i := Finset.sum_le_sum hlow
    _ ≤ ∑ i, count i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ z ∈ good, Δ₀(polynomialCurveEval u z, polynomialCurveEval p z) := hsum.symm
    _ ≤ ∑ _z ∈ good, e := Finset.sum_le_sum hclose
    _ = good.card * e := by rw [Finset.sum_const, smul_eq_mul]

/-- A word `δ`-close to the code is within `⌊δ n⌋` of a codeword. -/
theorem exists_close_codeword [Nonempty ι] (domain : ι ↪ F) (k : ℕ) {w : ι → F} {δ : ℝ≥0}
    (hw : δᵣ(w, ReedSolomon.code domain k) ≤ δ) :
    ∃ v ∈ ReedSolomon.code domain k, Δ₀(w, v) ≤ Nat.floor (δ * Fintype.card ι) := by
  have hdist := (Code.relDistFromCode_le_iff_distFromCode_le
    (C := (ReedSolomon.code domain k : Set (ι → F))) w δ).1 hw
  exact (Code.closeToCode_iff_closeToCodeword_of_minDist
    (u := w) (C := (ReedSolomon.code domain k : Set (ι → F))) (e := _)).1 hdist

end Decoding

/-! ## Polishchuk–Spielman and the parameters -/

section Assembly

open Polynomial Polynomial.Bivariate

variable {ι : Type} [Fintype ι] [Nonempty ι] {F : Type} [Field F] [DecidableEq F]

/-- **Steps 1–3.** With an interpolant whose `Z`-degree budget is small against the number `a`
of good parameters (`b_x / n + (d_A + M) / a < 1`), Polishchuk–Spielman divides `B` by `A`;
the `Z`-coefficients of the quotient are codewords `p` and every good curve point is within
`e` of the curve point of `p`. -/
theorem exists_codewords_of_ratio {k : ℕ} [NeZero k] (domain : ι ↪ F) {M : ℕ}
    (u : Fin (M + 1) → ι → F) (good : Finset F) (Pz : F → Polynomial F) {e ax bx dA : ℕ}
    (hPz : ∀ z ∈ good, (Pz z).natDegree < k ∧ Δ₀(polynomialCurveEval u z, (Pz z).eval ∘ domain) ≤ e)
    (hax : ax + (k - 1) = bx) (hk : k ≤ Fintype.card ι) (hmin : e + ax ≤ Fintype.card ι - k)
    (hbx : bx < Fintype.card ι - e)
    (hdim : Fintype.card ι * (dA + M + 1) < (dA + 1) * (ax + 1) + (dA + M + 1) * (bx + 1))
    (hgood : 0 < good.card)
    (hratio : (bx : ℚ) / (Fintype.card ι : ℚ) + ((dA + M : ℕ) : ℚ) / (good.card : ℚ) < 1) :
    ∃ p : Fin (M + 1) → ι → F, (∀ j, p j ∈ ReedSolomon.code domain k) ∧
      ∀ z ∈ good, Δ₀(polynomialCurveEval u z, polynomialCurveEval p z) ≤ e := by
  classical
  obtain ⟨A, B, hA0, hAX, hAY, hBX, hBY, hAB⟩ :=
    exists_interpolant domain u ax bx dA (by omega) hdim
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  let Px : Finset F := Finset.univ.map domain
  have : Nonempty Px := ⟨⟨domain (Classical.arbitrary ι), Finset.mem_map_of_mem _
    (Finset.mem_univ _)⟩⟩
  have : Nonempty good := (Finset.card_pos.mp hgood).to_subtype
  obtain ⟨P, -, hPX, -, ⟨Qx, hQcard, hQsub, hQeval⟩, -⟩ :=
    polishchuk_spielman ax dA bx (dA + M) ⟨Fintype.card ι, hn⟩ ⟨good.card, hgood⟩
      (by omega) (by omega) A B hA0 hAX hBX hAY hBY Px good Pz
      (fun x => colPoly u (Function.invFun domain x))
      (by simp only [Px, Finset.card_map, Finset.card_univ, PNat.mk_coe, le_refl])
      (le_refl _)
      (fun z hz => ⟨by have := (hPz z hz).1; omega,
        row_identity domain u A B hax hbx hAX hBX hAB z (Pz z) (hPz z hz).1 (hPz z hz).2⟩)
      (fun x hx => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
        rw [Function.leftInverse_invFun domain.injective i]
        exact ⟨(colPoly_natDegree_le u i).trans (by omega), hAB i⟩)
      (by simpa only [PNat.mk_coe, gt_iff_lt] using hratio)
  obtain ⟨p, hp, hD⟩ := exists_codewords_of_quotient (k := k) domain u P Qx (ax := ax)
    (hPX.trans (by omega)) (by simpa only [PNat.mk_coe] using hQcard)
    hQsub (fun i hi => by
      rw [hQeval _ hi, Function.leftInverse_invFun domain.injective i])
  exact ⟨p, hp, fun z hz => polynomialCurveEval_close domain u p hp hk hmin hD z (Pz z)
    (hPz z hz).1 (hPz z hz).2⟩

/-- **Parameters.** `e = ⌊δ n⌋`, `a_x = n - k - e`, `b_x = n - e - 1`,
`d_A = ⌊M e / (n - k - 2e + 1)⌋` satisfy the degree, dimension and ratio conditions, and
`(d_A + M) / δ ≤ M T₁`. -/
theorem params_spec {n k M e ax bx dA : ℕ} (δ : ℝ≥0) (hk : 0 < k) (hn : 0 < n)
    (hδ : 0 < (δ : ℝ)) (h_ud : (δ : ℝ) ≤ (1 - (k : ℝ) / n) / 2 - 1 / n)
    (he : e = Nat.floor (δ * n)) (hax : ax = n - k - e) (hbx : bx = n - e - 1)
    (hdA : dA = M * e / (n - k - 2 * e + 1)) :
    ax + (k - 1) = bx ∧ k ≤ n ∧ e + ax ≤ n - k ∧ bx < n - e ∧
      n * (dA + M + 1) < (dA + 1) * (ax + 1) + (dA + M + 1) * (bx + 1) ∧
      (bx : ℝ) / n < 1 - δ ∧
      ((dA + M : ℕ) : ℝ) / δ ≤
        M * ((1 - (k : ℝ) / n - δ) / ((δ : ℝ) * (1 - (k : ℝ) / n - 2 * δ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heNN : (e : ℝ≥0) ≤ δ * n := he ▸ Nat.floor_le (by positivity)
  have heR : (e : ℝ) ≤ δ * n := by exact_mod_cast heNN
  have heNN' : δ * n < (e : ℝ≥0) + 1 := he ▸ Nat.lt_floor_add_one _
  have heR' : (δ : ℝ) * n < e + 1 := by exact_mod_cast heNN'
  have hkn : (k : ℝ) / n * n = k := div_mul_cancel₀ _ hnR.ne'
  have hud : (δ : ℝ) * n ≤ (n - k) / 2 - 1 := by
    have h1 := mul_le_mul_of_nonneg_right h_ud hnR.le
    have h2 : ((1 - (k : ℝ) / n) / 2 - 1 / n) * n = (n - k) / 2 - 1 := by
      field_simp
    linarith
  have hmargin : k + 2 * e + 2 ≤ n := by
    have : (k : ℝ) + 2 * e + 2 ≤ n := by linarith
    exact_mod_cast this
  generalize hg : n - k - 2 * e + 1 = gap at hdA
  have hgap : 0 < gap := by omega
  have hgR : (gap : ℝ) + k + 2 * e = n + 1 := by exact_mod_cast (show gap + k + 2 * e = n + 1
    by omega)
  have hcover : M * e < (dA + 1) * gap := by
    have := Nat.lt_div_mul_add (a := M * e) hgap
    rw [hdA]
    linarith
  subst hax hbx
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · have h1 : (n - k - e + 1) + (n - e - 1 + 1) = n + gap := by omega
    have h2 : n - e - 1 + 1 + e = n := by omega
    nlinarith
  · have hb : ((n - e - 1 : ℕ) : ℝ) + e + 1 = n := by
      exact_mod_cast (show n - e - 1 + e + 1 = n by omega)
    rw [div_lt_iff₀ hnR]
    nlinarith
  · generalize hρ : (k : ℝ) / n = ρ at hkn ⊢
    have hden : 0 < 1 - ρ - 2 * (δ : ℝ) := by
      have : (1 - ρ - 2 * δ) * n = n - k - 2 * (δ * n) := by rw [← hkn]; ring
      nlinarith
    have hdAR : (dA : ℝ) * gap ≤ M * e := by
      have := Nat.div_mul_le_self (M * e) gap
      rw [← hdA] at this
      exact_mod_cast this
    have hngap : n * (1 - ρ - 2 * (δ : ℝ)) ≤ gap := by
      have : n * (1 - ρ - 2 * (δ : ℝ)) = n - k - 2 * (δ * n) := by rw [← hkn]; ring
      linarith
    have hkey : (dA : ℝ) * (1 - ρ - 2 * δ) ≤ M * δ := by
      have h3 : (dA : ℝ) * (n * (1 - ρ - 2 * δ)) ≤ dA * gap :=
        mul_le_mul_of_nonneg_left hngap (Nat.cast_nonneg _)
      have h4 : (M : ℝ) * e ≤ M * (δ * n) := mul_le_mul_of_nonneg_left heR (Nat.cast_nonneg _)
      have : (dA : ℝ) * (1 - ρ - 2 * δ) * n ≤ M * δ * n := by nlinarith
      exact le_of_mul_le_mul_right this hnR
    rw [div_le_iff₀ hδ, show (M : ℝ) * ((1 - ρ - δ) / (δ * (1 - ρ - 2 * δ))) * δ =
      M * (1 - ρ - δ) / (1 - ρ - 2 * δ) by field_simp, le_div_iff₀ hden]
    push_cast
    nlinarith

end Assembly

/-! ## Main results -/

section Main

open Polynomial

variable {ι : Type} [Fintype ι] [Nonempty ι] {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The parameters `z` at which the curve point `∑ⱼ zʲ uⱼ` is `δ`-close to the Reed–Solomon
code. -/
noncomputable def goodCoeffs (domain : ι ↪ F) (k : ℕ) {M : ℕ} (u : Fin (M + 1) → ι → F)
    (δ : ℝ≥0) : Finset F :=
  Finset.univ.filter fun z => δᵣ(polynomialCurveEval u z, ReedSolomon.code domain k) ≤ δ

/-- **Joint codewords.** If more than `M · max(T₁, T₂)` curve points are `δ_fld`-close, there are
codewords `p₀, …, p_M` such that every close curve point is within `⌊δ_fld n⌋` of `∑ⱼ zʲ pⱼ`
(co-curvilinearity), and `p` differs from `u` on at most `δ_int n` coordinates. -/
theorem exists_jointCodewords (domain : ι ↪ F) (k M : ℕ) (u : Fin (M + 1) → ι → F)
    (δ_fld δ_int : ℝ≥0)
    (h_ud : (δ_fld : ℝ) ≤ (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (h_pos : 0 < δ_fld) (h_lt : δ_fld < δ_int)
    (hcon : M * max
        ((1 - (k : ℝ) / Fintype.card ι - δ_fld) /
          ((δ_fld : ℝ) * (1 - (k : ℝ) / Fintype.card ι - 2 * δ_fld)))
        ((δ_int : ℝ) / (δ_int - δ_fld)) < (goodCoeffs domain k u δ_fld).card) :
    ∃ p : Fin (M + 1) → ι → F, (∀ j, p j ∈ ReedSolomon.code domain k) ∧
      (∀ z ∈ goodCoeffs domain k u δ_fld,
        Δ₀(polynomialCurveEval u z, polynomialCurveEval p z) ≤ Nat.floor (δ_fld * Fintype.card ι)) ∧
      ((disagree u p).card : ℝ) ≤ δ_int * Fintype.card ι := by
  classical
  set good := goodCoeffs domain k u δ_fld
  set n := Fintype.card ι
  set a := good.card
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hT1 := (mul_le_mul_of_nonneg_left (le_max_left _ _) hM0).trans_lt hcon
  have hT2 := (mul_le_mul_of_nonneg_left (le_max_right _ _) hM0).trans_lt hcon
  have hδR : (0 : ℝ) < δ_fld := by exact_mod_cast h_pos
  have hltR : (δ_fld : ℝ) < δ_int := by exact_mod_cast h_lt
  have hgap : (a : ℝ) * δ_fld < (a - M) * δ_int := by
    rw [← mul_div_assoc, div_lt_iff₀ (sub_pos.mpr hltR)] at hT2
    linarith
  have haM : M < a := by
    by_contra h
    have : (a : ℝ) ≤ M := by exact_mod_cast not_lt.mp h
    nlinarith
  set e := Nat.floor (δ_fld * n)
  obtain ⟨p, hp, hclose⟩ : ∃ p : Fin (M + 1) → ι → F,
      (∀ j, p j ∈ ReedSolomon.code domain k) ∧
        ∀ z ∈ good, Δ₀(polynomialCurveEval u z, polynomialCurveEval p z) ≤ e := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨0, fun _ => Submodule.zero_mem _, fun z hz => ?_⟩
      obtain ⟨v, hv, hd⟩ := exists_close_codeword domain 0 (Finset.mem_filter.mp hz).2
      rw [ReedSolomon.code_zero, Submodule.mem_bot] at hv
      have h0 : polynomialCurveEval (0 : Fin (M + 1) → ι → F) z = 0 := by
        simp only [polynomialCurveEval, Pi.zero_apply, smul_zero, Finset.sum_const_zero]
      rwa [h0, ← hv]
    · have : NeZero k := ⟨hk.ne'⟩
      have hex : ∀ z, ∃ P : Polynomial F, z ∈ good →
          P.natDegree < k ∧ Δ₀(polynomialCurveEval u z, P.eval ∘ domain) ≤ e := fun z => by
        by_cases hz : z ∈ good
        · obtain ⟨v, ⟨P, hP, rfl⟩, hd⟩ :=
            exists_close_codeword domain k (Finset.mem_filter.mp hz).2
          exact ⟨P, fun _ => ⟨ReedSolomon.natDegree_lt_of_mem_degreeLT hP, hd⟩⟩
        · exact ⟨0, fun h => absurd h hz⟩
      choose Pz hPz using hex
      obtain ⟨hax, hkn, hmin, hbx, hdim, hbxR, hdz⟩ :=
        params_spec (n := n) (k := k) (M := M) (e := e) (ax := n - k - e) (bx := n - e - 1)
          (dA := M * e / (n - k - 2 * e + 1)) δ_fld hk Fintype.card_pos hδR h_ud rfl rfl rfl rfl
      have haR : (0 : ℝ) < a := by exact_mod_cast (Nat.zero_le M).trans_lt haM
      have hdzR : ((M * e / (n - k - 2 * e + 1) + M : ℕ) : ℝ) / a < δ_fld := by
        rw [div_lt_iff₀ haR]
        have := (div_lt_iff₀ hδR).mp (hdz.trans_lt hT1)
        linarith
      have hreal : ((n - e - 1 : ℕ) : ℝ) / n +
          ((M * e / (n - k - 2 * e + 1) + M : ℕ) : ℝ) / a < 1 := by linarith
      exact exists_codewords_of_ratio domain u good Pz (fun z hz => hPz z hz) hax hkn hmin
        hbx hdim ((Nat.zero_le M).trans_lt haM)
        ((Rat.cast_lt (K := ℝ)).mp (by push_cast at hreal ⊢; exact hreal))
  have hdc := double_count good u p e hclose
  refine ⟨p, hp, hclose, ?_⟩
  have hdcR : ((a : ℝ) - M) * (disagree u p).card ≤ a * e := by
    have := (Nat.cast_le (α := ℝ)).mpr hdc
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub haM.le] at this
    exact this
  have heR : (e : ℝ) ≤ δ_fld * n := by
    have : (e : ℝ≥0) ≤ δ_fld * n := Nat.floor_le (by positivity)
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have haM' : (0 : ℝ) < a - M := by
    have : (M : ℝ) < a := by exact_mod_cast haM
    linarith
  have hlt : ((a : ℝ) - M) * (disagree u p).card < (a - M) * (δ_int * n) := by
    have h1 : (a : ℝ) * e ≤ a * (δ_fld * n) := mul_le_mul_of_nonneg_left heR (by positivity)
    have h2 : (a : ℝ) * (δ_fld * n) < (a - M) * δ_int * n := by
      rw [← mul_assoc]
      exact mul_lt_mul_of_pos_right hgap hnR
    linarith
  exact (lt_of_mul_lt_mul_left hlt haM'.le).le

/-- **Curve CA, count.** If `u₀, …, u_M` are not jointly `δ_int`-close to the Reed–Solomon
code, at most `M · max(T₁, T₂)` curve points `∑ⱼ zʲ uⱼ` are `δ_fld`-close to it. -/
theorem card_goodCoeffs_le (domain : ι ↪ F) (k M : ℕ) (u : Fin (M + 1) → ι → F)
    (δ_fld δ_int : ℝ≥0)
    (h_ud : (δ_fld : ℝ) ≤ (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (h_pos : 0 < δ_fld) (h_lt : δ_fld < δ_int)
    (hjoint : ¬ Code.jointProximity
      (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ_int) :
    ((goodCoeffs domain k u δ_fld).card : ℝ) ≤
      M * max
        ((1 - (k : ℝ) / Fintype.card ι - δ_fld) /
          ((δ_fld : ℝ) * (1 - (k : ℝ) / Fintype.card ι - 2 * δ_fld)))
        ((δ_int : ℝ) / (δ_int - δ_fld)) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨p, hp, -, hD⟩ := exists_jointCodewords domain k M u δ_fld δ_int h_ud h_pos h_lt hcon
  exact hjoint (jointProximity_of_disagree_card_le _ u p δ_int hp
    (Nat.le_floor (by exact_mod_cast hD)))

end Main

end CodingTheory.UniqueDecoding

#print axioms CodingTheory.UniqueDecoding.exists_jointCodewords
#print axioms CodingTheory.UniqueDecoding.card_goodCoeffs_le
