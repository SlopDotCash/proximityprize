/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GroundLineInterpolation
import ArkLib.ToMathlib.ClearedGammaDefect
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.S5Genuine
import ArkLib.ToMathlib.ZLinearClosureAudit

/-!
# Claim 5.9 (ground line), assembled: per-coordinate kills + interpolation (#304 / #138)

This file assembles the **faithful ground-line Claim 5.9** of [BCIKS20] §5.2.7 from the two
landed bricks, in the monic regime:

* the per-coordinate Claim 5.10 kill
  (`ClearedGammaDefect.gammaEvalTrunc_eq_ground_of_large` — the eq.-(5.16) defect element,
  the linear Claim-A.2 budget, and Lemma A.1);
* the `k+1`-point ground-line interpolation
  (`GroundLineInterpolation.groundLine_of_eval_groundLine`).

## Main results

* `gammaTruncPoly` — the truncated Hensel value as a polynomial over `𝕃 H`, with
  `coeff`/`natDegree`/`eval` readings.
* `claim59_groundLine` — **the assembly**: per-coordinate ground-line values at `k+1`
  coordinates (the Claim 5.10 outputs) + tail vanishing (Claim 5.8′) give polynomials
  `v₀ v₁ : F[X]` of degree `≤ k` with
  `αGenuine t = fieldTo𝕃 (v₀.coeff t) + Z·fieldTo𝕃 (v₁.coeff t)` for **every** `t`
  (`Z = liftToFunctionField X`, the ground variable).
* `claim59_paperZ_linear` — the output in the faithful paper rendering
  (`ZLinearClosureAudit.gammaGenuine_paperZ_linear`).
* `claim59_curve_collapse` — **the curve collapse, as in the 2025 rewrite**: the counting
  package forces `H.natDegree = 1` (`R = Y − P(X,Z)` is the theorem; a branch of degree
  `≥ 2` cannot carry the full §5 matching package).
* `claim59_T_target` — the in-tree T-form target `gammaGenuine_Z_linear_target` follows
  (with `c₁ = 0`: the ground line sits inside the `{1,T}`-span trivially).
* `claim59_alphaWeightLe` — **the #138 weight-1 invariant `AlphaGenuineRegularWeightLe`, AS A
  THEOREM under the §5 counting hypotheses** (witness: the ground-line section `wSection`).
  No contradiction with the machine refutations: their witnesses do not carry the counting
  package — the invariant is *false* under bare `ClaimA2.Hypotheses` and *true* under §5
  counting, exactly the paper's logical placement of the remark.
* `claim59_of_counting` — the composed front door: budgets + per-coordinate counting data
  (matching sets larger than `N·d_H` at `k+1` coordinates) + tail vanishing ⟹ all of the
  above, with the per-coordinate kills fired internally.

Axiom-clean.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5.2.7 (Claims 5.9–5.11), Appendix A.
* Ben-Sasson, Carmon, Kopparty, Saraf, *On Proximity Gaps for Reed–Solomon Codes* (2025
  rewrite), §"Hensel lift" summary: the step-4 conclusion `R(X,Y,Z) = Y − P(X,Z)`.
-/

noncomputable section

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open ArkLib.ClearedGammaDefect

namespace ArkLib.Claim59GroundLine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## The truncated value as a polynomial over `𝕃 H` -/

/-- The truncated Hensel value `∑_{t≤k} α_t X^t` as a polynomial over `𝕃 H`. -/
def gammaTruncPoly (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ) :
    Polynomial (𝕃 H) :=
  ∑ t ∈ Finset.range (k + 1), Polynomial.C (αGenuine H x₀ R hHyp t) * Polynomial.X ^ t

lemma natDegree_gammaTruncPoly_le (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ) :
    (gammaTruncPoly H x₀ R hHyp k).natDegree ≤ k := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun t ht => ?_)
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (by rw [Polynomial.natDegree_X_pow]; exact Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))

/-- For `t ≤ k` the polynomial reads off the genuine coefficient. -/
lemma coeff_gammaTruncPoly (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    {k t : ℕ} (ht : t ≤ k) :
    (gammaTruncPoly H x₀ R hHyp k).coeff t = αGenuine H x₀ R hHyp t := by
  unfold gammaTruncPoly
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single t
    (fun i _ hit => by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hit h.symm),
        mul_zero])
    (fun hmem => absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le ht)) hmem)]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]

/-- Evaluating the truncated polynomial at the embedded coordinate gives the per-coordinate
truncated value `gammaEvalTrunc` of the defect file. -/
lemma eval_gammaTruncPoly (x₀ x : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (k : ℕ) :
    (gammaTruncPoly H x₀ R hHyp k).eval (fieldTo𝕃 (x - x₀))
      = gammaEvalTrunc H x₀ x R hHyp k := by
  unfold gammaTruncPoly gammaEvalTrunc
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-! ## The assembly -/

/-- **Claim 5.9, ground line (assembled).**  Per-coordinate ground-line values at `k+1`
coordinates (the Claim 5.10 kills) plus tail vanishing (Claim 5.8′) produce `v₀ v₁ : F[X]` of
degree `≤ k` with `αGenuine t = fieldTo𝕃 (v₀.coeff t) + Z · fieldTo𝕃 (v₁.coeff t)` for every
`t` — the coefficients of `γ` are linear in the ground variable `Z = liftToFunctionField X`. -/
theorem claim59_groundLine (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (k : ℕ) (xs : Finset F) (hxs : xs.card = k + 1) (u₀ u₁ : F → F)
    (hcoord : ∀ x ∈ xs,
      gammaEvalTrunc H x₀ x R hHyp k
        = fieldTo𝕃 (u₀ x) + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (u₁ x))
    (htail : ∀ t, k < t → αGenuine H x₀ R hHyp t = 0) :
    ∃ v₀ v₁ : F[X], v₀.natDegree ≤ k ∧ v₁.natDegree ≤ k ∧
      ∀ t, αGenuine H x₀ R hHyp t
        = fieldTo𝕃 (v₀.coeff t)
          + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (v₁.coeff t) := by
  classical
  -- Work with the `fieldTo𝕃`-induced algebra structure (so `algebraMap = fieldTo𝕃` by `rfl`).
  letI : Algebra F (𝕃 H) := (fieldTo𝕃 (H := H)).toAlgebra
  -- The shifted coordinate set: `k+1` distinct base points.
  set s : Finset F := xs.image (fun x => x - x₀) with hs
  have hsub_inj : Function.Injective (fun x : F => x - x₀) := fun a b h => by
    simpa using congrArg (· + x₀) h
  have hscard : s.card = k + 1 := by
    rw [hs, Finset.card_image_of_injective xs hsub_inj, hxs]
  -- Fire the interpolation at the shifted line data.
  obtain ⟨v₀, v₁, hv₀, hv₁, hrep⟩ :=
    ArkLib.GroundLine.groundLine_of_eval_groundLine
      (γ := gammaTruncPoly H x₀ R hHyp k)
      (natDegree_gammaTruncPoly_le H x₀ R hHyp k)
      (liftToFunctionField (H := H) Polynomial.X) s hscard
      (fun y => u₀ (y + x₀)) (fun y => u₁ (y + x₀))
      (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hs ▸ hy)
        show (gammaTruncPoly H x₀ R hHyp k).eval (fieldTo𝕃 (x - x₀)) = _
        rw [eval_gammaTruncPoly, hcoord x hx]
        simp only [sub_add_cancel]
        rfl)
  refine ⟨v₀, v₁, hv₀, hv₁, fun t => ?_⟩
  by_cases htk : t ≤ k
  · -- coefficient reading of the interpolation identity.
    have := congrArg (fun p => p.coeff t) hrep
    simp only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_C_mul] at this
    rw [coeff_gammaTruncPoly H x₀ R hHyp htk] at this
    exact this
  · -- tail: both sides vanish.
    push_neg at htk
    rw [htail t htk, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hv₀ htk),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hv₁ htk)]
    simp only [map_zero, mul_zero, add_zero]

/-! ## Corollaries -/

/-- The output in the faithful paper rendering (`gammaGenuine_paperZ_linear`): every genuine
coefficient is `lift (C a + X·C b)` — on the ground line. -/
theorem claim59_paperZ_linear (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (k : ℕ) (xs : Finset F) (hxs : xs.card = k + 1) (u₀ u₁ : F → F)
    (hcoord : ∀ x ∈ xs,
      gammaEvalTrunc H x₀ x R hHyp k
        = fieldTo𝕃 (u₀ x) + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (u₁ x))
    (htail : ∀ t, k < t → αGenuine H x₀ R hHyp t = 0) :
    BCIKS20.ZLinearClosureAudit.gammaGenuine_paperZ_linear H x₀ R hHyp := by
  obtain ⟨v₀, v₁, _, _, hread⟩ :=
    claim59_groundLine H x₀ R hHyp k xs hxs u₀ u₁ hcoord htail
  refine ⟨fun t => v₀.coeff t, fun t => v₁.coeff t, fun t => ?_⟩
  rw [hread t, map_add, map_mul]
  rfl

/-- **The curve collapse (the 2025-rewrite reading of Claim 5.9):** the §5 counting package
forces `H.natDegree = 1`.  A branch of degree `≥ 2` cannot carry per-coordinate ground-line
values at `k+1` coordinates together with the tail vanishing — `R = Y − P(X,Z)` is the
theorem, not a per-curve invariant. -/
theorem claim59_curve_collapse (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (k : ℕ) (xs : Finset F) (hxs : xs.card = k + 1) (u₀ u₁ : F → F)
    (hcoord : ∀ x ∈ xs,
      gammaEvalTrunc H x₀ x R hHyp k
        = fieldTo𝕃 (u₀ x) + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (u₁ x))
    (htail : ∀ t, k < t → αGenuine H x₀ R hHyp t = 0) :
    H.natDegree = 1 :=
  BCIKS20.ZLinearClosureAudit.natDegree_eq_one_of_gammaGenuine_paperZ_linear H hHyp
    (claim59_paperZ_linear H x₀ R hHyp k xs hxs u₀ u₁ hcoord htail)

/-- **The `hrepT`-mootness export (the contrapositive of the collapse).**  At any branch of
`Y`-degree `≥ 2`, the §5 counting package is **unsatisfiable**: no `k+1`-coordinate family of
ground-line values with tail vanishing exists.  Consequence for the architecture: the open
"`hrepT` ab initio at `d_H = 2`" converter loop (`LocalSeriesCorrected` honest residual) is
not on the end-to-end path — a branch that reaches the §5 counting thresholds has `d_H = 1`,
where the ground representative is satisfiable and the off-centre bundles are non-empty. -/
theorem counting_package_empty_of_two_le_natDegree (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hd2 : 2 ≤ H.natDegree) (k : ℕ) :
    ¬ ∃ (xs : Finset F) (u₀ u₁ : F → F), xs.card = k + 1
      ∧ (∀ x ∈ xs,
          gammaEvalTrunc H x₀ x R hHyp k
            = fieldTo𝕃 (u₀ x) + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (u₁ x))
      ∧ (∀ t, k < t → αGenuine H x₀ R hHyp t = 0) := by
  rintro ⟨xs, u₀, u₁, hxs, hcoord, htail⟩
  have h1 := claim59_curve_collapse H x₀ R hHyp k xs hxs u₀ u₁ hcoord htail
  omega

/-- The in-tree T-form Claim 5.9 target follows (ground line ⊆ `{1,T}`-span, `c₁ = 0`). -/
theorem claim59_T_target (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (k : ℕ) (xs : Finset F) (hxs : xs.card = k + 1) (u₀ u₁ : F → F)
    (hcoord : ∀ x ∈ xs,
      gammaEvalTrunc H x₀ x R hHyp k
        = fieldTo𝕃 (u₀ x) + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (u₁ x))
    (htail : ∀ t, k < t → αGenuine H x₀ R hHyp t = 0) :
    BCIKS20.HenselNumerator.S5Genuine.gammaGenuine_Z_linear_target H x₀ R hHyp := by
  obtain ⟨v₀, v₁, _, _, hread⟩ :=
    claim59_groundLine H x₀ R hHyp k xs hxs u₀ u₁ hcoord htail
  refine BCIKS20.HenselNumerator.S5Genuine.gammaGenuine_Z_linear_of_coeffs_Z_linear H hHyp
    (fun t => ⟨Polynomial.C (v₀.coeff t) + Polynomial.X * Polynomial.C (v₁.coeff t), 0, ?_⟩)
  rw [hread t, map_zero, mul_zero, add_zero, map_add, map_mul]
  rfl

/-- **The #138 weight-1 invariant `AlphaGenuineRegularWeightLe`, AS A THEOREM under the §5
counting hypotheses.**  The witness at order `t` is the ground-line section
`wSection (v₀.coeff t) (v₁.coeff t)`, of weight `≤ 1` by construction.  This is the honest
placement of the paper's `Λ(α_t) = Λ(Y) = 1` remark: an *output* of §5 counting (false under
bare `ClaimA2.Hypotheses`, as the machine refutations show — their witnesses carry no
counting package). -/
theorem claim59_alphaWeightLe (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (k : ℕ) (xs : Finset F) (hxs : xs.card = k + 1) (u₀ u₁ : F → F)
    (hcoord : ∀ x ∈ xs,
      gammaEvalTrunc H x₀ x R hHyp k
        = fieldTo𝕃 (u₀ x) + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (u₁ x))
    (htail : ∀ t, k < t → αGenuine H x₀ R hHyp t = 0) :
    BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe H x₀ R hHyp hH D := by
  obtain ⟨v₀, v₁, _, _, hread⟩ :=
    claim59_groundLine H x₀ R hHyp k xs hxs u₀ u₁ hcoord htail
  intro t
  refine ⟨wSection H (v₀.coeff t) (v₁.coeff t), ?_, ?_⟩
  · rw [embed_wSection, hread t]
  · exact weight_wSection_le H hD hH _ _

/-! ## The composed front door -/

/-- **Claim 5.9 from counting (composed).**  Budgets + per-coordinate matching data
(`|S_x| > N·d_H` at each of `k+1` coordinates, each place reading a decoded polynomial that
matches the coordinate's line value) + tail vanishing fire the per-coordinate Claim 5.10
kills internally and assemble the ground-line Claim 5.9. -/
theorem claim59_of_counting (hlc : H.leadingCoeff = 1)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ)
    (wβ : ℕ → ℕ) (bξ N : ℕ)
    (hwβ : ∀ t ∈ Finset.range (k + 1),
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D ≤ (WithBot.some (wβ t) : WithBot ℕ))
    (hbξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D ≤ (WithBot.some bξ : WithBot ℕ))
    (hN1 : ∀ t ≤ k, wβ t + (eClear k - eClear t) * bξ ≤ N)
    (hN2 : 1 + eClear k * bξ ≤ N)
    (xs : Finset F) (hxs : xs.card = k + 1) (u₀ u₁ : F → F)
    (Sx : F → Finset F)
    (hS : ∀ x ∈ xs, ∀ z ∈ Sx x, ∃ root : rationalRoot (H_tilde' H) z, ∃ p : F[X],
      p.natDegree ≤ k
        ∧ (∀ t ∈ Finset.range (k + 1),
            π_z z root (βHensel H x₀ R hHyp t)
              = p.coeff t * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
        ∧ p.eval (x - x₀) = u₀ x + z * u₁ x)
    (hcard : ∀ x ∈ xs, N * H.natDegree < (Sx x).card)
    (htail : ∀ t, k < t → αGenuine H x₀ R hHyp t = 0) :
    (∃ v₀ v₁ : F[X], v₀.natDegree ≤ k ∧ v₁.natDegree ≤ k ∧
        ∀ t, αGenuine H x₀ R hHyp t
          = fieldTo𝕃 (v₀.coeff t)
            + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (v₁.coeff t))
      ∧ H.natDegree = 1
      ∧ BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe H x₀ R hHyp hH D := by
  have hcoord : ∀ x ∈ xs,
      gammaEvalTrunc H x₀ x R hHyp k
        = fieldTo𝕃 (u₀ x) + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (u₁ x) := by
    intro x hx
    exact gammaEvalTrunc_eq_ground_of_large H hlc hD hH x₀ x (u₀ x) (u₁ x) R hHyp k
      wβ bξ N hwβ hbξ hN1 hN2 (Sx x) (hS x hx) (hcard x hx)
  exact ⟨claim59_groundLine H x₀ R hHyp k xs hxs u₀ u₁ hcoord htail,
    claim59_curve_collapse H x₀ R hHyp k xs hxs u₀ u₁ hcoord htail,
    claim59_alphaWeightLe H x₀ R hHyp hH hD k xs hxs u₀ u₁ hcoord htail⟩

end ArkLib.Claim59GroundLine

section AxiomAudit
#print axioms ArkLib.Claim59GroundLine.coeff_gammaTruncPoly
#print axioms ArkLib.Claim59GroundLine.eval_gammaTruncPoly
#print axioms ArkLib.Claim59GroundLine.claim59_groundLine
#print axioms ArkLib.Claim59GroundLine.claim59_paperZ_linear
#print axioms ArkLib.Claim59GroundLine.claim59_curve_collapse
#print axioms ArkLib.Claim59GroundLine.counting_package_empty_of_two_le_natDegree
#print axioms ArkLib.Claim59GroundLine.claim59_T_target
#print axioms ArkLib.Claim59GroundLine.claim59_alphaWeightLe
#print axioms ArkLib.Claim59GroundLine.claim59_of_counting
end AxiomAudit
