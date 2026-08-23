/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FaithfulFrontierComposition

/-!
# Issue #304 — the frontier bundle is INHABITED (the end-to-end satisfiability witness)

The audit history of the §5 keystone surfaces (the transposed representative, the `∀-P`
quantifier, the uninhabited total-root fields, the Claim-5.9 codomain refutations) demands that
any new interface carry an inhabitation witness.  This file provides it for the round-2 frontier
bundle `FaithfulFrontier.FaithfulFrontierData` — the per-`(u, P)` composition surface whose
fields are the named honest residuals of the producer lanes.

**The witness**: `H := T` (the fiber variable itself — monic, linear, irreducible, with the
rational root `t_z = 0` at every place, so the total-root field is genuinely total here),
`R := T² − T` (constant in the inner and middle variables — separable in every characteristic
via the `ℤ`-identity `(2T−1)² − 4(T²−T) = 1`, of fiber degree 2), the zero word stack, and the
zero decoded family.  Then:

* the genuine Hensel root is **exactly zero** (`gammaGenuine_w`, by Hensel uniqueness against
  the constant root of `T² − T`), so every genuine coefficient vanishes (`αGenuine_w`);
* the recursion numerator vanishes at order 1 (`βHensel_one_w`: the order-0 partition is
  excluded and the empty-partition term dies on `Δ_X¹ R = 0`), giving the ingredient-C
  matching points with a *proven* `coeffExtract`;
* all three §6 condition discriminants are **nonzero constants**
  (`mem_discMatchingSet_w`: `discLC = 1`, `elimPoly ξ = −1`, `elimPoly W = 1` via
  `resultant_C_right`), so every place is in the canonical matching set;
* `frontierWitness` — **the inhabitation**: for every finite field above the witness's explicit
  counting budget, `FaithfulFrontierData` carries a full instance; and
* `goodSet_w_eq_univ` — **the anti-cheat**: the good set at the witness is all of `F`
  (the zero curve is a codeword at every parameter) — nothing is discharged through emptiness.

Together with `curveFamilyData_of_faithfulFrontier`, the witness pins the decoded family to the
(zero) polynomial curve end-to-end through the full producer chain: §6 counting → signed graded
weight collapse → genuine window vanishing → truncation → per-place readings → Hensel
uniqueness → the faithful extraction.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5, §6.2, Appendix A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityPrize.BCIKS20.GammaGenuine
open scoped NNReal

namespace ArkLib

namespace FrontierWitness

variable {F : Type} [Field F]

/-- The witness factor: `H := T` (the outer variable). -/
noncomputable def Hw : F[X][Y] := Polynomial.X

/-- The witness curve polynomial: `R := T² − T`, constant in the inner and middle variables. -/
noncomputable def Rw : F[X][X][Y] := Polynomial.X ^ 2 - Polynomial.X

theorem Hw_natDegree : (Hw (F := F)).natDegree = 1 := Polynomial.natDegree_X

theorem Hw_monic : (Hw (F := F)).Monic := Polynomial.monic_X

theorem Hw_irreducible : Irreducible (Hw (F := F)) := Polynomial.prime_X.irreducible

theorem Hw_natDegree_pos : 0 < (Hw (F := F)).natDegree := by
  rw [Hw_natDegree]; omega

/-- `R = T·(T − 1)`. -/
theorem Rw_factor : Rw (F := F) = Polynomial.X * (Polynomial.X - Polynomial.C 1) := by
  unfold Rw; rw [Polynomial.C_1]; ring

theorem Rw_natDegreeY : Bivariate.natDegreeY (Rw (F := F)) = 2 := by
  show (Rw (F := F)).natDegree = 2
  rw [Rw_factor, Polynomial.natDegree_mul Polynomial.X_ne_zero
    (Polynomial.X_sub_C_ne_zero 1), Polynomial.natDegree_X, Polynomial.natDegree_X_sub_C]

/-- `evalX` at any centre is the identity on the constant-in-X family: `R(x₀) = T² − T`. -/
theorem evalX_Rw (x₀ : F) :
    Bivariate.evalX (Polynomial.C x₀) (Rw (F := F)) = Polynomial.X ^ 2 - Polynomial.X := by
  rw [Rw, Bivariate.evalX_eq_map, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]

/-- `T² − T` is separable over any commutative ring in every characteristic:
`(−4)·(T²−T) + (2T−1)·(2T−1) = 1` is a `ℤ`-identity. -/
theorem sep_quad {K : Type} [CommRing K] :
    (Polynomial.X ^ 2 - Polynomial.X : K[X]).Separable := by
  rw [Polynomial.separable_def]
  refine ⟨-4, 2 * Polynomial.X - 1, ?_⟩
  rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
  simp only [Nat.cast_ofNat, map_ofNat]
  ring

theorem Hw_dvd (x₀ : F) : Hw (F := F) ∣ Bivariate.evalX (Polynomial.C x₀) (Rw (F := F)) := by
  rw [evalX_Rw]
  exact ⟨Polynomial.X - Polynomial.C 1, by rw [Polynomial.C_1, Hw]; ring⟩

theorem hypw (x₀ : F) : Hypotheses x₀ (Rw (F := F)) (Hw (F := F)) where
  dvd_evalX := Hw_dvd x₀
  separable_evalX := by rw [evalX_Rw]; exact sep_quad

instance instFactIrrHw : Fact (Irreducible (Hw (F := F))) := ⟨Hw_irreducible⟩
instance instFactPosHw : Fact (0 < (Hw (F := F)).natDegree) := ⟨Hw_natDegree_pos⟩

/-- The witness GS bundle at any centre. -/
noncomputable def bundlew (x₀ : F) : GSFactorData.Bundle (F := F) x₀ where
  R := Rw
  H := Hw
  hIrr := instFactIrrHw
  hPos := instFactPosHw
  hHyp := hypw x₀
  hH := Hw_natDegree_pos
  D := Bivariate.totalDegree (Hw (F := F))
  hD := le_refl _

theorem residualw (x₀ : F) : GSFactorData.MonicHighYResidual (bundlew (F := F) x₀) where
  hmonic := Hw_monic
  hd2 := by rw [show (bundlew (F := F) x₀).R = Rw from rfl, Rw_natDegreeY]

/-- `H̃′(T) = T`. -/
theorem H_tilde'_Hw : H_tilde' (Hw (F := F)) = Polynomial.X := by
  rw [H_tilde', if_neg (by rw [Hw_natDegree]; omega)]
  rw [Hw_natDegree]
  simp [Hw]

/-- The everywhere-defined rational root: `t_z = 0` at every place. -/
noncomputable def rootw : (z : F) → rationalRoot (H_tilde' (Hw (F := F))) z := fun z =>
  ⟨0, by rw [H_tilde'_Hw]; simp [Polynomial.evalEval]⟩

/-! ## Stage 3a — the genuine objects vanish at the witness -/

/-- `T ↦ 0` in the function field of `T`: the generator lies in the defining ideal. -/
theorem functionFieldT_Hw : functionFieldT (H := Hw (F := F)) = 0 := by
  rw [functionFieldT, Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.subset_span ?_
  rw [Set.mem_singleton_iff, ← map_H_tilde'_eq_H_tilde, H_tilde'_Hw, Polynomial.map_X]

theorem α₀_Hw : α₀ (Hw (F := F)) = 0 := by
  rw [α₀, functionFieldT_Hw, zero_div]

/-- `Q = T² − T` over the series ring. -/
theorem Q_w (x₀ : F) : Q x₀ (Rw (F := F)) (Hw (F := F))
    = Polynomial.X ^ 2 - Polynomial.X := by
  rw [Q, Rw, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]

/-- **The genuine Hensel root of the witness is `0`** (Hensel uniqueness against the constant
root `0` of `T² − T`). -/
theorem gammaGenuine_w (x₀ : F) :
    gammaGenuine x₀ (Rw (F := F)) (Hw (F := F)) (hypw x₀) = 0 := by
  refine hensel_root_unique (Q x₀ (Rw (F := F)) (Hw (F := F)))
    (a₀ := 0) (gammaGenuine_root (hypw x₀)) ?_ ?_ ?_ ?_
  · -- 0 is a root of T² − T
    rw [Q_w]
    simp [Polynomial.IsRoot]
  · -- γ − 0 ∈ (X): constantCoeff γ = α₀ = 0
    rw [sub_zero, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff,
      gammaGenuine_constantCoeff (hypw x₀), α₀_Hw]
  · -- 0 − 0 ∈ (X)
    rw [sub_zero]
    exact Ideal.zero_mem _
  · -- derivative (T² − T) at 0 is −1, a unit
    rw [Q_w, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
    simp

/-- Every genuine Hensel coefficient of the witness vanishes. -/
theorem αGenuine_w (x₀ : F) (t : ℕ) :
    BCIKS20.HenselNumerator.αGenuine (Hw (F := F)) x₀ (Rw (F := F)) (hypw x₀) t = 0 := by
  rw [BCIKS20.HenselNumerator.αGenuine, gammaGenuine_w, map_zero]

/-! ## Stage 3b — the recursion numerator vanishes at order 1 -/

open BCIKS20.HenselNumerator in
/-- The first X-Hasse derivative of the constant-in-X witness vanishes. -/
theorem hasseDerivX_one_Rw : hasseDerivX 1 (Rw (F := F)) = 0 := by
  rw [hasseDerivX, Polynomial.sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  suffices h : Polynomial.hasseDeriv 1 ((Rw (F := F)).coeff n) = 0 by
    rw [h, Polynomial.monomial_zero_right]
  rw [Rw, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  split_ifs <;> simp

open BCIKS20.HenselNumerator in
/-- The first X-Hasse derivative kills every Y-Hasse derivative of the witness (all
coefficients are X-constants). -/
theorem hasseDerivX_one_hasseDerivY_Rw (m : ℕ) :
    hasseDerivX 1 (hasseDerivY m (Rw (F := F))) = 0 := by
  rw [hasseDerivY, hasseDerivX, Polynomial.sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  suffices h : Polynomial.hasseDeriv 1
      ((Polynomial.hasseDeriv m (Rw (F := F))).coeff n) = 0 by
    rw [h, Polynomial.monomial_zero_right]
  rw [Polynomial.hasseDeriv_coeff, Rw, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
    Polynomial.coeff_X]
  split_ifs <;> simp

open BCIKS20.HenselNumerator in
/-- The order-1 canonical Faà-di-Bruno coefficients vanish (any Y-Hasse order: the
X-derivative already kills the representative). -/
theorem hasseCoeffRepr_one_Rw (x₀ : F) (m : ℕ) :
    hasseCoeffRepr𝒪 (Hw (F := F)) x₀ (Rw (F := F)) 1 m = 0 := by
  rw [hasseCoeffRepr𝒪, hasseDerivX_one_hasseDerivY_Rw, Bivariate.evalX_eq_map,
    Polynomial.map_zero, map_zero]

theorem partition_zero_parts (p : Nat.Partition 0) : p.parts = 0 := by
  by_contra h
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero h
  have h1 := p.parts_pos ha
  have h2 : a ≤ p.parts.sum := Multiset.single_le_sum (fun x _ => Nat.zero_le x) a ha
  rw [p.parts_sum] at h2
  omega

theorem partition_one_mem (p : Nat.Partition 1) : 1 ∈ p.parts := by
  have hne : p.parts ≠ 0 := by
    intro h
    have hs := p.parts_sum
    rw [h] at hs
    simp at hs
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  have h1 := p.parts_pos ha
  have h2 : a ≤ p.parts.sum := Multiset.single_le_sum (fun x _ => Nat.zero_le x) a ha
  rw [p.parts_sum] at h2
  have ha1 : a = 1 := by omega
  exact ha1 ▸ ha

open BCIKS20.HenselNumerator in
/-- The order-1 recursion numerator of the witness vanishes. -/
theorem βHensel_one_w (x₀ : F) :
    βHensel (Hw (F := F)) x₀ (Rw (F := F)) (hypw x₀) 1 = 0 := by
  rw [βHensel_succ (Hw (F := F)) x₀ (Rw (F := F)) (hypw x₀) 0]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h0 : ((Finset.univ : Finset (Nat.Partition (0 + 1 - 0))).filter
      (fun lam => (0 + 1) ∉ lam.parts)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p _
    rw [not_not]
    exact partition_one_mem p
  have h1 : ∀ lam ∈ ((Finset.univ : Finset (Nat.Partition (0 + 1 - 1))).filter
      (fun lam => (0 + 1) ∉ lam.parts)),
      (W𝒪 (Hw (F := F))) ^ (1 + deltaSave 1 - 1)
        * (ξ x₀ (Rw (F := F)) (Hw (F := F)) (hypw x₀)) ^ (2 * 1 + sigmaLambda lam - 2)
        * B_coeff (Hw (F := F)) x₀ (Rw (F := F)) 1 lam
        * partitionProd lam
            (fun l => if _h : l < 0 + 1 then βHensel (Hw (F := F)) x₀ (Rw (F := F)) (hypw x₀) l else 0)
      = 0 := by
    intro lam _
    rw [B_coeff, hasseCoeffRepr_one_Rw]
    simp
  rw [h0, Finset.sum_empty, Finset.sum_eq_zero h1, add_zero, neg_zero]

open BCIKS20.HenselNumerator in
/-- The order-1 signed-capsule numerator of the witness vanishes. -/
theorem betaRec_signed_one_w (x₀ : F) :
    betaRec x₀ (Rw (F := F)) (Hw (F := F)) (hypw x₀)
      (BetaRecGenuineBridge.BcoeffSigned (Hw (F := F)) x₀ (Rw (F := F))) 1 = 0 := by
  rw [BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel, βHensel_one_w]

/-! ## Stage 4 — the condition discs are nonzero constants -/

theorem βHensel_zero_w (x₀ : F) :
    BCIKS20.HenselNumerator.βHensel (Hw (F := F)) x₀ (Rw (F := F)) (hypw x₀) 0 = 0 := by
  rw [BCIKS20.HenselNumerator.βHensel_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by rw [Set.mem_singleton_iff, H_tilde'_Hw])

/-- The order-0 coefficient of the specialized derivative is `−1`. -/
theorem coeff_zero_P_w (x₀ : F) :
    (Bivariate.evalX (Polynomial.C x₀) (Polynomial.derivative (Rw (F := F)))).coeff 0 = -1 := by
  rw [Rw, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X,
    Bivariate.evalX_eq_map, Polynomial.coeff_map]
  simp

/-- The order-0 outer evaluation of the `ξ` representative is `−1`. -/
theorem eval_zero_ξ_pre (x₀ : F) :
    Polynomial.eval 0 (ξ_pre x₀ (Rw (F := F)) (Hw (F := F))) = -1 := by
  have hd : (Rw (F := F)).natDegree = 2 := Rw_natDegreeY
  simp only [ξ_pre, hd]
  rw [if_pos (by omega : 2 ≤ 2)]
  simp [coeff_zero_P_w, Hw_monic.leadingCoeff]

theorem ξ_w_ne_zero (x₀ : F) : ξ x₀ (Rw (F := F)) (Hw (F := F)) (hypw x₀) ≠ 0 := by
  intro h
  rw [ξ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, H_tilde'_Hw] at h
  obtain ⟨g, hg⟩ := h
  have heval := congrArg (Polynomial.eval 0) hg
  rw [eval_zero_ξ_pre, Polynomial.eval_mul, Polynomial.eval_X, zero_mul] at heval
  exact neg_ne_zero.mpr one_ne_zero heval

theorem canonicalRep_w (p : F[X][Y]) :
    canonicalRepOf𝒪 (Hw_natDegree_pos (F := F))
      (Ideal.Quotient.mk (Ideal.span {H_tilde' (Hw (F := F))}) p)
      = Polynomial.C (Polynomial.eval 0 p) := by
  rw [canonicalRepOf𝒪, H_tilde'_Hw, Polynomial.modByMonic_X]
  congr 1
  have hmk : Ideal.Quotient.mk (Ideal.span {H_tilde' (Hw (F := F))})
      (Ideal.Quotient.mk (Ideal.span {H_tilde' (Hw (F := F))}) p).out
      = Ideal.Quotient.mk (Ideal.span {H_tilde' (Hw (F := F))}) p := Ideal.Quotient.mk_out _
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, H_tilde'_Hw] at hmk
  obtain ⟨g, hg⟩ := hmk
  have h := congrArg (Polynomial.eval 0) hg
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, zero_mul] at h
  exact sub_eq_zero.mp h

theorem elimPoly_mk_w (p : F[X][Y]) :
    elimPoly (Hw_natDegree_pos (F := F))
      (Ideal.Quotient.mk (Ideal.span {H_tilde' (Hw (F := F))}) p)
      = Polynomial.eval 0 p := by
  rw [elimPoly, canonicalRep_w, H_tilde'_Hw, Polynomial.natDegree_X, Polynomial.natDegree_C,
    Polynomial.resultant_C_right]
  simp

section WithFintype

variable [Fintype F] [DecidableEq F]

/-- Every place satisfies all three condition discriminants at the witness. -/
theorem mem_discMatchingSet_w (x₀ z : F) :
    z ∈ Match304.discMatchingSet Finset.univ
      (Match304.conditionDiscs (Polynomial.X : F[X][Y]) x₀ (Rw (F := F)) (Hw (F := F))
        Hw_natDegree_pos (hypw x₀)) := by
  rw [Match304.mem_discMatchingSet]
  intro i _
  fin_cases i
  · show Polynomial.eval z (ArkLib.PerPlaceSep.discLC (Polynomial.X : F[X][Y])) ≠ 0
    rw [ArkLib.PerPlaceSep.discLC,
      Polynomial.discr_of_degree_eq_one Polynomial.degree_X, Polynomial.leadingCoeff_X,
      one_mul, Polynomial.eval_one]
    exact one_ne_zero
  · show Polynomial.eval z
      (elimPoly Hw_natDegree_pos (ξ x₀ (Rw (F := F)) (Hw (F := F)) (hypw x₀))) ≠ 0
    rw [ξ, elimPoly_mk_w, eval_zero_ξ_pre]
    simp
  · show Polynomial.eval z
      (elimPoly Hw_natDegree_pos (BCIKS20.HenselNumerator.W𝒪 (Hw (F := F)))) ≠ 0
    rw [BCIKS20.HenselNumerator.W𝒪, elimPoly_mk_w]
    simp [Hw_monic.leadingCoeff]

/-! ## Stage 5 — the inhabitation -/

instance instFactIrrGB (x₀ : F) :
    Fact (Irreducible (GSFactorData.GradedBundle.ofBundle (bundlew (F := F) x₀)).H) :=
  instFactIrrHw

instance instFactPosGB (x₀ : F) :
    Fact (0 < (GSFactorData.GradedBundle.ofBundle (bundlew (F := F) x₀)).H.natDegree) :=
  instFactPosHw

/-- Any double polynomial-map image of the witness curve polynomial is `T² − T`. -/
theorem map_map_Rw {A B : Type} [CommRing A] [CommRing B]
    (φ : F[X][X] →+* A) (ψ : A →+* B) :
    ((Rw (F := F)).map φ).map ψ = Polynomial.X ^ 2 - Polynomial.X := by
  rw [Rw, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]

/-- The local Hensel series of the witness has vanishing constant coefficient. -/
theorem constantCoeff_localSeries_w (x₀ z : F)
    (root : rationalRoot (H_tilde' (Hw (F := F))) z)
    (hx : (π_z z root) (ξ x₀ (Rw (F := F)) (Hw (F := F)) (hypw x₀)) ≠ 0) :
    PowerSeries.constantCoeff (localSeries (hypw x₀) z root hx) = 0 := by
  simp only [localSeries, assembledLoc, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, βHensel_zero_w, IsLocalization.mk'_zero,
    map_zero]

set_option maxHeartbeats 1000000 in
open FaithfulFrontier in
/-- **THE FRONTIER BUNDLE IS INHABITED.**  For every finite field above the witness's explicit
counting budget, `FaithfulFrontierData` carries a full instance at the witness curve data
(`H = T`, `R = T² − T`, the zero word-stack, the zero decoded family) — with the good set equal
to **all of `F`** (nonempty; nothing is discharged through emptiness). -/
noncomputable def frontierWitness {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} (x₀ : F)
    (hbig : gradedCardBudget (Bivariate.natDegreeY (Rw (F := F)))
        (GSFactorData.GradedBundle.ofBundle (bundlew (F := F) x₀)).D
        (Hw (F := F)).natDegree 1
      + ∑ i, (Match304.conditionDiscs (Polynomial.X : F[X][Y]) x₀ (Rw (F := F)) (Hw (F := F))
          Hw_natDegree_pos (hypw x₀) i).natDegree
      < Fintype.card F) :
    FaithfulFrontierData (k := k) (deg := deg) (domain := domain) (δ := δ)
      (fun _ _ => (0 : F)) (fun _ => (0 : F[X])) where
  x₀ := x₀
  gb := GSFactorData.GradedBundle.ofBundle (bundlew x₀)
  hres := ⟨Hw_monic, by show 2 ≤ Bivariate.natDegreeY (Rw (F := F)); rw [Rw_natDegreeY]⟩
  hRsep := sep_quad
  n := 1
  hn := by omega
  c := fun _ => 0
  T := 1
  fB := Polynomial.X
  hfBdeg := by rw [Polynomial.natDegree_X]; omega
  hfBdiscr := by
    rw [Polynomial.discr_of_degree_eq_one Polynomial.degree_X]
    exact one_ne_zero
  hfBne := Polynomial.X_ne_zero
  hbig := hbig
  root := rootw
  mpFin := by
    intro t h1 h2 z _
    have ht : t = 1 := by omega
    subst ht
    exact
      { f := Polynomial.X ^ 2 - Polynomial.X
        aβ := 0
        aP := 0
        a₀ := 0
        haβ_root := by simp [Polynomial.IsRoot]
        haP_root := by simp [Polynomial.IsRoot]
        haβ_cong := by simp
        haP_cong := by simp
        hderiv := by
          rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
          simp
        coeffExtract := fun _ => by
          show (π_z z (rootw z)) (betaRec x₀ (Rw (F := F)) (Hw (F := F)) (hypw x₀)
            (BetaRecGenuineBridge.BcoeffSigned (Hw (F := F)) x₀ (Rw (F := F))) 1) = 0
          rw [betaRec_signed_one_w]
          exact map_zero _ }
  htailBeyond := fun t _ => αGenuine_w x₀ t
  hgoodDisc := fun z _ => mem_discMatchingSet_w x₀ z
  htrunc := by
    intro z hz
    have hc := constantCoeff_localSeries_w x₀ z (rootw z)
      (xiReading_ne_zero_of_mem_discMatchingSet (F := F) (mem_discMatchingSet_w x₀ z) (rootw z))
    ext j
    rw [PowerSeries.coeff_trunc]
    have hrhs : (∑ t ∈ Finset.range 1, (z - x₀) ^ t • (0 : F[X])).coeff j = 0 := by
      simp
    rw [hrhs]
    split_ifs with hj
    · have hj0 : j = 0 := by omega
      subst hj0
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hc
    · rfl
  hdvd := by
    intro z hz
    rw [show ((((fun _ => (0 : F[X])) z : F[X]) : PowerSeries F)) = 0 from Polynomial.coe_zero,
      map_zero, sub_zero]
    have key : ∀ M : Polynomial (PowerSeries F), M = Polynomial.X ^ 2 - Polynomial.X →
        (Polynomial.X : Polynomial (PowerSeries F)) ∣ M := by
      rintro M rfl
      exact ⟨Polynomial.X - 1, by ring⟩
    exact key _ (map_map_Rw _ _)
  hcong := by
    intro z hz
    show (((0 : F[X]) : PowerSeries F)) - PowerSeries.C ((π_z z (rootw z))
        (BCIKS20.HenselNumerator.βHensel (Hw (F := F)) x₀ (Rw (F := F)) (hypw x₀) 0))
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
    rw [βHensel_zero_w, map_zero, map_zero, Polynomial.coe_zero, sub_zero]
    exact Ideal.zero_mem _

/-- **The witness good set is everything** (the zero curve is a codeword at every parameter):
the inhabitation above is at a good set equal to all of `F` — nothing is discharged through
emptiness. -/
theorem goodSet_w_eq_univ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} :
    ProximityGap.RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain)
      (fun _ _ => (0 : F)) δ = Finset.univ := by
  rw [ProximityGap.RS_goodCoeffsCurve]
  refine Finset.filter_true_of_mem ?_
  intro z _
  have hsum : (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • (fun _ _ => (0 : F)) t : ι → F)
      = fun _ => (0 : F) := by
    funext i
    simp
  rw [hsum]
  have hmem : (fun _ => (0 : F)) ∈ (ReedSolomon.code domain deg : Set (ι → F)) := by
    have h0 : (fun _ => (0 : F)) = (0 : ι → F) := rfl
    rw [h0, SetLike.mem_coe]
    exact zero_mem _
  refine le_trans (Code.relDistFromCode_le_relDist_to_mem (ι := ι) (fun _ => (0 : F)) _ hmem) ?_
  have hd : Code.relHammingDist ((fun _ => (0 : F)) : ι → F) ((fun _ => (0 : F)) : ι → F)
      = 0 := by
    simp [Code.relHammingDist]
  rw [hd]
  exact le_trans (le_of_eq (by rw [ENNReal.coe_NNRat_coe_NNReal]; norm_num)) (zero_le _)

end WithFintype

end FrontierWitness

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.FrontierWitness.gammaGenuine_w
#print axioms ArkLib.FrontierWitness.αGenuine_w
#print axioms ArkLib.FrontierWitness.βHensel_one_w
#print axioms ArkLib.FrontierWitness.betaRec_signed_one_w
#print axioms ArkLib.FrontierWitness.mem_discMatchingSet_w
#print axioms ArkLib.FrontierWitness.frontierWitness
#print axioms ArkLib.FrontierWitness.goodSet_w_eq_univ
