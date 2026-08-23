/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.S5GenuineZLinearQuadratic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicWeightRefutation

/-!
# #138 X-degree budget probe: the graded rescue is DEAD (kernel-checked)

`S5GenuineZLinearQuadratic.alphaGenuineRegularWeightLe_of_monic_natDegree_two_of_budget` reduces
the monic-quadratic #138 weight invariant to the **X-degree budget** on the canonical
representative of the integral preimage of each `αGenuine t`.  The natural rescue hope was that
the budget follows from the GS *graded* structure of `R` — the paper grading
`hRgrade : ∀ j, degreeX (R.coeff j) ≤ D − j` consumed by
`GenuineTruncationFin.weight_βHensel_le_graded` / `GSGradedBundle.GradedBundle`.  This file
settles that probe **negatively, by kernel-checked computation on the
`P1MonicWeightRefutation` witness** (`H = Y² − 2`, `R = Y² − 2 + Z·s` over `ZMod 3`):

1. **`witness_D_pinned`** — in the weight-1 regime (`totalDegree H ≤ D ≤ natDegree H`) the
   degree parameter is pinned to `D = 2` for the witness.
2. **`witness_hRgrade`** — the witness **satisfies** the paper grading at `D = 2`:
   `degreeX (R.coeff 0) = 1 ≤ 2`, `degreeX (R.coeff 2) = 0 ≤ 0` (`degreeX_liftCoeff_eq_one`
   pins the exact value).  It also satisfies every other graded side condition of
   `weight_βHensel_le_graded` (`witness_totalDegree_H`, `witness_totalDegree_evalX`,
   `witness_natDegreeY_R`, monicity) — see `graded_rescue_dead`.
3. **`witness_trivariate_grade`** — the witness even satisfies the *strongest* pointwise
   trivariate grading `deg_X ((R.coeff j).coeff i) ≤ D − j − i` (lift variable `Z` graded with
   full weight), and `R` is `Z`-linear — the exact `u₀ + Z·u₁` shape of a genuine GS line
   interpolant.  No degree bookkeeping on `R` separates the witness from GS-produced data.
4. **`witness_budget_refuted`** — yet the X-degree budget **fails** at `t = 1`: the unique
   integral preimage of `αGenuine 1` is `mk (monomial 1 (−X))` (`alphaOne_preimage_forced`,
   computed through the monic lift identity + `ξ`-inversion), whose `Y¹`-coefficient has
   `X`-degree `1`, so `(D+1−d_H) + 1 = 2 > 1`.
5. **`graded_rescue_dead`** — the packaged conjunction: ALL graded side conditions hold at the
   unique admissible `D = 2` AND the budget fails.  Hence the budget is **not** implied by any
   in-tree (or paper-shaped) grading of `R`; its provenance must be the GS *geometry* (the
   agreement/vanishing structure tying the `Z`-direction coefficients to codewords), not degree
   bookkeeping.  The budget stays open as a genuinely geometric named core.

The file also lands the **weight → X-degree extraction** (task (iii)):

* `natDegree_coeff_canonicalRep_le_of_weight_le` — `Λ_𝒪(a) ≤ W` bounds the `X`-degree of every
  `Y`-coefficient of the canonical representative by `W` (the `Λ`-weight *does* control the
  canonical rep's `X`-degrees; the per-`Y`-power refinement is `weight_Λ_le_iff`).
* `weight_le_one_iff_budget` — for monic quadratic `H` and `D ≤ natDegree H`, the per-element
  budget is **exactly equivalent** to `Λ_𝒪(a) ≤ 1`.
* `alphaGenuineRegularWeightLe_iff_budget` — the #138 monic-quadratic invariant is **exactly
  equivalent** to the budget (no slack in the reformulation; the budget IS the open core).
* `witness_alphaWeightLe_refuted` — corollary: the full `AlphaGenuineRegularWeightLe` fails on
  the witness at `D = 2` (the invariant-native form of `weight_refuted`).
-/

set_option linter.style.longLine false

noncomputable section

open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.HenselNumerator BCIKS20.HenselNumerator.S5Genuine
open BCIKS20.HenselNumerator.WeightWitness

namespace ArkLib.XDegreeBudgetProbe

/-! ## Part 1 — the weight → X-degree extraction (general) -/

section Extraction

variable {F : Type} [Field F]

/-- **`Λ`-weight bounds the X-degree of the canonical representative.**  If
`Λ_𝒪(a) ≤ W`, then every `Y`-coefficient of `canonicalRepOf𝒪 a` has `X`-degree `≤ W` (the
per-`Y`-power refinement, with slack `n·(D+1−d_H)`, is `weight_Λ_le_iff`). -/
theorem natDegree_coeff_canonicalRep_le_of_weight_le {H : F[X][Y]} (hH : 0 < H.natDegree)
    {a : 𝒪 H} {D W : ℕ} (hw : weight_Λ_over_𝒪 hH a D ≤ WithBot.some W) (n : ℕ) :
    ((canonicalRepOf𝒪 hH a).coeff n).natDegree ≤ W := by
  unfold weight_Λ_over_𝒪 at hw
  rw [weight_Λ_le_iff] at hw
  by_cases hn : n ∈ (canonicalRepOf𝒪 hH a).support
  · have := hw n hn
    omega
  · rw [Polynomial.notMem_support_iff.mp hn]
    simp

variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The X-degree budget is exactly the weight-`≤ 1` bound (monic quadratic).**  For monic `H`
of `Y`-degree `2` and `D ≤ natDegree H`, an `𝒪`-element satisfies `Λ_𝒪(a) ≤ 1` **iff** its
canonical-representative coefficients satisfy the budget
`deg_X c₀ ≤ 1 ∧ (D+1−d_H) + deg_X c₁ ≤ 1`.  So the budget hypothesis of
`alphaGenuineRegularWeightLe_of_monic_natDegree_two_of_budget` is not an artifact of the
zLinear route: it is the entire per-element content of the #138 weight invariant. -/
theorem weight_le_one_iff_budget (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hd2 : H.natDegree = 2) {D : ℕ} (hD : D ≤ H.natDegree) (a : 𝒪 H) :
    weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 ↔
      (((canonicalRepOf𝒪 hH a).coeff 0).natDegree ≤ 1
        ∧ (D + 1 - Bivariate.natDegreeY H) + ((canonicalRepOf𝒪 hH a).coeff 1).natDegree ≤ 1) := by
  constructor
  · intro hw
    unfold weight_Λ_over_𝒪 at hw
    rw [weight_Λ_le_iff] at hw
    constructor
    · by_cases h0 : (0 : ℕ) ∈ (canonicalRepOf𝒪 hH a).support
      · simpa using hw 0 h0
      · rw [Polynomial.notMem_support_iff.mp h0]
        simp
    · by_cases h1 : (1 : ℕ) ∈ (canonicalRepOf𝒪 hH a).support
      · have := hw 1 h1
        rwa [one_mul] at this
      · rw [Polynomial.notMem_support_iff.mp h1]
        have hnd : Bivariate.natDegreeY H = H.natDegree := rfl
        rw [hnd, hd2, Polynomial.natDegree_zero]
        have hD2 : D ≤ 2 := hd2 ▸ hD
        omega
  · rintro ⟨hb0, hb1⟩
    rw [← mk_canonicalRep_zLinear_of_monic_natDegree_le_two H hH hlc (le_of_eq hd2) a]
    exact weight_Λ_over_𝒪_zLinear_le_one hH (le_of_eq hd2.symm) _ _ D hb0 hb1

/-- **The #138 monic-quadratic weight invariant is exactly the X-degree budget.**  Combined with
`alphaGenuineRegularWeightLe_of_monic_natDegree_two_of_budget` (the `←` direction) and uniqueness
of integral preimages (`embeddingOf𝒪Into𝕃_injective`, the `→` direction), the budget is a
faithful reformulation of the open core — refuting it on an instance refutes the invariant. -/
theorem alphaGenuineRegularWeightLe_iff_budget {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    (hlc : H.leadingCoeff = 1) (hd2 : H.natDegree = 2) {D : ℕ} (hD : D ≤ H.natDegree) :
    AlphaWeight.AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      (∀ t : ℕ, ∀ a : 𝒪 H, embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t →
        ((canonicalRepOf𝒪 hH a).coeff 0).natDegree ≤ 1
          ∧ (D + 1 - Bivariate.natDegreeY H)
              + ((canonicalRepOf𝒪 hH a).coeff 1).natDegree ≤ 1) := by
  constructor
  · intro hα t a ha
    obtain ⟨b, hb, hwb⟩ := hα t
    have hab : a = b := embeddingOf𝒪Into𝕃_injective hH (ha.trans hb.symm)
    rw [hab]
    exact (weight_le_one_iff_budget H hH hlc hd2 hD b).mp hwb
  · intro hbudget
    exact alphaGenuineRegularWeightLe_of_monic_natDegree_two_of_budget H hHyp hH hlc hd2 D hbudget

end Extraction

/-! ## Part 2 — the witness satisfies EVERY graded side condition at the pinned `D = 2` -/

/-- The `Y`-coefficients of the refutation witness `H = Y² − 2`. -/
lemma myH_coeff (j : ℕ) : myH.coeff j
    = (if (2 : ℕ) = j then (1 : K[X]) else 0) + (if (0 : ℕ) = j then (-2 : K[X]) else 0) := by
  rw [myH, Polynomial.coeff_add, Polynomial.coeff_monomial, Polynomial.coeff_monomial]

/-- `totalDegree (Y² − 2) = 2`: the graded side condition `totalDegree H ≤ D` holds at `D = 2`
(with equality, which pins `D`). -/
theorem witness_totalDegree_H : Bivariate.totalDegree myH = 2 := by
  apply le_antisymm
  · unfold Polynomial.Bivariate.totalDegree
    apply Finset.sup_le
    intro j hj
    by_cases h2 : j = 2
    · subst h2
      rw [myH_coeff]
      norm_num
    · by_cases h0 : j = 0
      · subst h0
        rw [myH_coeff]
        norm_num
      · exfalso
        rw [Polynomial.mem_support_iff, myH_coeff, if_neg (by omega), if_neg (by omega),
          add_zero] at hj
        exact hj rfl
  · have h2 : (2 : ℕ) ∈ myH.support := by
      rw [Polynomial.mem_support_iff, myH_coeff]
      norm_num
    have hle := Finset.le_sup (f := fun m => (myH.coeff m).natDegree + m) h2
    unfold Polynomial.Bivariate.totalDegree
    exact le_trans (Nat.le_add_left 2 _) hle

/-- **`D` is pinned to `2` on the witness**: the weight-1 regime
`totalDegree H ≤ D ≤ natDegree H` admits exactly `D = 2`. -/
theorem witness_D_pinned {D : ℕ} (hDH : Bivariate.totalDegree myH ≤ D)
    (hD : D ≤ myH.natDegree) : D = 2 := by
  rw [witness_totalDegree_H] at hDH
  rw [myH_natDegree] at hD
  omega

/-- Graded side condition (iv) at `D = 2`: `totalDegree (evalX (C 0) R) = totalDegree H = 2`. -/
theorem witness_totalDegree_evalX :
    Bivariate.totalDegree (Bivariate.evalX (Polynomial.C (0 : K)) myR) = 2 := by
  rw [evalX_myR]
  exact witness_totalDegree_H

/-- The witness `R` has `Y`-degree `2` (the `2 ≤ natDegreeY R` side condition holds). -/
theorem witness_natDegreeY_R : Bivariate.natDegreeY myR = 2 := myR_natDegree

/-- The lift-direction coefficient `R.coeff 0 = Z·s − 2` as an explicit monomial sum. -/
lemma liftCoeff_eq : (Polynomial.X * Polynomial.C (Polynomial.X : K[X]) - 2 : K[X][X])
    = Polynomial.monomial 1 (Polynomial.X : K[X]) - Polynomial.C (2 : K[X]) := by
  rw [Polynomial.X_mul_C, Polynomial.C_mul_X_eq_monomial, (map_ofNat Polynomial.C 2).symm]

/-- The bivariate coefficients of the lift-direction coefficient. -/
lemma liftCoeff_coeff (n : ℕ) :
    (Polynomial.X * Polynomial.C (Polynomial.X : K[X]) - 2 : K[X][X]).coeff n
      = (if (1 : ℕ) = n then (Polynomial.X : K[X]) else 0)
        - (if n = 0 then (2 : K[X]) else 0) := by
  rw [liftCoeff_eq, Polynomial.coeff_sub, Polynomial.coeff_monomial, Polynomial.coeff_C]

/-- **The witness's only nontrivial `X`-degree datum**: `degreeX (R.coeff 0) = 1` — the ground
`X`-degree carried by the lift (`Z`) direction.  Strictly within the paper-grading budget
`D − 0 = 2`. -/
theorem degreeX_liftCoeff_eq_one :
    Bivariate.degreeX (Polynomial.X * Polynomial.C (Polynomial.X : K[X]) - 2 : K[X][X]) = 1 := by
  apply le_antisymm
  · unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro n _
    rw [liftCoeff_coeff]
    split_ifs with h1 h2
    · omega
    · simp
    · simp
    · simp
  · have h1 : (1 : ℕ) ∈
        (Polynomial.X * Polynomial.C (Polynomial.X : K[X]) - 2 : K[X][X]).support := by
      rw [Polynomial.mem_support_iff, liftCoeff_coeff, if_pos rfl, if_neg one_ne_zero, sub_zero]
      exact Polynomial.X_ne_zero
    have hle := Finset.le_sup
      (f := fun n => ((Polynomial.X * Polynomial.C (Polynomial.X : K[X]) - 2 : K[X][X]).coeff
        n).natDegree) h1
    unfold Polynomial.Bivariate.degreeX
    refine le_trans ?_ hle
    show 1 ≤ ((Polynomial.X * Polynomial.C (Polynomial.X : K[X]) - 2 : K[X][X]).coeff 1).natDegree
    rw [liftCoeff_coeff, if_pos rfl, if_neg one_ne_zero, sub_zero, Polynomial.natDegree_X]

/-- The `Y`-coefficients of the refutation witness `R = Y² − 2 + Z·s`. -/
lemma myR_coeff (j : ℕ) : myR.coeff j
    = (if (2 : ℕ) = j then (1 : K[X][X]) else 0)
      + (if (0 : ℕ) = j then
          (Polynomial.X * Polynomial.C (Polynomial.X : K[X]) - 2 : K[X][X]) else 0) := by
  rw [myR, Polynomial.coeff_add, Polynomial.coeff_monomial, Polynomial.coeff_monomial]

/-- **PROBE ANSWER (negative): the refutation witness SATISFIES the paper grading `hRgrade`
at the pinned `D = 2`.**  `degreeX (R.coeff 0) = 1 ≤ 2`, `degreeX (R.coeff 2) = 0 ≤ 0`, all
other coefficients vanish.  This is the exact hypothesis `hR` of
`GenuineTruncationFin.weight_βHensel_le_graded` and `GSGradedBundle.GradedBundle`. -/
theorem witness_hRgrade : ∀ j : ℕ, Bivariate.degreeX (myR.coeff j) ≤ 2 - j := by
  intro j
  by_cases h0 : j = 0
  · subst h0
    rw [myR_coeff, if_neg (by norm_num), if_pos rfl, zero_add]
    exact le_trans (le_of_eq degreeX_liftCoeff_eq_one) (by norm_num)
  · by_cases h2 : j = 2
    · subst h2
      rw [myR_coeff, if_pos rfl, if_neg (by norm_num), add_zero]
      unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le
      intro n _
      rw [Polynomial.coeff_one]
      split_ifs <;> simp
    · rw [myR_coeff, if_neg (by omega), if_neg (by omega), add_zero]
      simp [Polynomial.Bivariate.degreeX]

/-- **The witness even satisfies the STRONGEST pointwise trivariate grading**
`deg_X ((R.coeff j).coeff i) ≤ D − j − i` at `D = 2` (lift variable `Z` graded at full
weight).  Together with `Z`-linearity of the witness (`R = u₀ + Z·u₁`, the genuine GS line
shape), no grading of `(ground-X, Z, Y)`-degrees of `R` separates the witness from GS-produced
data: the budget's provenance must be the agreement geometry, not degree bookkeeping. -/
theorem witness_trivariate_grade : ∀ j i : ℕ, ((myR.coeff j).coeff i).natDegree ≤ 2 - j - i := by
  intro j i
  by_cases h0 : j = 0
  · subst h0
    rw [myR_coeff, if_neg (by norm_num), if_pos rfl, zero_add, liftCoeff_coeff]
    split_ifs with h1 h2
    · omega
    · simp [← h1]
    · simp
    · simp
  · by_cases h2 : j = 2
    · subst h2
      rw [myR_coeff, if_pos rfl, if_neg (by norm_num), add_zero, Polynomial.coeff_one]
      split_ifs <;> simp
    · rw [myR_coeff, if_neg (by omega), if_neg (by omega), add_zero]
      simp

/-! ## Part 3 — yet the budget FAILS at `t = 1` (the graded rescue is dead) -/

/-- **The forced integral preimage of `αGenuine 1` on the witness.**  Through the monic lift
identity (`βHensel_lift_identity`, `W = 1`, `ξ`-exponent `1`) and the explicit `ξ`-inverse
`mk X`, any `a` with `embed a = αGenuine 1` equals `mk (monomial 1 (−X))` — the `Y¹·X`-element
whose budget conjunct fails. -/
theorem alphaOne_preimage_forced (hH : 0 < myH.natDegree) (a : 𝒪 myH)
    (ha : embeddingOf𝒪Into𝕃 myH a = αGenuine myH 0 myR myHyp 1) :
    a = Ideal.Quotient.mk (Ideal.span {H_tilde' myH})
        (Polynomial.monomial 1 (-(Polynomial.X : K[X]))) := by
  have hzero := faaDiBrunoSuccSumZeroResidual_of_leadingCoeff_one myH 0 myR myHyp
    myH_leadingCoeff
  have hlift := βHensel_lift_identity myH 0 myR myHyp hzero 1
  rw [myH_leadingCoeff, map_one, one_pow, mul_one, ← ha,
    show (2 * 1 - 1 : ℕ) = 1 from rfl, pow_one, ← map_mul] at hlift
  have hbeta : βHensel myH 0 myR myHyp 1 = a * ClaimA2.ξ 0 myR myH myHyp :=
    embeddingOf𝒪Into𝕃_injective hH hlift
  have hstep : a = βHensel myH 0 myR myHyp 1
      * Ideal.Quotient.mk (Ideal.span {H_tilde' myH}) Polynomial.X := by
    conv_lhs => rw [← mul_one a, ← hξinv, ← mul_assoc, ← hbeta]
  rw [hstep, hβ1, neg_mul, ← map_mul, ← map_neg]
  congr 1
  rw [show Polynomial.C (Polynomial.X : K[X]) = Polynomial.monomial 0 (Polynomial.X : K[X]) from
      (Polynomial.monomial_zero_left _).symm, Polynomial.monomial_mul_X,
    ← Polynomial.monomial_neg]

/-- **The X-degree budget is FALSE on the witness at the pinned `D = 2`** — the exact budget
hypothesis of `alphaGenuineRegularWeightLe_of_monic_natDegree_two_of_budget` fails at `t = 1`:
the forced preimage's canonical representative is `monomial 1 (−X)`, whose `Y¹`-coefficient has
`X`-degree `1`, so `(D+1−d_H) + 1 = 2 > 1`. -/
theorem witness_budget_refuted (hH : 0 < myH.natDegree) :
    ¬ (∀ t : ℕ, ∀ a : 𝒪 myH, embeddingOf𝒪Into𝕃 myH a = αGenuine myH 0 myR myHyp t →
        ((canonicalRepOf𝒪 hH a).coeff 0).natDegree ≤ 1
          ∧ (2 + 1 - Bivariate.natDegreeY myH)
              + ((canonicalRepOf𝒪 hH a).coeff 1).natDegree ≤ 1) := by
  intro hbudget
  obtain ⟨a, ha⟩ := alphaGenuine_regular_of_monic myH 0 myR myHyp
    (faaDiBrunoSuccSumZeroResidual_of_leadingCoeff_one myH 0 myR myHyp myH_leadingCoeff)
    myH_leadingCoeff 1
  obtain ⟨-, hb1⟩ := hbudget 1 a ha
  rw [alphaOne_preimage_forced hH a ha] at hb1
  have hdeg : (Polynomial.monomial 1 (-(Polynomial.X : K[X]))).degree
      < (H_tilde' myH).degree := by
    rw [BCIKS20.HenselNumerator.H_tilde'_eq_self_of_monic myH myH_leadingCoeff,
      Polynomial.degree_monomial 1 (by simp : (-(Polynomial.X : K[X])) ≠ 0),
      Polynomial.degree_eq_natDegree myH_ne_zero, myH_natDegree]
    decide
  rw [canonicalRepOf𝒪_mk_eq_self_of_degree_lt hH hdeg] at hb1
  have hnd : Bivariate.natDegreeY myH = 2 := myH_natDegree
  rw [hnd, Polynomial.coeff_monomial, if_pos rfl] at hb1
  simp only [Polynomial.natDegree_neg, Polynomial.natDegree_X] at hb1
  omega

/-- **The graded rescue is DEAD (packaged).**  On the `P1MonicWeightRefutation` witness, at the
unique admissible `D = 2` (`witness_D_pinned`): monicity, `totalDegree H ≤ D`,
`natDegree H ≤ D`, `2 ≤ natDegreeY R`, `totalDegree (evalX (C x₀) R) ≤ D` and the paper grading
`hRgrade` ALL hold — every graded hypothesis of `weight_βHensel_le_graded` /
`GSGradedBundle.GradedBundle` — and the X-degree budget still FAILS.  The budget is therefore
genuinely GS-geometric: it cannot be recovered from any in-tree graded structure on `R`. -/
theorem graded_rescue_dead (hH : 0 < myH.natDegree) :
    (myH.Monic
      ∧ Bivariate.totalDegree myH ≤ 2
      ∧ myH.natDegree ≤ 2
      ∧ 2 ≤ Bivariate.natDegreeY myR
      ∧ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C (0 : K)) myR) ≤ 2
      ∧ (∀ j, Bivariate.degreeX (myR.coeff j) ≤ 2 - j))
    ∧ ¬ (∀ t : ℕ, ∀ a : 𝒪 myH, embeddingOf𝒪Into𝕃 myH a = αGenuine myH 0 myR myHyp t →
        ((canonicalRepOf𝒪 hH a).coeff 0).natDegree ≤ 1
          ∧ (2 + 1 - Bivariate.natDegreeY myH)
              + ((canonicalRepOf𝒪 hH a).coeff 1).natDegree ≤ 1) :=
  ⟨⟨myH_monic, le_of_eq witness_totalDegree_H, le_of_eq myH_natDegree,
      le_of_eq witness_natDegreeY_R.symm, le_of_eq witness_totalDegree_evalX, witness_hRgrade⟩,
    witness_budget_refuted hH⟩

/-- Corollary (the invariant-native form of `weight_refuted`): the full
`AlphaGenuineRegularWeightLe` fails on the witness at `D = 2`, via the budget equivalence. -/
theorem witness_alphaWeightLe_refuted (hH : 0 < myH.natDegree) :
    ¬ AlphaWeight.AlphaGenuineRegularWeightLe myH 0 myR myHyp hH 2 := fun hα =>
  witness_budget_refuted hH
    ((alphaGenuineRegularWeightLe_iff_budget myH myHyp hH myH_leadingCoeff myH_natDegree
      (le_of_eq myH_natDegree.symm)).mp hα)

end ArkLib.XDegreeBudgetProbe

end

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.XDegreeBudgetProbe.natDegree_coeff_canonicalRep_le_of_weight_le
#print axioms ArkLib.XDegreeBudgetProbe.weight_le_one_iff_budget
#print axioms ArkLib.XDegreeBudgetProbe.alphaGenuineRegularWeightLe_iff_budget
#print axioms ArkLib.XDegreeBudgetProbe.myH_coeff
#print axioms ArkLib.XDegreeBudgetProbe.witness_totalDegree_H
#print axioms ArkLib.XDegreeBudgetProbe.witness_D_pinned
#print axioms ArkLib.XDegreeBudgetProbe.witness_totalDegree_evalX
#print axioms ArkLib.XDegreeBudgetProbe.witness_natDegreeY_R
#print axioms ArkLib.XDegreeBudgetProbe.liftCoeff_eq
#print axioms ArkLib.XDegreeBudgetProbe.liftCoeff_coeff
#print axioms ArkLib.XDegreeBudgetProbe.degreeX_liftCoeff_eq_one
#print axioms ArkLib.XDegreeBudgetProbe.myR_coeff
#print axioms ArkLib.XDegreeBudgetProbe.witness_hRgrade
#print axioms ArkLib.XDegreeBudgetProbe.witness_trivariate_grade
#print axioms ArkLib.XDegreeBudgetProbe.alphaOne_preimage_forced
#print axioms ArkLib.XDegreeBudgetProbe.witness_budget_refuted
#print axioms ArkLib.XDegreeBudgetProbe.graded_rescue_dead
#print axioms ArkLib.XDegreeBudgetProbe.witness_alphaWeightLe_refuted
