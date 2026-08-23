/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BetaWeightGradedSupply
import ArkLib.ToMathlib.BetaRecGenuineBridge

/-!
# Issue #304 — the graded App-A.4 weight collapse WITHOUT the monic hypothesis

The graded weight collapse for the `(A.1)` recursion capsule
(`betaRec_weight_le_graded`, `betaRec_weight_le_graded_of_budget`,
`GenuineMonicCapstone.betaRec_weight_le_graded_signed`) was proven under `H.Monic`, used in
exactly ONE place: the `hbW` budget, where monicity gives `W_𝒪 H = 1` and hence the trivial
`Λ`-weight budget `bW = 0` (`W𝒪_weight_le_zero_of_monic`).

But the analytic chain never needs `W = 1`: the rings `𝒪 H`/`𝕃 H` are built on the
**already-monicized** `H_tilde' H`/`H_tilde H` (`RationalFunctionsCore`), and every other
collapse input (`weight_ξ_bound`, `B_coeff_weight_le_graded`, `weight_mk_X_le`, the
`GradedHtele` telescoping) is monicity-free.  For general `H` the honest `W`-budget is the
CONSTANT

  `bW = (H.leadingCoeff).natDegree`  (the `X`-degree of the leading `Y`-coefficient `W`),

since `W_𝒪 H = mk (C H.leadingCoeff)` and constants weigh their `F[X]`-degree
(`weight_Λ_over_𝒪_C_le`).  Because `betaRec_weight_le_excl` is **parametric in `bW`**, the
graded collapse re-runs with the slack slope bumped by exactly that constant:

  `wβ t = (d·A + D + A + L)·(2t − 1) + A`,  `L = (H.leadingCoeff).natDegree`,

using the per-term `W`-exponent bound `betaWExp i₁ ≤ 2i₁ + σ − 1` (valid on every
non-forbidden `(i₁, λ)` pair).  At monic `H` we have `L = 0` and the original budgets are
recovered verbatim (`betaRec_weight_le_graded_of_budget_of_monic_recovered`), so this file
strictly generalizes the monic collapse — **the monic hypothesis is eliminated from the
weight/cardinality lane entirely**.  Downstream, the discriminant-supplied `hcardFin`
producers are rebuilt at the bumped budget (`gradedCardBudgetW`,
`gradedConcreteFinW_of_disc`, `hcardFin_of_graded_nonmonic`,
`hcardFin_of_graded_signed_nonmonic`), so the off-centre §5 bundle's cardinality front no
longer requires monic `H`.  (The remaining monic-only lane is the *identity* front
`gammaLocal = gammaGenuine` of `BetaRecGenuineBridge` — a separate, genuinely deep core.)

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, Appendix A.1 (monicization `H̃`), A.2 (weight `Λ`), A.4 (recursion `(A.1)`).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace NonmonicWeight

variable {F : Type} [Field F]

/-! ## Part 0 — the non-monic `W`-budget and the `W`-exponent bound -/

/-- **The non-monic `W`-budget**: `Λ_𝒪(W) ≤ (H.leadingCoeff).natDegree`, unconditionally.
`W_𝒪 H = mk (C H.leadingCoeff)` and constants weigh their `F[X]`-degree.  At monic `H` this
recovers the `bW = 0` budget (`natDegree 1 = 0`). -/
lemma W_𝒪_weight_le_natDegree_leadingCoeff {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    weight_Λ_over_𝒪 hH (W_𝒪 H) D
      ≤ (WithBot.some (H.leadingCoeff).natDegree : WithBot ℕ) :=
  weight_Λ_over_𝒪_C_le hD hH H.leadingCoeff

/-- The `(A.1)` `W`-exponent obeys `betaWExp i₁ ≤ 2i₁ + σ − 1` whenever `σ ≥ 1`
(`betaWExp 0 = 0 ≤ σ − 1`; `betaWExp i₁ = i₁ − 1` for `i₁ ≥ 1`). -/
lemma betaWExp_le_of_card_pos {i₁ σ : ℕ} (hσ1 : 1 ≤ σ) :
    betaWExp i₁ ≤ 2 * i₁ + σ - 1 := by
  simp only [betaWExp, betaδ]
  split_ifs with h0 <;> omega

/-! ## Part 1 — the budget-abstracted graded collapse, non-monic -/

/-- **The graded weight theorem WITHOUT monicity, budget-abstracted.**  Identical to
`betaRec_weight_le_graded_of_budget` except: the `hmonic` hypothesis is GONE, and the slack
slope is bumped by the constant `L = (H.leadingCoeff).natDegree` (the honest non-monic
`W`-budget).  At monic `H`, `L = 0` and the original statement is recovered. -/
theorem betaRec_weight_le_graded_of_budget_nonmonic (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D
          ≤ (WithBot.some ((Bivariate.natDegreeY R - Multiset.card p.parts)
              * (D - H.natDegree + 1) + (D - Multiset.card p.parts)) : WithBot ℕ)) :
    ∀ t : ℕ, weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D
      ≤ (WithBot.some
          ((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1)
              + (H.leadingCoeff).natDegree)
              * (2 * t - 1)
            + (D - H.natDegree + 1)) : WithBot ℕ) := by
  classical
  set d := Bivariate.natDegreeY R with hd
  set A := D - H.natDegree + 1 with hA
  set L := (H.leadingCoeff).natDegree with hL
  set α := d * A + D + A with hα
  refine betaRec_weight_le_excl x₀ R H hHyp Bcoeff
    hD hH (bW := L) (bξ := (d - 1) * A)
    (bB := fun i₁ {m} p => (d - Multiset.card p.parts) * A + (D - Multiset.card p.parts))
    (wβ := fun t => (α + L) * (2 * t - 1) + A) ?_ ?_ ?_ ?_ ?_
  · -- hbW: the NON-monic `W`-budget
    rw [hL]
    exact W_𝒪_weight_le_natDegree_leadingCoeff hD hH
  · -- hbξ via weight_ξ_bound (monicity-free)
    have h := weight_ξ_bound (H := H) (R := R) x₀ hH hHyp hd2 hD hD_Rx0
    have hbridge : (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)
        = (d - 1) * A := by
      have : Bivariate.natDegreeY H = H.natDegree := rfl
      rw [this, ← hd, ← hA]
    rwa [hbridge] at h
  · -- hbB: the abstract budget hypothesis
    intro i₁ m p
    exact hbB i₁ p
  · -- hβ0: weight(mk X) ≤ wβ 0 = (α+L)·0 + A = A
    have h := weight_mk_X_le (H := H) hD hH hdHD
    simpa [← hA] using h
  · -- htele (non-forbidden), with the extra `betaWExp·L` column
    intro s i₁ hi₁ p hexcl
    have hi₁' : i₁ < s + 2 := Finset.mem_range.mp hi₁
    beta_reduce
    rw [partsCount_affine_sum p (α + L) A,
      show betaξExp i₁ p = 2 * i₁ + Multiset.card p.parts - 2 from rfl]
    set σ := Multiset.card p.parts with hσ
    rcases Nat.eq_zero_or_pos σ with hσ0 | hσ1
    · -- empty partition: m = 0, i₁ = s+1, betaWExp = s
      have hcard0 : Multiset.card p.parts = 0 := by rw [← hσ]; exact hσ0
      have hp0 : p.parts = 0 := Multiset.card_eq_zero.mp hcard0
      have hm0 : s + 1 - i₁ = 0 := by
        have hps := p.parts_sum
        rw [hp0] at hps
        simp at hps
        omega
      have hi : i₁ = s + 1 := by omega
      rw [hσ0, hm0]
      simp only [Nat.sub_zero, mul_zero, add_zero]
      rw [show 2 * i₁ - 2 = 2 * s from by omega]
      have hWe : betaWExp i₁ = s := by
        simp only [betaWExp, betaδ]
        rw [if_neg (by omega : ¬ i₁ = 0)]
        omega
      rw [hWe]
      have h1 : 2 * s * ((d - 1) * A) + (d * A + D) ≤ α * (2 * s) + α := by
        have hα_ge : d * A ≤ α := by rw [hα]; omega
        have h2 : 2 * s * ((d - 1) * A) ≤ α * (2 * s) := by
          calc 2 * s * ((d - 1) * A)
              ≤ 2 * s * (d * A) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_right A (Nat.sub_le d 1))
            _ ≤ 2 * s * α := Nat.mul_le_mul_left _ hα_ge
            _ = α * (2 * s) := Nat.mul_comm _ _
        have h3 : d * A + D ≤ α := by rw [hα]; omega
        omega
      have h2 : s * L ≤ L * (2 * s + 1) := by
        calc s * L ≤ (2 * s + 1) * L := Nat.mul_le_mul_right L (by omega)
          _ = L * (2 * s + 1) := Nat.mul_comm _ _
      calc s * L + 2 * s * ((d - 1) * A) + (d * A + D)
          = s * L + (2 * s * ((d - 1) * A) + (d * A + D)) := Nat.add_assoc _ _ _
        _ ≤ L * (2 * s + 1) + (α * (2 * s) + α) := Nat.add_le_add h2 h1
        _ = (α + L) * (2 * s + 1) := by ring
        _ ≤ (α + L) * (2 * (s + 1) - 1) + A := by
            rw [show 2 * (s + 1) - 1 = 2 * s + 1 from by omega]
            exact Nat.le_add_right _ _
    · -- σ ≥ 1: graded_htele_arith + the W-exponent bound betaWExp ≤ 2i₁+σ−1
      have hexcl' : ¬(i₁ = 0 ∧ σ = 1) := by
        rintro ⟨hi0, hσ1'⟩
        apply hexcl
        refine ⟨hi0, ?_⟩
        obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp (hσ ▸ hσ1')
        have hsum := p.parts_sum
        rw [ha] at hsum ⊢
        simp at hsum
        rw [hsum]
        subst hi0
        norm_num
      have harith := GradedHtele.graded_htele_arith d D H.natDegree
        (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hH)) (by omega) hdHD
        i₁ σ hσ1 hexcl'
      have hσm : σ ≤ s + 1 - i₁ := by
        rw [hσ]
        exact betaRec_card_le p
      have hkey : 2 * i₁ + σ - 1 + (2 * (s + 1 - i₁) - σ) = 2 * s + 1 := by omega
      have hWL : betaWExp i₁ * L ≤ L * (2 * i₁ + σ - 1) := by
        calc betaWExp i₁ * L
            ≤ (2 * i₁ + σ - 1) * L := Nat.mul_le_mul_right L (betaWExp_le_of_card_pos hσ1)
          _ = L * (2 * i₁ + σ - 1) := Nat.mul_comm _ _
      calc betaWExp i₁ * L + (2 * i₁ + σ - 2) * ((d - 1) * A)
            + ((d - σ) * A + (D - σ))
            + ((α + L) * (2 * (s + 1 - i₁) - σ) + A * σ)
          = betaWExp i₁ * L
            + (((2 * i₁ + σ - 2) * ((d - 1) * (D - H.natDegree + 1))
                + ((d - σ) * (D - H.natDegree + 1) + (D - σ))
                + (D - H.natDegree + 1) * σ)
              + (α + L) * (2 * (s + 1 - i₁) - σ)) := by
            rw [← hA]; ring
        _ ≤ L * (2 * i₁ + σ - 1)
            + (((d * (D - H.natDegree + 1) + D + (D - H.natDegree + 1)) * (2 * i₁ + σ - 1)
                + (D - H.natDegree + 1))
              + (α + L) * (2 * (s + 1 - i₁) - σ)) :=
            Nat.add_le_add hWL (Nat.add_le_add_right harith _)
        _ = (α + L) * (2 * i₁ + σ - 1) + (α + L) * (2 * (s + 1 - i₁) - σ) + A := by
            rw [hα, hA]; ring
        _ = (α + L) * ((2 * i₁ + σ - 1) + (2 * (s + 1 - i₁) - σ)) + A := by ring
        _ = (α + L) * (2 * s + 1) + A := by rw [hkey]
        _ = (α + L) * (2 * (s + 1) - 1) + A := by
            rw [show (2 * (s + 1) - 1 : ℕ) = 2 * s + 1 from by omega]

/-! ## Part 2 — instantiations: the canonical and signed families -/

/-- **The non-monic graded collapse at the canonical Faà-di-Bruno family `B_coeff`** (the
analogue of `betaRec_weight_le_graded`, monicity eliminated): the per-coefficient budget is
discharged by the monicity-free `B_coeff_weight_le_graded`. -/
theorem betaRec_weight_le_graded_nonmonic (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j) :
    ∀ t : ℕ, weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp (BCIKS20.HenselNumerator.B_coeff H x₀ R) t) D
      ≤ (WithBot.some
          ((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1)
              + (H.leadingCoeff).natDegree)
              * (2 * t - 1)
            + (D - H.natDegree + 1)) : WithBot ℕ) := by
  refine betaRec_weight_le_graded_of_budget_nonmonic x₀ R H hHyp
    (BCIKS20.HenselNumerator.B_coeff H x₀ R) hD hH hd2 hdHD hD_Rx0 ?_
  intro i₁ m p
  have h := BCIKS20.HenselNumerator.B_coeff_weight_le_graded (H := H) x₀ R i₁ p hH hD hR
  have hbridge : (Bivariate.natDegreeY R - BCIKS20.HenselNumerator.sigmaLambda p)
        * (D + 1 - Bivariate.natDegreeY H)
        + (D - BCIKS20.HenselNumerator.sigmaLambda p)
      = (Bivariate.natDegreeY R - Multiset.card p.parts) * (D - H.natDegree + 1)
        + (D - Multiset.card p.parts) := by
    have h1 : Bivariate.natDegreeY H = H.natDegree := rfl
    have h2 : BCIKS20.HenselNumerator.sigmaLambda p = Multiset.card p.parts := rfl
    have h3 : D + 1 - H.natDegree = D - H.natDegree + 1 := by omega
    rw [h1, h2, h3]
  rwa [hbridge] at h

/-- **The non-monic graded collapse at the signed canonical family `BcoeffSigned`** (the
analogue of `GenuineMonicCapstone.betaRec_weight_le_graded_signed`, monicity eliminated): the
budget transports through negation-invariance of the `Λ`-weight. -/
theorem betaRec_weight_le_graded_signed_nonmonic (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j) :
    ∀ t : ℕ, weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t) D
      ≤ (WithBot.some
          ((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1)
              + (H.leadingCoeff).natDegree)
              * (2 * t - 1)
            + (D - H.natDegree + 1)) : WithBot ℕ) := by
  refine betaRec_weight_le_graded_of_budget_nonmonic x₀ R H hHyp
    (BetaRecGenuineBridge.BcoeffSigned H x₀ R) hD hH hd2 hdHD hD_Rx0 ?_
  intro i₁ m p
  have hneg : weight_Λ_over_𝒪 hH (BetaRecGenuineBridge.BcoeffSigned H x₀ R i₁ p) D
      = weight_Λ_over_𝒪 hH (BCIKS20.HenselNumerator.B_coeff H x₀ R i₁ p) D := by
    rw [BetaRecGenuineBridge.BcoeffSigned_apply, weight_Λ_over_𝒪_neg]
  rw [hneg]
  have h := BCIKS20.HenselNumerator.B_coeff_weight_le_graded (H := H) x₀ R i₁ p hH hD hR
  have hbridge : (Bivariate.natDegreeY R - BCIKS20.HenselNumerator.sigmaLambda p)
        * (D + 1 - Bivariate.natDegreeY H)
        + (D - BCIKS20.HenselNumerator.sigmaLambda p)
      = (Bivariate.natDegreeY R - Multiset.card p.parts) * (D - H.natDegree + 1)
        + (D - Multiset.card p.parts) := by
    have h1 : Bivariate.natDegreeY H = H.natDegree := rfl
    have h2 : BCIKS20.HenselNumerator.sigmaLambda p = Multiset.card p.parts := rfl
    have h3 : D + 1 - H.natDegree = D - H.natDegree + 1 := by omega
    rw [h1, h2, h3]
  rwa [hbridge] at h

/-! ## Part 3 — the monic case is recovered (consistency: this is a strict generalization) -/

/-- At monic `H` the non-monic `W`-budget constant vanishes: `L = natDegree 1 = 0`. -/
lemma natDegree_leadingCoeff_eq_zero_of_monic {H : F[X][Y]} (hmonic : H.Monic) :
    (H.leadingCoeff).natDegree = 0 := by
  rw [Polynomial.Monic.leadingCoeff hmonic]
  exact Polynomial.natDegree_one

/-- **Consistency**: the monic budget-abstracted collapse
(`betaRec_weight_le_graded_of_budget`'s statement) is recovered verbatim from the non-monic
theorem at `L = 0` — the generalization is strict, not a re-parameterization. -/
theorem betaRec_weight_le_graded_of_budget_of_monic_recovered
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D
          ≤ (WithBot.some ((Bivariate.natDegreeY R - Multiset.card p.parts)
              * (D - H.natDegree + 1) + (D - Multiset.card p.parts)) : WithBot ℕ)) :
    ∀ t : ℕ, weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D
      ≤ (WithBot.some
          ((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
              * (2 * t - 1)
            + (D - H.natDegree + 1)) : WithBot ℕ) := by
  intro t
  have h := betaRec_weight_le_graded_of_budget_nonmonic x₀ R H hHyp Bcoeff
    hD hH hd2 hdHD hD_Rx0 hbB t
  rwa [natDegree_leadingCoeff_eq_zero_of_monic hmonic, Nat.add_zero] at h

/-! ## Part 4 — the non-monic `hcardFin` production chain (discriminant-supplied) -/

/-- Right-multiplication monotonicity for `WithBot ℕ` weight bounds (local copy of the
private `BetaWeightGradedSupply` helper). -/
private theorem withBot_mul_right_le''' {a : WithBot ℕ} {c e : ℕ}
    (h : a ≤ (c : WithBot ℕ)) : a * (e : WithBot ℕ) ≤ ((c * e : ℕ) : WithBot ℕ) := by
  have hce : ((c * e : ℕ) : WithBot ℕ) = (c : WithBot ℕ) * (e : WithBot ℕ) := by
    push_cast; ring
  rw [hce]
  gcongr

/-- The non-monic graded cardinality budget at index `t`: the monic `gradedCardBudget` with the
slope bumped by the `W`-budget constant `L`.  `gradedCardBudgetW dY D dH 0 = gradedCardBudget`
(see `gradedCardBudgetW_zero`). -/
def gradedCardBudgetW (dY D dH L t : ℕ) : ℕ :=
  ((dY * (D - dH + 1) + D + (D - dH + 1) + L) * (2 * t - 1) + (D - dH + 1)) * dH

/-- At `L = 0` the non-monic budget is the monic one. -/
lemma gradedCardBudgetW_zero (dY D dH t : ℕ) :
    gradedCardBudgetW dY D dH 0 t = gradedCardBudget dY D dH t := by
  simp [gradedCardBudgetW, gradedCardBudget]

/-- The non-monic graded budget is monotone in `t`. -/
lemma gradedCardBudgetW_mono (dY D dH L : ℕ) {t T : ℕ} (h : t ≤ T) :
    gradedCardBudgetW dY D dH L t ≤ gradedCardBudgetW dY D dH L T := by
  unfold gradedCardBudgetW
  have h1 : 2 * t - 1 ≤ 2 * T - 1 := by omega
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ h1) _)

section Discriminant

variable [Fintype F] [DecidableEq F]

/-- **The discriminant-supplied non-monic graded cardinality family.**  As
`gradedConcreteFin_of_disc`, at the bumped budget `gradedCardBudgetW`. -/
theorem gradedConcreteFinW_of_disc {disc : F[X]} (hdisc : disc ≠ 0)
    {matchingSet : Finset F}
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    {dY D dH L k T : ℕ}
    (hbig : gradedCardBudgetW dY D dH L T + disc.natDegree < Fintype.card F) :
    ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > ((((dY * (D - dH + 1) + D + (D - dH + 1) + L) * (2 * t - 1)
            + (D - dH + 1)) * dH : ℕ) : WithBot ℕ) := by
  intro t _hkt htT
  have hT : gradedCardBudgetW dY D dH L T < matchingSet.card :=
    ArkLib.Match304.card_matching_gt_of_disc hdisc hcover hbig
  have ht : gradedCardBudgetW dY D dH L t < matchingSet.card :=
    lt_of_le_of_lt (gradedCardBudgetW_mono dY D dH L htT) hT
  have : (gradedCardBudgetW dY D dH L t : WithBot ℕ) < (matchingSet.card : WithBot ℕ) := by
    exact_mod_cast ht
  simpa [gradedCardBudgetW] using this

end Discriminant

/-- **The non-monic finite-range `hcardFin` family at the canonical family `B_coeff`.**  As
`hcardFin_of_graded` with the monic hypothesis ELIMINATED (budget bumped by
`L = (H.leadingCoeff).natDegree`). -/
theorem hcardFin_of_graded_nonmonic (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    {D k T : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {matchingSet : Finset F}
    (hconcreteFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > ((((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1)
                + (H.leadingCoeff).natDegree)
                * (2 * t - 1)
              + (D - H.natDegree + 1)) * H.natDegree : ℕ) : WithBot ℕ)) :
    ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH
          (betaRec x₀ R H hHyp (BCIKS20.HenselNumerator.B_coeff H x₀ R) t) D
        * H.natDegree := by
  intro t hkt htT
  have hwt := betaRec_weight_le_graded_nonmonic x₀ R H hHyp hD hH hd2 hdHD hD_Rx0 hR t
  have hmul : weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp (BCIKS20.HenselNumerator.B_coeff H x₀ R) t) D
        * (H.natDegree : WithBot ℕ)
      ≤ ((((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1)
              + (H.leadingCoeff).natDegree)
              * (2 * t - 1)
            + (D - H.natDegree + 1)) * H.natDegree : ℕ) : WithBot ℕ) :=
    withBot_mul_right_le''' (by simpa using hwt)
  exact lt_of_le_of_lt hmul (hconcreteFin t hkt htT)

/-- **The non-monic finite-range `hcardFin` family at the signed canonical family
`BcoeffSigned`** — the exact `hcardFin` shape consumed by the off-centre §5 bundle producer
(`section5DataOffcentreFin_of_producers`), with the monic hypothesis ELIMINATED. -/
theorem hcardFin_of_graded_signed_nonmonic (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    {D k T : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {matchingSet : Finset F}
    (hconcreteFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > ((((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1)
                + (H.leadingCoeff).natDegree)
                * (2 * t - 1)
              + (D - H.natDegree + 1)) * H.natDegree : ℕ) : WithBot ℕ)) :
    ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH
          (betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t) D
        * H.natDegree := by
  intro t hkt htT
  have hwt := betaRec_weight_le_graded_signed_nonmonic x₀ R H hHyp hD hH hd2 hdHD hD_Rx0 hR t
  have hmul : weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t) D
        * (H.natDegree : WithBot ℕ)
      ≤ ((((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1)
              + (H.leadingCoeff).natDegree)
              * (2 * t - 1)
            + (D - H.natDegree + 1)) * H.natDegree : ℕ) : WithBot ℕ) :=
    withBot_mul_right_le''' (by simpa using hwt)
  exact lt_of_le_of_lt hmul (hconcreteFin t hkt htT)

end NonmonicWeight

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.NonmonicWeight.W_𝒪_weight_le_natDegree_leadingCoeff
#print axioms ArkLib.NonmonicWeight.betaWExp_le_of_card_pos
#print axioms ArkLib.NonmonicWeight.betaRec_weight_le_graded_of_budget_nonmonic
#print axioms ArkLib.NonmonicWeight.betaRec_weight_le_graded_nonmonic
#print axioms ArkLib.NonmonicWeight.betaRec_weight_le_graded_signed_nonmonic
#print axioms ArkLib.NonmonicWeight.natDegree_leadingCoeff_eq_zero_of_monic
#print axioms ArkLib.NonmonicWeight.betaRec_weight_le_graded_of_budget_of_monic_recovered
#print axioms ArkLib.NonmonicWeight.gradedCardBudgetW_zero
#print axioms ArkLib.NonmonicWeight.gradedCardBudgetW_mono
#print axioms ArkLib.NonmonicWeight.gradedConcreteFinW_of_disc
#print axioms ArkLib.NonmonicWeight.hcardFin_of_graded_nonmonic
#print axioms ArkLib.NonmonicWeight.hcardFin_of_graded_signed_nonmonic
