/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BetaWeightInduction

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

variable {F : Type} [Field F]

/-- **`betaRec_weight_le` with the telescoping hypothesis required only on NON-FORBIDDEN pairs**
(the forbidden `(i₁ = 0, parts = {s+1})` summand is `0`, so its budget is vacuous). This is the
form the graded App-A budgets satisfy: at `(i₁ = 0, σ = 1)` the only partition is the forbidden
one, where the graded arithmetic genuinely fails. -/
theorem betaRec_weight_le_excl (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    {bW bξ : ℕ} (bB : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → ℕ) (wβ : ℕ → ℕ)
    (hbW : weight_Λ_over_𝒪 hH (W_𝒪 H) D ≤ (WithBot.some bW : WithBot ℕ))
    (hbξ : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤ (WithBot.some bξ : WithBot ℕ))
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D ≤ (WithBot.some (bB i₁ p) : WithBot ℕ))
    (hβ0 : weight_Λ_over_𝒪 hH
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y]) : 𝒪 H) D
        ≤ (WithBot.some (wβ 0) : WithBot ℕ))
    (htele : ∀ s : ℕ, ∀ i₁ ∈ Finset.range (s + 2), ∀ p : Nat.Partition (s + 1 - i₁),
        ¬ (i₁ = 0 ∧ p.parts = ({s + 1} : Multiset ℕ)) →
        betaWExp i₁ * bW + betaξExp i₁ p * bξ + bB i₁ p
            + ∑ l ∈ p.parts.toFinset.attach, p.parts.count l.1 * wβ l.1
          ≤ wβ (s + 1)) :
    ∀ t : ℕ, weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D
      ≤ (WithBot.some (wβ t) : WithBot ℕ) := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    match t with
    | 0 =>
        rw [betaRec_zero]
        exact hβ0
    | (s + 1) =>
        -- Reduce to per-term budgets, each `≤ wβ (s+1)`, via the L7/L9 skeleton.
        refine betaRec_weightBound_of_term_bounds x₀ R H hHyp Bcoeff s hD hH ?_
        intro i₁ hi₁ p
        -- Split on the forbidden pair: the forbidden summand is `0` (weight `⊥`), trivially in
        -- budget; the genuine summand is bounded by `betaTerm_weight_le` + the `htele` collapse.
        by_cases hexcl : ¬ (i₁ = 0 ∧ p.parts = ({s + 1} : Multiset ℕ))
        · -- Genuine term: `recursionStep_lt` gives `l < s+1` for every part, so the IH applies.
          have hbβ : ∀ l ∈ p.parts.toFinset,
              weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff l) D
                ≤ (WithBot.some (wβ l) : WithBot ℕ) := by
            intro l hl
            exact IH l (recursionStep_lt p hexcl (Multiset.mem_toFinset.mp hl))
          refine le_trans
            (betaTerm_weight_le x₀ R H hHyp Bcoeff s i₁ p hD hH wβ hbW hbξ (hbB i₁ p) hbβ) ?_
          rw [WithBot.coe_le_coe]
          exact htele s i₁ hi₁ p hexcl
        · -- Forbidden pair: `betaTerm = 0`, weight `⊥ ≤ wβ (s+1)`.
          have hterm0 : betaTerm x₀ R H hHyp Bcoeff s i₁ p = 0 := by
            unfold betaTerm; rw [if_neg hexcl]
          rw [hterm0, weight_Λ_over_𝒪_zero' hH]
          exact bot_le


end ArkLib

#print axioms ArkLib.betaRec_weight_le_excl
