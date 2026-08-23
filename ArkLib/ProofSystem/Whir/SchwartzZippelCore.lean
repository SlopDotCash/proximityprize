/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.CheckedVerifier
import ArkLib.Data.Probability.MarginalBound

/-!
# The Schwartz–Zippel core for the WHIR checked verifier (#302)

The Schwartz–Zippel core for the WHIR checked verifier's sub-unit flip
bound — `listEval` is polynomial evaluation (Horner), so the salvage set
`{r | listEval cs r = listEval cs' r}` of a genuinely different coefficient list has at most
`max(len cs, len cs')` elements; hence the per-round flip probability over a uniform challenge
is at most `max-len / |F|`. -/

namespace Whir302SZ

open Polynomial

variable {F : Type} [Field F]

/-- The polynomial whose Horner evaluation is `listEval`. -/
noncomputable def listPoly (cs : List F) : F[X] :=
  cs.foldr (fun c acc => Polynomial.C c + Polynomial.X * acc) 0

theorem listPoly_eval (cs : List F) (x : F) :
    (listPoly cs).eval x = Whir302Checked.listEval cs x := by
  induction cs with
  | nil => simp [listPoly, Whir302Checked.listEval]
  | cons c cs ih =>
      simp [listPoly, Whir302Checked.listEval, List.foldr_cons] at ih ⊢
      rw [← ih]
      simp

theorem listPoly_cons (c : F) (cs : List F) :
    listPoly (c :: cs) = Polynomial.C c + Polynomial.X * listPoly cs := rfl

theorem listPoly_natDegree_lt (cs : List F) (h : cs ≠ []) :
    (listPoly cs).natDegree < cs.length := by
  induction cs with
  | nil => exact absurd rfl h
  | cons c cs ih =>
      rw [listPoly_cons, List.length_cons]
      refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
      rw [Polynomial.natDegree_C]
      rcases eq_or_ne (listPoly cs) 0 with h0 | h0
      · rw [h0, mul_zero, Polynomial.natDegree_zero]
        omega
      · have hcs : cs ≠ [] := by rintro rfl; exact h0 rfl
        have hb := Polynomial.natDegree_mul (p := (Polynomial.X : F[X]))
          (q := listPoly cs) Polynomial.X_ne_zero h0
        have hlt := ih hcs
        rw [hb, Polynomial.natDegree_X]
        omega

variable [Fintype F] [DecidableEq F]

/-- **The Schwartz–Zippel salvage bound for `listEval`** (the WHIR sumcheck flip event): if two
coefficient lists evaluate differently somewhere (the chains genuinely disagree), the set of
challenges where they agree has at most `max(len cs, len cs') − 1 < max len` elements; counted
against the full field. -/
theorem card_listEval_eq_le (cs cs' : List F)
    (hne : listPoly cs ≠ listPoly cs') (hcs : cs ≠ []) (hcs' : cs' ≠ []) :
    (Finset.univ.filter
        (fun r : F => Whir302Checked.listEval cs r = Whir302Checked.listEval cs' r)).card
      ≤ max cs.length cs'.length := by
  classical
  have hsub : Finset.univ.filter
      (fun r : F => Whir302Checked.listEval cs r = Whir302Checked.listEval cs' r)
      ⊆ (listPoly cs - listPoly cs').roots.toFinset := by
    intro r hr
    rw [Finset.mem_filter] at hr
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (sub_ne_zero.mpr hne)]
    rw [Polynomial.IsRoot, Polynomial.eval_sub, sub_eq_zero, listPoly_eval, listPoly_eval]
    exact hr.2
  calc (Finset.univ.filter _).card
      ≤ (listPoly cs - listPoly cs').roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (listPoly cs - listPoly cs').roots := Multiset.toFinset_card_le _
    _ ≤ (listPoly cs - listPoly cs').natDegree := Polynomial.card_roots' _
    _ ≤ max (listPoly cs).natDegree (listPoly cs').natDegree :=
        Polynomial.natDegree_sub_le _ _
    _ ≤ max cs.length cs'.length := by
        have h1 := listPoly_natDegree_lt cs hcs
        have h2 := listPoly_natDegree_lt cs' hcs'
        omega

end Whir302SZ

-- ## The probability-side accounting

section Probability

open OracleComp OracleSpec ProbabilityTheory
open scoped ENNReal NNReal

universe v

namespace Whir302SZ

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {β : Type} {m : Type → Type v} [Monad m] [HasEvalSPMF m]

/-- **The per-round salvage probability bound** (the quantitative WHIR flip estimate): in any
game that draws a challenge `r` whose marginal is dominated by uniform-on-`F` and then runs a
continuation whose success forces the salvage equation `listEval cs r = listEval cs' r` for two
genuinely different chains, the success probability is at most `max(len cs, len cs') / |F|`. -/
theorem probEvent_salvage_le (mx : m F) (k : F → m β) (q : β → Prop)
    (cs cs' : List F)
    (hne : listPoly cs ≠ listPoly cs') (hcs : cs ≠ []) (hcs' : cs' ≠ [])
    (hunif : ∀ x : F, Pr[= x | mx] ≤ (Fintype.card F : ℝ≥0∞)⁻¹)
    (hsalvage : ∀ x : F, ¬ (Whir302Checked.listEval cs x = Whir302Checked.listEval cs' x) →
      Pr[ q | k x] = 0) :
    Pr[ q | mx >>= k]
      ≤ ((max cs.length cs'.length : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  refine le_trans
    (probEvent_bind_le_uniform_marginal mx k q
      {x : F | Whir302Checked.listEval cs x = Whir302Checked.listEval cs' x}
      hunif hsalvage) ?_
  apply ENNReal.div_le_div_right
  have hcard := card_listEval_eq_le cs cs' hne hcs hcs'
  have hfilter : (Finset.univ.filter
        (· ∈ {x : F | Whir302Checked.listEval cs x = Whir302Checked.listEval cs' x}))
      = (Finset.univ.filter
        (fun r : F => Whir302Checked.listEval cs r = Whir302Checked.listEval cs' r)) := by
    apply Finset.filter_congr
    intro x _
    simp [Set.mem_setOf_eq]
  rw [hfilter]
  exact_mod_cast hcard

end Whir302SZ

end Probability

#print axioms Whir302SZ.listPoly_eval
#print axioms Whir302SZ.listPoly_natDegree_lt
#print axioms Whir302SZ.card_listEval_eq_le
#print axioms Whir302SZ.probEvent_salvage_le
