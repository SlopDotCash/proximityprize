/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupSoundnessClose

/-!
# LogUp outer soundness: the SHARP (support-cleared) check polynomial (issue #13)

## The finding: the cleared-over-`univ` check polynomial has spurious roots

`grandSumCheckPoly` (`SoundnessConverse.lean`) clears the grand-sum denominators over **all** of
`F`: `P = ∑_{a : F} C (c a) · ∏_{b ∈ univ.erase a} (X + C b)`.  Evaluating at `x = -b₀` kills every
summand with `a ≠ b₀` (the factor `X + C b₀` vanishes), leaving `c b₀ · ∏_{b ≠ b₀} (b - b₀)`.
Hence `P(-b₀) = 0` for **every** `b₀ outside the support of `c`** — that is, `|F| - |supp c|`
*spurious* roots that do not witness the grand-sum identity at all
(`grandSumCheckPoly_eval_neg_of_coeff_eq_zero` below).  Consequently, for a bad lookup the language
`midSoundnessLanguage oStmt = {x | P(x) = 0}` is hit by a uniform challenge with probability at
least `(|F| - |supp c|)/|F| ≈ 1` (`prob_midSoundnessLanguage_ge_compl_support`) — far above the
paper budget `outerSoundnessError`.  The corrected outer-soundness obligation `hOuter` over
`midSoundnessProtocolLanguage` is therefore **unsatisfiable in the typical regime** as currently
stated: the degenerate-language bug of the original `midLanguage` recurs one level down, caused by
clearing denominators over `univ` instead of over the poles.

## The repair: clear over the support only

`grandSumCheckPolyS` clears the denominators over the **support** `checkSupport oStmt` only:

`P_S = ∑_{a ∈ S} C (c a) · ∏_{b ∈ S.erase a} (X + C b)`, where `S = {a | c a ≠ 0}`.

* `grandSumCheckPoly_eq_polyS_mul_compl` — the exact factorization
  `P = P_S · ∏_{b ∉ S} (X + C b)`: the spurious roots are precisely the cofactor's roots.
* `grandSumCheckPolyS_ne_zero_of_bad_lookup` — a bad lookup still forces `P_S ≠ 0` (same
  uncancelled-residue argument, now inside `S`).
* `checkSupport_card_le` — `|S| ≤ M · 2ⁿ` (each support value carries at least one lookup entry,
  and there are `M · 2ⁿ` entries in total).
* `grandSumCheckPolyS_natDegree_le` — `natDegree P_S ≤ |S| - 1 ≤ M · 2ⁿ - 1`: the **paper**
  degree, replacing the useless `|F| - 1` bound of the unrestricted clearing.
* `outerSoundness_sharp` — Schwartz–Zippel at the paper budget: for a bad lookup, a uniform
  challenge lands in the sharp language `midSoundnessLanguageSharp oStmt = {x | P_S(x) = 0}` with
  probability at most `(M · 2ⁿ - 1)/|F|`.
* `sharp_error_le_outerSoundnessError` — `(M · 2ⁿ - 1)/|F| ≤ outerSoundnessError F n M params`
  whenever `2ⁿ < |F|`: the sharp Schwartz–Zippel error fits inside the paper-shaped outer error.
* `outerSoundness_sharp_le_outerSoundnessError` — the headline composition: the sharp-language
  bad-accept marginal is bounded by `outerSoundnessError` itself.

The protocol-level intermediate language for the soundness composition should therefore be
`midSoundnessProtocolLanguageSharp` (defined below by pulling `midSoundnessLanguageSharp` back
through the carried `xChallenge`, exactly as `midSoundnessProtocolLanguage` does for the
unrestricted-clearing language).  The language-generic composition front door
`logup_soundness_msgSeam_anyMid` (`LogupSoundnessMsgSeam.lean`) accepts it directly.
-/

open scoped NNReal ENNReal
open Polynomial Finset ProbabilityTheory

namespace Logup

section OuterSoundnessSharp

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M : ℕ}

/-! ### The check coefficient and its support -/

/-- The grand-sum check coefficient at value `a`: the lookup-column count on values absent from
the table, `0` on table values.  This is exactly the coefficient `grandSumCheckPoly` carries at
`a` (definitional). -/
noncomputable def checkCoeff (oStmt : ∀ i, OStmtIn F n M i) (a : F) : F :=
  if tableMultiplicityCount oStmt a = 0 then (lookupMultiplicityCount oStmt a : F) else 0

/-- The (finite) support of the check coefficients. -/
noncomputable def checkSupport (oStmt : ∀ i, OStmtIn F n M i) : Finset F :=
  Finset.univ.filter (fun a => checkCoeff oStmt a ≠ 0)

theorem mem_checkSupport_iff (oStmt : ∀ i, OStmtIn F n M i) (a : F) :
    a ∈ checkSupport oStmt ↔ checkCoeff oStmt a ≠ 0 := by
  simp [checkSupport]

/-! ### The spurious roots of the unrestricted clearing -/

/-- **Spurious vanishing.** The cleared-over-`univ` check polynomial vanishes at `-b₀` for *every*
`b₀` outside the coefficient support: only the `a = b₀` summand survives the evaluation, and its
coefficient is `0`. -/
theorem grandSumCheckPoly_eval_neg_of_coeff_eq_zero (oStmt : ∀ i, OStmtIn F n M i)
    (b₀ : F) (h : checkCoeff oStmt b₀ = 0) :
    (grandSumCheckPoly oStmt).eval (-b₀) = 0 := by
  rw [eval_grandSumCheckPoly]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  by_cases hab : a = b₀
  · subst hab
    rw [show (if tableMultiplicityCount oStmt a = 0
        then (lookupMultiplicityCount oStmt a : F) else 0) = 0 from h, zero_mul]
  · exact mul_eq_zero_of_right _
      (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b₀⟩)
        (neg_add_cancel b₀))

/-- Every `-b₀` with `b₀` outside the support lies in `midSoundnessLanguage` — the spurious
members of the unrestricted-clearing language. -/
theorem neg_mem_midSoundnessLanguage_of_not_mem_checkSupport (oStmt : ∀ i, OStmtIn F n M i)
    (b₀ : F) (h : b₀ ∉ checkSupport oStmt) :
    -b₀ ∈ midSoundnessLanguage oStmt := by
  have hc : checkCoeff oStmt b₀ = 0 := by
    by_contra hne
    exact h ((mem_checkSupport_iff oStmt b₀).mpr hne)
  exact grandSumCheckPoly_eval_neg_of_coeff_eq_zero oStmt b₀ hc

/-- **Quantitative refutation of the unrestricted-clearing language.**  A uniform challenge lands
in `midSoundnessLanguage oStmt` with probability at least `(|F| - |supp|)/|F|` — for a typical bad
lookup (small support) this is `≈ 1`, far above `outerSoundnessError`.  Hence the protocol-level
outer-soundness obligation stated over `midSoundnessProtocolLanguage` is unsatisfiable in the
typical regime, and the soundness composition must use the *sharp* language below instead. -/
theorem prob_midSoundnessLanguage_ge_compl_support (oStmt : ∀ i, OStmtIn F n M i) :
    (((Fintype.card F - (checkSupport oStmt).card : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0∞)
      ≤ Pr_{ let x ←$ᵖ F }[ x ∈ midSoundnessLanguage oStmt ] := by
  classical
  rw [prob_uniform_eq_card_filter_div_card]
  have hsub : ((Finset.univ \ checkSupport oStmt).image (fun b => -b))
      ⊆ Finset.univ.filter (fun x : F => x ∈ midSoundnessLanguage oStmt) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨b₀, hb₀, rfl⟩ := hx
    rw [Finset.mem_sdiff] at hb₀
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      neg_mem_midSoundnessLanguage_of_not_mem_checkSupport oStmt b₀ hb₀.2⟩
  have hcard : Fintype.card F - (checkSupport oStmt).card
      ≤ (Finset.univ.filter (fun x : F => x ∈ midSoundnessLanguage oStmt)).card := by
    calc Fintype.card F - (checkSupport oStmt).card
        = (Finset.univ \ checkSupport oStmt).card := (Finset.card_univ_diff _).symm
      _ = ((Finset.univ \ checkSupport oStmt).image (fun b => -b)).card := by
          rw [Finset.card_image_of_injective _ neg_injective]
      _ ≤ _ := Finset.card_le_card hsub
  gcongr

/-! ### The sharp (support-cleared) check polynomial -/

/-- The **sharp** grand-sum check polynomial: denominators cleared over the support only.
Its degree is bounded by the paper quantity `|supp| - 1 ≤ M · 2ⁿ - 1`, and (unlike the
unrestricted clearing) it has no spurious roots: `P = P_S · ∏_{b ∉ supp} (X + C b)`. -/
noncomputable def grandSumCheckPolyS (oStmt : ∀ i, OStmtIn F n M i) : Polynomial F :=
  ∑ a ∈ checkSupport oStmt,
    Polynomial.C (checkCoeff oStmt a) *
      ∏ b ∈ (checkSupport oStmt).erase a, (Polynomial.X + Polynomial.C b)

/-- **Factorization.** The unrestricted clearing is the sharp polynomial times the product of the
spurious linear factors. -/
theorem grandSumCheckPoly_eq_polyS_mul_compl (oStmt : ∀ i, OStmtIn F n M i) :
    grandSumCheckPoly oStmt =
      grandSumCheckPolyS oStmt *
        ∏ b ∈ Finset.univ \ checkSupport oStmt, (Polynomial.X + Polynomial.C b) := by
  classical
  have hLHS : grandSumCheckPoly oStmt =
      ∑ a ∈ checkSupport oStmt,
        Polynomial.C (checkCoeff oStmt a) *
          ∏ b ∈ Finset.univ.erase a, (Polynomial.X + Polynomial.C b) := by
    unfold grandSumCheckPoly
    refine (Finset.sum_subset (Finset.subset_univ (checkSupport oStmt)) ?_).symm
    intro a _ ha
    have hc : checkCoeff oStmt a = 0 := by
      by_contra hne
      exact ha ((mem_checkSupport_iff oStmt a).mpr hne)
    rw [show (if tableMultiplicityCount oStmt a = 0
        then (lookupMultiplicityCount oStmt a : F) else 0) = 0 from hc]
    rw [Polynomial.C_0, zero_mul]
  rw [hLHS]
  unfold grandSumCheckPolyS
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have hsplit : Finset.univ.erase a =
      (checkSupport oStmt).erase a ∪ (Finset.univ \ checkSupport oStmt) := by
    ext b
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_sdiff,
      true_and]
    constructor
    · intro hb
      by_cases hbS : b ∈ checkSupport oStmt
      · exact Or.inl ⟨hb, hbS⟩
      · exact Or.inr hbS
    · rintro (⟨hba, _⟩ | hbS)
      · exact hba
      · intro hEq
        exact hbS (hEq ▸ ha)
  have hdisj : Disjoint ((checkSupport oStmt).erase a) (Finset.univ \ checkSupport oStmt) := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    exact (Finset.mem_sdiff.mp hb').2 (Finset.mem_of_mem_erase hb)
  rw [hsplit, Finset.prod_union hdisj, mul_assoc]

/-! ### Sharp degree: the paper bound -/

/-- The support has at most `M · 2ⁿ` elements: each support value carries at least one
lookup-column entry, and there are `M · 2ⁿ` entries in total. -/
theorem checkSupport_card_le (oStmt : ∀ i, OStmtIn F n M i) :
    (checkSupport oStmt).card ≤ M * 2 ^ n := by
  classical
  have hpos : ∀ a ∈ checkSupport oStmt, 1 ≤ lookupMultiplicityCount oStmt a := by
    intro a ha
    rw [mem_checkSupport_iff] at ha
    by_contra hlt
    have h0 : lookupMultiplicityCount oStmt a = 0 := by omega
    apply ha
    unfold checkCoeff
    split
    · rw [h0, Nat.cast_zero]
    · rfl
  have hsum_le : (checkSupport oStmt).card ≤ ∑ a ∈ checkSupport oStmt,
      lookupMultiplicityCount oStmt a := by
    calc (checkSupport oStmt).card
        = ∑ _a ∈ checkSupport oStmt, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ _ := Finset.sum_le_sum hpos
  have htotal : ∑ a ∈ (Finset.univ : Finset F), lookupMultiplicityCount oStmt a = M * 2 ^ n := by
    unfold lookupMultiplicityCount
    rw [← Finset.card_eq_sum_card_fiberwise
      (f := fun ix : Fin M × Hypercube n => evalOnHypercube (columnOracle oStmt ix.1) ix.2)
      (fun x _ => Finset.mem_univ _)]
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, card_hypercube]
  calc (checkSupport oStmt).card
      ≤ ∑ a ∈ checkSupport oStmt, lookupMultiplicityCount oStmt a := hsum_le
    _ ≤ ∑ a ∈ (Finset.univ : Finset F), lookupMultiplicityCount oStmt a :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = M * 2 ^ n := htotal

/-- **The sharp degree bound (paper degree).**  `natDegree P_S ≤ |supp| - 1`. -/
theorem grandSumCheckPolyS_natDegree_le (oStmt : ∀ i, OStmtIn F n M i) :
    (grandSumCheckPolyS oStmt).natDegree ≤ (checkSupport oStmt).card - 1 := by
  classical
  unfold grandSumCheckPolyS
  refine Polynomial.natDegree_sum_le_of_forall_le (s := checkSupport oStmt)
    (f := fun a : F => Polynomial.C (checkCoeff oStmt a) *
      ∏ b ∈ (checkSupport oStmt).erase a, (Polynomial.X + Polynomial.C b)) ?_
  intro a ha
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  have hfac : ∀ b ∈ (checkSupport oStmt).erase a,
      (Polynomial.X + Polynomial.C b : F[X]).natDegree ≤ 1 := by
    intro b _
    exact le_trans (Polynomial.natDegree_add_le _ _)
      (by simp [Polynomial.natDegree_X, Polynomial.natDegree_C])
  calc (∑ b ∈ (checkSupport oStmt).erase a, (Polynomial.X + Polynomial.C b : F[X]).natDegree)
      ≤ ∑ _b ∈ (checkSupport oStmt).erase a, 1 := Finset.sum_le_sum hfac
    _ = ((checkSupport oStmt).erase a).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ = (checkSupport oStmt).card - 1 := Finset.card_erase_of_mem ha

/-- The sharp degree fits the paper budget: `natDegree P_S ≤ M · 2ⁿ - 1`. -/
theorem grandSumCheckPolyS_natDegree_le_paper (oStmt : ∀ i, OStmtIn F n M i) :
    (grandSumCheckPolyS oStmt).natDegree ≤ M * 2 ^ n - 1 := by
  refine le_trans (grandSumCheckPolyS_natDegree_le oStmt) ?_
  have := checkSupport_card_le oStmt
  omega

/-! ### A bad lookup forces the sharp polynomial nonzero -/

/-- **Sharp nonvanishing.**  For a bad lookup the sharp check polynomial is nonzero: the residue
at the uncancelled column-only pole survives the support-restricted clearing. -/
theorem grandSumCheckPolyS_ne_zero_of_bad_lookup
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M)) :
    grandSumCheckPolyS oStmt ≠ 0 := by
  classical
  obtain ⟨a₀, hlook, htab⟩ := bad_lookup_exists_column_only_value stmt oStmt hBad
  have hc₀ : checkCoeff oStmt a₀ ≠ 0 := by
    unfold checkCoeff
    rw [if_pos htab]
    exact lookupMultiplicityCount_natCast_ne_zero stmt oStmt a₀ hlook
  have ha₀ : a₀ ∈ checkSupport oStmt := (mem_checkSupport_iff oStmt a₀).mpr hc₀
  intro hzero
  have heval : (grandSumCheckPolyS oStmt).eval (-a₀) = 0 := by rw [hzero]; simp
  unfold grandSumCheckPolyS at heval
  rw [Polynomial.eval_finset_sum] at heval
  have hterms : ∀ a ∈ checkSupport oStmt, a ≠ a₀ →
      (Polynomial.C (checkCoeff oStmt a) *
        ∏ b ∈ (checkSupport oStmt).erase a, (Polynomial.X + Polynomial.C b)).eval (-a₀) = 0 := by
    intro a _ hane
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero
      (Finset.mem_erase.mpr ⟨Ne.symm hane, ha₀⟩) ?_)
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, neg_add_cancel]
  rw [Finset.sum_eq_single a₀ hterms (fun hni => absurd ha₀ hni)] at heval
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at heval
  rcases mul_eq_zero.mp heval with hc | hprod
  · exact hc₀ hc
  · rw [Finset.prod_eq_zero_iff] at hprod
    obtain ⟨b, hb, hb0⟩ := hprod
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at hb0
    rw [Finset.mem_erase] at hb
    exact hb.1 (by linear_combination hb0)

/-! ### The sharp languages and the Schwartz–Zippel bound at the paper budget -/

/-- **The sharp intermediate claim language**: challenges at which the *support-cleared* check
polynomial vanishes.  Unlike `midSoundnessLanguage`, this has no spurious members: for a bad
lookup it consists of at most `M · 2ⁿ - 1` points. -/
def midSoundnessLanguageSharp (oStmt : ∀ i, OStmtIn F n M i) : Set F :=
  { x : F | (grandSumCheckPolyS oStmt).eval x = 0 }

/-- **Sharp Schwartz–Zippel at the paper budget.**  For a bad lookup, a uniformly sampled outer
challenge lands in the sharp claim language with probability at most `(M · 2ⁿ - 1)/|F|`. -/
theorem outerSoundness_sharp
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M)) :
    Pr_{ let x ←$ᵖ F }[ x ∈ midSoundnessLanguageSharp oStmt ]
      ≤ (((M * 2 ^ n - 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0∞) := by
  refine le_trans (prob_grandSumCheckPoly_root_le (grandSumCheckPolyS oStmt)
    (grandSumCheckPolyS_ne_zero_of_bad_lookup stmt oStmt hBad)) ?_
  gcongr
  exact_mod_cast grandSumCheckPolyS_natDegree_le_paper oStmt

/-! ### The sharp error fits inside the paper-shaped outer error -/

variable {params : ProtocolParams M}

omit [Field F] [DecidableEq F] in
/-- The sharp Schwartz–Zippel error fits inside the paper-shaped `outerSoundnessError` whenever
the field is larger than the hypercube (`2ⁿ < |F|`): the first summand of `outerSoundnessError`
has a larger numerator (`(M+1)·2ⁿ - 1 ≥ M·2ⁿ - 1`) and a smaller denominator (`|F| - 2ⁿ ≤ |F|`). -/
theorem sharp_error_le_outerSoundnessError
    (hcard : 2 ^ n < Fintype.card F) :
    ((M * 2 ^ n - 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)
      ≤ outerSoundnessError F n M params := by
  unfold outerSoundnessError
  refine le_trans ?_ (le_add_of_nonneg_right (zero_le _))
  rw [card_hypercube]
  have hden : (0 : ℝ≥0) < ((Fintype.card F - 2 ^ n : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.sub_pos_of_lt hcard
  have hcardF : (0 : ℝ≥0) < ((Fintype.card F : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le _) hcard
  rw [div_le_div_iff₀ hcardF hden]
  have hnat : (M * 2 ^ n - 1) * (Fintype.card F - 2 ^ n)
      ≤ ((M + 1) * 2 ^ n - 1) * Fintype.card F := by
    have h2 : M * 2 ^ n ≤ (M + 1) * 2 ^ n :=
      Nat.mul_le_mul (Nat.le_succ M) (le_refl (2 ^ n))
    exact Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.sub_le _ _)
  exact_mod_cast hnat

/-- **Headline: the sharp bad-accept marginal is bounded by `outerSoundnessError`.**  This is the
challenge-level mathematical core of the *correctly stated* outer-soundness obligation: for a bad
lookup, the uniformly sampled outer challenge lands in the sharp claim language with probability
at most the paper-shaped outer error. -/
theorem outerSoundness_sharp_le_outerSoundnessError
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (hcard : 2 ^ n < Fintype.card F) :
    Pr_{ let x ←$ᵖ F }[ x ∈ midSoundnessLanguageSharp oStmt ]
      ≤ (outerSoundnessError F n M params : ℝ≥0∞) := by
  refine le_trans (outerSoundness_sharp stmt oStmt hBad) ?_
  exact_mod_cast sharp_error_le_outerSoundnessError (params := params) hcard

/-! ### The sharp protocol-level intermediate language -/

/-- **The sharp protocol-level intermediate language** for the LogUp soundness composition: the
after-outer pairs whose carried challenge is a root of the *support-cleared* check polynomial of
the reconstructed input oracles.  This is the corrected replacement for
`midSoundnessProtocolLanguage` (which uses the unrestricted clearing and is therefore hit almost
surely; see `prob_midSoundnessLanguage_ge_compl_support`).  The language-generic composition
front door `logup_soundness_msgSeam_anyMid` accepts it directly as the intermediate language. -/
def midSoundnessProtocolLanguageSharp (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n M : ℕ) (params : ProtocolParams M) :
    Set (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) :=
  { p | p.1.xChallenge ∈ midSoundnessLanguageSharp (fun i => p.2 (.input i)) }

/-- Membership in the sharp protocol language collapses onto the carried challenge (the analogue
of `outerVerify_output_mem_midSoundnessProtocolLanguage_iff` for the sharp language). -/
theorem mem_midSoundnessProtocolLanguageSharp_iff
    {params : ProtocolParams M}
    (oStmt : ∀ i, OStmtIn F n M i)
    (stmtOut : StmtAfterOuter F n M params)
    (oStmtOut : ∀ i, OStmtAfterOuter F n M params i)
    (hInput : ∀ i, oStmtOut (.input i) = oStmt i) :
    ((stmtOut, oStmtOut) ∈ midSoundnessProtocolLanguageSharp F n M params)
      ↔ stmtOut.xChallenge ∈ midSoundnessLanguageSharp oStmt := by
  unfold midSoundnessProtocolLanguageSharp
  simp only [Set.mem_setOf_eq]
  rw [funext hInput]

end OuterSoundnessSharp

end Logup

/-! ### Axiom audit (issue #13 sharp outer check polynomial) -/

#print axioms Logup.grandSumCheckPoly_eval_neg_of_coeff_eq_zero
#print axioms Logup.prob_midSoundnessLanguage_ge_compl_support
#print axioms Logup.grandSumCheckPoly_eq_polyS_mul_compl
#print axioms Logup.checkSupport_card_le
#print axioms Logup.grandSumCheckPolyS_natDegree_le_paper
#print axioms Logup.grandSumCheckPolyS_ne_zero_of_bad_lookup
#print axioms Logup.outerSoundness_sharp
#print axioms Logup.outerSoundness_sharp_le_outerSoundnessError
#print axioms Logup.mem_midSoundnessProtocolLanguageSharp_iff
