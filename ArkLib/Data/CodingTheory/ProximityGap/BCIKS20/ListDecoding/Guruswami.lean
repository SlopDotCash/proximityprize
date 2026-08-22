/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic
import ArkLib.Data.CodingTheory.GuruswamiSudan.GuruswamiSudan
import ArkLib.Data.Polynomial.Trivariate
import Mathlib.Combinatorics.Pigeonhole

/-!
# BCIKS20 §5 trivariate Guruswami–Sudan interpolation

This file builds the trivariate Guruswami–Sudan interpolation machinery used by the [BCIKS20]
§5 proximity-gap list-decoding argument (Claim 5.4 and surrounding).  Working with
`Q : F[Z][X][Y]` over the coefficient ring `S = F[Z]` (an integral domain, not a field), it
re-establishes the order-`m` vanishing criterion `triv_rootMultiplicity_ge_of_shift_zero` over
any domain, develops generic weighted-degree sub-additivity and trivariate monomial degree
facts, sets up the Guruswami–Sudan linear system together with its box/budget counting
inequality and `Z`-degree budget, and proves existence of a nonzero kernel element.
-/

namespace ProximityGap

-- Decidability/Fintype instances are threaded through the sections for the §5 machinery;
-- several statement-level lemmas do not mention them directly.
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

universe u v w k l

/-! ### Generic order-of-vanishing lower bound over an integral-domain coefficient ring

The bivariate root-multiplicity lower bound `GuruswamiSudan.rootMultiplicity_ge_of_shift_zero`
is stated over a field.  The trivariate Guruswami–Sudan setting of [BCIKS20] Claim 5.4 evaluates
multiplicity of `Q : F[Z][X][Y]` over the coefficient ring `S = F[Z] = Polynomial F`, which is an
integral domain but not a field.  The lemmas below re-establish the order-`m` vanishing criterion
(`triv_rootMultiplicity_ge_of_shift_zero`) over any `[CommRing S] [IsDomain S]`, mirroring the
field proof but only using `NoZeroDivisors`. -/
section GenericTrivariateMultiplicity

open Polynomial Polynomial.Bivariate

variable {S : Type} [CommRing S] [IsDomain S] [DecidableEq S]

private lemma triv_comp_add_C_eq_zero_iff (p : S[X]) (a : S) :
    p.comp (Polynomial.X + Polynomial.C a) = 0 ↔ p = 0 := by
  rw [Polynomial.comp_eq_zero_iff]
  refine ⟨?_, fun h => Or.inl h⟩
  rintro (h | ⟨_, h2⟩)
  · exact h
  · exfalso; have := congrArg (fun q => Polynomial.coeff q 1) h2; simp at this

private lemma triv_compRingHom_addC_injective (a : S) :
    Function.Injective
      (Polynomial.compRingHom (Polynomial.X + Polynomial.C a) : S[X] →+* S[X]) := by
  rw [injective_iff_map_eq_zero]; intro r hr
  rw [Polynomial.coe_compRingHom] at hr; exact (triv_comp_add_C_eq_zero_iff r a).mp hr

omit [IsDomain S] in
private lemma triv_rm0_none_imp_zero (g : S[X][Y]) (hg : rootMultiplicity₀ g = none) :
    g = 0 := by
  unfold rootMultiplicity₀ at hg
  cases hwd : weightedDegree g 1 1 with
  | none => exact absurd hwd (weightedDegree_ne_none _ _ _)
  | some deg =>
    rw [hwd] at hg; simp only at hg
    rw [List.min?_eq_none_iff, List.filterMap_eq_nil_iff] at hg
    have hcoeff_zero : ∀ s t, s ≤ deg → t ≤ deg → coeff g s t = 0 := by
      intro s t hs ht
      have hmem := hg (s, t) (by
        rw [List.product, List.mem_flatMap]
        refine ⟨s, List.mem_range.mpr (Nat.lt_succ_of_le hs), ?_⟩
        rw [List.mem_map]; exact ⟨t, List.mem_range.mpr (Nat.lt_succ_of_le ht), rfl⟩)
      by_contra hc; simp only [hc, if_false] at hmem; exact (Option.some_ne_none _ hmem)
    have hwd_nat : natWeightedDegree g 1 1 = deg := by
      rw [weightedDegree_eq_natWeightedDegree] at hwd; exact Option.some.inj hwd
    have hcn : ∀ nn, g.coeff nn = 0 := by
      intro nn; by_contra hgn
      have hb : 1 * (g.coeff nn).natDegree + 1 * nn ≤ natWeightedDegree g 1 1 :=
        Finset.le_sup (f := fun mm => 1 * (g.coeff mm).natDegree + 1 * mm)
          (Polynomial.mem_support_iff.mpr hgn)
      rw [hwd_nat] at hb; simp only [one_mul] at hb
      have hn' : nn ≤ deg := by omega
      apply hgn; ext s; simp only [Polynomial.coeff_zero]
      by_cases hs : s ≤ deg
      · have := hcoeff_zero s nn hs hn'; rwa [Bivariate.coeff] at this
      · push Not at hs; exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    exact Polynomial.ext (fun nn => by rw [hcn nn, Polynomial.coeff_zero])

private lemma triv_shift_eq_zero_iff (f : S[X][Y]) (x y : S) :
    shift f x y = 0 ↔ f = 0 := by
  unfold shift
  rw [Polynomial.map_eq_zero_iff (triv_compRingHom_addC_injective x)]
  exact triv_comp_add_C_eq_zero_iff f (Polynomial.C y)

omit [IsDomain S] in
private lemma triv_rm0_some_witness (g : S[X][Y]) (val : ℕ)
    (hg : rootMultiplicity₀ g = some val) :
    ∃ s t, coeff g s t ≠ 0 ∧ s + t = val := by
  unfold rootMultiplicity₀ at hg
  cases hwd : weightedDegree g 1 1 with
  | none => rw [hwd] at hg; simp at hg
  | some deg =>
    rw [hwd] at hg; simp only at hg
    have hmem := List.min?_mem hg
    rw [List.mem_filterMap] at hmem
    obtain ⟨⟨s, t⟩, _, hval⟩ := hmem
    by_cases hc : coeff g s t = 0
    · simp [hc] at hval
    · simp only [hc, if_false] at hval; exact ⟨s, t, hc, by simpa using hval⟩

/-- Order-`m` vanishing from shifted-coefficient vanishing, over an integral-domain coefficient
ring `S`.  This is the `[CommRing S] [IsDomain S]` port of the field-only
`GuruswamiSudan.rootMultiplicity_ge_of_shift_zero`, needed for the trivariate setting `S = F[Z]`. -/
private lemma triv_rootMultiplicity_ge_of_shift_zero {f : S[X][Y]} {x y : S}
    {m : ℕ} (hf : f ≠ 0)
    (h : ∀ s t, s + t < m → ((shift f x y).coeff t).coeff s = 0) :
    (m : ℕ) ≤ Bivariate.rootMultiplicity f x y := by
  unfold Bivariate.rootMultiplicity
  cases hrm : rootMultiplicity₀ (shift f x y) with
  | none => exact absurd ((triv_shift_eq_zero_iff f x y).mp (triv_rm0_none_imp_zero _ hrm)) hf
  | some val =>
    show (m : Option ℕ) ≤ some val
    have hmval : m ≤ val := by
      by_contra hlt
      push Not at hlt
      obtain ⟨s, t, hne, hst⟩ := triv_rm0_some_witness (shift f x y) val hrm
      apply hne; rw [Bivariate.coeff]; exact h s t (by omega)
    exact_mod_cast hmval

end GenericTrivariateMultiplicity

/-! ### Generic weighted-degree sub-additivity (any coefficient semiring)

These mirror `GuruswamiSudan.natWeightedDegree_{add,sum,smul}_le` (which are proven for a field
coefficient ring) over an arbitrary semiring `S`, so they apply to the trivariate setting where the
coefficient ring is `S = F[Z]`. -/
section GenericTrivariateDegree

open Polynomial Polynomial.Bivariate

variable {S : Type} [Semiring S]

lemma tri_natWeightedDegree_add_le (p q : S[X][Y]) (u v : ℕ) :
    natWeightedDegree (p + q) u v ≤ max (natWeightedDegree p u v) (natWeightedDegree q u v) := by
  refine Finset.sup_le fun mm hm ↦ ?_
  by_cases h : mm ∈ p.support <;>
  by_cases h' : mm ∈ q.support <;>
    simp_all only [Polynomial.mem_support_iff, coeff_add, ne_eq, le_sup_iff]
  · have h_deg : (p.coeff mm + q.coeff mm).natDegree ≤
        max ((p.coeff mm).natDegree) ((q.coeff mm).natDegree) :=
      natDegree_add_le (p.coeff mm) (q.coeff mm)
    cases max_cases (natDegree (p.coeff mm)) (natDegree (q.coeff mm)) <;>
      simp_all only [sup_of_le_left, sup_eq_left, and_self, natWeightedDegree]
    · exact Or.inl (le_trans (add_le_add (mul_le_mul_of_nonneg_left h_deg <| Nat.zero_le _) le_rfl)
        <| Finset.le_sup (f := fun mm ↦ u * natDegree (p.coeff mm) + v * mm) <| by aesop)
    · exact Or.inr (le_trans (add_le_add (mul_le_mul_of_nonneg_left h_deg <| Nat.zero_le _) le_rfl)
        <| Finset.le_sup (f := fun mm ↦ u * natDegree (q.coeff mm) + v * mm) <| by aesop)
  all_goals simp_all only [not_not, add_zero, zero_add, not_false_eq_true]
  · exact Or.inl <| Finset.le_sup (f := fun mm ↦ u * natDegree (p.coeff mm) + v * mm) <| by aesop
  · exact Or.inr <| Finset.le_sup (f := fun mm ↦ u * natDegree (q.coeff mm) + v * mm) <| by aesop
  · simp at hm

lemma tri_natWeightedDegree_sum_le {ι : Type*} (s : Finset ι) (f : ι → S[X][Y]) (u v : ℕ) :
    natWeightedDegree (∑ i ∈ s, f i) u v ≤ s.sup (fun i ↦ natWeightedDegree (f i) u v) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty, Finset.sup_empty, Nat.bot_eq_zero, nonpos_iff_eq_zero,
      natWeightedDegree, Polynomial.support_zero, coeff_zero, natDegree_zero, mul_zero, zero_add,
      Finset.sup_empty, Nat.bot_eq_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sup_insert]
                        exact le_trans (tri_natWeightedDegree_add_le _ _ _ _) (max_le_max le_rfl ih)

end GenericTrivariateDegree

section BCIKS20ProximityGapSection5

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n : ℕ}

section

open GuruswamiSudan Polynomial.Bivariate RatFunc Trivariate

/-- The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan in Lemma 5.3 of [BCIKS20].
`D_X(m) = (m + 1/2)√rhon.` -/
noncomputable def D_X (rho : ℚ) (n m : ℕ) : ℝ := (m + 1/2) * (Real.sqrt rho) * n

omit [DecidableEq (RatFunc F)] in
/-- The first part of Lemma 5.3 from [BCIKS20].
Given `D_X` (`proximity_gap_degree_bound`) and `δ₀` (`proximity_gap_johnson`), a solution to
Guruswami-Sudan system exists. -/
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    (hm : 1 ≤ m) :
    ∃ Q, Conditions (k + 1) m (_root_.proximity_gap_degree_bound (k + 1) n m) ωs f Q :=
    GuruswamiSudan.proximity_gap_existence (k + 1) n ωs f hm

omit [DecidableEq (RatFunc F)] in
open Polynomial in
/-- The second part of Lemma 5.3 from [BCIKS20].
For any solution `Q` of the Guruswami-Sudan system, and for any polynomial `P ∈ RS[n, k, rho]`
such that `δᵣ(w, P) ≤ δ₀(rho, m)`, we have that `Y - P(X)` divides `Q(X, Y)` in the polynomial ring
`F[X][Y]`. Note that in `F[X][Y]`, the term `X` actually refers to the outer variable, `Y`.
-/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs : Fin n ↪ F}
    {w : Fin n → F}
    {Q : F[X][Y]}
    (hk : k + 2 ≤ n) (hm : 1 ≤ m)
    (cond : Conditions (k + 1) m (_root_.proximity_gap_degree_bound (k + 1) n m) ωs w Q)
    {p : ReedSolomon.code ωs (k + 1)}
    (h : (↑Δ₀(w, fun i ↦ Polynomial.eval (ωs i) (ReedSolomon.codewordToPoly p)) : ℝ) / ↑n <
         _root_.proximity_gap_johnson (k + 1) n m) :
    (Polynomial.X - Polynomial.C (ReedSolomon.codewordToPoly p)) ∣ Q :=
  GuruswamiSudan.proximity_gap_divisibility hk hm p cond h

/-- The Guruswami-Sudan condition as it is stated in [BCIKS20]. -/
structure ModifiedGuruswami
  (m n k : ℕ)
  (ωs : Fin n ↪ F)
  (Q : F[Z][X][Y])
  (u₀ u₁ : Fin n → F)
  where
  Q_ne_0 : Q ≠ 0
  /-- Degree of the polynomial. -/
  Q_deg : natWeightedDegree Q 1 k < D_X ((k + 1) / (n : ℚ)) n m
  /-- Multiplicity of the roots is at least `m`. -/
  Q_multiplicity : ∀ i, rootMultiplicity Q
              (Polynomial.C <| ωs i)
              ((Polynomial.C <| u₀ i) + Polynomial.X * (Polynomial.C <| u₁ i))
            ≥ m
  /-- The X-degree bound. -/
  Q_deg_X :
    degreeX Q < D_X ((k + 1) / (n : ℚ)) n m
  /-- The Y-degree bound. -/
  Q_D_Y :
    D_Y Q < D_X ((k + 1 : ℚ) / n) n m / k
  /-- The YZ-degree bound. -/
  Q_D_YZ :
    D_YZ Q ≤ n * (m + 1/(2 : ℚ))^3 / (6 * Real.sqrt ((k + 1) / n))

section ModifiedGuruswamiHelpers

/-! ### Degree facts for the trivariate constant `1`

The constant polynomial `1 : F[Z][X][Y]` has all (bivariate-over-`F[Z]`) degree measures equal
to `0` and root multiplicity `0` at every curve point. These are the base facts used when
building/reasoning about candidate solutions `Q` of `ModifiedGuruswami` and, in particular, they
pin down the value of each `ModifiedGuruswami` constraint on the simplest nonzero witness. -/

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The `X`-degree of the trivariate constant `1` is `0`. -/
lemma degreeX_one_triv : degreeX (1 : F[Z][X][Y]) = 0 := by
  unfold Polynomial.Bivariate.degreeX
  apply le_antisymm _ (Nat.zero_le _)
  apply Finset.sup_le
  intro i hi
  rw [Polynomial.mem_support_iff] at hi
  rcases eq_or_ne i 0 with h | h
  · subst h; simp
  · simp [Polynomial.coeff_one, h] at hi

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The `Y`-degree of the trivariate constant `1` is `0`. -/
lemma natDegreeY_one_triv : natDegreeY (1 : F[Z][X][Y]) = 0 := by
  unfold Polynomial.Bivariate.natDegreeY
  simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The `(u, v)`-weighted degree of the trivariate constant `1` is `0`. -/
lemma natWeightedDegree_one_triv (u v : ℕ) :
    natWeightedDegree (1 : F[Z][X][Y]) u v = 0 := by
  unfold Polynomial.Bivariate.natWeightedDegree
  apply le_antisymm _ (Nat.zero_le _)
  apply Finset.sup_le
  intro i hi
  rw [Polynomial.mem_support_iff] at hi
  rcases eq_or_ne i 0 with h | h
  · subst h; simp
  · simp [Polynomial.coeff_one, h] at hi

omit [DecidableEq (RatFunc F)] in
/-- The root multiplicity of the trivariate constant `1` at any point `(x, y)` is `0`.
Here the coefficient ring is `F[Z] = Polynomial (Polynomial F)`. -/
lemma rootMultiplicity_one_triv (x y : Polynomial F) :
    rootMultiplicity (1 : F[Z][X][Y]) x y = some 0 := by
  unfold Polynomial.Bivariate.rootMultiplicity
  rw [show Polynomial.Bivariate.shift (1 : F[Z][X][Y]) x y = 1 from by
    unfold Polynomial.Bivariate.shift; simp]
  unfold Polynomial.Bivariate.rootMultiplicity₀
  have hw : weightedDegree (1 : F[Z][X][Y]) 1 1 = some 0 := by
    unfold Polynomial.Bivariate.weightedDegree
    simp [Polynomial.natDegree_one]
  rw [hw]
  simp only [Nat.succ_eq_add_one, Nat.zero_add, List.range_one]
  have hp : ([0].product [0]) = [((0 : ℕ), (0 : ℕ))] := rfl
  rw [hp]
  simp only [List.filterMap_cons, List.filterMap_nil]
  have hc : coeff (1 : F[Z][X][Y]) 0 0 = 1 := by
    simp [Polynomial.Bivariate.coeff, Polynomial.coeff_one]
  rw [hc, if_neg one_ne_zero]
  simp

/-! ### Necessity of `0 < n` and `0 < k`

The statement of Claim 5.4 below quantifies over **all** `n, k, m`.  As formalized this is
**unsatisfiable** when `n = 0` or `k = 0`: the degree bound `D_X ρ n m` collapses to `0`, while
the `X`-degree (resp. `Y`-degree) of any polynomial is a natural number `≥ 0`, so the strict
constraints `degreeX Q < D_X …` (resp. `D_Y Q < D_X … / k`) cannot hold.

The two lemmas below record this precisely: any solution forces a contradiction.  Hence a faithful
restatement of Claim 5.4 must assume `0 < n` and `0 < k` (matching the non-degenerate Reed–Solomon
regime `k + 1 ≤ n` of [BCIKS20], and the `1 < k`, `n ≠ 0` hypotheses of the bivariate analogue
`GuruswamiSudan.gs_existence`). -/

omit [DecidableEq (RatFunc F)] in
/-- For `n = 0`, no `Q` can satisfy `ModifiedGuruswami`: the `X`-degree bound `D_X ρ 0 m = 0`
forces `(degreeX Q : ℝ) < 0`, which is impossible. -/
lemma modified_guruswami_unsat_of_n_zero {m k : ℕ} {ωs : Fin 0 ↪ F} {Q : F[Z][X][Y]}
    {u₀ u₁ : Fin 0 → F} (h : ModifiedGuruswami m 0 k ωs Q u₀ u₁) : False := by
  have hX := h.Q_deg_X
  unfold D_X at hX
  simp only [mul_zero, CharP.cast_eq_zero] at hX
  exact absurd hX (not_lt.mpr (Nat.cast_nonneg _))

omit [DecidableEq (RatFunc F)] in
/-- For `k = 0`, no `Q` can satisfy `ModifiedGuruswami`: the `Y`-degree bound `D_X ρ n m / 0 = 0`
forces `(D_Y Q : ℝ) < 0`, which is impossible. -/
lemma modified_guruswami_unsat_of_k_zero {m n : ℕ} {ωs : Fin n ↪ F} {Q : F[Z][X][Y]}
    {u₀ u₁ : Fin n → F} (h : ModifiedGuruswami m n 0 ωs Q u₀ u₁) : False := by
  have hY := h.Q_D_Y
  simp only [Nat.cast_zero, div_zero] at hY
  exact absurd hY (not_lt.mpr (Nat.cast_nonneg _))

/-! ### Trivariate monomial degree facts

The candidate solution `Q` of `ModifiedGuruswami` is assembled from the monomials `X^i Y^j Z^t`.
The lemmas below pin down each degree measure of a single such monomial, which is what controls
where a sum of monomials sits relative to the `ModifiedGuruswami` degree bounds. -/

/-- The trivariate monomial `X^i Y^j Z^t` as an element of `F[Z][X][Y]`. -/
noncomputable def triMonomial (i j t : ℕ) : F[Z][X][Y] :=
  Polynomial.monomial j (Polynomial.monomial i (Polynomial.monomial t (1 : F)))

omit [DecidableEq (RatFunc F)] in
/-- The trivariate monomial `X^i Y^j Z^t` is nonzero. -/
lemma triMonomial_ne_zero (i j t : ℕ) : triMonomial (F := F) i j t ≠ 0 := by
  unfold triMonomial; simp

omit [DecidableEq (RatFunc F)] in
/-- `degreeX (X^i Y^j Z^t) = i`. -/
lemma degreeX_triMonomial (i j t : ℕ) : degreeX (triMonomial (F := F) i j t) = i := by
  unfold degreeX triMonomial
  rw [Polynomial.support_monomial _
    (by simp : (Polynomial.monomial i (Polynomial.monomial t (1:F))) ≠ 0)]
  simp [Polynomial.coeff_monomial, Polynomial.natDegree_monomial]

omit [DecidableEq (RatFunc F)] in
/-- `natDegreeY (X^i Y^j Z^t) = j`. -/
lemma natDegreeY_triMonomial (i j t : ℕ) : natDegreeY (triMonomial (F := F) i j t) = j := by
  unfold natDegreeY triMonomial
  rw [Polynomial.natDegree_monomial]
  simp

omit [DecidableEq (RatFunc F)] in
/-- `natWeightedDegree (X^i Y^j Z^t) u v = u*i + v*j`. -/
lemma natWeightedDegree_triMonomial (i j t u v : ℕ) :
    natWeightedDegree (triMonomial (F := F) i j t) u v = u * i + v * j := by
  unfold natWeightedDegree triMonomial
  rw [Polynomial.support_monomial _
    (by simp : (Polynomial.monomial i (Polynomial.monomial t (1:F))) ≠ 0)]
  simp [Polynomial.coeff_monomial, Polynomial.natDegree_monomial]

omit [DecidableEq (RatFunc F)] in
/-- The `D_YZ` measure (as defined in `Trivariate.lean`) of a monomial `X^i Y^j Z^t` with `i ≠ j`
equals just the `Y`-degree index `j`.

This records a property of the *current* `D_YZ` definition: it computes
`max over j_Y of (j_Y + max over k_X of (Bivariate.coeff Q j_Y k_X).natDegree)`, and since
`Bivariate.coeff Q a b = (Q.coeff b).coeff a` (the first argument is the inner `X`-index), the
inner contribution vanishes for a single monomial unless `i = j`.  In particular the `Z`-degree
`t` is not captured, which makes the `Q_D_YZ` bound of `ModifiedGuruswami` easy to satisfy. -/
lemma D_YZ_triMonomial_of_ne (i j t : ℕ) (hij : i ≠ j) :
    D_YZ (triMonomial (F := F) i j t) = j := by
  unfold D_YZ triMonomial
  rw [Polynomial.support_monomial _
    (by simp : (Polynomial.monomial i (Polynomial.monomial t (1:F))) ≠ 0)]
  simp only [Finset.image_singleton, Finset.max_singleton]
  have hcj : (Polynomial.monomial j (Polynomial.monomial i (Polynomial.monomial t (1:F)))).coeff j
      = Polynomial.monomial i (Polynomial.monomial t (1:F)) := by
    rw [Polynomial.coeff_monomial, if_pos rfl]
  rw [hcj]
  rw [Polynomial.support_monomial _ (by simp : (Polynomial.monomial t (1:F)) ≠ 0)]
  simp only [Finset.image_singleton, Finset.max_singleton]
  unfold Polynomial.Bivariate.coeff
  rw [Polynomial.coeff_monomial, if_neg (Ne.symm hij)]
  simp [Polynomial.natDegree_zero]
  rfl

/-! ### Assembling a candidate from box-indexed coefficients

`triCoeffsToPoly box c` assembles `Q = ∑ c_{i,j,t} · X^i Y^j Z^t` over a finite index box of
triples `(i, j, t)`.  `natWeightedDegree_triCoeffsToPoly_le` bounds its `(u,v)`-weighted degree by
the box's weighted cap; specialising `(u,v)` recovers the `degreeX` and `natDegreeY` bounds via
`degreeX_as_weighted_deg` / `degreeY_as_weighted_deg`. -/

/-- `a · X^i Y^j Z^t` as nested monomials (carries the coefficient inside, avoiding the long
`SMul F (F[Z][X][Y])` synthesis path). -/
noncomputable def triMonC (i j t : ℕ) (a : F) : F[Z][X][Y] :=
  Polynomial.monomial j (Polynomial.monomial i (Polynomial.monomial t a))

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The `(u,v)`-weighted degree of `a · X^i Y^j Z^t` is at most `u*i + v*j`. -/
lemma natWeightedDegree_triMonC_le (i j t u v : ℕ) (a : F) :
    natWeightedDegree (triMonC (F := F) i j t a) u v ≤ u * i + v * j := by
  classical
  unfold natWeightedDegree triMonC
  refine Finset.sup_le fun b hb ↦ ?_
  have hbj : b = j := by
    by_contra hbj
    rw [Polynomial.mem_support_iff, Polynomial.coeff_monomial, if_neg (Ne.symm hbj)] at hb
    exact hb rfl
  subst hbj
  rw [Polynomial.coeff_monomial, if_pos rfl]
  refine add_le_add (Nat.mul_le_mul_left u ?_) le_rfl
  exact Polynomial.natDegree_monomial_le _

/-- Assemble a trivariate polynomial from box-indexed coefficients. -/
noncomputable def triCoeffsToPoly (box : Finset (ℕ × ℕ × ℕ)) (c : box → F) : F[Z][X][Y] :=
  ∑ p : box, triMonC (F := F) p.1.1 p.1.2.1 p.1.2.2 (c p)

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The weighted degree of the assembled polynomial is bounded by the box's weighted-degree cap. -/
lemma natWeightedDegree_triCoeffsToPoly_le (box : Finset (ℕ × ℕ × ℕ)) (c : box → F) (u v D : ℕ)
    (hbox : ∀ p ∈ box, u * p.1 + v * p.2.1 ≤ D) :
    natWeightedDegree (triCoeffsToPoly box c) u v ≤ D := by
  classical
  unfold triCoeffsToPoly
  refine le_trans (tri_natWeightedDegree_sum_le _ _ _ _) ?_
  refine Finset.sup_le fun p _ ↦ ?_
  exact le_trans (natWeightedDegree_triMonC_le _ _ _ _ _ _) (hbox p.1 p.2)

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The `(i, j, t)`-coefficient of `a · X^i Y^j Z^t` (i.e. `((·.coeff j).coeff i).coeff t`). -/
lemma coeff_triMonC (i j t i' j' t' : ℕ) (a : F) :
    (((triMonC (F := F) i' j' t' a).coeff j).coeff i).coeff t
      = if (i', j', t') = (i, j, t) then a else 0 := by
  unfold triMonC
  rw [Polynomial.coeff_monomial]
  by_cases hj : j' = j
  · subst hj
    rw [if_pos rfl, Polynomial.coeff_monomial]
    by_cases hi : i' = i
    · subst hi
      rw [if_pos rfl, Polynomial.coeff_monomial]
      by_cases ht : t' = t
      · subst ht; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg ht, if_neg (by simp [ht])]
    · rw [if_neg hi, Polynomial.coeff_zero, if_neg (by simp [hi])]
  · rw [if_neg hj, Polynomial.coeff_zero, Polynomial.coeff_zero, if_neg (by simp [hj])]

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- Coefficient extraction for `triCoeffsToPoly`: the coefficient of `X^i Y^j Z^t` at a box index
`p = (i, j, t)` is exactly `c p`. -/
lemma coeff_triCoeffsToPoly (box : Finset (ℕ × ℕ × ℕ)) (c : box → F) (p : box) :
    (((triCoeffsToPoly box c).coeff p.1.2.1).coeff p.1.1).coeff p.1.2.2 = c p := by
  unfold triCoeffsToPoly
  rw [Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single p]
  · rw [coeff_triMonC, if_pos rfl]
  · intro q _ hq
    rw [coeff_triMonC, if_neg]
    intro heq
    exact hq (Subtype.ext heq)
  · intro h; exact absurd (Finset.mem_univ p) h

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- A nonzero coefficient vector yields a nonzero assembled polynomial (the `Q_ne_0` field). -/
lemma triCoeffsToPoly_ne_zero (box : Finset (ℕ × ℕ × ℕ)) (c : box → F) (hc : c ≠ 0) :
    triCoeffsToPoly box c ≠ 0 := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hc
  rw [Pi.zero_apply] at hp
  intro hQ
  apply hp
  rw [← coeff_triCoeffsToPoly box c p, hQ]
  simp

/-! ### The trivariate Guruswami–Sudan linear system

Mirroring the bivariate `GuruswamiSudan.{coeffsToPoly, evalConstraint, constraintMap}`, we build
the F-linear system whose nonzero kernel elements give multiplicity-`m` solutions `Q`.  The
trivariate twist: each multiplicity constraint `((shift Q x y).coeff t).coeff s = 0` is an equation
in the coefficient ring `S = F[Z]`, so we extract every `Z`-coefficient up to a budget `zMax`,
turning each `(s, t)` constraint into `zMax + 1` scalar `F`-constraints. -/

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- `a · X^i Y^j Z^t = a • (X^i Y^j Z^t)` (carrying the scalar inside the nested monomials equals
the `F`-scalar action). -/
lemma triMonC_eq_smul (i j t : ℕ) (a : F) :
    triMonC (F := F) i j t a = a • triMonomial (F := F) i j t := by
  unfold triMonC triMonomial
  rw [Polynomial.smul_monomial, Polynomial.smul_monomial, Polynomial.smul_monomial, smul_eq_mul,
    mul_one]

/-- Linear assembly of a trivariate polynomial from box-indexed coefficients, as an `F`-linear map.
This is the linear version of `triCoeffsToPoly`; the two agree (`triCoeffsToPolyₗ_apply`). -/
noncomputable def triCoeffsToPolyₗ (box : Finset (ℕ × ℕ × ℕ)) : (box → F) →ₗ[F] F[Z][X][Y] :=
  Finsupp.linearCombination F (fun p : box ↦ triMonomial (F := F) p.1.1 p.1.2.1 p.1.2.2) ∘ₗ
    (Finsupp.linearEquivFunOnFinite F F box).symm.toLinearMap

omit [DecidableEq (RatFunc F)] in
/-- The linear assembly `triCoeffsToPolyₗ` agrees with `triCoeffsToPoly`. -/
lemma triCoeffsToPolyₗ_apply (box : Finset (ℕ × ℕ × ℕ)) (c : box → F) :
    triCoeffsToPolyₗ box c = triCoeffsToPoly box c := by
  classical
  unfold triCoeffsToPolyₗ triCoeffsToPoly
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Finsupp.linearCombination_apply]
  rw [Finsupp.sum_fintype]
  · refine Finset.sum_congr rfl (fun p _ ↦ ?_)
    rw [triMonC_eq_smul]
    congr 1
  · intro p; simp

/-- The `F`-linear functional extracting the `z`-th `Z`-coefficient of the `(s, t)`-shifted
coefficient `((shift f x y).coeff t).coeff s` at the curve point `(x, y) ∈ F[Z] × F[Z]`. -/
noncomputable def triEvalConstraint (x y : Polynomial F) (s t z : ℕ) : F[Z][X][Y] →ₗ[F] F where
  toFun f := (((Polynomial.Bivariate.shift f x y).coeff t).coeff s).coeff z
  map_add' f g := by simp [Polynomial.Bivariate.shift]
  map_smul' a f := by simp [Polynomial.Bivariate.shift]

/-- The trivariate Guruswami–Sudan constraint map: sends a box-indexed coefficient vector to the
`Z`-coefficients (up to budget `zMax`) of the multiplicity constraints at all `n` curve points.
A nonzero kernel element gives a `Q` with multiplicity `≥ m` at each point. -/
noncomputable def triConstraintMap (box : Finset (ℕ × ℕ × ℕ)) (m zMax : ℕ)
    (ωs : Fin n ↪ F) (u₀ u₁ : Fin n → F) :
    (box → F) →ₗ[F] (Fin n × GuruswamiSudan.constraintIndices m × Fin (zMax + 1) → F) :=
  (LinearMap.pi fun i ↦ triEvalConstraint (Polynomial.C (ωs i.1))
      (Polynomial.C (u₀ i.1) + Polynomial.X * Polynomial.C (u₁ i.1))
      i.2.1.1.1 i.2.1.1.2 i.2.2.1) ∘ₗ triCoeffsToPolyₗ box

/-! ### Box, budget and the counting inequality

We instantiate the linear system with a concrete box of `(i, j, t)` triples and a `Z`-budget large
enough that the number of unknowns strictly exceeds the number of constraints.  The `(i, j)` part is
the bivariate Guruswami–Sudan box `weigthBoundIndices (k+1) Dpg` (so its size is the proven
`numVars (k+1) Dpg`); the `Z`-index `t` ranges over `0 … zCap`.  Choosing `zCap =
(#constraints)·Dpg`
makes the strict bivariate gap `numVars > numConstraints` dominate the extra `Z`-degree the shift
introduces, giving `#box > #constraints`. -/

open GuruswamiSudan in
/-- The bivariate degree cap used for Claim 5.4: the proximity-gap degree bound with `ρ=(k+1)/n`. -/
noncomputable def gsDpg (n m k : ℕ) : ℕ := proximity_gap_degree_bound (k + 1) n m

/-- The `Z`-budget of the box: large enough that the `Z`-degree introduced by shifting (`≤ Dpg`)
cannot overturn the strict bivariate counting gap. -/
noncomputable def gsZCap (n m k : ℕ) : ℕ := GuruswamiSudan.numConstraints n m * gsDpg n m k

/-- The number of `Z`-coefficients the constraints can occupy: the box `Z`-budget plus the maximal
`Y`-degree `≤ Dpg` (the shift `Y ← Y + (u₀ + Z·u₁)` raises the `Z`-degree by at most the
`Y`-degree).
-/
noncomputable def gsZMax (n m k : ℕ) : ℕ := gsZCap n m k + gsDpg n m k

/-- The embedding `((i,j),t) ↦ (i,j,t)`. -/
def gsTriple : (ℕ × ℕ) × ℕ → ℕ × ℕ × ℕ := fun p ↦ (p.1.1, p.1.2, p.2)

lemma gsTriple_injective : Function.Injective gsTriple := by
  intro ⟨⟨i, j⟩, t⟩ ⟨⟨i', j'⟩, t'⟩ h
  simp only [gsTriple, Prod.mk.injEq] at h
  obtain ⟨hi, hj, ht⟩ := h
  simp [hi, hj, ht]

open GuruswamiSudan in
/-- The box of `(i, j, t)` triples: bivariate Guruswami–Sudan `(i,j)`-box times `Z`-budget. -/
noncomputable def gsBox (n m k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((weigthBoundIndices (k + 1) (gsDpg n m k)) ×ˢ (Finset.range (gsZCap n m k + 1))).image gsTriple

open GuruswamiSudan in
/-- The cardinality of the box is `numVars (k+1) Dpg · (zCap+1)`. -/
lemma card_gsBox (n m k : ℕ) :
    (gsBox n m k).card = numVars (k + 1) (gsDpg n m k) * (gsZCap n m k + 1) := by
  classical
  unfold gsBox numVars
  rw [Finset.card_image_of_injective _ gsTriple_injective, Finset.card_product, Finset.card_range]

open GuruswamiSudan in
/-- Membership in the box: `(i, j, t) ∈ gsBox` iff `(i,j) ∈ weigthBoundIndices (k+1) Dpg` and
`t ≤ zCap`. -/
lemma mem_gsBox {n m k : ℕ} {p : ℕ × ℕ × ℕ} :
    p ∈ gsBox n m k ↔
      (p.1, p.2.1) ∈ weigthBoundIndices (k + 1) (gsDpg n m k) ∧ p.2.2 ≤ gsZCap n m k := by
  classical
  unfold gsBox
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨i, j⟩, t⟩, hmem, rfl⟩
    rw [Finset.mem_product] at hmem
    simp only [gsTriple, Finset.mem_range] at *
    exact ⟨hmem.1, Nat.lt_succ_iff.mp hmem.2⟩
  · intro ⟨h1, h2⟩
    refine ⟨((p.1, p.2.1), p.2.2), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_range]
      exact ⟨h1, Nat.lt_succ_of_le h2⟩
    · simp [gsTriple]

open GuruswamiSudan in
/-- The counting inequality: `#box > #constraints`.  This is the trivariate analogue of
`numVars_gt_numConstraints`, with the `Z`-budget chosen so the strict bivariate gap dominates. -/
lemma card_gsBox_gt_constraints (n m k : ℕ) :
    (gsBox n m k).card >
      n * (constraintIndices m).card * (gsZMax n m k + 1) := by
  rw [card_gsBox]
  set Dpg := gsDpg n m k with hDpg
  set B := numConstraints n m with hB
  -- A := numVars (k+1) Dpg ≥ B + 1
  have hAB : numVars (k + 1) Dpg ≥ B + 1 := by
    have h := numVars_gt_numConstraints (k + 1) n m
    have hDpg' : Dpg = proximity_gap_degree_bound (k + 1) n m := hDpg
    rw [hDpg', hB]; omega
  have hzcap : gsZCap n m k = B * Dpg := by rw [gsZCap, hDpg, hB]
  have hzmax : gsZMax n m k = B * Dpg + Dpg := by rw [gsZMax, hzcap, hDpg]
  have hBconstr : n * (constraintIndices m).card = B := by rw [hB, numConstraints]
  rw [hBconstr, hzmax, hzcap]
  -- numVars · (B·Dpg + 1) > B · (B·Dpg + Dpg + 1)
  calc n * (constraintIndices m).card * (B * Dpg + Dpg + 1)
      = B * (B * Dpg + Dpg + 1) := by rw [hBconstr]
    _ < (B + 1) * (B * Dpg + 1) := by ring_nf; omega
    _ ≤ numVars (k + 1) Dpg * (B * Dpg + 1) := by
        exact Nat.mul_le_mul_right _ hAB

/-! ### `Z`-degree budget of the shifted constraints

To turn the finite system "all `Z`-coefficients up to `zMax` vanish" into the genuine multiplicity
condition "the `F[Z]`-coefficient vanishes", we bound the `Z`-degree of every constraint output.
`ZdegLE f d` says all bivariate coefficients of `f : F[Z][X][Y]` are `F[Z]`-polynomials of degree
`≤ d`.  Shifting raises the `Z`-degree by at most the `Y`-degree (the only point coordinate with
positive `Z`-degree is `y = u₀ + Z·u₁`). -/

/-- `ZdegLE f d`: every bivariate coefficient `((f.coeff j).coeff i)` of `f : F[Z][X][Y]` is an
`F[Z]`-polynomial of degree at most `d`. -/
def ZdegLE (f : F[Z][X][Y]) (d : ℕ) : Prop := ∀ i j, ((f.coeff j).coeff i).natDegree ≤ d

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE_zero (d : ℕ) : ZdegLE (0 : F[Z][X][Y]) d := by
  intro i j; simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE.add {f g : F[Z][X][Y]} {d : ℕ} (hf : ZdegLE f d) (hg : ZdegLE g d) :
    ZdegLE (f + g) d := by
  intro i j
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (hf i j) (hg i j))

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE.mono {f : F[Z][X][Y]} {d e : ℕ} (hf : ZdegLE f d) (hde : d ≤ e) : ZdegLE f e :=
  fun i j ↦ le_trans (hf i j) hde

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE_sum {ι : Type*} (s : Finset ι) (g : ι → F[Z][X][Y]) (d : ℕ)
    (h : ∀ i ∈ s, ZdegLE (g i) d) : ZdegLE (∑ i ∈ s, g i) d := by
  classical
  induction s using Finset.induction with
  | empty => simpa using ZdegLE_zero d
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add (ih (fun i hi ↦ h i (Finset.mem_insert_of_mem
        hi)))

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE.mul {f g : F[Z][X][Y]} {d e : ℕ} (hf : ZdegLE f d) (hg : ZdegLE g e) :
    ZdegLE (f * g) (d + e) := by
  classical
  intro i j
  rw [Polynomial.coeff_mul]
  rw [Polynomial.finset_sum_coeff]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun p hp ↦ ?_)
  rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun q hq ↦ ?_)
  exact le_trans (Polynomial.natDegree_mul_le) (Nat.add_le_add (hf _ _) (hg _ _))

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE_one : ZdegLE (1 : F[Z][X][Y]) 0 := by
  intro i j
  rw [Polynomial.coeff_one]
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl, Polynomial.coeff_one]
    by_cases hi : i = 0
    · rw [if_pos hi]; simp
    · rw [if_neg hi]; simp
  · rw [if_neg hj]; simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE.pow {f : F[Z][X][Y]} {d : ℕ} (hf : ZdegLE f d) (a : ℕ) :
    ZdegLE (f ^ a) (a * d) := by
  induction a with
  | zero => simpa using ZdegLE_one.mono (Nat.zero_le _)
  | succ a ih =>
      rw [pow_succ]
      exact (ih.mul hf).mono (by ring_nf; omega)

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- `ZdegLE (C P) d` whenever every `X`-coefficient of `P : F[Z][X]` has `Z`-degree `≤ d`. -/
lemma ZdegLE_C {P : F[Z][X]} {d : ℕ} (hP : ∀ i, (P.coeff i).natDegree ≤ d) :
    ZdegLE (Polynomial.C P) d := by
  intro i j
  rw [Polynomial.coeff_C]
  by_cases hj : j = 0
  · rw [if_pos hj]; exact hP i
  · rw [if_neg hj]; simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The double-constant `C (C s)` (constant in `X` and `Y`) has `Z`-degree `s.natDegree`. -/
lemma ZdegLE_CC (s : Polynomial F) : ZdegLE (Polynomial.C (Polynomial.C s)) s.natDegree := by
  refine ZdegLE_C (fun i ↦ ?_)
  rw [Polynomial.coeff_C]
  by_cases hi : i = 0
  · rw [if_pos hi]
  · rw [if_neg hi]; simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The outer variable `Y` has `Z`-degree `0`. -/
lemma ZdegLE_Y : ZdegLE (Polynomial.X : F[Z][X][Y]) 0 := by
  intro i j
  rw [Polynomial.coeff_X]
  by_cases hj : 1 = j
  · rw [if_pos hj]; simp [Polynomial.coeff_one]; by_cases hi : i = 0 <;> simp [hi]
  · rw [if_neg hj]; simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- `comp`-closure for the outer `Y`-substitution: substituting `Y ↦ Y + c` raises the `Z`-degree
by at most `(Y-degree of f) · (Z-degree of c)`. -/
lemma ZdegLE.comp_addYC {f c : F[Z][X][Y]} {d e : ℕ} (hf : ZdegLE f d) (hc : ZdegLE c e) :
    ZdegLE (f.comp (Polynomial.X + c)) (d + f.natDegree * e) := by
  classical
  rw [Polynomial.comp, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  refine ZdegLE_sum _ _ _ (fun a ha ↦ ?_)
  have hCa : ZdegLE (Polynomial.C (f.coeff a)) d := ZdegLE_C (fun i ↦ hf i a)
  have hYc : ZdegLE (Polynomial.X + c) e := (ZdegLE_Y.mono (Nat.zero_le e)).add hc
  have hpow : ZdegLE ((Polynomial.X + c) ^ a) (a * e) := hYc.pow a
  have hbound : ZdegLE (Polynomial.C (f.coeff a) * (Polynomial.X + c) ^ a) (d + a * e) :=
    hCa.mul hpow
  refine hbound.mono ?_
  have ha_le : a ≤ f.natDegree := Polynomial.le_natDegree_of_mem_supp a ha
  exact Nat.add_le_add_left (Nat.mul_le_mul_right e ha_le) d

/-- `ZdegLE1 p d`: every `X`-coefficient of `p : F[Z][X]` is an `F[Z]`-polynomial of degree `≤ d`.
The middle-variable analogue of `ZdegLE`, used to push a `Z`-degree bound through the inner
`X ↦ X + C(C ω)` substitution. -/
def ZdegLE1 (p : F[Z][X]) (d : ℕ) : Prop := ∀ i, (p.coeff i).natDegree ≤ d

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE1_zero (d : ℕ) : ZdegLE1 (0 : F[Z][X]) d := by intro i; simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE1.add {p q : F[Z][X]} {d : ℕ} (hp : ZdegLE1 p d) (hq : ZdegLE1 q d) :
    ZdegLE1 (p + q) d := by
  intro i; rw [Polynomial.coeff_add]
  exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (hp i) (hq i))

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE1.mono {p : F[Z][X]} {d e : ℕ} (hp : ZdegLE1 p d) (hde : d ≤ e) : ZdegLE1 p e :=
  fun i ↦ le_trans (hp i) hde

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE1_sum {ι : Type*} (s : Finset ι) (g : ι → F[Z][X]) (d : ℕ)
    (h : ∀ i ∈ s, ZdegLE1 (g i) d) : ZdegLE1 (∑ i ∈ s, g i) d := by
  classical
  induction s using Finset.induction with
  | empty => simpa using ZdegLE1_zero d
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi)))

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE1.mul {p q : F[Z][X]} {d e : ℕ} (hp : ZdegLE1 p d) (hq : ZdegLE1 q e) :
    ZdegLE1 (p * q) (d + e) := by
  classical
  intro i; rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun x _ ↦ ?_)
  exact le_trans Polynomial.natDegree_mul_le (Nat.add_le_add (hp _) (hq _))

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE1_one : ZdegLE1 (1 : F[Z][X]) 0 := by
  intro i; rw [Polynomial.coeff_one]
  by_cases hi : i = 0
  · rw [if_pos hi]; simp
  · rw [if_neg hi]; simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
lemma ZdegLE1.pow {p : F[Z][X]} {d : ℕ} (hp : ZdegLE1 p d) (a : ℕ) : ZdegLE1 (p ^ a) (a * d) := by
  induction a with
  | zero => simpa using ZdegLE1_one.mono (Nat.zero_le _)
  | succ a ih => rw [pow_succ]; exact (ih.mul hp).mono (by ring_nf; omega)

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- `X` has `Z`-degree `0` at the middle level. -/
lemma ZdegLE1_X : ZdegLE1 (Polynomial.X : F[Z][X]) 0 := by
  intro i; rw [Polynomial.coeff_X]
  by_cases hi : 1 = i
  · rw [if_pos hi]; simp
  · rw [if_neg hi]; simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- `C (C ω)` (constant in `X`, scalar in `Z`) has `Z`-degree `0`. -/
lemma ZdegLE1_CC (ω : F) : ZdegLE1 (Polynomial.C (Polynomial.C ω) : F[Z][X]) 0 := by
  intro i; rw [Polynomial.coeff_C]
  by_cases hi : i = 0
  · rw [if_pos hi]; simp
  · rw [if_neg hi]; simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- Pushing a middle-level `Z`-degree bound through the substitution `X ↦ X + C(C ω)` (which is
`Z`-degree `0`): the bound is preserved. -/
lemma ZdegLE1.comp_addXCC {p : F[Z][X]} {d : ℕ} (hp : ZdegLE1 p d) (ω : F) :
    ZdegLE1 (p.comp (Polynomial.X + Polynomial.C (Polynomial.C ω))) d := by
  classical
  rw [Polynomial.comp, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  refine ZdegLE1_sum _ _ _ (fun a _ ↦ ?_)
  have hCa : ZdegLE1 (Polynomial.C (p.coeff a)) d := by
    intro i; rw [Polynomial.coeff_C]
    by_cases hi : i = 0
    · rw [if_pos hi]; exact hp a
    · rw [if_neg hi]; simp
  have hg : ZdegLE1 ((Polynomial.X + Polynomial.C (Polynomial.C ω)) ^ a) 0 :=
    ((ZdegLE1_X.mono (le_refl 0)).add (ZdegLE1_CC ω)).pow a |>.mono (by simp)
  exact (hCa.mul hg).mono (by simp)

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- Pushing the `Z`-degree bound through the outer map `X ↦ X + C(C ω)` of `shift`. -/
lemma ZdegLE.map_compX {f : F[Z][X][Y]} {d : ℕ} (hf : ZdegLE f d) (ω : F) :
    ZdegLE (f.map (Polynomial.compRingHom (Polynomial.X + Polynomial.C (Polynomial.C ω)))) d := by
  intro i j
  rw [Polynomial.coeff_map, Polynomial.coe_compRingHom]
  exact (ZdegLE1.comp_addXCC (fun i' ↦ hf i' j) ω) i

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- `s = u₀ + Z·u₁ : F[Z]` has `Z`-degree at most `1`. -/
lemma natDegree_u0_add_Z_u1 (u0 u1 : F) :
    (Polynomial.C u0 + Polynomial.X * Polynomial.C u1 : Polynomial F).natDegree ≤ 1 := by
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
  · simp
  · rw [mul_comm]
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) (le_of_eq Polynomial.natDegree_X)

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- **Master `Z`-degree bound for the shift.**  At the Claim-5.4 curve point
`(x, y) = (C ω, u₀ + Z·u₁)`, shifting raises the `Z`-degree by at most the `Y`-degree of `Q`
(since only `y` carries positive `Z`-degree, `≤ 1`).  Hence every constraint output
`((shift Q x y).coeff t).coeff s` is an `F[Z]`-polynomial of degree `≤ d + natDegreeY Q`. -/
lemma ZdegLE_shift {Q : F[Z][X][Y]} {d : ℕ} (hQ : ZdegLE Q d) (ω u0 u1 : F) :
    ZdegLE (Polynomial.Bivariate.shift Q (Polynomial.C ω)
        (Polynomial.C u0 + Polynomial.X * Polynomial.C u1)) (d + Q.natDegree) := by
  unfold Polynomial.Bivariate.shift
  set s : Polynomial F := Polynomial.C u0 + Polynomial.X * Polynomial.C u1 with hs
  have hcdeg : s.natDegree ≤ 1 := natDegree_u0_add_Z_u1 u0 u1
  have hc : ZdegLE (Polynomial.C (Polynomial.C s) : F[Z][X][Y]) s.natDegree := ZdegLE_CC s
  have hcomp : ZdegLE (Q.comp (Polynomial.X + Polynomial.C (Polynomial.C s)))
      (d + Q.natDegree) :=
    (hQ.comp_addYC hc).mono (by
      refine Nat.add_le_add_left ?_ d
      calc Q.natDegree * s.natDegree ≤ Q.natDegree * 1 := Nat.mul_le_mul_left _ hcdeg
        _ = Q.natDegree := Nat.mul_one _)
  exact hcomp.map_compX ω

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The monomial `a · X^i Y^j Z^t` has `Z`-degree `≤ t`. -/
lemma ZdegLE_triMonC (i j t : ℕ) (a : F) : ZdegLE (triMonC (F := F) i j t a) t := by
  intro i' j'
  unfold triMonC
  rw [Polynomial.coeff_monomial]
  by_cases hj : j = j'
  · subst hj; rw [if_pos rfl, Polynomial.coeff_monomial]
    by_cases hi : i = i'
    · subst hi; rw [if_pos rfl]; exact Polynomial.natDegree_monomial_le _
    · rw [if_neg hi]; simp
  · rw [if_neg hj]; simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- If every box index has `Z`-degree `t ≤ zCap`, the assembled `Q` has `Z`-degree `≤ zCap`. -/
lemma ZdegLE_triCoeffsToPoly (box : Finset (ℕ × ℕ × ℕ)) (c : box → F) (zCap : ℕ)
    (hbox : ∀ p ∈ box, p.2.2 ≤ zCap) :
    ZdegLE (triCoeffsToPoly box c) zCap := by
  classical
  unfold triCoeffsToPoly
  refine ZdegLE_sum _ _ _ (fun p _ ↦ ?_)
  exact (ZdegLE_triMonC _ _ _ _).mono (hbox p.1 p.2)

/-! ### Existence of a nonzero kernel element

Rank-nullity over the box: since `#box > #constraints`, the linear constraint map has a nonzero
kernel, mirroring `GuruswamiSudan.exists_nonzero_solution_gen`. -/

open GuruswamiSudan in
/-- There is a nonzero box-coefficient vector in the kernel of the trivariate constraint map. -/
lemma exists_nonzero_triSolution (n m k : ℕ) (ωs : Fin n ↪ F) (u₀ u₁ : Fin n → F) :
    ∃ c : (gsBox n m k) → F, c ≠ 0 ∧
      triConstraintMap (gsBox n m k) m (gsZMax n m k) ωs u₀ u₁ c = 0 := by
  classical
  have h_kernel_nontrivial :
      Module.finrank F ((gsBox n m k) → F) >
        Module.finrank F (Fin n × constraintIndices m × Fin (gsZMax n m k + 1) → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin]
    have h := card_gsBox_gt_constraints n m k
    rw [gt_iff_lt, ← mul_assoc]
    exact h
  have h_inj : ¬ Function.Injective
      (triConstraintMap (gsBox n m k) m (gsZMax n m k) ωs u₀ u₁) := by
    intro h_inj
    exact h_kernel_nontrivial.not_ge
      (LinearMap.finrank_range_of_inj h_inj ▸ Submodule.finrank_le _)
  contrapose! h_inj
  exact LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr fun x hx ↦
    by_contra fun hx' ↦ h_inj x hx' <| by simpa using hx)

/-! ### Box degree facts and the multiplicity bridge -/

open GuruswamiSudan in
omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- For a box index `(i,j,t)`: `i + k·j ≤ Dpg`. -/
lemma gsBox_weighted_le {n m k : ℕ} {p : ℕ × ℕ × ℕ} (_hk : 0 < k) (hp : p ∈ gsBox n m k) :
    1 * p.1 + k * p.2.1 ≤ gsDpg n m k := by
  rw [mem_gsBox] at hp
  have hw := hp.1
  unfold weigthBoundIndices at hw
  rw [Finset.mem_filter] at hw
  have := hw.2
  simp only [Nat.add_sub_cancel] at this
  omega

open GuruswamiSudan in
omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- For a box index `(i,j,t)`: `j ≤ Dpg`. -/
lemma gsBox_Y_le {n m k : ℕ} {p : ℕ × ℕ × ℕ} (hk : 0 < k) (hp : p ∈ gsBox n m k) :
    0 * p.1 + 1 * p.2.1 ≤ gsDpg n m k := by
  have := gsBox_weighted_le hk hp
  have hk1 : 1 ≤ k := hk
  nlinarith [this]

open GuruswamiSudan in
omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- For a box index `(i,j,t)`: `i ≤ Dpg`. -/
lemma gsBox_X_le {n m k : ℕ} {p : ℕ × ℕ × ℕ} (hk : 0 < k) (hp : p ∈ gsBox n m k) :
    1 * p.1 + 0 * p.2.1 ≤ gsDpg n m k := by
  have := gsBox_weighted_le hk hp
  omega

open GuruswamiSudan in
omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- For a box index `(i,j,t)`: `t ≤ zCap`. -/
lemma gsBox_Z_le {n m k : ℕ} {p : ℕ × ℕ × ℕ} (hp : p ∈ gsBox n m k) :
    p.2.2 ≤ gsZCap n m k := by
  rw [mem_gsBox] at hp; exact hp.2

open GuruswamiSudan Polynomial.Bivariate in
omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The `Y`-degree of the box-assembled `Q` is at most `Dpg`. -/
lemma natDegree_gsQ_le {n m k : ℕ} (hk : 0 < k) (c : (gsBox n m k) → F) :
    (triCoeffsToPoly (gsBox n m k) c).natDegree ≤ gsDpg n m k := by
  have h := natWeightedDegree_triCoeffsToPoly_le (gsBox n m k) c 0 1 (gsDpg n m k)
    (fun p hp ↦ gsBox_Y_le hk hp)
  rwa [← degreeY_as_weighted_deg, natDegreeY] at h

open GuruswamiSudan Polynomial.Bivariate in
omit [DecidableEq (RatFunc F)] in
/-- **Multiplicity bridge.**  If `c` lies in the kernel of the constraint map, the assembled
nonzero `Q` has root multiplicity `≥ m` at every curve point `(C ωᵢ, u₀ᵢ + Z·u₁ᵢ)`.

The kernel forces every `Z`-coefficient (up to `zMax`) of each order-`< m` shifted coefficient to
vanish; combined with the `Z`-degree budget (`ZdegLE_shift` + the box bound), the whole `F[Z]`
coefficient vanishes, and `triv_rootMultiplicity_ge_of_shift_zero` yields multiplicity `≥ m`. -/
lemma gsQ_multiplicity {n m k : ℕ} (hk : 0 < k) (ωs : Fin n ↪ F) (u₀ u₁ : Fin n → F)
    (c : (gsBox n m k) → F) (hc : c ≠ 0)
    (hker : triConstraintMap (gsBox n m k) m (gsZMax n m k) ωs u₀ u₁ c = 0) (i : Fin n) :
    (m : ℕ) ≤ rootMultiplicity (triCoeffsToPoly (gsBox n m k) c)
        (Polynomial.C (ωs i)) (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i)) := by
  classical
  set Q := triCoeffsToPoly (gsBox n m k) c with hQdef
  set x := Polynomial.C (ωs i) with hx
  set y := Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i) with hy
  -- Q ≠ 0
  have hQne : Q ≠ 0 := triCoeffsToPoly_ne_zero (gsBox n m k) c hc
  -- Q has Z-degree ≤ zCap and Y-degree ≤ Dpg
  have hQz : ZdegLE Q (gsZCap n m k) :=
    ZdegLE_triCoeffsToPoly (gsBox n m k) c (gsZCap n m k) (fun p hp ↦ gsBox_Z_le hp)
  have hQy : Q.natDegree ≤ gsDpg n m k := natDegree_gsQ_le hk c
  -- the shifted constraint output has Z-degree ≤ zMax
  have hshiftZ : ZdegLE (shift Q x y) (gsZMax n m k) := by
    refine (ZdegLE_shift hQz (ωs i) (u₀ i) (u₁ i)).mono ?_
    rw [gsZMax]; exact Nat.add_le_add_left hQy _
  -- apply the order-of-vanishing criterion
  refine triv_rootMultiplicity_ge_of_shift_zero hQne (fun s t hst ↦ ?_)
  -- every Z-coefficient up to zMax vanishes, and Z-degree ≤ zMax ⟹ the F[Z] coeff is 0
  apply Polynomial.ext
  intro z
  rw [Polynomial.coeff_zero]
  by_cases hz : z ≤ gsZMax n m k
  · -- use the kernel: the (i, (s,t), z) coordinate is 0
    have hst' : (s, t) ∈ constraintIndices m := by
      unfold constraintIndices
      rw [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range,
        Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, hst⟩
    have hcoord := congr_fun hker (i, ⟨(s, t), hst'⟩, ⟨z, Nat.lt_succ_of_le hz⟩)
    simp only [triConstraintMap, LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply,
      triEvalConstraint, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hcoord
    rw [triCoeffsToPolyₗ_apply] at hcoord
    exact hcoord
  · -- beyond the Z-degree budget: the coefficient is 0 by the degree bound
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hshiftZ s t) (by omega))

/-! ### Box degree facts for the `ModifiedGuruswami` degree fields -/

open GuruswamiSudan Polynomial.Bivariate in
omit [DecidableEq (RatFunc F)] in
/-- The `(1,k)`-weighted degree of the box-assembled `Q` is at most `Dpg`. -/
lemma natWeightedDegree_gsQ_1k_le {n m k : ℕ} (hk : 0 < k) (c : (gsBox n m k) → F) :
    natWeightedDegree (triCoeffsToPoly (gsBox n m k) c) 1 k ≤ gsDpg n m k :=
  natWeightedDegree_triCoeffsToPoly_le (gsBox n m k) c 1 k (gsDpg n m k)
    (fun _p hp ↦ gsBox_weighted_le hk hp)

open GuruswamiSudan Polynomial.Bivariate in
omit [DecidableEq (RatFunc F)] in
/-- The `X`-degree of the box-assembled `Q` is at most `Dpg`. -/
lemma degreeX_gsQ_le {n m k : ℕ} (hk : 0 < k) (c : (gsBox n m k) → F) :
    degreeX (triCoeffsToPoly (gsBox n m k) c) ≤ gsDpg n m k := by
  have h := natWeightedDegree_triCoeffsToPoly_le (gsBox n m k) c 1 0 (gsDpg n m k)
    (fun p hp ↦ gsBox_X_le hk hp)
  rwa [← degreeX_as_weighted_deg] at h

open GuruswamiSudan Polynomial.Bivariate in
omit [DecidableEq (RatFunc F)] in
/-- `k · (Y-degree of the box-assembled `Q`) ≤ Dpg` (the `Y`-degree is `≤ Dpg/k`). -/
lemma k_mul_natDegreeY_gsQ_le {n m k : ℕ} (hk : 0 < k) (c : (gsBox n m k) → F) :
    k * natDegreeY (triCoeffsToPoly (gsBox n m k) c) ≤ gsDpg n m k := by
  classical
  set Q := triCoeffsToPoly (gsBox n m k) c with hQ
  have hwd : natWeightedDegree Q 0 k ≤ gsDpg n m k :=
    natWeightedDegree_triCoeffsToPoly_le (gsBox n m k) c 0 k (gsDpg n m k)
      (fun p hp ↦ by
        have := gsBox_weighted_le hk hp; omega)
  refine le_trans ?_ hwd
  rcases eq_or_ne Q 0 with hQ0 | hQ0
  · simp [hQ0, natDegreeY]
  · -- the maximal Y-index `d := natDegreeY Q` is in the support
    have hd : natDegreeY Q ∈ Q.support := by
      rw [natDegreeY, Polynomial.mem_support_iff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hQ0
    have := Finset.le_sup (f := fun mm ↦ 0 * (Q.coeff mm).natDegree + k * mm) hd
    simpa [natWeightedDegree] using this

/-! ### `D_YZ` upper bound and box facts -/

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- A `Finset ℕ` all of whose elements are `≤ B` has `(max).getD 0 ≤ B`.  This is the
`Option.getD`-wrapped form of `Finset.max_le_iff`, matching the shape of `D_YZ`. -/
lemma finset_max_getD_le {s : Finset ℕ} {B : ℕ} (h : ∀ x ∈ s, x ≤ B) :
    (s.max).getD 0 ≤ B := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.max_empty, Option.getD]; exact Nat.zero_le _
  · obtain ⟨b, hb⟩ := Finset.max_of_nonempty hne
    rw [hb]
    exact h b (Finset.mem_of_max hb)

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- **`D_YZ` upper bound.**  If `Q` has `Y`-degree `≤ d` and every bivariate coefficient has
`Z`-degree `≤ e` (`ZdegLE Q e`), then `D_YZ Q ≤ d + e`.

`D_YZ Q = maxⱼ maxₖ (j + Zdeg(coeff of `X^j Y^k`))`; the outer `j` is a `Y`-degree `≤ d` and every
`Z`-degree term is `≤ e`, so each summand is `≤ d + e`. -/
lemma D_YZ_le_of_ZdegLE {Q : F[Z][X][Y]} {d e : ℕ}
    (hY : Polynomial.Bivariate.natDegreeY Q ≤ d) (hZ : ZdegLE Q e) :
    Trivariate.D_YZ Q ≤ d + e := by
  classical
  unfold Trivariate.D_YZ
  apply finset_max_getD_le
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  apply finset_max_getD_le
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨kx, hkx, rfl⟩ := hy
  have hjd : j ≤ d := le_trans (Polynomial.le_natDegree_of_mem_supp j hj) hY
  have hze : (Polynomial.Bivariate.coeff Q j kx).natDegree ≤ e := by
    unfold Polynomial.Bivariate.coeff
    exact hZ j kx
  omega

end ModifiedGuruswamiHelpers


omit [DecidableEq (RatFunc F)] in
/-- Claim 5.4 from [BCIKS20].
It essentially claims that there exists a solution to the Guruswami-Sudan constraints above.

NOTE: As currently formalized this lemma is **false** for `n = 0` or `k = 0` (see
`modified_guruswami_unsat_of_n_zero` / `modified_guruswami_unsat_of_k_zero`): the degree bound
`D_X` collapses to `0` and the strict degree constraints become unsatisfiable.  The statement
below therefore carries the proven-necessary side conditions `0 < n` and `0 < k` (the paper's
non-degenerate regime is `k + 1 ≤ n`, `1 ≤ m`).

It also carries two **regime side conditions** on the construction parameters, both honest
parameter inequalities (no per-`Q` assumption — the `Q`-specific bounds are *proved* from them):

* `hDx`: the (integer) degree cap `gsDpg = ⌊D_X⌋₊` of the construction box lies strictly below the
  real bound `D_X = (m+½)·√ρ·n`.  This is forced because the three strict `ModifiedGuruswami`
  degree fields (`Q_deg`, `Q_deg_X`, `Q_D_Y`) all reduce to `(gsDpg : ℝ) < D_X`, which FAILS exactly
  when `D_X` is attained by an integer (e.g. `k+1=4, n=1, m=0`).  In the paper's non-integer regime
  it holds; we expose it as a hypothesis rather than silently weaken the (uneditable)
  `ModifiedGuruswami` fields from `<` to `≤`.

* `hYZ`: the box's `Y`+`Z` degree budget `gsDpg + gsZCap` fits under the `YZ`-degree bound.  The
  current `D_YZ` definition adds a monomial's `Y`-degree to the `Z`-degree of its transpose, so a
  kernel element with nonzero high-`Z` coefficients on a transpose-paired pair realizes
  `D_YZ Q ≈ gsZCap`.  With the (uneditable, counting-locked) budget `gsZCap = #constraints · gsDpg`,
  the only honest way to guarantee `Q_D_YZ` for an arbitrary kernel element is to assume the box
  budget itself fits the bound; we then *prove* `D_YZ Q ≤ gsDpg + gsZCap ≤ RHS` via
  `D_YZ_le_of_ZdegLE`.  (Shrinking `gsZCap` to make this unconditional would require re-deriving a
  quantitative bivariate counting gap `numVars − numConstraints ≥ g`; with the structural gap
  `g = 1` the minimal feasible `gsZCap` is exactly `#constraints · gsDpg`, so this side condition is
  the faithful regime statement for the present infrastructure.) -/
lemma modified_guruswami_has_a_solution {m n k : ℕ} (_hn : 0 < n) (hk : 0 < k)
    {ωs : Fin n ↪ F} {u₀ u₁ : Fin n → F}
    (hDx : ((gsDpg n m k : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    (hYZ : ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n))) :
    ∃ Q : F[Z][X][Y], ModifiedGuruswami m n k ωs Q u₀ u₁ := by
  classical
  -- a nonzero kernel element gives the assembled candidate `Q`
  obtain ⟨c, hc_ne, hc_ker⟩ := exists_nonzero_triSolution n m k ωs u₀ u₁
  set Q := triCoeffsToPoly (gsBox n m k) c with hQdef
  have hQne : Q ≠ 0 := triCoeffsToPoly_ne_zero (gsBox n m k) c hc_ne
  -- real-arithmetic helpers
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Q_ne_0
    exact hQne
  · -- Q_deg : natWeightedDegree Q 1 k < D_X
    have h1 : (natWeightedDegree Q 1 k : ℝ) ≤ (gsDpg n m k : ℝ) := by
      exact_mod_cast natWeightedDegree_gsQ_1k_le hk c
    exact lt_of_le_of_lt h1 hDx
  · -- Q_multiplicity
    intro i
    exact gsQ_multiplicity hk ωs u₀ u₁ c hc_ne hc_ker i
  · -- Q_deg_X : degreeX Q < D_X
    have h1 : (degreeX Q : ℝ) ≤ (gsDpg n m k : ℝ) := by
      exact_mod_cast degreeX_gsQ_le hk c
    exact lt_of_le_of_lt h1 hDx
  · -- Q_D_Y : D_Y Q < D_X / k
    have hkD : (k : ℝ) * (D_Y Q : ℝ) ≤ (gsDpg n m k : ℝ) := by
      have := k_mul_natDegreeY_gsQ_le hk c
      have : (k * natDegreeY Q : ℕ) ≤ gsDpg n m k := this
      push_cast at this ⊢
      simpa [D_Y, mul_comm] using (by exact_mod_cast this :
        (k : ℝ) * (natDegreeY Q : ℝ) ≤ (gsDpg n m k : ℝ))
    have : (k : ℝ) * (D_Y Q : ℝ) < D_X ((k + 1) / (n : ℚ)) n m := lt_of_le_of_lt hkD hDx
    rw [lt_div_iff₀ hkR, mul_comm]
    convert this using 2
  · -- Q_D_YZ : D_YZ Q ≤ RHS
    have hYdeg : Polynomial.Bivariate.natDegreeY Q ≤ gsDpg n m k := natDegree_gsQ_le hk c
    have hZdeg : ZdegLE Q (gsZCap n m k) :=
      ZdegLE_triCoeffsToPoly (gsBox n m k) c (gsZCap n m k) (fun p hp ↦ gsBox_Z_le hp)
    have hbound : Trivariate.D_YZ Q ≤ gsDpg n m k + gsZCap n m k :=
      D_YZ_le_of_ZdegLE hYdeg hZdeg
    calc (D_YZ Q : ℝ) ≤ ((gsDpg n m k + gsZCap n m k : ℕ) : ℝ) := by exact_mod_cast hbound
      _ ≤ n * (m + 1 / (2 : ℚ)) ^ 3 / (6 * Real.sqrt ((k + 1) / n)) := hYZ

end

variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
         [Finite F]

noncomputable instance {α : Type} (s : Set α) [inst : Finite s] : Fintype s := Fintype.ofFinite _

/-- The set `S` (equation 5.2 of [BCIKS20]). -/
noncomputable def coeffs_of_close_proximity (ωs : Fin n ↪ F) (δ : ℚ) (u₀ u₁ : Fin n → F) : Finset F := Set.toFinset { z | ∃ v : ReedSolomon.code ωs (k + 1), δᵣ(u₀ + z • u₁, v) ≤ δ}

open Polynomial

omit [DecidableEq (RatFunc F)] in
/-- There exists a `δ`-close polynomial `P_z` for each `z` from the set `S`. -/
lemma exists_Pz_of_coeffs_of_close_proximity
    {k : ℕ}
  {z : F}
  (hS : z ∈ coeffs_of_close_proximity (k := k) ωs δ u₀ u₁) :
  ∃ Pz : F[X], Pz.natDegree ≤ k ∧ δᵣ(u₀ + z • u₁, Pz.eval ∘ ωs) ≤ δ := by
    unfold coeffs_of_close_proximity at hS
    obtain ⟨w, hS, dist⟩ : ∃ a ∈ ReedSolomon.code ωs (k + 1), ↑δᵣ(u₀ + z • u₁, a) ≤ δ := by
      simpa using hS
    obtain ⟨p, hS⟩ : ∃ y ∈ degreeLT F (k + 1), (ReedSolomon.evalOnPoints ωs) y = w := by
      simpa using hS
    exact ⟨p, ⟨
      by if h : p = 0
         then simp [h]
         else rw [mem_degreeLT, degree_eq_natDegree h, Nat.cast_lt] at hS; grind,
      by convert dist; rw [←hS.2]; rfl
    ⟩⟩

/-- The `δ`-close polynomial `Pz` for each `z` from the set `S` (`coeffs_of_close_proximity`). -/
noncomputable def Pz {k : ℕ} {z : F} (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁) : F[X] :=
  (exists_Pz_of_coeffs_of_close_proximity (n := n) (k := k) hS).choose

omit [DecidableEq (RatFunc F)] in
/-- The chosen close polynomial `Pz` has degree at most `k`. -/
lemma Pz_natDegree_le {k : ℕ} {z : F}
    (hS : z ∈ coeffs_of_close_proximity (k := k) ωs δ u₀ u₁) :
    (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hS).natDegree
      ≤ k := by
  exact (Classical.choose_spec
    (exists_Pz_of_coeffs_of_close_proximity (n := n) (k := k) hS)).1

omit [DecidableEq (RatFunc F)] in
/-- The chosen close polynomial `Pz` is `δ`-close to the corresponding line word. -/
lemma Pz_relDist_le {k : ℕ} {z : F}
    (hS : z ∈ coeffs_of_close_proximity (k := k) ωs δ u₀ u₁) :
    δᵣ(u₀ + z • u₁,
        (Pz (n := n) (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) hS).eval
          ∘ ωs) ≤ δ := by
  exact (Classical.choose_spec
    (exists_Pz_of_coeffs_of_close_proximity (n := n) (k := k) hS)).2

/-- *Tagged-fiber pigeonhole* (self-contained combinatorial core of [BCIKS20] Prop 5.5).

If every element of a finite index set `S : Finset ι` carries a `tag x` lying in a finite tag
set `T : Finset τ` (`hmaps`), and `T` is nonempty, then some tag class `y ∈ T` is shared by at
least `#S / #T` (nat division = `⌊#S/#T⌋`, the floor of the average fiber size) elements of `S`.

This is the abstract pigeonhole behind Prop 5.5: there the index set is `S =
coeffs_of_close_proximity` and the tag would be the irreducible `Y`-factor of `Q` whose
graph passes through `(z, Pz)`, of which there are at most `D_Y Q`.  Specialized with `#T ≤ D_Y Q`
this yields a fiber of size `≥ #S / D_Y Q`; whether that exceeds the strict target
`#S / (2 · D_Y Q)` is *not* a free consequence (nat division: `#S/(2M) < #S/M` fails for small
`#S`, e.g. `#S = 1, M = 2`), but holds in the paper's regime where `#S` is large relative to
`D_Y Q` (i.e. `δ` below the list-decoding radius). -/
lemma tagged_fiber_pigeonhole {ι τ : Type} [DecidableEq τ] (S : Finset ι) (tag : ι → τ)
    (T : Finset τ) (hmaps : ∀ x ∈ S, tag x ∈ T) (hT : T.Nonempty) :
    ∃ y ∈ T, #S / #T ≤ #{x ∈ S | tag x = y} := by
  classical
  refine exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps hT ?_
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self (#S) (#T)

end BCIKS20ProximityGapSection5

end ProximityGap
