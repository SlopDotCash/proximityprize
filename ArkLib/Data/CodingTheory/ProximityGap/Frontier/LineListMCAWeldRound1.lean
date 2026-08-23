/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListReduction
import ArkLib.Data.CodingTheory.ProximityGap.FarLineIncidenceEquivariance
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The line-list ↔ MCA weld (#466 lane L1; re-derivation of the phantom #464 brick)

This file lands the missing middle link between the two halves of the positive-side
programme, previously claimed on the #464 thread (2026-06-26) but never landed
(dossier v3 §12 "phantom bricks"):

* the **MCA side** (`Errors.lean` / `FarCosetExplosion.lean`): the bad event `mcaEvent`
  and its scalar filter, whose normalized count is `ε_mca`, feeding `mcaDeltaStar`;
* the **line-list side** (`LineListReduction.lean`): `lineBadScalars` ≤
  `lineAppearingCodewords · ⌊n/a⌋`, isolating the affine-line list size `Λ` as the single
  production obligation.

The weld is the two-step inclusion, derived here:

  `{γ : mcaEvent}  ⊆  explainableScalars  ⊆  lineBadScalars`   (at `a ≤ (1−δ)·n`)

(first step: `mcaEvent` simply *is* explainability plus a no-joint clause — drop the
clause; second step: an explainability witness set `S` has `|S| ≥ (1−δ)n ≥ a` and sits
inside the agreement set of its codeword with the line). Both agreement notions coincide
exactly — `mcaEvent`'s witness clause `∀ i ∈ S, w i = u₀ i + γ • u₁ i` puts
`S ⊆ agreeSet w (u₀ + γ•u₁)` — so **no definitional mismatch exists** between the two
bad-scalar notions; the far-restriction is NOT needed for this (upper-bound) direction.

## Results (all axiom-clean)

1. `mcaEvent_badScalars_card_le_lineList_mul` — for a nonvanishing direction `u₁` and
   threshold `a ≤ (1−δ)·n`, `#{γ : mcaEvent} ≤ Λ · ⌊n/a⌋` where
   `Λ = #lineAppearingCodewords`. (The thread's claimed shape had a `FarFromCode`
   hypothesis; it is *unnecessary* for this direction and is dropped — a strictly
   stronger statement. Far only matters for the matching *equality/lower* bound,
   already landed as `FarCosetExplosion.badScalars_eq_explainable`.)
2. `mcaDeltaStar_ge_of_lineList_budget` — the floor consumer: a uniform line-list
   budget `Λ ≤ L` on nonvanishing directions, a named control on the vanishing-direction
   residual, and the fit `L·⌊n/a⌋ / q ≤ ε*` yield `δ ≤ mcaDeltaStar` via
   `le_mcaDeltaStar_of_good`. (Deviation from the thread shape: the fit is stated as
   `(L·⌊n/a⌋ : ℝ≥0∞)/q ≤ ε*` rather than `L·⌊n/a⌋ ≤ q·ε*` — the division form is what
   `epsMCA` consumes directly; they agree for finite nonzero `q`. The vanishing-direction
   hypothesis `hvanish` is an honest explicit residual: `epsMCA` sups over ALL stacks,
   and the heavy-scalar fiber bound genuinely needs `u₁ i ≠ 0` everywhere.)
3. `aligned_line_lambda_ge_q` — the refuter: if `(u₀,u₁)` are constant on a size-`≥ a`
   subset with the `u₁`-constant nonzero, then EVERY constant codeword appears on the
   line, so `Λ ≥ q` and the line-list budget is worthless there. This forces any
   production budget to restrict to far (in particular non-aligned) directions.

## References

* `LineListReduction.lean` (`lineBadScalars`, `lineAppearingCodewords`,
  `lineBadScalars_card_le_lineAppearingCodewords_card_mul`);
* `FarCosetExplosion.lean` (`badScalars_eq_explainable`, `epsMCA_ge_far_incidence`);
* `FarLineIncidenceEquivariance.lean` (`explainableScalars`);
* `MCAThresholdLedger.lean` (`mcaDeltaStar`, `le_mcaDeltaStar_of_good`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.LineListMCAWeld.Round1

open ProximityGap ProximityGap.SpikeFloor ProximityGap.Ownership
open ProximityGap.FarCosetExplosion ProximityGap.MCAThresholdLedger

/-! ## Generic half: the mcaEvent filter is inside the explainable-scalar set,
and a uniform bad-scalar budget bounds `ε_mca` and floors `mcaDeltaStar`. -/

section Generic

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **Weld step 1 (generic, unconditional).** The MCA bad-scalar filter sits inside the
explainable-scalar set: `mcaEvent` is explainability *plus* a no-joint clause, so dropping
the clause is an inclusion. (For far directions this is an equality —
`FarCosetExplosion.badScalars_eq_explainable` — but the upper-bound direction needs no
far hypothesis.) -/
theorem mcaEvent_filter_subset_explainableScalars
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    Finset.univ.filter (fun γ : F => mcaEvent C δ u₀ u₁ γ)
      ⊆ explainableScalars (F := F) C δ u₀ u₁ := by
  intro γ hγ
  rw [Finset.mem_filter] at hγ
  obtain ⟨-, S, hS, hline, -⟩ := hγ
  rw [explainableScalars, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, S, hS, hline⟩

open Classical in
/-- **Uniform bad-scalar budget ⟹ `ε_mca` bound.** If every stack has at most `B` bad
scalars, then `ε_mca(C, δ) ≤ B/q`. This is the generic consumer turning per-line counting
into the probability bound `mcaDeltaStar` needs. -/
theorem epsMCA_le_of_uniform_mcaEvent_budget
    (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (hbad : ∀ u₀ u₁ : ι → A,
      (Finset.univ.filter (fun γ : F => mcaEvent C δ u₀ u₁ γ)).card ≤ B) :
    epsMCA (F := F) (A := A) C δ ≤ (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast hbad (u 0) (u 1)

open Classical in
/-- **Floor consumer (generic).** A uniform bad-scalar budget `B` with fit `B/q ≤ ε*`
puts `δ` below the formal MCA threshold, via `le_mcaDeltaStar_of_good`. -/
theorem mcaDeltaStar_ge_of_uniform_mcaEvent_budget
    (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} (hδ : δ ≤ 1) (B : ℕ)
    (hbad : ∀ u₀ u₁ : ι → A,
      (Finset.univ.filter (fun γ : F => mcaEvent C δ u₀ u₁ γ)).card ≤ B)
    (hfit : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := A) C εstar :=
  le_mcaDeltaStar_of_good C εstar hδ
    (le_trans (epsMCA_le_of_uniform_mcaEvent_budget C δ B hbad) hfit)

end Generic

/-! ## RS half: the middle link and the welded count bound. -/

section RS

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **Weld step 2 — THE MIDDLE LINK.** For the Reed–Solomon code, every explainable
scalar at radius `δ` is a line-list bad scalar at any agreement threshold
`a ≤ (1−δ)·n`: the explainability witness set `S` has `|S| ≥ (1−δ)n ≥ a` and is
contained in the agreement set of its codeword with the line word. The two bad-scalar
notions (`mcaEvent`-side real-threshold witness sets vs `lineBadScalars`-side natural
agreement counts) genuinely coincide across this bridge — no definitional mismatch. -/
theorem explainableScalars_subset_lineBadScalars
    (dom : Fin n ↪ F) (k a : ℕ) (δ : ℝ≥0)
    (hthr : (a : ℝ≥0) ≤ (1 - δ) * (n : ℝ≥0)) (u₀ u₁ : Fin n → F) :
    explainableScalars (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁
      ⊆ lineBadScalars dom k a u₀ u₁ := by
  intro γ hγ
  simp only [explainableScalars, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
  obtain ⟨S, hS, w, hwC, hw⟩ := hγ
  simp only [lineBadScalars, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨w, hwC, ?_⟩
  have hcard : a ≤ S.card := by
    have h1 : (a : ℝ≥0) ≤ (1 - δ) * ((Fintype.card (Fin n) : ℕ) : ℝ≥0) := by
      simpa [Fintype.card_fin] using hthr
    exact_mod_cast le_trans h1 hS
  refine le_trans hcard (Finset.card_le_card fun i hi => ?_)
  simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hw i hi

open Classical in
/-- **THE WELD (result 1).** For any nonvanishing direction `u₁` and agreement
threshold `a ≤ (1−δ)·n`, the MCA bad-scalar count injects into the line-list bound:

  `#{γ : mcaEvent(RS, δ, u₀, u₁, γ)} ≤ #lineAppearingCodewords · ⌊n/a⌋`.

Chains weld step 1, the middle link, and
`lineBadScalars_card_le_lineAppearingCodewords_card_mul`. No far hypothesis is needed
(strictly stronger than the thread's claimed shape). -/
theorem mcaEvent_badScalars_card_le_lineList_mul
    (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a) (δ : ℝ≥0)
    (hthr : (a : ℝ≥0) ≤ (1 - δ) * (n : ℝ≥0))
    (u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ (lineAppearingCodewords dom k a u₀ u₁).card * (n / a) := by
  refine le_trans (Finset.card_le_card ?_)
    (lineBadScalars_card_le_lineAppearingCodewords_card_mul dom k a ha u₀ u₁ hu₁)
  exact subset_trans
    (mcaEvent_filter_subset_explainableScalars _ δ u₀ u₁)
    (explainableScalars_subset_lineBadScalars dom k a δ hthr u₀ u₁)

open Classical in
/-- Budgeted form of the weld: a line-list budget `Λ ≤ L` bounds the MCA bad-scalar
count by `L · ⌊n/a⌋`. -/
theorem mcaEvent_badScalars_card_le_of_lineListBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a) (δ : ℝ≥0)
    (hthr : (a : ℝ≥0) ≤ (1 - δ) * (n : ℝ≥0))
    (u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) {L : ℕ}
    (hL : LineListBudgeted dom k a u₀ u₁ L) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ L * (n / a) :=
  le_trans
    (mcaEvent_badScalars_card_le_lineList_mul dom k a ha δ hthr u₀ u₁ hu₁)
    (Nat.mul_le_mul_right (n / a) hL)

open Classical in
/-- **The floor consumer (result 2).** A uniform line-list budget `L` on nonvanishing
directions, an explicit control `hvanish` on the vanishing-direction residual (an honest
named obligation: `ε_mca` sups over ALL stacks, and the heavy-scalar fiber argument
needs `u₁ i ≠ 0` everywhere), and the fit `L·⌊n/a⌋ / q ≤ ε*` give the MCA-threshold
floor `δ ≤ mcaDeltaStar(RS, ε*)` through `le_mcaDeltaStar_of_good`.

⚠️ **VACUOUS AT THE PRIZE BUDGET (referee finding, 2026-07-01):** the `hL` hypothesis
quantifies over ALL nonvanishing directions, and the constant direction `u₁ = 1` is
nonvanishing yet aligned, so `hL` is unsatisfiable for any `L < q` once `1 ≤ k`
(`LineListMCAWeld.not_forall_nonvanishing_lineListBudgeted_of_lt_field`).  Kept as the
round-1 historical form; the PRODUCTION consumer is the far-restricted
`LineListMCAWeld.mcaDeltaStar_ge_of_farLineListBudgeted` (root file), whose budget
hypothesis excludes aligned directions and is not refuted by them. -/
theorem mcaDeltaStar_ge_of_lineList_budget
    (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a) (δ : ℝ≥0) (hδ : δ ≤ 1)
    (hthr : (a : ℝ≥0) ≤ (1 - δ) * (n : ℝ≥0)) (L : ℕ) (εstar : ℝ≥0∞)
    (hL : ∀ u₀ u₁ : Fin n → F, (∀ i, u₁ i ≠ 0) → LineListBudgeted dom k a u₀ u₁ L)
    (hvanish : ∀ u₀ u₁ : Fin n → F, ¬ (∀ i, u₁ i ≠ 0) →
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ L * (n / a))
    (hfit : ((L * (n / a) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar := by
  refine mcaDeltaStar_ge_of_uniform_mcaEvent_budget _ εstar hδ (L * (n / a)) ?_ hfit
  intro u₀ u₁
  by_cases hu₁ : ∀ i, u₁ i ≠ 0
  · exact mcaEvent_badScalars_card_le_of_lineListBudgeted
      dom k a ha δ hthr u₀ u₁ hu₁ (hL u₀ u₁ hu₁)
  · exact hvanish u₀ u₁ hu₁

open Classical in
/-- **The refuter (result 3).** If `u₀` and `u₁` are constant (values `b`, `v`) on a
subset `T` of size at least `a`, with `v ≠ 0`, then EVERY constant codeword appears on
the line with agreement ≥ `a` (at scalar `γ = (t−b)/v` the line is constantly `t` on
`T`), so the line list has size at least `q`. Aligned lines therefore make the
line-list budget worthless — any production budget `L < q` must exclude them, i.e.
restrict to far directions (`FarFromCode` kills exactly such `u₁`, whose coset
minimum weight on witness-sized sets would be violated by an interpolating codeword
once `a` is witness-sized and `k ≥ 1`). -/
theorem constantPatch_line_lambda_ge_q
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (T : Finset (Fin n)) (hT : a ≤ T.card)
    (b v : F) (hv : v ≠ 0)
    (h₀ : ∀ i ∈ T, u₀ i = b) (h₁ : ∀ i ∈ T, u₁ i = v) :
    Fintype.card F ≤ (lineAppearingCodewords dom k a u₀ u₁).card := by
  have hconst_mem : ∀ t : F,
      (fun _ : Fin n => t) ∈ lineAppearingCodewords dom k a u₀ u₁ := by
    intro t
    rw [lineAppearingCodewords, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, (t - b) / v, ?_⟩
    · -- the constant codeword: `C t` has degree ≤ 0 < k
      refine ⟨Polynomial.C t, lt_of_le_of_lt Polynomial.degree_C_le ?_, ?_⟩
      · exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
      · funext i; simp
    · -- at `γ = (t−b)/v` the line equals `t` on all of `T`
      refine le_trans hT (Finset.card_le_card ?_)
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [h₀ i hi, h₁ i hi, smul_eq_mul, div_mul_cancel₀ _ hv]
      ring
  calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
    _ ≤ (lineAppearingCodewords dom k a u₀ u₁).card := by
        refine Finset.card_le_card_of_injOn (fun t => fun _ : Fin n => t)
          (fun t _ => hconst_mem t) ?_
        intro t _ t' _ h
        have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
        exact congrFun h i0

end RS

end ProximityGap.LineListMCAWeld.Round1

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.LineListMCAWeld.Round1.mcaEvent_filter_subset_explainableScalars
#print axioms ProximityGap.LineListMCAWeld.Round1.epsMCA_le_of_uniform_mcaEvent_budget
#print axioms ProximityGap.LineListMCAWeld.Round1.mcaDeltaStar_ge_of_uniform_mcaEvent_budget
#print axioms ProximityGap.LineListMCAWeld.Round1.explainableScalars_subset_lineBadScalars
#print axioms ProximityGap.LineListMCAWeld.Round1.mcaEvent_badScalars_card_le_lineList_mul
#print axioms ProximityGap.LineListMCAWeld.Round1.mcaEvent_badScalars_card_le_of_lineListBudgeted
#print axioms ProximityGap.LineListMCAWeld.Round1.mcaDeltaStar_ge_of_lineList_budget
#print axioms ProximityGap.LineListMCAWeld.Round1.constantPatch_line_lambda_ge_q
