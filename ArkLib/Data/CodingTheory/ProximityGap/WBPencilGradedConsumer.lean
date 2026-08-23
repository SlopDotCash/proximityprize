/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilGradedLadder

/-!
# The graded ladder consumer (#371): ε_mca and δ* floors at every fixed slice past UDR

Wires WB-6 (`badScalars_card_le_of_graded`) into the threshold engine.  The
single named residual per grade is `GradedAnchoredTwinFree`: every
doubly-WB-solvable stack admits representations whose grade-`c` pencil selection
is anchored and twin-free.  Under it:

* `epsMCA_le_of_graded` — `ε_mca(RS, δ) ≤ gradedBudget/q` at every radius
  `δ ≤ w/n`, where `gradedBudget = (w+1) + Σ_{j<c} C(n,n−j) + C(n,c)·c(w+1)` —
  polynomial in `n` for fixed `c`;
* `le_mcaDeltaStar_of_graded` — the δ* floor: every such radius is good once the
  budget clears `ε*`.

Since the generic grade is `1 + (slices past the unique-decoding boundary)`
(probe-pinned at grades 1–3), this gives, per fixed slice depth, the first
machine-checked conditional δ* floors PAST unique decoding on the pencil route —
with the residual's structure itself probe-pinned (twins = torus-normalizer
alignment classes).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The grade-`c` count budget. -/
def gradedBudget (n _k w c : ℕ) : ℕ :=
  (w + 1) + (∑ j ∈ Finset.range c, n.choose (n - j)) + n.choose c * (c * (w + 1))

/-- **The per-grade named residual**: every doubly-WB-solvable stack admits WB
representations whose grade-`c` pencil selection is anchored and twin-free.
Probe record: generic stacks at `1 + (slices past boundary) = c` satisfy it
(grades 1–3 pinned); the twin exceptions are exactly the torus-normalizer
alignment classes (`probe_wb_twin_classification.py`, 3/3). -/
def GradedAnchoredTwinFree (dom : Fin n ↪ F) (k w c : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, WBSolvable dom k w u₀ → WBSolvable dom k w u₁ →
    ∃ ℓ₀ R₀ ℓ₁ R₁ : F[X],
      ℓ₀.natDegree ≤ w ∧ ℓ₁.natDegree ≤ w ∧
      R₀.natDegree ≤ w + k - 1 ∧ R₁.natDegree ≤ w + k - 1 ∧
      (∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i)) ∧
      (∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i)) ∧
      ∃ (J : WCol n k w → Fin (3 * w + k)) (C₀ : Finset (WCol n k w))
        (τ : WCol n k w → WCol n k w),
        C₀.card = c ∧
        (pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).det ≠ 0 ∧
        (∀ T ∈ Finset.powersetCard C₀.card (Finset.univ : Finset (Fin n)),
          gradedCoinc dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ T ≠ 0)

open Classical in
omit [DecidableEq F] in
/-- Fixed-stack probability form of the graded consumer: under the grade-`c` residual,
every stack's bad-scalar probability is bounded by the WB-6 graded budget divided by the
field size. -/
theorem mcaEvent_prob_le_of_gradedResidual (dom : Fin n ↪ F) {k w c : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) (hc : 1 ≤ c) (hcn : c ≤ n) {δ : ℝ≥0}
    (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hres : GradedAnchoredTwinFree dom k w c) (u₀ u₁ : Fin n → F) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ]
      ≤ ((gradedBudget n k w c : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  -- the far-branch budget comparison
  have hbudget : w + 3 ≤ gradedBudget n k w c := by
    have h1 : 1 ≤ ∑ j ∈ Finset.range c, n.choose (n - j) := by
      have hterm : n.choose (n - 0) = 1 := by
        rw [Nat.sub_zero, Nat.choose_self]
      calc 1 = n.choose (n - 0) := hterm.symm
        _ ≤ ∑ j ∈ Finset.range c, n.choose (n - j) :=
            Finset.single_le_sum (f := fun j => n.choose (n - j))
              (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr hc)
    have h2 : 1 ≤ n.choose c * (c * (w + 1)) := by
      have hpos : 0 < n.choose c := Nat.choose_pos hcn
      have hcw : 1 ≤ c * (w + 1) := Nat.mul_pos hc (by omega)
      calc 1 = 1 * 1 := by omega
        _ ≤ n.choose c * (c * (w + 1)) := Nat.mul_le_mul hpos hcw
    rw [gradedBudget]
    omega
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  by_cases h1 : WBSolvable dom k w u₁
  · by_cases h0 : WBSolvable dom k w u₀
    · obtain ⟨ℓ₀, R₀, ℓ₁, R₁, hd₀, hd₁, hr₀, hr₁, hrel₀, hrel₁, J, C₀, τ,
        hCc, hdet, htwin⟩ := hres u₀ u₁ h0 h1
      have hc1 : 1 ≤ C₀.card := by omega
      have := badScalars_card_le_of_graded dom hk hδn hd₀ hd₁ hr₀ hr₁ hrel₀ hrel₁
        hc1 hdet htwin
      rw [hCc] at this
      exact_mod_cast le_trans this (le_of_eq rfl)
    · have hswap := badScalars_card_swap_le
        (rsCode dom k : Submodule F (Fin n → F)) δ u₀ u₁
      have hfar := badScalars_card_le_of_far_snd dom hk hwk hδn
        (u₀ := u₁) (u₁ := u₀) h0
      have hb : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
          u₀ u₁ γ)).card ≤ gradedBudget n k w c := by omega
      exact_mod_cast hb
  · have hfar := badScalars_card_le_of_far_snd dom hk hwk hδn
      (u₀ := u₀) (u₁ := u₁) h1
    have hb : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        u₀ u₁ γ)).card ≤ gradedBudget n k w c := by omega
    exact_mod_cast hb

open Classical in
omit [DecidableEq F] in
/-- **The graded ε_mca law**: under the grade-`c` residual, every radius
`δ ≤ w/n` has `ε_mca(RS, δ) ≤ gradedBudget/q`. -/
theorem epsMCA_le_of_graded (dom : Fin n ↪ F) {k w c : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) (hc : 1 ≤ c) (hcn : c ≤ n) {δ : ℝ≥0}
    (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hres : GradedAnchoredTwinFree dom k w c) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((gradedBudget n k w c : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA]
  exact iSup_le fun u =>
    mcaEvent_prob_le_of_gradedResidual dom hk hwk hc hcn hδn hres (u 0) (u 1)

open Classical in
omit [DecidableEq F] in
/-- **The graded δ* floor**: under the grade-`c` residual, every radius
`δ ≤ w/n` whose graded budget clears `ε*` is a good point of the threshold. -/
theorem le_mcaDeltaStar_of_graded (dom : Fin n ↪ F) {k w c : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) (hc : 1 ≤ c) (hcn : c ≤ n) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hres : GradedAnchoredTwinFree dom k w c)
    {εstar : ℝ≥0∞}
    (hbudget : ((gradedBudget n k w c : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (epsMCA_le_of_graded dom hk hwk hc hcn hδn hres) hbudget)

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.mcaEvent_prob_le_of_gradedResidual
#print axioms ProximityGap.WBPencil.epsMCA_le_of_graded
#print axioms ProximityGap.WBPencil.le_mcaDeltaStar_of_graded
