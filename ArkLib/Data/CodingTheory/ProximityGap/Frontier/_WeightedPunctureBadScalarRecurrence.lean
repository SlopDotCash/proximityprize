/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BelowUDRPuncture

/-!
# A multiplicity-preserving puncture recurrence for MCA bad scalars

`BelowUDRPuncture.mcaEvent_puncture` sends a bad scalar through every zero of the
direction which lies in its witness.  The earlier induction used only a union bound and
therefore discarded how many such zeros each witness contains.  This file keeps that
multiplicity.

Let `Z = {i | u₁ i = 0}` and let the parent agreement be `m+1-w`.  Every witness `S`
has

```text
  |S ∩ Z| ≥ |Z| - w.
```

Puncturing at each point of this intersection preserves the same scalar.  Double
counting the pairs `(bad scalar, puncturable zero)` gives the exact recurrence surface

```text
  #bad(parent) * (|Z| - w)
    ≤ ∑ i∈Z #bad(puncture at i).
```

This is strictly stronger than the old union-bound step whenever `w < |Z|`.  Iterating
it would accumulate falling-factorial multiplicities instead of paying a raw branching
factor at every zero.  It does not by itself close the production good side: one still
needs a bound on the punctured children once the zero surplus is exhausted.  It does,
however, isolate that residual without losing the large-zero mass.

Issue #466.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership.Frontier.WeightedPunctureBadScalarRecurrence

open ProximityGap ProximityGap.SpikeFloor ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **Multiplicity-preserving puncture recurrence.**  At the exact integer radius
`w/(m+1)`, every parent bad scalar is counted in at least `|Z|-w` punctured child bad
sets, where `Z` is the zero set of the direction. -/
theorem weighted_puncture_badScalars
    {m k w : ℕ} (hm : 0 < m) (hw : w ≤ m)
    (dom : Fin (m + 1) ↪ F) (u₀ u₁ : Fin (m + 1) → F) :
    let B := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F)) :
        Set (Fin (m + 1) → F))
      ((w : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) u₀ u₁ γ)
    let Z := Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0)
    B.card * (Z.card - w) ≤
      ∑ i ∈ Z, (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode (punctureDom dom i) k : Submodule F (Fin m → F)) :
          Set (Fin m → F))
        ((w : ℝ≥0) / (m : ℝ≥0))
        (punctureWord dom i u₀) (punctureWord dom i u₁) γ)).card := by
  classical
  let δ : ℝ≥0 := (w : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let B : Finset F := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F)) :
      Set (Fin (m + 1) → F)) δ u₀ u₁ γ)
  let Z : Finset (Fin (m + 1)) :=
    Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0)
  let S : F → Finset (Fin (m + 1)) := fun γ =>
    if hγ : γ ∈ B then
      ((Finset.mem_filter.mp hγ).2).choose
    else ∅
  have hSspec : ∀ γ ∈ B,
      ((S γ).card : ℝ≥0) ≥ (1 - δ) * Fintype.card (Fin (m + 1)) ∧
      (∃ wd ∈ (rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F)),
        ∀ i ∈ S γ, wd i = u₀ i + γ • u₁ i) ∧
      ¬ pairJointAgreesOn
        ((rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F)) :
          Set (Fin (m + 1) → F)) (S γ) u₀ u₁ := by
    intro γ hγ
    simp only [S, dif_pos hγ]
    exact ((Finset.mem_filter.mp hγ).2).choose_spec
  have hratio :
      (1 - δ) * ((m + 1 : ℕ) : ℝ≥0) = ((m + 1 - w : ℕ) : ℝ≥0) := by
    have hden : (((m + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
    calc
      (1 - δ) * ((m + 1 : ℕ) : ℝ≥0)
          = ((m + 1 : ℕ) : ℝ≥0) - (w : ℝ≥0) := by
              rw [tsub_mul, one_mul]
              simp only [δ]
              rw [div_mul_cancel₀ _ hden]
      _ = ((m + 1 - w : ℕ) : ℝ≥0) := (Nat.cast_tsub (m + 1) w).symm
  have hSsize : ∀ γ ∈ B, m + 1 - w ≤ (S γ).card := by
    intro γ hγ
    have hs := (hSspec γ hγ).1
    rw [Fintype.card_fin, hratio] at hs
    exact_mod_cast hs
  have hinter : ∀ γ ∈ B, Z.card - w ≤ (S γ ∩ Z).card := by
    intro γ hγ
    have hcu := Finset.card_union_add_card_inter (S γ) Z
    have hunion : (S γ ∪ Z).card ≤ m + 1 := by
      calc
        (S γ ∪ Z).card ≤ (Finset.univ : Finset (Fin (m + 1))).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = m + 1 := by rw [Finset.card_univ, Fintype.card_fin]
    have hs := hSsize γ hγ
    omega
  have hchild : ∀ γ ∈ B, ∀ i ∈ Z, i ∈ S γ →
      mcaEvent (F := F)
        ((rsCode (punctureDom dom i) k : Submodule F (Fin m → F)) :
          Set (Fin m → F))
        ((w : ℝ≥0) / (m : ℝ≥0))
        (punctureWord dom i u₀) (punctureWord dom i u₁) γ := by
    intro γ hγ i hiZ hiS
    have hz : u₁ i = 0 := (Finset.mem_filter.mp hiZ).2
    exact mcaEvent_puncture hm hw dom i hz (hSsize γ hγ) hiS
      (hSspec γ hγ).2.1 (hSspec γ hγ).2.2
  have hcard_sum : ∀ γ : F,
      (S γ ∩ Z).card = ∑ i ∈ Z, if i ∈ S γ then 1 else 0 := by
    intro γ
    rw [← Finset.card_filter]
    congr 1
    ext i
    simp [and_comm]
  change B.card * (Z.card - w) ≤ _
  calc
    B.card * (Z.card - w) = ∑ _γ ∈ B, (Z.card - w) := by
      rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ B, (S γ ∩ Z).card :=
      Finset.sum_le_sum (fun γ hγ => hinter γ hγ)
    _ = ∑ γ ∈ B, ∑ i ∈ Z, if i ∈ S γ then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro γ _hγ
      exact hcard_sum γ
    _ = ∑ i ∈ Z, ∑ γ ∈ B, if i ∈ S γ then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ Z, (B.filter (fun γ => i ∈ S γ)).card := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.card_filter]
    _ ≤ ∑ i ∈ Z, (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode (punctureDom dom i) k : Submodule F (Fin m → F)) :
            Set (Fin m → F))
          ((w : ℝ≥0) / (m : ℝ≥0))
          (punctureWord dom i u₀) (punctureWord dom i u₁) γ)).card := by
      apply Finset.sum_le_sum
      intro i hiZ
      apply Finset.card_le_card
      intro γ hγ
      have hγB : γ ∈ B := (Finset.mem_filter.mp hγ).1
      have hγS : i ∈ S γ := (Finset.mem_filter.mp hγ).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hchild γ hγB i hiZ hγS⟩

open Classical in
/-- Divided form of `weighted_puncture_badScalars`, valid when the direction has
strictly more zeros than the error budget. -/
theorem weighted_puncture_badScalars_le_div
    {m k w : ℕ} (hm : 0 < m) (hw : w ≤ m)
    (dom : Fin (m + 1) ↪ F) (u₀ u₁ : Fin (m + 1) → F)
    (hzw : w < (Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0)).card) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F)) :
        Set (Fin (m + 1) → F))
      ((w : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) u₀ u₁ γ)).card ≤
      (∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0),
        (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode (punctureDom dom i) k : Submodule F (Fin m → F)) :
            Set (Fin m → F))
          ((w : ℝ≥0) / (m : ℝ≥0))
          (punctureWord dom i u₀) (punctureWord dom i u₁) γ)).card) /
        ((Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0)).card - w) := by
  apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hzw)).2
  exact weighted_puncture_badScalars hm hw dom u₀ u₁

open Classical in
/-- Uniform-child consumer: if every punctured child has at most `M` bad scalars,
the parent pays only the ratio `|Z|/(|Z|-w)` rather than the raw `|Z|` union bound. -/
theorem weighted_puncture_badScalars_le_of_child_cap
    {m k w M : ℕ} (hm : 0 < m) (hw : w ≤ m)
    (dom : Fin (m + 1) ↪ F) (u₀ u₁ : Fin (m + 1) → F)
    (hzw : w < (Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0)).card)
    (hcap : ∀ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0),
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode (punctureDom dom i) k : Submodule F (Fin m → F)) :
          Set (Fin m → F))
        ((w : ℝ≥0) / (m : ℝ≥0))
        (punctureWord dom i u₀) (punctureWord dom i u₁) γ)).card ≤ M) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F)) :
        Set (Fin (m + 1) → F))
      ((w : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) u₀ u₁ γ)).card ≤
      (Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0)).card * M /
        ((Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0)).card - w) := by
  refine le_trans (weighted_puncture_badScalars_le_div hm hw dom u₀ u₁ hzw) ?_
  apply Nat.div_le_div_right
  calc
    ∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0),
        (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode (punctureDom dom i) k : Submodule F (Fin m → F)) :
            Set (Fin m → F))
          ((w : ℝ≥0) / (m : ℝ≥0))
          (punctureWord dom i u₀) (punctureWord dom i u₁) γ)).card
      ≤ ∑ _i ∈ Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0), M :=
        Finset.sum_le_sum (fun i hi => hcap i hi)
    _ = (Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0)).card * M := by
      rw [Finset.sum_const, smul_eq_mul]

/-- Pure arithmetic consumer for a weighted recurrence.  If `B * (Z-w) ≤ Z*M`,
the useful zero floor is any `K ≤ Z` above the error budget. -/
theorem weighted_recurrence_floor_arith
    {B Z w K M : ℕ} (hwK : w < K) (hK : K ≤ Z)
    (hrec : B * (Z - w) ≤ Z * M) :
    B * (K - w) ≤ K * M := by
  have hwZ : w < Z := hwK.trans_le hK
  have hcross : Z * M * (K - w) ≤ K * M * (Z - w) := by
    have hwK' : w ≤ K := hwK.le
    have hwZ' : w ≤ Z := hwZ.le
    have hKw : K - w + w = K := Nat.sub_add_cancel hwK'
    have hZK : Z - K + K = Z := Nat.sub_add_cancel hK
    have hZw : Z - w + w = Z := Nat.sub_add_cancel hwZ'
    have h1 : K * (Z - w) = Z * (K - w) + w * (Z - K) := by
      nlinarith
    calc
      Z * M * (K - w) = M * (Z * (K - w)) := by ring
      _ ≤ M * (K * (Z - w)) := by
        apply Nat.mul_le_mul_left
        rw [h1]
        exact Nat.le_add_right _ _
      _ = K * M * (Z - w) := by ring
  have hscaled := Nat.mul_le_mul_right (K - w) hrec
  have hcancel : (B * (K - w)) * (Z - w) ≤
      (K * M) * (Z - w) := by
    calc
      (B * (K - w)) * (Z - w)
          = (B * (Z - w)) * (K - w) := by ring
      _ ≤ (Z * M) * (K - w) := hscaled
      _ ≤ (K * M) * (Z - w) := hcross
  exact Nat.le_of_mul_le_mul_right hcancel (Nat.sub_pos_of_lt hwZ)

open Classical in
/-- Dimension-floor form of the recurrence.  If the shifted direction has at least
`K` zeros, `w < K`, and every punctured child has cap `M`, then

`#bad(parent) * (K-w) ≤ K*M`.

This is the form suited to iteration after coset-normalizing an RS direction: Lagrange
interpolation always supplies a representative with at least `K` zeros for a
dimension-`K` code. -/
theorem weighted_puncture_badScalars_mul_sub_le_of_zero_floor
    {m k w K M : ℕ} (hm : 0 < m) (hw : w ≤ m)
    (dom : Fin (m + 1) ↪ F) (u₀ u₁ : Fin (m + 1) → F)
    (hwK : w < K)
    (hK : K ≤ (Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0)).card)
    (hcap : ∀ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0),
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode (punctureDom dom i) k : Submodule F (Fin m → F)) :
          Set (Fin m → F))
        ((w : ℝ≥0) / (m : ℝ≥0))
        (punctureWord dom i u₀) (punctureWord dom i u₁) γ)).card ≤ M) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F)) :
        Set (Fin (m + 1) → F))
      ((w : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) u₀ u₁ γ)).card * (K - w)
      ≤ K * M := by
  let Z : Finset (Fin (m + 1)) :=
    Finset.univ.filter (fun i : Fin (m + 1) => u₁ i = 0)
  let B : Finset F := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F)) :
      Set (Fin (m + 1) → F))
    ((w : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) u₀ u₁ γ)
  have hrec : B.card * (Z.card - w) ≤ Z.card * M := by
    calc
      B.card * (Z.card - w)
          ≤ ∑ i ∈ Z, (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
              ((rsCode (punctureDom dom i) k : Submodule F (Fin m → F)) :
                Set (Fin m → F))
              ((w : ℝ≥0) / (m : ℝ≥0))
              (punctureWord dom i u₀) (punctureWord dom i u₁) γ)).card :=
            weighted_puncture_badScalars hm hw dom u₀ u₁
      _ ≤ ∑ _i ∈ Z, M := Finset.sum_le_sum (fun i hi => hcap i hi)
      _ = Z.card * M := by rw [Finset.sum_const, smul_eq_mul]
  change B.card * (K - w) ≤ K * M
  exact weighted_recurrence_floor_arith hwK hK hrec

end ProximityGap.Ownership.Frontier.WeightedPunctureBadScalarRecurrence

/-! ## Axiom audit -/
#print axioms
  ProximityGap.Ownership.Frontier.WeightedPunctureBadScalarRecurrence.weighted_puncture_badScalars
#print axioms
  ProximityGap.Ownership.Frontier.WeightedPunctureBadScalarRecurrence.weighted_puncture_badScalars_le_div
#print axioms
  ProximityGap.Ownership.Frontier.WeightedPunctureBadScalarRecurrence.weighted_puncture_badScalars_le_of_child_cap
#print axioms
  ProximityGap.Ownership.Frontier.WeightedPunctureBadScalarRecurrence.weighted_puncture_badScalars_mul_sub_le_of_zero_floor
