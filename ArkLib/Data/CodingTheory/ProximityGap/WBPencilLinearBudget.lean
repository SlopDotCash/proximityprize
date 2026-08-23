/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilRationalReduction

/-!
# The repaired below-UDR capstone: the LINEAR budget (#371)

`WindowRationalBounded` (budget `w + 3`) is **refuted**: the normalizer-pair family
(DISPROOF_LOG 2026-06-12, `probe_normalizer_pair_family.py`) produces doubly-rational
stacks with `(n−2)/2` bad scalars at the first beyond-ladder slice — `7 > w+3` at
`(97,16,11,2)` (the 2-power production shape) and `9 > w+3` at `(41,20,15,2)`,
q-independently.  This file is the repair:

* **`genuine_row_not_explainable`** — a genuinely rational row (`ℓ ∤ R`, denominator
  nonvanishing) admits NO codeword explanation on any witness of size `≥ n − w`, in
  the ENTIRE below-UDR range `2w + k ≤ n` (degree forcing; sharper hypothesis than
  WB-3a's ladder reach).  Consequently the no-joint clause of `mcaEvent` is FREE for
  genuine rational stacks: explainable ⟺ bad.  This is the lemma that makes the
  normalizer-pair refutation work, and it is equally the workhorse of the repaired
  good side.
* **`WindowRationalLinear`** — the repaired named residual: doubly-WB-solvable stacks
  have at most `n` bad scalars.  Consistent with every known family: the
  normalizer-pair `(n−2)/2`, the `μ_w`-coset `n/w`, the per-family `w+1`
  (`FamilyBadBound.lean`), WB-1's `w+2`, WB-3a/3b's `0/1`.
* **`epsMCA_le_below_udr_linear`** — under the Prop: `ε_mca(RS, δ) ≤ n/q` at every
  below-UDR radius.  At production budget (`q ≥ 2¹⁹²`, `n ≤ 2³⁰`):
  `n/q ≤ 2^{−162} ≪ 2^{−128}` — the production floor `(1−ρ)/2` is unchanged by the
  refutation; only toy-scale sharpness moved.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The no-joint-freeness lemma**: in the whole below-UDR range `2w + k ≤ n`, a
genuinely rational row is never explained by a codeword on `≥ n − w` points.  (The
agreement polynomial `P·ℓ − R` has degree `≤ w + k − 1 < n − w` and `≥ n − w` roots.) -/
theorem genuine_row_not_explainable (dom : Fin n ↪ F) {k w : ℕ}
    (hudr : 2 * w + k ≤ n) (hk : 1 ≤ k)
    {ℓ R : F[X]} (hℓd : ℓ.natDegree ≤ w) (hRd : R.natDegree ≤ w + k - 1)
    (hℓv : ∀ i : Fin n, ℓ.eval (dom i) ≠ 0) (hgen : ¬ ℓ ∣ R) :
    ¬ ∃ S : Finset (Fin n), n - w ≤ S.card ∧
      ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
        ∀ i ∈ S, c i = R.eval (dom i) / ℓ.eval (dom i) := by
  rintro ⟨S, hScard, c, hc, hag⟩
  obtain ⟨P, hPdeg, rfl⟩ := hc
  set Q : F[X] := P * ℓ - R with hQ
  have hQvan : ∀ i ∈ S, Q.eval (dom i) = 0 := by
    intro i hi
    have h : P.eval (dom i) = R.eval (dom i) / ℓ.eval (dom i) := hag i hi
    have h0 := hℓv i
    rw [hQ]
    simp only [eval_sub, eval_mul]
    rw [h]
    field_simp
    ring
  have hPdeg' : P.natDegree ≤ k - 1 := by
    by_cases hP0 : P = 0
    · subst hP0; simp
    · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
      omega
  have hQdeg : Q.natDegree ≤ w + k - 1 := by
    rw [hQ]
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · calc (P * ℓ).natDegree ≤ P.natDegree + ℓ.natDegree := natDegree_mul_le
        _ ≤ (k - 1) + w := Nat.add_le_add hPdeg' hℓd
        _ ≤ w + k - 1 := by omega
    · omega
  have hQ0 : Q = 0 := by
    by_contra hQne
    have hroots : (S.image dom).card ≤ Q.roots.toFinset.card := by
      refine Finset.card_le_card ?_
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [Multiset.mem_toFinset, mem_roots hQne]
      exact hQvan i hi
    have himg : (S.image dom).card = S.card :=
      Finset.card_image_of_injective _ dom.injective
    have h1 := Q.roots.toFinset_card_le
    have h2 := Q.card_roots'
    omega
  exact hgen ⟨P, by linear_combination (norm := ring_nf) - (sub_eq_zero.mp hQ0)⟩

open Classical in
/-- The no-joint clause is free for stacks whose first row is genuinely rational:
no pair of codewords jointly explains on any witness of size `≥ n − w`. -/
theorem not_pairJointAgreesOn_of_genuine_fst (dom : Fin n ↪ F) {k w : ℕ}
    (hudr : 2 * w + k ≤ n) (hk : 1 ≤ k)
    {ℓ R : F[X]} (hℓd : ℓ.natDegree ≤ w) (hRd : R.natDegree ≤ w + k - 1)
    (hℓv : ∀ i : Fin n, ℓ.eval (dom i) ≠ 0) (hgen : ¬ ℓ ∣ R)
    {S : Finset (Fin n)} (hS : n - w ≤ S.card) (u₁ : Fin n → F) :
    ¬ pairJointAgreesOn
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) S
      (fun i => R.eval (dom i) / ℓ.eval (dom i)) u₁ := by
  rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
  exact genuine_row_not_explainable dom hudr hk hℓd hRd hℓv hgen
    ⟨S, hS, v₀, hv₀, fun i hi => (hagree i hi).1⟩

open Classical in
/-- **The repaired named residual** (linear budget): every doubly-WB-solvable stack
has at most `n` bad scalars.  Replaces the REFUTED `WindowRationalBounded` (`w + 3`):
the normalizer-pair family attains `(n−2)/2`, the `μ_w`-coset family `n/w`; no known
family exceeds `n`. -/
def WindowRationalLinear (dom : Fin n ↪ F) (k w : ℕ) (δ : ℝ≥0) : Prop :=
  ∀ u₀ u₁ : Fin n → F, WBSolvable dom k w u₀ → WBSolvable dom k w u₁ →
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ n

open Classical in
/-- **THE REPAIRED BELOW-UDR LAW**: under `WindowRationalLinear`, at every radius
`δ ≤ w/n` with `w + 3 ≤ n`, `ε_mca(RS, δ) ≤ n/q`.  Production-silent for
`q ≥ n·2¹²⁸`. -/
theorem epsMCA_le_below_udr_linear (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) (hw3 : w + 3 ≤ n)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hwin : WindowRationalLinear dom k w δ) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA]
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  by_cases h1 : WBSolvable dom k w (u 1)
  · by_cases h0 : WBSolvable dom k w (u 0)
    · exact_mod_cast hwin (u 0) (u 1) h0 h1
    · have hswap := badScalars_card_swap_le
        (rsCode dom k : Submodule F (Fin n → F)) δ (u 0) (u 1)
      have hfar := badScalars_card_le_of_far_snd dom hk hwk hδn
        (u₀ := u 1) (u₁ := u 0) h0
      exact_mod_cast le_trans hswap (by omega)
  · have := badScalars_card_le_of_far_snd dom hk hwk hδn
      (u₀ := u 0) (u₁ := u 1) h1
    exact_mod_cast le_trans this (by omega)

open Classical in
/-- The threshold form of the repaired law: the production floor moves to UDR
whenever `n/q ≤ ε*` — at the deployed budget (`q ≥ 2¹⁹²`, `n ≤ 2³⁰`, `ε* = 2⁻¹²⁸`)
this holds with `2³⁴` to spare. -/
theorem le_mcaDeltaStar_below_udr_linear (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) (hw3 : w + 3 ≤ n) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hwin : WindowRationalLinear dom k w δ)
    {εstar : ℝ≥0∞}
    (hbudget : ((n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (epsMCA_le_below_udr_linear dom hk hwk hw3 hδn hwin) hbudget)

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.genuine_row_not_explainable
#print axioms ProximityGap.WBPencil.not_pairJointAgreesOn_of_genuine_fst
#print axioms ProximityGap.WBPencil.epsMCA_le_below_udr_linear
#print axioms ProximityGap.WBPencil.le_mcaDeltaStar_below_udr_linear
