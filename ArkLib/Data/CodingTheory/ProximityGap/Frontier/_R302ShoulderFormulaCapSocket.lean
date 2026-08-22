/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R302 shoulder formula-cap socket)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

/-!
# R302 (#466): the n=128 piecewise shoulder formula cap as a named socket

R296–R301 verified the executable cap `cap(M) = 8192·⌈(M+10000)/15000⌉` escape-free on the
full late window `M = 50001..80000` (probe evidence, three segments R298/R299/R301).  This
socket names the cap as a ℕ-function, proves its structural properties (monotonicity, the
window value pins), and provides the window-concatenation glue that is exactly how the three
probe segments compose — so the numeric certificate can be consumed as ONE named `Prop`
(`WindowFormulaCap rows tailRank 50001 80000`) by the punctured-list budget sockets.

Probe evidence is NOT imported as a theorem: the window instance itself stays a named
hypothesis for its consumers, per the honesty contract.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R302ShoulderFormulaCapSocket

/-- The R296 piecewise shoulder cap `8192·⌈(M+10000)/15000⌉`, as a ℕ-function
(`⌈a/b⌉ = (a + b − 1)/b` in ℕ-division). -/
def shoulderCapFormula (M : ℕ) : ℕ :=
  8192 * ((M + 10000 + 14999) / 15000)

/-- The cap formula is monotone in the index `M`. -/
theorem shoulderCapFormula_monotone : Monotone shoulderCapFormula := by
  intro M M' h
  unfold shoulderCapFormula
  exact Nat.mul_le_mul_left _ (Nat.div_le_div_right (by omega))

/-- Value pin at the window opening: `cap(50001) = 40960` (the fifth rung). -/
theorem shoulderCapFormula_50001 : shoulderCapFormula 50001 = 40960 := by decide

/-- Value pin on the late segment: `cap(80000) = 49152` (the sixth rung, as reported by the
R298–R301 probe runs). -/
theorem shoulderCapFormula_80000 : shoulderCapFormula 80000 = 49152 := by decide

/-- All row tail-ranks bounded by a cap. -/
def RowCapBound {ι : Type*} (rows : Finset ι) (tailRank : ι → ℕ) (cap : ℕ) : Prop :=
  ∀ i ∈ rows, tailRank i ≤ cap

/-- A cap bound upgrades along the cap order. -/
theorem rowCapBound_mono {ι : Type*} {rows : Finset ι} {tailRank : ι → ℕ} {cap cap' : ℕ}
    (h : RowCapBound rows tailRank cap) (hle : cap ≤ cap') :
    RowCapBound rows tailRank cap' :=
  fun i hi => le_trans (h i hi) hle

/-- **The window formula-cap predicate**: on every index `M` of the window `[lo, hi]`, the
`M`-indexed row family satisfies the formula cap.  The R296–R301 probe evidence is the
numeric certificate for `lo = 50001`, `hi = 80000`; consumers take this `Prop` as the named
hypothesis. -/
def WindowFormulaCap {ι : Type*} (rows : ℕ → Finset ι) (tailRank : ι → ℕ)
    (lo hi : ℕ) : Prop :=
  ∀ M : ℕ, lo ≤ M → M ≤ hi → RowCapBound (rows M) tailRank (shoulderCapFormula M)

/-- **Window concatenation** — the formal composition of the R298/R299/R301 probe segments:
certificates on `[lo, mid]` and `[mid+1, hi]` give the certificate on `[lo, hi]`. -/
theorem windowFormulaCap_append {ι : Type*} (rows : ℕ → Finset ι) (tailRank : ι → ℕ)
    {lo mid hi : ℕ}
    (h₁ : WindowFormulaCap rows tailRank lo mid)
    (h₂ : WindowFormulaCap rows tailRank (mid + 1) hi) :
    WindowFormulaCap rows tailRank lo hi := by
  intro M hlo hhi
  by_cases hM : M ≤ mid
  · exact h₁ M hlo hM
  · exact h₂ M (by omega) hhi

/-- **Uniform-cap consumer form**: on a window whose top value pins the formula, the whole
window certificate collapses to the single cap `shoulderCapFormula hi` (monotonicity). -/
theorem rowCapBound_top_of_windowFormulaCap {ι : Type*} (rows : ℕ → Finset ι)
    (tailRank : ι → ℕ) {lo hi : ℕ}
    (h : WindowFormulaCap rows tailRank lo hi)
    {M : ℕ} (hlo : lo ≤ M) (hhi : M ≤ hi) :
    RowCapBound (rows M) tailRank (shoulderCapFormula hi) :=
  rowCapBound_mono (h M hlo hhi) (shoulderCapFormula_monotone hhi)

end ArkLib.ProximityGap.Frontier.R302ShoulderFormulaCapSocket

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R302ShoulderFormulaCapSocket.shoulderCapFormula_monotone
#print axioms ArkLib.ProximityGap.Frontier.R302ShoulderFormulaCapSocket.shoulderCapFormula_50001
#print axioms ArkLib.ProximityGap.Frontier.R302ShoulderFormulaCapSocket.shoulderCapFormula_80000
#print axioms ArkLib.ProximityGap.Frontier.R302ShoulderFormulaCapSocket.windowFormulaCap_append
#print axioms
  ArkLib.ProximityGap.Frontier.R302ShoulderFormulaCapSocket.rowCapBound_top_of_windowFormulaCap
