/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.TerminalDomainSecurity
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCubicExact

/-! # A domain-independent exact rate-one-sixteenth crossing at budget twice the length

The cubic order theorem yields a numerator of at most twice the domain length
at 715827881 errors over all finite fields of sufficiently large characteristic.
Small prime fields satisfy this cardinal bound directly. In the budget class
with exactly 2147483648 permitted scalar labels, the next error count is bad
on every injective domain and at every positive interleaving width.
-/
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.UniversalCubicThreshold
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open TerminalDomainSecurity SecondPrimeActualPopulations HalfPredecessorBadEventRichPointBridge
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]

/-- Finite witness count for any domain and any received pair, at the predecessor
agreement count, whenever the scalar characteristic exceeds the actual polar degree. -/
theorem family_cap (dom : I ↪ F) (hn : Fintype.card I=n) {p : ℕ} [CharP F p] (hp : 1744830589<p)
    (δ : ℝ≥0) (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 357913943)
    (u : Code.WordStack F (Fin 2) I) (fam : Family dom δ u) : fam.G.card ≤ 2147483648 := by
  classical
  let φ := algebraMap F (AlgebraicClosure F)
  let _ : CharP (AlgebraicClosure F) p := charP_of_injective_ringHom φ.injective p
  apply family_cap_of_order φ hp dom hn δ ht u fam
  exact fun f hi hy hw htot hproper hpop =>
    SecondPrimeCubicExact.received_budget fam φ p hp f hi hy hw htot hproper hpop

omit [Nonempty I] [DecidableEq I] in
private theorem agreement (hn : Fintype.card I=n) :
    ⌈(1-predecessor)*(Fintype.card I : ℝ≥0)⌉₊ = 357913943 := by
  rw [hn]
  have h := TwoCorePackingThreshold.agreement_ceiling 715827881 (by decide)
  rw [Fintype.card_fin] at h
  exact h

/-- Probability form of the uniform bound, including every finite prime field
and every finite extension above the characteristic cutoff. -/
theorem predecessor_eps (dom : I ↪ F) (hn : Fintype.card I=n) {p : ℕ} [CharP F p]
    (hchar : 1744830589<p ∨ Fintype.card F≤2147483648) :
    epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) predecessor ≤
      (2147483648:ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) := by
  apply eps_of_family_cap dom
  intro u
  let fam := canonicalBadScalarRichPointFamily dom (k:=k) predecessor u (by decide)
  change fam.G.card ≤ _
  rcases hchar with hp | hq
  · exact family_cap dom hn hp predecessor (agreement hn) u fam
  · exact (Finset.card_le_univ fam.G).trans hq

/-- The predecessor numerator bound over every prime field, with no characteristic
restriction and no multiplicative structure on the evaluation domain. -/
theorem prime_predecessor {p : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n) :
    epsMCA (F:=ZMod p) (ReedSolomon.code dom k : Set (I → ZMod p)) predecessor ≤
      (2147483648:ℝ≥0∞)/(p:ℝ≥0∞) := by
  have h : 1744830589<p ∨ Fintype.card (ZMod p)≤2147483648 := by rw [ZMod.card]; omega
  simpa only [ZMod.card] using predecessor_eps dom hn h

/-- At budget twice the length, all domains over a sufficiently large
characteristic field have the same exact supremum and open good interval. -/
theorem classification (dom : I ↪ F) (hn : Fintype.card I=n) {p : ℕ} [CharP F p]
    (hp : 1744830589<p) (hB : Fintype.card F / 2^128 = 2147483648)
    (width : ℕ) [NeZero width] :
    mcaDeltaStar (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) tolerance = boundary ∧
    ∀ δ : ℝ≥0, epsMCA (F:=F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) δ ≤ tolerance ↔ δ<boundary := by
  apply classification_of_good dom hn hB.le _ width
  have h := (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide : 0 < 2^128)).2 hB.ge
  exact (predecessor_eps dom hn (.inl hp)).trans (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using h)

/-- Every prime field in the concrete 128-bit budget interval and every domain,
including every admissible smooth domain, satisfies the full threshold classification. -/
theorem prime_classification {p : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hB : p/2^128=2147483648) (width : ℕ) [NeZero width] :
    mcaDeltaStar (F:=ZMod p) ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)) tolerance = boundary ∧
    ∀ δ : ℝ≥0, epsMCA (F:=ZMod p) ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)) δ ≤ tolerance ↔ δ<boundary := by
  apply classification dom hn (p:=p) (by omega) (by simpa only [ZMod.card] using hB) width

/-- Scalar line-MCA on the unmodified evaluation code in every prime field of
this budget class. The boundary radius itself is the first failure. -/
theorem scalar_prime_classification {p : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hB : p/2^128=2147483648) :
    mcaDeltaStar (F:=ZMod p) (ReedSolomon.code dom k : Set (I → ZMod p)) tolerance = boundary ∧
    ∀ δ : ℝ≥0, epsMCA (F:=ZMod p) (ReedSolomon.code dom k : Set (I → ZMod p)) δ ≤ tolerance ↔ δ<boundary := by
  simpa only [mcaDeltaStar_interleaved_eq, epsMCA_interleaved_eq] using prime_classification dom hn hB 1

#print axioms scalar_prime_classification
#print axioms family_cap
#print axioms prime_predecessor
#print axioms classification
#print axioms prime_classification
end ArkLib.ProximityGap.Frontier.UniversalCubicThreshold
