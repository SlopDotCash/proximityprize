/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterFreshPetalPruning

/-!
# Rate-quarter high cores: outsider petal growth

The proper-core pruning argument works inside the complement of a fixed line
core.  This file adapts it to a relevant high core `D`, with `|D| >= h` in a
`2h`-coordinate domain.

Line-core packing bounds the population on the source line by
`2h - |D|`.  If every secant petal between outsiders has size at most `s`, the
reduced-universe Rankin bound also bounds the outsider population by
`2h - |D|`, provided

```text
  (2h - |D|) * s <= (h + 1 - (k - 1))^2 - 1.
```

Since `|D| >= h`, the two populations sum to at most `2h`.  Thus a
counterexample forces a quantitatively large petal.  Taking `s = h - 1`
conditionally produces a second relevant half-core; the exact budget failure
is retained when this is impossible.  At the saturated quarter rate `h=2k`,
every counterexample with one high core unconditionally produces a fresh
petal of size at least `floor(k/2)+3` outside that core.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalPruning

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCorePetalGrowth

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Line packing always charges the population on a relevant line against the
complement of its core. -/
theorem pointsOn_card_le_core_complement
    {dom : I ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hn : Fintype.card I = 2 * h)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    (pointsOn family line).card ≤
      2 * h - (jointCore dom (u 0) (u 1) line.1 line.2).card := by
  have hpack := pointsOn_card_mul_max_add_core_le family hline
  have hone : 1 ≤ max 1
      (⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊ -
        (jointCore dom (u 0) (u 1) line.1 line.2).card) :=
    le_max_left _ _
  have hlineMul : (pointsOn family line).card ≤
      (pointsOn family line).card * max 1
        (⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊ -
          (jointCore dom (u 0) (u 1) line.1 line.2).card) := by
    simpa only [mul_one] using
      Nat.mul_le_mul_left (pointsOn family line).card hone
  have hsum :
      (pointsOn family line).card +
          (jointCore dom (u 0) (u 1) line.1 line.2).card ≤
        Fintype.card I := by
    exact (Nat.add_le_add_right hlineMul _).trans hpack
  rw [hn] at hsum
  omega

/-- **High-core reduced-universe cap closure.**  If all outsider secant petals
are at most `s`, the exact reduced Rankin budget bounds the outsiders by the
core-complement size.  Line packing gives the same bound for points on the
source line.  A core of size at least `h` therefore forces `|G| <= 2h`. -/
theorem card_le_two_mul_of_high_core_secantPetal_cap
    {dom : I ↪ F} {k h s : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : h ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hbudget :
      (2 * h - (jointCore dom (u 0) (u 1) line.1 line.2).card) * s ≤
        (h + 1 - (k - 1)) ^ 2 - 1)
    (hpetal : ∀ gamma ∈ outsideLine family line,
      ∀ beta ∈ outsideLine family line, gamma ≠ beta →
        (secantPetal family line gamma beta).card ≤ s) :
    family.G.card ≤ 2 * h := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset I := Finset.univ \ D
  let K := {gamma // gamma ∈ outsideLine family line}
  let A : K → Finset I := fun gamma =>
    fullAgreement dom (u 0) (u 1) gamma.1 (family.q gamma.1) \ D
  have hlineCard : (pointsOn family line).card ≤ V.card := by
    have hlineBound := pointsOn_card_le_core_complement family hn hline
    have hVcard : V.card = 2 * h - D.card := by
      simp only [V, Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ, hn]
    simpa only [hVcard, D] using hlineBound
  have hAsub : ∀ gamma : K, A gamma ⊆ V := by
    intro gamma i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hrPos : 1 ≤ h + 1 - (k - 1) := by omega
  have hAsize : ∀ gamma : K,
      h + 1 - (k - 1) ≤ (A gamma).card := by
    intro gamma
    have hfresh := threshold_sub_pred_le_fresh_card
      family line hk hline gamma.2
    rw [hthreshold] at hfresh
    simpa only [A, D] using hfresh
  have hApair : Pairwise fun gamma beta : K =>
      (A gamma ∩ A beta).card ≤ s := by
    intro gamma beta hne
    have hvalue : gamma.1 ≠ beta.1 := by
      intro heq
      exact hne (Subtype.ext heq)
    rw [show A gamma ∩ A beta =
        secantPetal family line gamma.1 beta.1 by
      simpa only [A, D] using fresh_inter_eq_secantPetal
        family line
          ((mem_outsideLine_iff family line gamma.1).mp gamma.2).1
          ((mem_outsideLine_iff family line beta.1).mp beta.2).1 hvalue]
    exact hpetal gamma.1 gamma.2 beta.1 beta.2 hvalue
  have hVcard : V.card = 2 * h - D.card := by
    simp only [V, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn]
  have houtside := card_le_finset_of_card_ge_pair_inter_le
    V A (h + 1 - (k - 1)) s hrPos hAsub hAsize hApair
      (by simpa only [hVcard, D] using hbudget)
  have houtside' : (outsideLine family line).card ≤ V.card := by
    simpa only [K, Fintype.card_coe] using houtside
  have hpartition := pointsOn_card_add_outsideLine_card family line
  have hVle : V.card ≤ h := by
    rw [hVcard]
    change h ≤ D.card at hcore
    omega
  change (pointsOn family line).card +
      (outsideLine family line).card = family.G.card at hpartition
  omega

/-- A family larger than the domain forces a petal beyond every admissible
reduced-universe cap. -/
theorem exists_outside_secantPetal_card_gt_of_high_core
    {dom : I ↪ F} {k h s : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h) (hcard : 2 * h < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : h ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hbudget :
      (2 * h - (jointCore dom (u 0) (u 1) line.1 line.2).card) * s ≤
        (h + 1 - (k - 1)) ^ 2 - 1) :
    ∃ gamma ∈ outsideLine family line,
      ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
        s < (secantPetal family line gamma beta).card := by
  by_contra hnot
  have hcap : ∀ gamma ∈ outsideLine family line,
      ∀ beta ∈ outsideLine family line, gamma ≠ beta →
        (secantPetal family line gamma beta).card ≤ s := by
    intro gamma hgamma beta hbeta hne
    by_contra hlarge
    apply hnot
    exact ⟨gamma, hgamma, beta, hbeta, hne, by omega⟩
  have hle := card_le_two_mul_of_high_core_secantPetal_cap
    family hk hn hthreshold hrate hline hcore hbudget hcap
  omega

/-- Dichotomy form of the exact high-core petal increment. -/
theorem card_le_two_mul_or_exists_high_core_petal_gt
    {dom : I ↪ F} {k h s : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : h ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hbudget :
      (2 * h - (jointCore dom (u 0) (u 1) line.1 line.2).card) * s ≤
        (h + 1 - (k - 1)) ^ 2 - 1) :
    family.G.card ≤ 2 * h ∨
      ∃ gamma ∈ outsideLine family line,
        ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
          s < (secantPetal family line gamma beta).card := by
  by_cases hcard : family.G.card ≤ 2 * h
  · exact Or.inl hcard
  · exact Or.inr <| exists_outside_secantPetal_card_gt_of_high_core
      family hk hn hthreshold hrate (by omega) hline hcore hbudget

/-! ## Second-core and near-cover consequences -/

/-- A petal of size at least `h` belongs to a distinct relevant secant line
with a half-domain core. -/
theorem exists_second_high_core_of_large_petal
    {dom : I ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    {line : LineParameter F}
    {gamma beta : F}
    (hgamma : gamma ∈ outsideLine family line)
    (hbeta : beta ∈ outsideLine family line)
    (hne : gamma ≠ beta)
    (hpetal : h ≤ (secantPetal family line gamma beta).card) :
    ∃ line2 ∈ lineParameters family, line2 ≠ line ∧
      h ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card := by
  let line2 := secantParameter family gamma beta
  have hgammaG := (mem_outsideLine_iff family line gamma).mp hgamma |>.1
  have hbetaG := (mem_outsideLine_iff family line beta).mp hbeta |>.1
  have hline2 : line2 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hgammaG hbetaG hne
  have hlineNe : line2 ≠ line := by
    intro heq
    have hgammaOn : gamma ∈ pointsOn family line2 :=
      first_point_mem_pointsOn_secant family hgammaG
    have hgammaEq := (mem_pointsOn_iff family line2 gamma).mp hgammaOn |>.2
    exact ((mem_outsideLine_iff family line gamma).mp hgamma).2
      (by simpa only [heq] using hgammaEq)
  have hpetalSub : secantPetal family line gamma beta ⊆
      jointCore dom (u 0) (u 1) line2.1 line2.2 := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).1
  exact ⟨line2, hline2, hlineNe,
    hpetal.trans (Finset.card_le_card hpetalSub)⟩

/-- If the reduced budget permits the cap `h-1`, a counterexample containing
one high core necessarily contains a second distinct high core. -/
theorem exists_second_high_core_of_reduced_budget
    {dom : I ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h) (hcard : 2 * h < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : h ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hbudget :
      (2 * h - (jointCore dom (u 0) (u 1) line.1 line.2).card) * (h - 1) ≤
        (h + 1 - (k - 1)) ^ 2 - 1) :
    ∃ line2 ∈ lineParameters family, line2 ≠ line ∧
      h ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card := by
  obtain ⟨gamma, hgamma, beta, hbeta, hne, hpetal⟩ :=
    exists_outside_secantPetal_card_gt_of_high_core
      family hk hn hthreshold hrate hcard hline hcore hbudget
  apply exists_second_high_core_of_large_petal
    family hgamma hbeta hne
  omega

/-- Exact obstruction to obtaining a second reference half-core from one high
core by the reduced-universe argument. -/
theorem second_high_core_or_reduced_budget_failure
    {dom : I ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h) (hcard : 2 * h < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : h ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card) :
    (∃ line2 ∈ lineParameters family, line2 ≠ line ∧
      h ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card) ∨
      (h + 1 - (k - 1)) ^ 2 - 1 <
        (2 * h -
          (jointCore dom (u 0) (u 1) line.1 line.2).card) * (h - 1) := by
  by_cases hbudget :
      (2 * h - (jointCore dom (u 0) (u 1) line.1 line.2).card) * (h - 1) ≤
        (h + 1 - (k - 1)) ^ 2 - 1
  · exact Or.inl <| exists_second_high_core_of_reduced_budget
      family hk hn hthreshold hrate hcard hline hcore hbudget
  · exact Or.inr (by omega)

/-- Coordinates missed by the union of a source core and another core are the
part of the source-core complement not occupied by the second core. -/
theorem twoCoreComplement_card_eq_complement_sub_petal
    (D D2 : Finset I) :
    (Finset.univ \ (D ∪ D2)).card =
      (Finset.univ \ D).card - (D2 \ D).card := by
  classical
  have hleft : Finset.univ \ (D ∪ D2) =
      (Finset.univ \ D) \ D2 := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, not_or]
  have hinter : D2 ∩ (Finset.univ \ D) = D2 \ D := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ,
      true_and]
  rw [hleft, Finset.card_sdiff, hinter]

/-- If the cap `|V|-3` satisfies the reduced Rankin budget, the forced petal
leaves at most two coordinates outside the two core union.  The saturated
complementary-core theorem then closes the family. -/
theorem card_le_two_mul_of_saturated_high_core_near_cover_budget
    {dom : I ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊ = h + 1)
    (hsaturated : h = 2 * k)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : h ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hbudget :
      let v := 2 * h -
        (jointCore dom (u 0) (u 1) line.1 line.2).card
      v * (v - 3) ≤ (h + 1 - (k - 1)) ^ 2 - 1) :
    family.G.card ≤ 2 * h := by
  by_contra hnot
  have hcard : 2 * h < family.G.card := by omega
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let v := 2 * h - D.card
  have hrate : 2 * k ≤ h := by omega
  have hbudget' : v * (v - 3) ≤
      (h + 1 - (k - 1)) ^ 2 - 1 := by
    simpa only [v, D] using hbudget
  obtain ⟨gamma, hgamma, beta, hbeta, hne, hpetal⟩ :=
    exists_outside_secantPetal_card_gt_of_high_core
      family hk hn hthreshold hrate hcard hline hcore hbudget'
  let line2 := secantParameter family gamma beta
  have hgammaG := (mem_outsideLine_iff family line gamma).mp hgamma |>.1
  have hbetaG := (mem_outsideLine_iff family line beta).mp hbeta |>.1
  have hline2 : line2 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hgammaG hbetaG hne
  have hpetalEq : secantPetal family line gamma beta =
      jointCore dom (u 0) (u 1) line2.1 line2.2 \ D := by
    rfl
  have hVcard : (Finset.univ \ D).card = v := by
    simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      hn, v]
  have hmissing :
      (Finset.univ \ (D ∪
        jointCore dom (u 0) (u 1) line2.1 line2.2)).card ≤ 2 := by
    rw [twoCoreComplement_card_eq_complement_sub_petal, hVcard]
    rw [← hpetalEq]
    omega
  have hle := card_le_two_mul_of_saturated_small_complement
    family hk hsaturated hn hthreshold.ge line line2 hline hline2
      (by simpa only [D] using hmissing)
  omega

/-! ## Saturated unconditional growth -/

/-- The cap `floor(k/2)+2` always fits the reduced-universe budget of a high
core at the saturated quarter rate. -/
theorem saturated_high_core_half_budget
    {k h z : ℕ} (hk : 1 ≤ k) (hsaturated : h = 2 * k)
    (hhigh : h ≤ z) :
    (2 * h - z) * (k / 2 + 2) ≤
      (h + 1 - (k - 1)) ^ 2 - 1 := by
  have hV : 2 * h - z ≤ 2 * k := by omega
  have hquot : 2 * (k / 2) ≤ k := Nat.mul_div_le k 2
  have hfirst := Nat.mul_le_mul_right (k / 2 + 2) hV
  have hsecond : 2 * k * (k / 2 + 2) ≤ k * k + 4 * k := by
    calc
      2 * k * (k / 2 + 2) = k * (2 * (k / 2)) + 4 * k := by ring
      _ ≤ k * k + 4 * k := Nat.add_le_add_right
        (Nat.mul_le_mul_left k hquot) (4 * k)
  have hr : h + 1 - (k - 1) = k + 2 := by omega
  rw [hr]
  have hthird : k * k + 4 * k ≤ (k + 2) ^ 2 - 1 := by
    rw [show (k + 2) ^ 2 = k * k + 4 * k + 4 by ring]
    omega
  exact hfirst.trans (hsecond.trans hthird)

/-- **Unconditional high-core growth at saturated rate quarter.**  A family
larger than the domain and containing one relevant high core forces two
outsiders whose canonical secant core gains at least `floor(k/2)+3` fresh
coordinates outside the source core. -/
theorem exists_saturated_high_core_petal_ge_half_add_three
    {dom : I ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊ = h + 1)
    (hsaturated : h = 2 * k) (hcard : 2 * h < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : h ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card) :
    ∃ gamma ∈ outsideLine family line,
      ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
        k / 2 + 3 ≤ (secantPetal family line gamma beta).card := by
  have hrate : 2 * k ≤ h := by omega
  obtain ⟨gamma, hgamma, beta, hbeta, hne, hpetal⟩ :=
    exists_outside_secantPetal_card_gt_of_high_core
      family hk hn hthreshold hrate hcard hline hcore
        (saturated_high_core_half_budget hk hsaturated hcore)
  exact ⟨gamma, hgamma, beta, hbeta, hne, by omega⟩

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCorePetalGrowth

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCorePetalGrowth
#print axioms pointsOn_card_le_core_complement
#print axioms card_le_two_mul_of_high_core_secantPetal_cap
#print axioms exists_outside_secantPetal_card_gt_of_high_core
#print axioms card_le_two_mul_or_exists_high_core_petal_gt
#print axioms exists_second_high_core_of_reduced_budget
#print axioms second_high_core_or_reduced_budget_failure
#print axioms twoCoreComplement_card_eq_complement_sub_petal
#print axioms card_le_two_mul_of_saturated_high_core_near_cover_budget
#print axioms saturated_high_core_half_budget
#print axioms exists_saturated_high_core_petal_ge_half_add_three
