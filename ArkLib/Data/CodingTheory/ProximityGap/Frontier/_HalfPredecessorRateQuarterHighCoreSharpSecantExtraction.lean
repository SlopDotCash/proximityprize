/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCorePetalGrowth

/-!
# Rate-quarter high cores: sharp secant extraction

The cap-`h-1` route cannot promote one saturated high core directly to a
second half core.  The same reduced universe nevertheless has a useful exact
cap.  If the source core has size `z`, put

```text
v = 4k-z,    N = (k+2)^2-1,    s = floor(N/v).
```

Then `v*s <= N` by division, and `s` is the largest cap with this property
when `v` is positive.  Rankin--Serre therefore forces a canonical outsider
secant petal of size at least `s+1`.  This is a genuinely `z`-dependent
improvement of the uniform `floor(k/2)+3` extraction.

At the maximal surviving source size `z=3k-4`, the smaller cap `s=k` already
fits.  The resulting petal has at least `k+1` coordinates, so its secant core
leaves at most three coordinates uncovered together with the source core.
The complementary-core theorem rules out zero, one, or two uncovered
coordinates in a counterexample.  Hence the complement and petal sizes are
forced exactly:

```text
|univ \ (D union D2)| = 3,    |D2 \ D| = k+1.
```

Thus the maximal stratum either produces a second half core, or reduces to a
strictly smaller three-hole residual with `|D inter D2| <= k-2`.  No failed
cap-`h-1` premise is used.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCorePetalGrowth

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreSharpSecantExtraction

attribute [local instance] Classical.propDecidable

/-- The first petal cardinality not ruled out by the exact reduced-universe
Rankin budget. -/
def sharpHighCorePetalThreshold (k z : Nat) : Nat :=
  ((k + 2) ^ 2 - 1) / (4 * k - z) + 1

/-- The quotient defining the sharp petal threshold always satisfies the
reduced Rankin budget.  Only `k >= 1` and saturation are needed for this
arithmetic statement. -/
theorem saturated_sharp_petal_floor_budget
    {k h z : Nat} (hk : 1 ≤ k) (hsaturated : h = 2 * k) :
    (2 * h - z) * (((k + 2) ^ 2 - 1) / (4 * k - z)) ≤
      (h + 1 - (k - 1)) ^ 2 - 1 := by
  have hcomplement : 2 * h - z = 4 * k - z := by omega
  have hthreshold : h + 1 - (k - 1) = k + 2 := by omega
  rw [hcomplement, hthreshold]
  exact Nat.mul_div_le ((k + 2) ^ 2 - 1) (4 * k - z)

/-- When the reduced universe is nonempty, the quotient is the largest
natural-number petal cap that satisfies the same budget. -/
theorem petal_floor_is_maximal_admissible
    {k z s : Nat} (hcomplement : 0 < 4 * k - z)
    (hbudget : (4 * k - z) * s ≤ (k + 2) ^ 2 - 1) :
    s ≤ ((k + 2) ^ 2 - 1) / (4 * k - z) := by
  apply (Nat.le_div_iff_mul_le hcomplement).2
  simpa only [Nat.mul_comm] using hbudget

/-- On the globally surviving high-core band, the sharp threshold is at
least the previously uniform `floor(k/2)+3` threshold. -/
theorem half_add_three_le_sharpHighCorePetalThreshold
    {k z : Nat} (hk : 1 ≤ k) (hhigh : 2 * k ≤ z)
    (hcap : z ≤ 3 * k - 4) :
    k / 2 + 3 ≤ sharpHighCorePetalThreshold k z := by
  have hk4 : 4 ≤ k := by omega
  have hcomplement : 0 < 4 * k - z := by omega
  have hbudget := saturated_high_core_half_budget
    (k := k) (h := 2 * k) (z := z) hk rfl hhigh
  have hleft : 2 * (2 * k) - z = 4 * k - z := by omega
  have hright : 2 * k + 1 - (k - 1) = k + 2 := by omega
  have hbudget' :
      (4 * k - z) * (k / 2 + 2) ≤ (k + 2) ^ 2 - 1 := by
    rw [hleft, hright] at hbudget
    exact hbudget
  have hfloor : k / 2 + 2 ≤
      ((k + 2) ^ 2 - 1) / (4 * k - z) :=
    petal_floor_is_maximal_admissible hcomplement hbudget'
  simp only [sharpHighCorePetalThreshold]
  omega

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **Sharp one-high-core secant extraction.**  The exact quotient budget
forces two outsiders whose canonical secant gains at least
`sharpHighCorePetalThreshold k |D|` coordinates beyond the source core. -/
theorem exists_saturated_high_core_petal_ge_sharp_threshold
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = h + 1)
    (hsaturated : h = 2 * k) (hcard : 2 * h < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : h ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card) :
    ∃ gamma ∈ outsideLine family line,
      ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
        sharpHighCorePetalThreshold k
            (jointCore dom (u 0) (u 1) line.1 line.2).card ≤
          (secantPetal family line gamma beta).card := by
  let z := (jointCore dom (u 0) (u 1) line.1 line.2).card
  let s := ((k + 2) ^ 2 - 1) / (4 * k - z)
  have hrate : 2 * k ≤ h := by omega
  have hbudget : (2 * h - z) * s ≤
      (h + 1 - (k - 1)) ^ 2 - 1 := by
    simpa only [s] using
      (saturated_sharp_petal_floor_budget (k := k) (h := h) (z := z)
        hk hsaturated)
  obtain ⟨gamma, hgamma, beta, hbeta, hne, hpetal⟩ :=
    exists_outside_secantPetal_card_gt_of_high_core
      family hk hn hthreshold hrate hcard hline hcore hbudget
  refine ⟨gamma, hgamma, beta, hbeta, hne, ?_⟩
  simp only [sharpHighCorePetalThreshold, z, s] at hpetal ⊢
  omega

/-- **Band-wide sharp secant trichotomy.**  A capped saturated high core
either bounds the family, produces a second high core, or produces a distinct
secant below the high-core threshold with all of the following quantitative
constraints:

* its petal reaches the maximal admissible Rankin threshold;
* the two cores miss at least three coordinates, but no more than the exact
  quotient remainder permits; and
* the source intersection plus the sharp petal threshold is still below `h`.

This is the explicit residual left by the sharp one-core extraction on the
whole band `2k <= z <= 3k-4`. -/
theorem card_le_or_second_high_core_or_sharp_secant_residual
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = h + 1)
    (hsaturated : h = 2 * k)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : h ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hcap :
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 3 * k - 4) :
    family.G.card ≤ 2 * h ∨
      (∃ line2 ∈ lineParameters family, line2 ≠ line ∧
        h ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card) ∨
      ∃ gamma ∈ outsideLine family line,
        ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
          let line2 := secantParameter family gamma beta
          let D := jointCore dom (u 0) (u 1) line.1 line.2
          let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
          line2 ∈ lineParameters family ∧ line2 ≠ line ∧
            k / 2 + 3 ≤ sharpHighCorePetalThreshold k D.card ∧
            sharpHighCorePetalThreshold k D.card ≤
              (secantPetal family line gamma beta).card ∧
            3 ≤ (Finset.univ \ (D ∪ D2)).card ∧
            (Finset.univ \ (D ∪ D2)).card ≤
              (4 * k - D.card) - sharpHighCorePetalThreshold k D.card ∧
            D2.card < h ∧
            sharpHighCorePetalThreshold k D.card +
                (D ∩ D2).card < h := by
  by_cases hcard : family.G.card ≤ 2 * h
  · exact Or.inl hcard
  have hcard' : 2 * h < family.G.card := by omega
  obtain ⟨gamma, hgamma, beta, hbeta, hne, hpetal⟩ :=
    exists_saturated_high_core_petal_ge_sharp_threshold
      family hk hn hthreshold hsaturated hcard' hline hcore
  let line2 := secantParameter family gamma beta
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let P := secantPetal family line gamma beta
  let R := Finset.univ \ (D ∪ D2)
  have hDhigh' : h ≤ D.card := by simpa only [D] using hcore
  have hDhigh : 2 * k ≤ D.card := by omega
  have hDcap : D.card ≤ 3 * k - 4 := by simpa only [D] using hcap
  have hsharpLower : k / 2 + 3 ≤
      sharpHighCorePetalThreshold k D.card :=
    half_add_three_le_sharpHighCorePetalThreshold hk hDhigh hDcap
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
  have hVcard : (Finset.univ \ D).card = 4 * k - D.card := by
    simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hn]
    omega
  have hpetalEq : P = D2 \ D := by rfl
  have hmissingEq : R.card = (4 * k - D.card) - P.card := by
    rw [show R = Finset.univ \ (D ∪ D2) by rfl,
      twoCoreComplement_card_eq_complement_sub_petal, hVcard, ← hpetalEq]
  have hmissingLower : 3 ≤ R.card := by
    by_contra hnot
    have hle := card_le_two_mul_of_saturated_small_complement
      family hk hsaturated hn hthreshold.ge line line2 hline hline2
        (by
          change (Finset.univ \ (D ∪ D2)).card ≤ 2
          simpa only [R] using (show R.card ≤ 2 by omega))
    omega
  by_cases hcore2 : h ≤ D2.card
  · exact Or.inr (Or.inl ⟨line2, hline2, hlineNe, hcore2⟩)
  apply Or.inr
  apply Or.inr
  have hcore2lt : D2.card < h := Nat.lt_of_not_ge hcore2
  have hsplit := Finset.card_sdiff_add_card_inter D2 D
  have hsharpPetal : sharpHighCorePetalThreshold k D.card ≤ P.card := by
    simpa only [D, P] using hpetal
  have hmissingUpper : R.card ≤
      (4 * k - D.card) - sharpHighCorePetalThreshold k D.card := by
    omega
  have hinter : sharpHighCorePetalThreshold k D.card +
      (D ∩ D2).card < h := by
    rw [Finset.inter_comm]
    rw [← hpetalEq] at hsplit
    omega
  refine ⟨gamma, hgamma, beta, hbeta, hne, ?_⟩
  dsimp only
  exact ⟨hline2, hlineNe, hsharpLower, hsharpPetal, hmissingLower,
    hmissingUpper, hcore2lt, hinter⟩

/-- **Maximal-band exact secant.**  If the source core has the largest size
allowed by the global high-core cap, a counterexample contains a distinct
canonical secant whose petal has exactly `k+1` coordinates and whose union
with the source core misses exactly three coordinates. -/
theorem exists_maximal_high_core_exact_three_hole_secant
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = h + 1)
    (hsaturated : h = 2 * k) (hcard : 2 * h < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : h ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hmax :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 3 * k - 4) :
    ∃ gamma ∈ outsideLine family line,
      ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
        let line2 := secantParameter family gamma beta
        line2 ∈ lineParameters family ∧ line2 ≠ line ∧
          (secantPetal family line gamma beta).card = k + 1 ∧
          (Finset.univ \ (
            jointCore dom (u 0) (u 1) line.1 line.2 ∪
              jointCore dom (u 0) (u 1) line2.1 line2.2)).card = 3 := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  have hDcard : D.card = 3 * k - 4 := by simpa only [D] using hmax
  have hk4 : 4 ≤ k := by omega
  have hrate : 2 * k ≤ h := by omega
  have hcomplement : 2 * h - D.card = k + 4 := by omega
  have hthresholdForm : h + 1 - (k - 1) = k + 2 := by omega
  have hsquare : (k + 2) ^ 2 = k * k + 4 * k + 4 := by ring
  have hproduct : (k + 4) * k = k * k + 4 * k := by ring
  have hbudget : (2 * h - D.card) * k ≤
      (h + 1 - (k - 1)) ^ 2 - 1 := by
    rw [hcomplement, hthresholdForm, hsquare, hproduct]
    omega
  obtain ⟨gamma, hgamma, beta, hbeta, hne, hpetalLarge⟩ :=
    exists_outside_secantPetal_card_gt_of_high_core
      family hk hn hthreshold hrate hcard hline hcore hbudget
  let line2 := secantParameter family gamma beta
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let P := secantPetal family line gamma beta
  let R := Finset.univ \ (D ∪ D2)
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
  have hVcard : (Finset.univ \ D).card = k + 4 := by
    simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hn]
    omega
  have hpetalEq : P = D2 \ D := by rfl
  have hmissingEq : R.card = k + 4 - P.card := by
    rw [show R = Finset.univ \ (D ∪ D2) by rfl,
      twoCoreComplement_card_eq_complement_sub_petal, hVcard, ← hpetalEq]
  have hpetalLower : k + 1 ≤ P.card := by
    simpa only [P] using (show k + 1 ≤
      (secantPetal family line gamma beta).card by omega)
  have hmissingUpper : R.card ≤ 3 := by omega
  have hmissingLower : 3 ≤ R.card := by
    by_contra hnot
    have hle := card_le_two_mul_of_saturated_small_complement
      family hk hsaturated hn hthreshold.ge line line2 hline hline2
        (by
          change (Finset.univ \ (D ∪ D2)).card ≤ 2
          simpa only [R] using (show R.card ≤ 2 by omega))
    omega
  have hmissing : R.card = 3 := by omega
  have hpetal : P.card = k + 1 := by omega
  refine ⟨gamma, hgamma, beta, hbeta, hne, ?_⟩
  dsimp only
  refine ⟨hline2, hlineNe, ?_, ?_⟩
  · simpa only [P] using hpetal
  · simpa only [R, D, D2, line2] using hmissing

/-- **One-high-core maximal-band trichotomy.**  At the top of the surviving
band, either the family is domain-bounded, the extracted secant is already a
second high core, or the exact three-hole secant has core size below `h` and
meets the source core in at most `k-2` coordinates. -/
theorem card_le_or_second_high_core_or_exact_three_hole_residual
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = h + 1)
    (hsaturated : h = 2 * k)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : h ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hmax :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 3 * k - 4) :
    family.G.card ≤ 2 * h ∨
      (∃ line2 ∈ lineParameters family, line2 ≠ line ∧
        h ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card) ∨
      ∃ gamma ∈ outsideLine family line,
        ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
          let line2 := secantParameter family gamma beta
          line2 ∈ lineParameters family ∧ line2 ≠ line ∧
            (secantPetal family line gamma beta).card = k + 1 ∧
            (Finset.univ \ (
              jointCore dom (u 0) (u 1) line.1 line.2 ∪
                jointCore dom (u 0) (u 1) line2.1 line2.2)).card = 3 ∧
            (jointCore dom (u 0) (u 1) line2.1 line2.2).card < h ∧
            (jointCore dom (u 0) (u 1) line.1 line.2 ∩
              jointCore dom (u 0) (u 1) line2.1 line2.2).card ≤ k - 2 := by
  by_cases hcard : family.G.card ≤ 2 * h
  · exact Or.inl hcard
  have hcard' : 2 * h < family.G.card := by omega
  obtain ⟨gamma, hgamma, beta, hbeta, hne, hline2, hlineNe,
      hpetal, hmissing⟩ :=
    exists_maximal_high_core_exact_three_hole_secant
      family hk hn hthreshold hsaturated hcard' hline hcore hmax
  let line2 := secantParameter family gamma beta
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  by_cases hcore2 : h ≤ D2.card
  · exact Or.inr (Or.inl ⟨line2, hline2, hlineNe, hcore2⟩)
  apply Or.inr
  apply Or.inr
  have hsplit := Finset.card_sdiff_add_card_inter D2 D
  have hpetalEq : secantPetal family line gamma beta = D2 \ D := by rfl
  have hinter : (D ∩ D2).card ≤ k - 2 := by
    rw [Finset.inter_comm]
    rw [← hpetalEq, hpetal] at hsplit
    omega
  refine ⟨gamma, hgamma, beta, hbeta, hne, ?_⟩
  dsimp only
  refine ⟨hline2, hlineNe, hpetal, hmissing, Nat.lt_of_not_ge hcore2, ?_⟩
  simpa only [D, D2, line2] using hinter

#print axioms saturated_sharp_petal_floor_budget
#print axioms petal_floor_is_maximal_admissible
#print axioms half_add_three_le_sharpHighCorePetalThreshold
#print axioms exists_saturated_high_core_petal_ge_sharp_threshold
#print axioms card_le_or_second_high_core_or_sharp_secant_residual
#print axioms exists_maximal_high_core_exact_three_hole_secant
#print axioms card_le_or_second_high_core_or_exact_three_hole_residual

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreSharpSecantExtraction
