/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterCoreBandSynthesis

/-!
# Rate-quarter half predecessor: fresh-petal pruning

Fix a relevant decoded line with proper joint core `D`.  Exact line-core
packing first gives

```text
  |pointsOn(D)| <= |D|.
```

Every point outside the line has at least

```text
  r = h + 1 - (k - 1)
```

agreements in the complementary coordinate set `U = univ \ D`.  Applying the
endpoint obtuse-set bound inside the subtype `U` gives a quantitative energy
increment: if the whole family has more than `2h` points, then two outsiders
have more than `s` common fresh agreements for every

```text
  (2h - |D|) * s <= r^2 - 1.
```

The common fresh agreements are exactly the petal of their canonical secant
core outside `D`.  At the saturated quarter rate `h = 2k`, an intermediate
core `|D| >= k+2` therefore forces a new secant petal of size at least
`floor(k/3)+2`.  Equivalently, the natural cap
`|petal| <= floor(k/3)+1` closes the entire intermediate-core band.

This is a pruning/charging lemma, not a closure of the unrestricted rate-quarter
problem: different large petals may still overlap, and controlling that overlap
is the remaining global step.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalPruning

attribute [local instance] Classical.propDecidable

/-! ## The endpoint obtuse bound inside a finite sub-universe -/

variable {I U : Type} [Fintype I] [Fintype U] [DecidableEq U]

/-- Restrict an ambient finset to a finite sub-universe, represented as its
subtype. -/
def restrictTo (V A : Finset U) : Finset V :=
  Finset.univ.filter fun x : V => x.1 ∈ A

/-- Restriction to a containing finite universe preserves cardinality. -/
theorem card_restrictTo (V A : Finset U) (hA : A ⊆ V) :
    (restrictTo V A).card = A.card := by
  classical
  refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    refine ⟨⟨x, hA hx⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩

/-- Restriction commutes with intersection. -/
theorem restrictTo_inter (V A B : Finset U) :
    restrictTo V (A ∩ B) = restrictTo V A ∩ restrictTo V B := by
  ext x
  simp only [restrictTo, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inter]

/-- **Finite-sub-universe endpoint bound.**  Sets of size at least `t` inside
`V`, with pair intersections at most `s`, form a family of size at most `|V|`
when `|V|*s <= t^2-1`.

This is the exact Rankin--Serre bound from
`card_le_universe_of_equal_card_pair_inter_le`, after truncating the sets and
moving them to the subtype of `V`. -/
theorem card_le_finset_of_card_ge_pair_inter_le
    (V : Finset U) (S : I → Finset U) (t s : ℕ)
    (ht : 1 ≤ t)
    (hsub : ∀ i, S i ⊆ V)
    (hsize : ∀ i, t ≤ (S i).card)
    (hpair : Pairwise fun i j : I => (S i ∩ S j).card ≤ s)
    (hbudget : V.card * s ≤ t ^ 2 - 1) :
    Fintype.card I ≤ V.card := by
  classical
  let T : I → Finset U := fun i =>
    Classical.choose (Finset.exists_subset_card_eq (hsize i))
  have hTsub : ∀ i, T i ⊆ S i := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).1
  have hTcard : ∀ i, (T i).card = t := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).2
  have hTV : ∀ i, T i ⊆ V := by
    intro i
    exact (hTsub i).trans (hsub i)
  let R : I → Finset V := fun i => restrictTo V (T i)
  have hRcard : ∀ i, (R i).card = t := by
    intro i
    rw [show R i = restrictTo V (T i) by rfl, card_restrictTo V (T i) (hTV i)]
    exact hTcard i
  have hRpair : Pairwise fun i j : I => (R i ∩ R j).card ≤ s := by
    intro i j hij
    rw [show R i = restrictTo V (T i) by rfl,
      show R j = restrictTo V (T j) by rfl, ← restrictTo_inter]
    rw [card_restrictTo V (T i ∩ T j)]
    · apply le_trans (Finset.card_le_card
        (Finset.inter_subset_inter (hTsub i) (hTsub j)))
      exact hpair hij
    · exact (Finset.inter_subset_left.trans (hTV i))
  have hcard := card_le_universe_of_equal_card_pair_inter_le
    R V.card t s (by simp only [Fintype.card_coe]) ht hRcard hRpair hbudget
  exact hcard

/-! ## Proper-core population and secant petals -/

variable {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The part of the canonical secant core through `gamma,beta` lying outside
the source line core. -/
noncomputable def secantPetal
    {dom : iota ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) (gamma beta : F) : Finset iota :=
  jointCore dom (u 0) (u 1)
      (secantParameter family gamma beta).1
      (secantParameter family gamma beta).2 \
    jointCore dom (u 0) (u 1) line.1 line.2

/-- Fresh agreement intersection for two selected points is exactly the petal
of their canonical secant core outside the source core. -/
theorem fresh_inter_eq_secantPetal
    {dom : iota ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) {gamma beta : F}
    (hgamma : gamma ∈ family.G) (hbeta : beta ∈ family.G)
    (hne : gamma ≠ beta) :
    ((fullAgreement dom (u 0) (u 1) gamma (family.q gamma) \
          jointCore dom (u 0) (u 1) line.1 line.2) ∩
        (fullAgreement dom (u 0) (u 1) beta (family.q beta) \
          jointCore dom (u 0) (u 1) line.1 line.2)) =
      secantPetal family line gamma beta := by
  let secant := secantParameter family gamma beta
  have hgammaOn : gamma ∈ pointsOn family secant :=
    first_point_mem_pointsOn_secant family (beta := beta) hgamma
  have hbetaOn : beta ∈ pointsOn family secant :=
    second_point_mem_pointsOn_secant family (gamma := gamma) hbeta hne
  have hgammaEq := (mem_pointsOn_iff family secant gamma).mp hgammaOn |>.2
  have hbetaEq := (mem_pointsOn_iff family secant beta).mp hbetaOn |>.2
  have hcoreEq :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          fullAgreement dom (u 0) (u 1) beta (family.q beta) =
        jointCore dom (u 0) (u 1) secant.1 secant.2 := by
    rw [hgammaEq, hbetaEq]
    exact fullAgreement_inter_eq_jointCore
      dom (u 0) (u 1) secant.1 secant.2 hne
  rw [show secantPetal family line gamma beta =
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          fullAgreement dom (u 0) (u 1) beta (family.q beta)) \
        jointCore dom (u 0) (u 1) line.1 line.2 by
      simpa only [secantPetal, secant] using congrArg
        (fun D : Finset iota =>
          D \ jointCore dom (u 0) (u 1) line.1 line.2) hcoreEq.symm]
  ext i
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- A proper nonempty relevant core pays for every point on its decoded line:
at threshold `h+1` in `2h` coordinates, `|pointsOn| <= |core|`. -/
theorem pointsOn_card_le_core_card_of_proper_core
    {dom : iota ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hn : Fintype.card iota = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card iota : ℝ≥0)⌉₊ = h + 1)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcorePos : 1 ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hcoreLt :
      (jointCore dom (u 0) (u 1) line.1 line.2).card < h) :
    (pointsOn family line).card ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card := by
  let z := (jointCore dom (u 0) (u 1) line.1 line.2).card
  let L := (pointsOn family line).card
  have hpack := pointsOn_card_mul_max_add_core_le family hline
  change L * max 1
      (⌈(1 - delta) * (Fintype.card iota : ℝ≥0)⌉₊ - z) + z ≤
    Fintype.card iota at hpack
  rw [hthreshold, hn] at hpack
  have hmax : max 1 (h + 1 - z) = h + 1 - z := by
    apply max_eq_right
    change z < h at hcoreLt
    omega
  rw [hmax] at hpack
  change 1 ≤ z at hcorePos
  change z < h at hcoreLt
  change L ≤ z
  by_contra hnot
  have hL : z + 1 ≤ L := by omega
  let d := h + 1 - z
  have hd : 2 ≤ d := by omega
  have heq : d + z = h + 1 := by omega
  have hzZ : (1 : ℤ) ≤ z := by exact_mod_cast hcorePos
  have hdZ : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have heqZ : (d : ℤ) + z = h + 1 := by exact_mod_cast heq
  have hmulZ : 0 ≤ ((z : ℤ) - 1) * ((d : ℤ) - 1) :=
    mul_nonneg (sub_nonneg.mpr hzZ) (sub_nonneg.mpr hdZ)
  have hstrict : 2 * h < (z + 1) * d + z := by
    exact_mod_cast (show (2 : ℤ) * h < ((z : ℤ) + 1) * d + z by
      nlinarith)
  have hprod := Nat.mul_le_mul_right d hL
  change L * d + z ≤ 2 * h at hpack
  omega

/-! ## Quantitative outsider pruning -/

/-- If all canonical secant petals between outsiders are at most `s`, then a
proper source core forces the sharp family bound whenever the exact reduced
obtuse budget holds. -/
theorem card_le_two_mul_of_proper_core_secantPetal_cap
    {dom : iota ↪ F} {k h s : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card iota = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card iota : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcorePos : 1 ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hcoreLt :
      (jointCore dom (u 0) (u 1) line.1 line.2).card < h)
    (hbudget :
      (2 * h - (jointCore dom (u 0) (u 1) line.1 line.2).card) * s ≤
        (h + 1 - (k - 1)) ^ 2 - 1)
    (hpetal : ∀ gamma ∈ outsideLine family line,
      ∀ beta ∈ outsideLine family line, gamma ≠ beta →
        (secantPetal family line gamma beta).card ≤ s) :
    family.G.card ≤ 2 * h := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset iota := Finset.univ \ D
  let K := {gamma // gamma ∈ outsideLine family line}
  let A : K → Finset iota := fun gamma =>
    fullAgreement dom (u 0) (u 1) gamma.1 (family.q gamma.1) \ D
  have hlineCard : (pointsOn family line).card ≤ D.card := by
    simpa only [D] using pointsOn_card_le_core_card_of_proper_core
      family hn hthreshold hline hcorePos hcoreLt
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
  have hDle : D.card ≤ 2 * h := by
    have hle := Finset.card_le_univ D
    simpa only [hn] using hle
  have hpartition := pointsOn_card_add_outsideLine_card family line
  rw [hVcard] at houtside'
  change (pointsOn family line).card + (outsideLine family line).card =
    family.G.card at hpartition
  omega

/-- **Exact energy increment from a proper core.**  In a family larger than the
domain, every reduced obtuse budget `s` is violated by a pair of outsiders;
equivalently, their canonical secant core has a petal larger than `s` outside
the source core. -/
theorem exists_outside_secantPetal_card_gt_of_card_gt_two_mul
    {dom : iota ↪ F} {k h s : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card iota = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card iota : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h) (hcard : 2 * h < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcorePos : 1 ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hcoreLt :
      (jointCore dom (u 0) (u 1) line.1 line.2).card < h)
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
  have hle := card_le_two_mul_of_proper_core_secantPetal_cap
    family hk hn hthreshold hrate hline hcorePos hcoreLt hbudget hcap
  omega

/-! ## Saturated rate-quarter specialization -/

/-- In the saturated intermediate band, `floor(k/3)+1` satisfies the exact
reduced obtuse budget. -/
theorem saturated_intermediate_third_budget
    {k h z : ℕ} (hk : 1 ≤ k) (hsaturated : h = 2 * k)
    (hlower : h / 2 + 2 ≤ z) (hupper : z < h) :
    (2 * h - z) * (k / 3 + 1) ≤
      (h + 1 - (k - 1)) ^ 2 - 1 := by
  have hzLower : k + 2 ≤ z := by omega
  have hN : 2 * h - z ≤ 3 * k := by omega
  have hquot : 3 * (k / 3) ≤ k := Nat.mul_div_le k 3
  have hfirst := Nat.mul_le_mul_right (k / 3 + 1) hN
  have hsecond : 3 * k * (k / 3 + 1) ≤ k * k + 3 * k := by
    calc
      3 * k * (k / 3 + 1) = k * (3 * (k / 3)) + 3 * k := by ring
      _ ≤ k * k + 3 * k := Nat.add_le_add_right
        (Nat.mul_le_mul_left k hquot) (3 * k)
  have hr : h + 1 - (k - 1) = k + 2 := by omega
  rw [hr]
  have hthird : k * k + 3 * k ≤ (k + 2) ^ 2 - 1 := by
    rw [show (k + 2) ^ 2 = k * k + 4 * k + 4 by ring]
    omega
  exact hfirst.trans (hsecond.trans hthird)

/-- **One-third petal increment.**  A counterexample containing an
intermediate source core at the saturated quarter rate forces two outsiders
whose secant core gains at least `floor(k/3)+2` new coordinates outside the
source core. -/
theorem exists_outside_secantPetal_card_gt_third_of_saturated_intermediate
    {dom : iota ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card iota = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card iota : ℝ≥0)⌉₊ = h + 1)
    (hsaturated : h = 2 * k) (hcard : 2 * h < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hlower : h / 2 + 2 ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hupper :
      (jointCore dom (u 0) (u 1) line.1 line.2).card < h) :
    ∃ gamma ∈ outsideLine family line,
      ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
        k / 3 + 1 < (secantPetal family line gamma beta).card := by
  have hrate : 2 * k ≤ h := by omega
  have hcorePos : 1 ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card := by omega
  apply exists_outside_secantPetal_card_gt_of_card_gt_two_mul
    family hk hn hthreshold hrate hcard hline hcorePos hupper
  exact saturated_intermediate_third_budget hk hsaturated hlower hupper

/-- **Core-band synthesis with quantitative pruning attached.**  The saturated
core-band dichotomy can be sharpened so that its intermediate branch carries a
canonical new secant petal of size at least `floor(k/3)+2`, in addition to the
failed complementary-cover and failed large-core inequalities already supplied
by `card_le_two_mul_or_saturated_high_core_or_saturated_intermediate_core`.

This theorem narrows the remaining band but does not eliminate it: the next
step must control overlap among the forced petals. -/
theorem card_le_two_mul_or_saturated_high_core_or_intermediate_with_third_petal
    {dom : iota ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card iota = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card iota : ℝ≥0)⌉₊ = h + 1)
    (hsaturated : h = 2 * k) :
    family.G.card ≤ 2 * h ∨
      (∃ line ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∧
        (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 3 * k - 4) ∨
      ∃ line ∈ lineParameters family,
        h / 2 + 2 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∧
        (jointCore dom (u 0) (u 1) line.1 line.2).card < h ∧
        (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 3 * k - 4 ∧
        (∀ line2 ∈ lineParameters family,
          h + 1 ≤
              (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card +
                2 * (k - 1) ∧
            3 ≤ (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card) ∧
        ∃ gamma ∈ outsideLine family line,
          ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
            k / 3 + 1 < (secantPetal family line gamma beta).card := by
  by_cases hcard : family.G.card ≤ 2 * h
  · exact Or.inl hcard
  have hcardGt : 2 * h < family.G.card := by omega
  rcases card_le_two_mul_or_saturated_high_core_or_saturated_intermediate_core
      family hk hn hthreshold hsaturated with hle | hhigh | hmid
  · exact (hcard hle).elim
  · exact Or.inr (Or.inl hhigh)
  · obtain ⟨line, hline, hlower, hupper, hcoreCap, hisolated⟩ := hmid
    have hpetal :=
      exists_outside_secantPetal_card_gt_third_of_saturated_intermediate
        family hk hn hthreshold hsaturated hcardGt hline hlower hupper
    exact Or.inr (Or.inr
      ⟨line, hline, hlower, hupper, hcoreCap, hisolated, hpetal⟩)

/-- **Intermediate-band closure under a natural local cap.**  At the saturated
quarter rate, if every outsider secant gains at most `floor(k/3)+1` fresh
coordinates beyond one intermediate core, then the family has at most the
domain size. -/
theorem card_le_two_mul_of_saturated_intermediate_secantPetal_cap
    {dom : iota ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card iota = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card iota : ℝ≥0)⌉₊ = h + 1)
    (hsaturated : h = 2 * k)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hlower : h / 2 + 2 ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hupper :
      (jointCore dom (u 0) (u 1) line.1 line.2).card < h)
    (hpetal : ∀ gamma ∈ outsideLine family line,
      ∀ beta ∈ outsideLine family line, gamma ≠ beta →
        (secantPetal family line gamma beta).card ≤ k / 3 + 1) :
    family.G.card ≤ 2 * h := by
  have hrate : 2 * k ≤ h := by omega
  have hcorePos : 1 ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card := by omega
  apply card_le_two_mul_of_proper_core_secantPetal_cap
    family hk hn hthreshold hrate hline hcorePos hupper
  · exact saturated_intermediate_third_budget hk hsaturated hlower hupper
  · exact hpetal

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalPruning

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalPruning
#print axioms card_le_finset_of_card_ge_pair_inter_le
#print axioms pointsOn_card_le_core_card_of_proper_core
#print axioms exists_outside_secantPetal_card_gt_of_card_gt_two_mul
#print axioms exists_outside_secantPetal_card_gt_third_of_saturated_intermediate
#print axioms card_le_two_mul_or_saturated_high_core_or_intermediate_with_third_petal
#print axioms card_le_two_mul_of_saturated_intermediate_secantPetal_cap
