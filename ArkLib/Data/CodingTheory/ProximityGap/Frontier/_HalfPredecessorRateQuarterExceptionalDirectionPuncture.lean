/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDirectionCapDichotomy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound

/-!
# Puncturing the exceptional direction branch at `n = 16`, `k = 4`

Translate every selected polynomial point by a fixed exceptional direction
`r`, writing

```text
a_gamma = q_gamma - gamma * r.
```

On the direction agreement core, the full agreement set of `gamma` is the
agreement trace of `a_gamma` with the base row.  Outside that core, a common
full-agreement coordinate makes `gamma` recoverable from `a_gamma`; hence two
distinct selected scalars using the same fresh coordinate have distinct
translated intercepts.  Their core traces consequently meet in at most
`k-1` coordinates.

At `n=16`, `k=4`, and threshold at least nine this closes the very-high-core
part of the exceptional branch.  A direction core of size fourteen leaves
two fresh coordinates.  Each coordinate bucket supplies seven-element core
traces with pair intersections at most three, so the exact constant-weight
Plotkin bound gives bucket size at most eight.  The resulting `2 * 8` bound
is sharp for this counting argument.  Core size fifteen is even smaller,
and core size sixteen is incompatible with the required fresh coordinate.

Thus failure of the automatic direction cap can be localized honestly to an
exceptional direction core of size between six and thirteen.  This does not
claim that such a core is impossible.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCapDichotomy
open ArkLib.ProximityGap.Frontier.ConstantWeightPlotkinBound

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterExceptionalDirectionPuncture

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Intercept obtained after translating a lifted polynomial point by the
fixed direction `r`. -/
noncomputable def translatedIntercept
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (r : F[X]) (gamma : F) : F[X] :=
  family.q gamma - C gamma * r

/-- The part of a full agreement contained in the fixed direction core. -/
noncomputable def directionCoreTrace
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (r : F[X]) (gamma : F) : Finset I :=
  fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
    directionAgreement dom (u 1) r

/-- The same core trace, with its ambient type punctured to the direction
core. -/
noncomputable def directionCoreTraceSubtype
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (r : F[X]) (gamma : F) :
    Finset {i : I // i ∈ directionAgreement dom (u 1) r} :=
  Finset.univ.filter fun i =>
    i.1 ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma)

/-- Full agreements outside the direction core, represented in the punctured
complement type. -/
noncomputable def directionFreshTraceSubtype
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (r : F[X]) (gamma : F) :
    Finset {i : I // i ∉ directionAgreement dom (u 1) r} :=
  Finset.univ.filter fun i =>
    i.1 ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma)

theorem translatedIntercept_add_direction
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (r : F[X]) (gamma : F) :
    translatedIntercept family r gamma + C gamma * r = family.q gamma := by
  simp only [translatedIntercept]
  ring

theorem translatedIntercept_natDegree_lt
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (r : F[X]) (hr : r.natDegree < k)
    {gamma : F} (hgamma : gamma ∈ family.G) :
    (translatedIntercept family r gamma).natDegree < k := by
  have hCr : (C gamma * r).natDegree ≤ r.natDegree :=
    natDegree_C_mul_le gamma r
  exact lt_of_le_of_lt (natDegree_sub_le _ _)
    (max_lt (family.degree_lt gamma hgamma) (lt_of_le_of_lt hCr hr))

/-- Translation identifies a point's trace on the direction core with the
joint core of its translated intercept and the fixed direction. -/
theorem directionCoreTrace_eq_jointCore
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (r : F[X]) (gamma : F) :
    directionCoreTrace family r gamma =
      jointCore dom (u 0) (u 1)
        (translatedIntercept family r gamma) r := by
  ext i
  simp only [directionCoreTrace, directionAgreement, fullAgreement,
    jointCore, translatedIntercept, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and, eval_sub, eval_mul, eval_C]
  constructor
  · rintro ⟨hq, hr⟩
    refine ⟨?_, hr⟩
    rw [hq, hr]
    ring
  · rintro ⟨ha, hr⟩
    refine ⟨?_, hr⟩
    rw [← ha, hr]
    ring

theorem directionCoreTraceSubtype_card
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (r : F[X]) (gamma : F) :
    (directionCoreTraceSubtype family r gamma).card =
      (directionCoreTrace family r gamma).card := by
  let e : {i : I // i ∈ directionAgreement dom (u 1) r} ↪ I :=
    ⟨fun i => i.1, fun _ _ h => Subtype.ext h⟩
  have hmap : (directionCoreTraceSubtype family r gamma).map e =
      directionCoreTrace family r gamma := by
    ext i
    simp [directionCoreTraceSubtype, directionCoreTrace, e]
  calc
    (directionCoreTraceSubtype family r gamma).card =
        ((directionCoreTraceSubtype family r gamma).map e).card := by
          rw [Finset.card_map]
    _ = (directionCoreTrace family r gamma).card :=
      congrArg Finset.card hmap

theorem directionFreshTraceSubtype_card
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (r : F[X]) (gamma : F) :
    (directionFreshTraceSubtype family r gamma).card =
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) \
        directionAgreement dom (u 1) r).card := by
  let e : {i : I // i ∉ directionAgreement dom (u 1) r} ↪ I :=
    ⟨fun i => i.1, fun _ _ h => Subtype.ext h⟩
  have hmap : (directionFreshTraceSubtype family r gamma).map e =
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) \
        directionAgreement dom (u 1) r := by
    ext i
    simp [directionFreshTraceSubtype, e]
  calc
    (directionFreshTraceSubtype family r gamma).card =
        ((directionFreshTraceSubtype family r gamma).map e).card := by
          rw [Finset.card_map]
    _ = _ := congrArg Finset.card hmap

/-- A common fresh coordinate separates translated intercepts.  This is the
puncturing step: outside the direction core, the nonzero direction error
recovers the scalar from the translated intercept value. -/
theorem translatedIntercept_ne_of_common_fresh
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (r : F[X]) {gamma beta : F} (hne : gamma ≠ beta)
    {i : I}
    (hgamma : i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma))
    (hbeta : i ∈ fullAgreement dom (u 0) (u 1) beta (family.q beta))
    (hout : i ∉ directionAgreement dom (u 1) r) :
    translatedIntercept family r gamma ≠
      translatedIntercept family r beta := by
  intro hintercept
  have hqgamma : (family.q gamma).eval (dom i) =
      u 0 i + gamma * u 1 i := by
    simpa only [fullAgreement, Finset.mem_filter, Finset.mem_univ,
      true_and] using hgamma
  have hqbeta : (family.q beta).eval (dom i) =
      u 0 i + beta * u 1 i := by
    simpa only [fullAgreement, Finset.mem_filter, Finset.mem_univ,
      true_and] using hbeta
  have hrne : r.eval (dom i) ≠ u 1 i := by
    intro hr
    apply hout
    simp only [directionAgreement, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hr
  have heval := congrArg (fun p : F[X] => p.eval (dom i)) hintercept
  simp only [translatedIntercept, eval_sub, eval_mul, eval_C] at heval
  rw [hqgamma, hqbeta] at heval
  have hmul : (gamma - beta) * (u 1 i - r.eval (dom i)) = 0 := by
    linear_combination heval
  have hscalar : gamma - beta ≠ 0 := sub_ne_zero.mpr hne
  have hdirection : u 1 i - r.eval (dom i) ≠ 0 :=
    sub_ne_zero.mpr hrne.symm
  exact (mul_ne_zero hscalar hdirection) hmul

/-- Two selected points using the same fresh coordinate have core traces
meeting in at most `k-1` coordinates. -/
theorem directionCoreTrace_pair_card_le_pred_of_common_fresh
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (r : F[X]) (hr : r.natDegree < k)
    {gamma beta : F} (hgammaG : gamma ∈ family.G)
    (hbetaG : beta ∈ family.G) (hne : gamma ≠ beta)
    {i : I}
    (hgamma : i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma))
    (hbeta : i ∈ fullAgreement dom (u 0) (u 1) beta (family.q beta))
    (hout : i ∉ directionAgreement dom (u 1) r) :
    (directionCoreTrace family r gamma ∩
      directionCoreTrace family r beta).card ≤ k - 1 := by
  have hane := translatedIntercept_ne_of_common_fresh
    family r hne hgamma hbeta hout
  have hoff : family.q gamma ≠
      translatedIntercept family r beta + C gamma * r := by
    intro hline
    apply hane
    calc
      translatedIntercept family r gamma =
          family.q gamma - C gamma * r := rfl
      _ = translatedIntercept family r beta := by rw [hline]; ring
  have hcap := fullAgreement_inter_jointCore_card_le
    dom (u 0) (u 1) hk
      (family.degree_lt gamma hgammaG)
      (translatedIntercept_natDegree_lt family r hr hbetaG)
      hr hoff
  have hsub : directionCoreTrace family r gamma ∩
      directionCoreTrace family r beta ⊆
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
        jointCore dom (u 0) (u 1)
          (translatedIntercept family r beta) r := by
    intro j hj
    have hj' := Finset.mem_inter.mp hj
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_inter.mp hj'.1 |>.1
    · rw [← directionCoreTrace_eq_jointCore family r beta]
      exact hj'.2
  exact (Finset.card_le_card hsub).trans hcap

/-- Subtype version consumed by the Plotkin bucket bound. -/
theorem directionCoreTraceSubtype_pair_card_le_pred_of_common_fresh
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (r : F[X]) (hr : r.natDegree < k)
    {gamma beta : F} (hgammaG : gamma ∈ family.G)
    (hbetaG : beta ∈ family.G) (hne : gamma ≠ beta)
    {i : I}
    (hgamma : i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma))
    (hbeta : i ∈ fullAgreement dom (u 0) (u 1) beta (family.q beta))
    (hout : i ∉ directionAgreement dom (u 1) r) :
    (directionCoreTraceSubtype family r gamma ∩
      directionCoreTraceSubtype family r beta).card ≤ k - 1 := by
  let e : {j : I // j ∈ directionAgreement dom (u 1) r} ↪ I :=
    ⟨fun j => j.1, fun _ _ h => Subtype.ext h⟩
  have hsub :
      (directionCoreTraceSubtype family r gamma ∩
        directionCoreTraceSubtype family r beta).map e ⊆
      directionCoreTrace family r gamma ∩
        directionCoreTrace family r beta := by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨x, hx, rfl⟩ := hj
    have hx' := Finset.mem_inter.mp hx
    simp only [directionCoreTraceSubtype, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx'
    simp only [directionCoreTrace, Finset.mem_inter]
    exact ⟨⟨hx'.1, x.2⟩, hx'.2, x.2⟩
  calc
    (directionCoreTraceSubtype family r gamma ∩
        directionCoreTraceSubtype family r beta).card =
      ((directionCoreTraceSubtype family r gamma ∩
        directionCoreTraceSubtype family r beta).map e).card := by
          rw [Finset.card_map]
    _ ≤ (directionCoreTrace family r gamma ∩
        directionCoreTrace family r beta).card := Finset.card_le_card hsub
    _ ≤ k - 1 :=
      directionCoreTrace_pair_card_le_pred_of_common_fresh
        family hk r hr hgammaG hbetaG hne hgamma hbeta hout

/-- At length sixteen and threshold at least nine, the direction-core trace
and direction-core cardinalities satisfy the exact puncturing budget

`9 + |D| <= 16 + |trace|`.

This subtraction-free form remains useful at every exceptional core size. -/
theorem nine_add_direction_core_card_le_sixteen_add_trace_card
    {dom : I ↪ F} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊)
    (r : F[X]) {gamma : F} (hgamma : gamma ∈ family.G) :
    9 + (directionAgreement dom (u 1) r).card ≤
      16 + (directionCoreTrace family r gamma).card := by
  let A := fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let D := directionAgreement dom (u 1) r
  let E := directionCoreTrace family r gamma
  let X := A \ D
  have hA : 9 ≤ A.card := by
    exact hthreshold.trans (family.threshold_le gamma hgamma)
  have hsplit : X.card + E.card = A.card := by
    have h := Finset.card_sdiff_add_card_inter A D
    simpa only [X, E, directionCoreTrace, A, D] using h
  have hXsub : X ⊆ Finset.univ \ D := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩
  have hX : X.card ≤ 16 - D.card := by
    have hle := Finset.card_le_card hXsub
    have hcomplement : (Finset.univ \ D).card = 16 - D.card := by
      simp only [Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ, hn]
    omega
  have hD : D.card ≤ 16 := by
    have hle := Finset.card_le_card (Finset.subset_univ D)
    simpa only [Finset.card_univ, hn] using hle
  change 9 + D.card ≤ 16 + E.card
  omega

/-- No-jointness makes every selected point's punctured fresh trace
nonempty. -/
theorem directionFreshTraceSubtype_nonempty
    {dom : I ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (r : F[X]) (hr : r.natDegree < k)
    {gamma : F} (hgamma : gamma ∈ family.G) :
    (directionFreshTraceSubtype family r gamma).Nonempty := by
  obtain ⟨i, hi, hout⟩ :=
    exists_fullAgreement_outside_directionAgreement family hgamma r hr
  refine ⟨⟨i, hout⟩, ?_⟩
  simp only [directionFreshTraceSubtype, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact hi

/-- Plotkin bound for the selected scalars using one fixed coordinate outside
the exceptional direction core.  The hypothesis `t <= |trace_gamma|` is
usually supplied by the puncturing budget above. -/
theorem fresh_coordinate_fiber_plotkin_div
    {dom : I ↪ F} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (r : F[X]) (hr : r.natDegree < 4)
    (i : {j : I // j ∉ directionAgreement dom (u 1) r})
    (t : ℕ)
    (htrace : ∀ gamma ∈ family.G,
      i.1 ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) →
      t ≤ (directionCoreTrace family r gamma).card)
    (hgap : (directionAgreement dom (u 1) r).card * 3 < t ^ 2) :
    Fintype.card
        {gamma : {gamma // gamma ∈ family.G} //
          i.1 ∈ fullAgreement dom (u 0) (u 1) gamma.1
            (family.q gamma.1)} ≤
      ((directionAgreement dom (u 1) r).card * (t - 3)) /
        (t ^ 2 - (directionAgreement dom (u 1) r).card * 3) := by
  let B := {gamma : {gamma // gamma ∈ family.G} //
    i.1 ∈ fullAgreement dom (u 0) (u 1) gamma.1
      (family.q gamma.1)}
  let U := {j : I // j ∈ directionAgreement dom (u 1) r}
  let A : B → Finset U := fun gamma =>
    directionCoreTraceSubtype family r gamma.1.1
  have hlarge : ∀ gamma : B, t ≤ (A gamma).card := by
    intro gamma
    rw [directionCoreTraceSubtype_card]
    exact htrace gamma.1.1 gamma.1.2 gamma.2
  let T : B → Finset U := fun gamma =>
    Classical.choose (Finset.exists_subset_card_eq (hlarge gamma))
  have hTsub : ∀ gamma : B, T gamma ⊆ A gamma := by
    intro gamma
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hlarge gamma))).1
  have hTcard : ∀ gamma : B, (T gamma).card = t := by
    intro gamma
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hlarge gamma))).2
  have hTpair : ∀ gamma beta : B, gamma ≠ beta →
      (T gamma ∩ T beta).card ≤ 3 := by
    intro gamma beta hne
    have hscalar : gamma.1.1 ≠ beta.1.1 := by
      intro h
      apply hne
      apply Subtype.ext
      apply Subtype.ext
      exact h
    apply (Finset.card_le_card
      (Finset.inter_subset_inter (hTsub gamma) (hTsub beta))).trans
    simpa only [A] using
      (directionCoreTraceSubtype_pair_card_le_pred_of_common_fresh
        family (by norm_num) r hr gamma.1.2 beta.1.2 hscalar
          gamma.2 beta.2 i.2)
  have hUcard : Fintype.card U =
      (directionAgreement dom (u 1) r).card := by
    simp only [U, Fintype.card_coe]
  have hplotkin := constantWeight_plotkin_div T t 3 hTcard hTpair (by
    simpa only [hUcard] using hgap)
  simpa only [B, U, hUcard] using hplotkin

/-- A fresh-coordinate bucket has size at most eight when the exceptional
direction core has size fourteen. -/
theorem fresh_coordinate_fiber_card_le_eight_of_core_fourteen
    {dom : I ↪ F} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 14)
    (i : {j : I // j ∉ directionAgreement dom (u 1) r}) :
    Fintype.card
        {gamma : {gamma // gamma ∈ family.G} //
          i.1 ∈ fullAgreement dom (u 0) (u 1) gamma.1
            (family.q gamma.1)} ≤ 8 := by
  have htrace : ∀ gamma ∈ family.G,
      i.1 ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) →
      7 ≤ (directionCoreTrace family r gamma).card := by
    intro gamma hgamma _hi
    have hbudget := nine_add_direction_core_card_le_sixteen_add_trace_card
      family hn hthreshold r hgamma
    omega
  have hplotkin := fresh_coordinate_fiber_plotkin_div
    family r hr i 7 htrace (by rw [hcore]; norm_num)
  rw [hcore] at hplotkin
  norm_num at hplotkin ⊢
  exact hplotkin

/-- A fresh-coordinate bucket has size at most three when the exceptional
direction core has size fifteen. -/
theorem fresh_coordinate_fiber_card_le_three_of_core_fifteen
    {dom : I ↪ F} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 15)
    (i : {j : I // j ∉ directionAgreement dom (u 1) r}) :
    Fintype.card
        {gamma : {gamma // gamma ∈ family.G} //
          i.1 ∈ fullAgreement dom (u 0) (u 1) gamma.1
            (family.q gamma.1)} ≤ 3 := by
  have htrace : ∀ gamma ∈ family.G,
      i.1 ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) →
      8 ≤ (directionCoreTrace family r gamma).card := by
    intro gamma hgamma _hi
    have hbudget := nine_add_direction_core_card_le_sixteen_add_trace_card
      family hn hthreshold r hgamma
    omega
  have hplotkin := fresh_coordinate_fiber_plotkin_div
    family r hr i 8 htrace (by rw [hcore]; norm_num)
  rw [hcore] at hplotkin
  norm_num at hplotkin ⊢
  exact hplotkin

/-- Incidence double counting converts a uniform fresh-coordinate fiber cap
into a family bound. -/
theorem family_card_le_direction_complement_mul_of_fiber_cap
    {dom : I ↪ F} {k B : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (r : F[X]) (hr : r.natDegree < k)
    (hcap : ∀ i : {j : I // j ∉ directionAgreement dom (u 1) r},
      Fintype.card
          {gamma : {gamma // gamma ∈ family.G} //
            i.1 ∈ fullAgreement dom (u 0) (u 1) gamma.1
              (family.q gamma.1)} ≤ B) :
    family.G.card ≤
      Fintype.card {j : I // j ∉ directionAgreement dom (u 1) r} * B := by
  let K := {gamma // gamma ∈ family.G}
  let U := {j : I // j ∉ directionAgreement dom (u 1) r}
  let S : K → Finset U := fun gamma =>
    directionFreshTraceSubtype family r gamma.1
  have hone : ∀ gamma : K, 1 ≤ (S gamma).card := by
    intro gamma
    exact Finset.card_pos.mpr
      (by simpa only [S] using
        (directionFreshTraceSubtype_nonempty family r hr gamma.2))
  have hlower : Fintype.card K ≤ ∑ gamma : K, (S gamma).card := by
    calc
      Fintype.card K = ∑ _gamma : K, 1 := by simp
      _ ≤ ∑ gamma : K, (S gamma).card :=
        Finset.sum_le_sum fun gamma _ => hone gamma
  have hdouble := ArkLib.Coverage.sum_card_eq_sum_degree S
  have hdegree : ∀ i : U,
      (Finset.univ.filter fun gamma : K => i ∈ S gamma).card ≤ B := by
    intro i
    let H := Finset.univ.filter fun gamma : K => i ∈ S gamma
    let P := {gamma : K //
      i.1 ∈ fullAgreement dom (u 0) (u 1) gamma.1
        (family.q gamma.1)}
    let e : {gamma // gamma ∈ H} ≃ P :=
      { toFun := fun gamma =>
          ⟨gamma.1, by
            have hmem := Finset.mem_filter.mp gamma.2 |>.2
            simpa only [S, directionFreshTraceSubtype,
              Finset.mem_filter, Finset.mem_univ, true_and] using hmem⟩
        invFun := fun gamma =>
          ⟨gamma.1, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, by
              simpa only [S, directionFreshTraceSubtype,
                Finset.mem_filter, Finset.mem_univ, true_and] using gamma.2⟩⟩
        left_inv := by intro gamma; exact Subtype.ext rfl
        right_inv := by intro gamma; exact Subtype.ext rfl }
    have heq := Fintype.card_congr e
    have hP : Fintype.card P ≤ B := by
      simpa only [P, K, U] using hcap i
    have hH : H.card = Fintype.card P := by
      simpa only [Fintype.card_coe] using heq
    simpa only [H] using hH.le.trans hP
  have hupper :
      (∑ i : U, (Finset.univ.filter fun gamma : K => i ∈ S gamma).card) ≤
        Fintype.card U * B := by
    calc
      (∑ i : U,
          (Finset.univ.filter fun gamma : K => i ∈ S gamma).card) ≤
          ∑ _i : U, B := Finset.sum_le_sum fun i _ => hdegree i
      _ = Fintype.card U * B := by simp
  have hcard : Fintype.card K ≤ Fintype.card U * B := by
    rw [hdouble] at hlower
    exact hlower.trans hupper
  simpa only [K, U, Fintype.card_coe] using hcard

/-- A fourteen-coordinate exceptional direction core already forces the
target family bound `|G| <= 16`. -/
theorem card_le_sixteen_of_direction_core_card_eq_fourteen
    {dom : I ↪ F} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 14) :
    family.G.card ≤ 16 := by
  have hcap : ∀ i : {j : I // j ∉ directionAgreement dom (u 1) r},
      Fintype.card
          {gamma : {gamma // gamma ∈ family.G} //
            i.1 ∈ fullAgreement dom (u 0) (u 1) gamma.1
              (family.q gamma.1)} ≤ 8 := by
    intro i
    exact fresh_coordinate_fiber_card_le_eight_of_core_fourteen
      family hn hthreshold r hr hcore i
  have hfamily := family_card_le_direction_complement_mul_of_fiber_cap
    family r hr hcap
  have hcomplement :
      Fintype.card {j : I // j ∉ directionAgreement dom (u 1) r} = 2 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_coe, hn, hcore]
  rw [hcomplement] at hfamily
  norm_num at hfamily ⊢
  exact hfamily

/-- A fifteen-coordinate exceptional direction core gives the stronger
bound `|G| <= 3`. -/
theorem card_le_three_of_direction_core_card_eq_fifteen
    {dom : I ↪ F} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 15) :
    family.G.card ≤ 3 := by
  have hcap : ∀ i : {j : I // j ∉ directionAgreement dom (u 1) r},
      Fintype.card
          {gamma : {gamma // gamma ∈ family.G} //
            i.1 ∈ fullAgreement dom (u 0) (u 1) gamma.1
              (family.q gamma.1)} ≤ 3 := by
    intro i
    exact fresh_coordinate_fiber_card_le_three_of_core_fifteen
      family hn hthreshold r hr hcore i
  have hfamily := family_card_le_direction_complement_mul_of_fiber_cap
    family r hr hcap
  have hcomplement :
      Fintype.card {j : I // j ∉ directionAgreement dom (u 1) r} = 1 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_coe, hn, hcore]
  rw [hcomplement] at hfamily
  simpa only [one_mul] using hfamily

/-- A full sixteen-coordinate direction core is incompatible with any
selected scalar, because every selected full agreement needs a fresh
coordinate outside it. -/
theorem card_eq_zero_of_direction_core_card_eq_sixteen
    {dom : I ↪ F} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 16) :
    family.G.card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro gamma hgamma
  obtain ⟨i, _hi, hout⟩ :=
    exists_fullAgreement_outside_directionAgreement family hgamma r hr
  have hfull : directionAgreement dom (u 1) r = Finset.univ :=
    Finset.eq_univ_of_card (directionAgreement dom (u 1) r)
      (hcore.trans hn.symm)
  exact hout (by rw [hfull]; exact Finset.mem_univ i)

/-- **Very-high exceptional direction closure.**  At `n=16`, `k=4`, and
threshold at least nine, every exceptional direction core of size at least
fourteen is harmless. -/
theorem card_le_sixteen_of_fourteen_le_direction_core
    {dom : I ↪ F} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : 14 ≤ (directionAgreement dom (u 1) r).card) :
    family.G.card ≤ 16 := by
  have hcoreUpper : (directionAgreement dom (u 1) r).card ≤ 16 := by
    have hle := Finset.card_le_card
      (Finset.subset_univ (directionAgreement dom (u 1) r))
    simpa only [Finset.card_univ, hn] using hle
  interval_cases hz : (directionAgreement dom (u 1) r).card
  · exact card_le_sixteen_of_direction_core_card_eq_fourteen
      family hn hthreshold r hr hz
  · exact (card_le_three_of_direction_core_card_eq_fifteen
      family hn hthreshold r hr hz).trans (by norm_num)
  · rw [card_eq_zero_of_direction_core_card_eq_sixteen
      family hn r hr hz]
    norm_num

/-- **Sharpened exceptional-direction residual.**  At the exact `n=16`,
`k=4`, threshold-nine half predecessor, either the target cardinal bound
already holds or there is one degree-`<4` direction polynomial whose common
agreement core has cardinality in the explicit surviving band `6..13`.
Every selected scalar still carries its certified fresh full-agreement
coordinate outside that same core.

The upper cutoff `13` is new; the lower cutoff `6` is the exact failure point
of `DirectionAgreementCapSucc`. -/
theorem card_le_sixteen_or_exceptional_direction_core_band
    {dom : I ↪ F} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : ℝ≥0)⌉₊ = 9) :
    family.G.card ≤ 16 ∨
      ∃ r : F[X], r.natDegree < 4 ∧
        6 ≤ (directionAgreement dom (u 1) r).card ∧
        (directionAgreement dom (u 1) r).card ≤ 13 ∧
        ∀ gamma ∈ family.G, ∃ i : I,
          i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
          i ∉ directionAgreement dom (u 1) r := by
  rcases directionAgreementCapSucc_or_exceptionalCore family with
    hcap | ⟨r, hr, hcoreLower, hfresh⟩
  · left
    have hle := card_le_two_mul_of_directionAgreementCapSucc
      family (h := 8) hn hthreshold (by norm_num) hcap
    norm_num at hle ⊢
    exact hle
  · by_cases hcoreHigh :
        14 ≤ (directionAgreement dom (u 1) r).card
    · left
      exact card_le_sixteen_of_fourteen_le_direction_core
        family hn hthreshold.ge r hr hcoreHigh
    · right
      refine ⟨r, hr, ?_, ?_, hfresh⟩
      · simpa only [Nat.reduceAdd] using hcoreLower
      · omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterExceptionalDirectionPuncture

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterExceptionalDirectionPuncture
#print axioms translatedIntercept_ne_of_common_fresh
#print axioms directionCoreTrace_pair_card_le_pred_of_common_fresh
#print axioms directionCoreTraceSubtype_pair_card_le_pred_of_common_fresh
#print axioms fresh_coordinate_fiber_plotkin_div
#print axioms family_card_le_direction_complement_mul_of_fiber_cap
#print axioms card_le_sixteen_of_direction_core_card_eq_fourteen
#print axioms card_le_three_of_direction_core_card_eq_fifteen
#print axioms card_eq_zero_of_direction_core_card_eq_sixteen
#print axioms card_le_sixteen_of_fourteen_le_direction_core
#print axioms card_le_sixteen_or_exceptional_direction_core_band
