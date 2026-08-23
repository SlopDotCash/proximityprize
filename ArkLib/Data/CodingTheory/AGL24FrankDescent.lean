/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.AGL24FrankInterface
import ArkLib.Data.CodingTheory.AGL24Submodular

/-!
# [AGL24]/Frank: the descent assembly of the rooted out-cut theorem (issue #354)

This file assembles the in-tree reorientation bricks into Frank's rooted orientation
theorem (`FrankRootedOutCutTheorem`), the standard out-cut import boundary of
`symbolicFullRank_of_classical_imports`.

Strategy. Fix a root `r`. The total positive deficiency over all proper root-containing
cuts,
`totalRootDeficiency O r k := ∑_{T : r ∈ T, T ≠ univ} cutDeficiency O T k`,
is a `ℕ`-valued potential. A zero-potential orientation satisfies the rooted out-cut
condition (`rootedOutCut_of_totalRootDeficiency_zero`, via the complement bridge of
`AGL24FrankInterface`). A single Frank reorientation step that strictly decreases the
potential drives a well-founded (`Nat.strong_induction`) descent to a zero-potential
orientation (`exists_zero_totalRootDeficiency_of_uncrossingStep`), which is the desired
orientation. Threading these with a canonical starting orientation and root `0` yields
`frankRootedOutCutTheorem_of_uncrossingResidual` and, composed with the existing out-cut
glue, `frankOrientationResidual_of_uncrossingResidual`.

What is fully discharged here (axiom-clean): the out-cut bridge, the well-founded descent
and its base case, the wiring to `FrankRootedOutCutTheorem` / `FrankOrientationResidual`,
and the *sharpening* bricks that exhibit (when the potential is positive) an inclusion-
*maximal* deficient root cut together with a crossing edge whose head lies outside it
(`exists_maximal_deficientRootCut`, `exists_maximal_deficientRootCut_crossing_edge`) — the
exact inputs the uncrossing acts on.

The single remaining named residual is the *uncrossing decrease step*
`FrankUncrossingResidual`: from any positive-potential orientation of a fixed `k`-WPC
family, produce one of strictly smaller potential. This is the Lovász/Frank maximal-tight-
set uncrossing argument (true, hence non-vacuous: Frank's theorem guarantees the minimum
potential over the finite set of orientations is `0`, so any positive-potential orientation
admits a strictly smaller one). Its remaining mathematical content is the net-change
accounting of a single reorientation against the supermodular uncrossing corollary
`cutDeficiency_union_or_inter_pos` (`AGL24Submodular`) and the cut supply `wpc_border_ge`
(`AGL24CutSupply`); closing it in full requires the secondary lexicographic potential of
the classical proof (to control reorientations that retighten an exactly-tight non-maximal
cut), which is left as the precisely-localized open core.
-/

open Finset

namespace AGL24

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- The proper root-containing cuts: subsets containing `r` and not equal to the whole
vertex set. These are exactly the cuts the rooted out-cut condition constrains. -/
noncomputable def properRootCuts (r : V) : Finset (Finset V) := by
  classical
  exact (Finset.univ : Finset V).powerset.filter (fun T => r ∈ T ∧ T ≠ Finset.univ)

theorem mem_properRootCuts {r : V} {T : Finset V} :
    T ∈ properRootCuts r ↔ r ∈ T ∧ T ≠ Finset.univ := by
  classical
  simp [properRootCuts]

/-- The total positive deficiency over all proper root-containing cuts: the Frank descent
potential. -/
noncomputable def totalRootDeficiency {e : ι → Finset V} (O : HeadOrientation e)
    (r : V) (k : ℕ) : ℕ :=
  ∑ T ∈ properRootCuts r, cutDeficiency O T k

omit [DecidableEq ι] in
/-- The potential is zero exactly when every proper root cut is tight. -/
theorem totalRootDeficiency_eq_zero_iff {e : ι → Finset V} (O : HeadOrientation e)
    (r : V) (k : ℕ) :
    totalRootDeficiency O r k = 0 ↔
      ∀ T ∈ properRootCuts r, cutDeficiency O T k = 0 := by
  classical
  rw [totalRootDeficiency, Finset.sum_eq_zero_iff]

/-- Double complement of a vertex subset. -/
theorem univ_sdiff_univ_sdiff (S : Finset V) :
    Finset.univ \ (Finset.univ \ S) = S := by
  classical
  rw [← Finset.compl_eq_univ_sdiff, ← Finset.compl_eq_univ_sdiff, compl_compl]

omit [DecidableEq ι] in
/-- A zero-potential orientation satisfies the standard rooted out-cut condition: every
nonempty `r`-avoiding set has at least `k` outgoing edges. This is the bridge from the Frank
descent potential to the published out-cut form. -/
theorem rootedOutCut_of_totalRootDeficiency_zero {e : ι → Finset V}
    (O : HeadOrientation e) (r : V) (k : ℕ)
    (hzero : totalRootDeficiency O r k = 0) :
    RootedOutCutCondition O r k := by
  classical
  rw [totalRootDeficiency_eq_zero_iff] at hzero
  intro S hSne hrS
  -- Translate `S` to the complementary cut `T = univ \ S`.
  set T : Finset V := Finset.univ \ S with hT
  have hrT : r ∈ T := by
    rw [hT]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, hrS⟩
  have hTne : T ≠ Finset.univ := by
    rw [hT]; intro hcon
    obtain ⟨x, hx⟩ := hSne
    have hxmem : x ∈ Finset.univ \ S := by rw [hcon]; exact Finset.mem_univ x
    exact (Finset.mem_sdiff.mp hxmem).2 hx
  have hmem : T ∈ properRootCuts r := mem_properRootCuts.mpr ⟨hrT, hTne⟩
  have hdef : cutDeficiency O T k = 0 := hzero T hmem
  -- `cutDeficiency = 0` means `k ≤ headBorderEdges O T`.
  have hge : k ≤ (headBorderEdges O T).card := by
    rw [cutDeficiency, Nat.sub_eq_zero_iff_le] at hdef; exact hdef
  -- Rewrite back to `rootedOutEdges O S`.
  have hbridge := rootedOutEdges_univ_sdiff_eq_headBorderEdges O T
  rw [hT] at hbridge
  rw [univ_sdiff_univ_sdiff S] at hbridge
  rw [hbridge]; exact hge

/-! ## The descent: well-founded recursion on the potential

The single named residual is the *uncrossing decrease step*: from any orientation of a fixed
`k`-WPC family whose potential is positive, produce an orientation of strictly smaller
potential. (This is the Lovász/Frank maximal-tight-set uncrossing argument; its ingredients —
the WPC cut supply `wpc_border_ge`, the one-cut decrease
`exists_updateHead_decreases_positive_deficiency_cut`, and the union/intersection uncrossing
corollary `cutDeficiency_union_or_inter_pos` — are all proven in `AGL24CutSupply` /
`AGL24Submodular`.) Given it, the descent terminates by `Nat.strong_induction` on the
potential and outputs a zero-potential orientation. -/

/-- The Frank uncrossing decrease step for a fixed root `r` and `k`-WPC family `e`: any
positive-potential orientation admits one of strictly smaller total root deficiency. -/
def FrankUncrossingStep {e : ι → Finset V} (r : V) (k : ℕ) : Prop :=
  ∀ O : HeadOrientation e, 0 < totalRootDeficiency O r k →
    ∃ O' : HeadOrientation e, totalRootDeficiency O' r k < totalRootDeficiency O r k

omit [DecidableEq ι] in
/-- **The descent.** Given the uncrossing decrease step, from any starting orientation the
descent reaches an orientation of zero potential, i.e. one satisfying the rooted out-cut
condition. The well-founded recursion is `Nat.strong_induction` on the potential value. -/
theorem exists_zero_totalRootDeficiency_of_uncrossingStep {e : ι → Finset V}
    {r : V} {k : ℕ} (hstep : FrankUncrossingStep (e := e) r k)
    (O₀ : HeadOrientation e) :
    ∃ O : HeadOrientation e, totalRootDeficiency O r k = 0 := by
  classical
  -- Strong induction on the potential value `n`, where some orientation realizes `n`.
  suffices h : ∀ n : ℕ, ∀ O : HeadOrientation e, totalRootDeficiency O r k = n →
      ∃ O' : HeadOrientation e, totalRootDeficiency O' r k = 0 by
    exact h (totalRootDeficiency O₀ r k) O₀ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro O hO
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact ⟨O, by rw [hO, hn]⟩
    · -- Positive potential: apply the uncrossing step and recurse on the smaller value.
      have hpos : 0 < totalRootDeficiency O r k := by rw [hO]; exact hn
      obtain ⟨O', hlt⟩ := hstep O hpos
      exact ih (totalRootDeficiency O' r k) (by rw [← hO]; exact hlt) O' rfl

omit [DecidableEq ι] in
/-- **The rooted out-cut orientation, conditional on the uncrossing step.** For a fixed root
`r` and `k`-WPC family, the uncrossing decrease step yields an orientation satisfying the
standard rooted out-cut condition. -/
theorem exists_rootedOutCut_of_uncrossingStep {e : ι → Finset V}
    {r : V} {k : ℕ} (hstep : FrankUncrossingStep (e := e) r k)
    (O₀ : HeadOrientation e) :
    ∃ O : HeadOrientation e, RootedOutCutCondition O r k := by
  obtain ⟨O, hO⟩ := exists_zero_totalRootDeficiency_of_uncrossingStep hstep O₀
  exact ⟨O, rootedOutCut_of_totalRootDeficiency_zero O r k hO⟩

/-- A starting head orientation always exists for a family of nonempty edges (pick any vertex
of each edge as its head). -/
noncomputable def initOrientation {e : ι → Finset V} (hne : ∀ i, (e i).Nonempty) :
    HeadOrientation e where
  head := fun i => (hne i).choose
  head_mem := fun i _ => (hne i).choose_spec

/-! ## Sharpening the residual: the maximal deficient cut

The uncrossing argument acts on an inclusion-*maximal* deficient root cut. The following
bricks discharge the existence of such a cut (a pure finiteness fact) and of a crossing edge
into it whose head lies outside (the WPC cut supply `exists_border_head_outside_…`). This
narrows the irreducible residual to the single net-change inequality of the maximal-cut
uncrossing step. -/

/-- The deficient proper root cuts of an orientation. -/
noncomputable def deficientRootCuts {e : ι → Finset V} (O : HeadOrientation e)
    (r : V) (k : ℕ) : Finset (Finset V) := by
  classical
  exact (properRootCuts r).filter (fun T => 0 < cutDeficiency O T k)

omit [DecidableEq ι] in
theorem mem_deficientRootCuts {e : ι → Finset V} (O : HeadOrientation e)
    {r : V} {k : ℕ} {T : Finset V} :
    T ∈ deficientRootCuts O r k ↔
      (r ∈ T ∧ T ≠ Finset.univ) ∧ 0 < cutDeficiency O T k := by
  classical
  rw [deficientRootCuts, Finset.mem_filter, mem_properRootCuts]

omit [DecidableEq ι] in
/-- A positive potential exhibits at least one deficient proper root cut. -/
theorem deficientRootCuts_nonempty_of_pos {e : ι → Finset V} (O : HeadOrientation e)
    {r : V} {k : ℕ} (hpos : 0 < totalRootDeficiency O r k) :
    (deficientRootCuts O r k).Nonempty := by
  classical
  rw [totalRootDeficiency] at hpos
  -- A positive sum has a positive summand.
  have hexists : ∃ T ∈ properRootCuts r, 0 < cutDeficiency O T k := by
    by_contra hcon
    push Not at hcon
    have : ∑ T ∈ properRootCuts r, cutDeficiency O T k = 0 :=
      Finset.sum_eq_zero (fun T hT => Nat.le_zero.mp (hcon T hT))
    omega
  obtain ⟨T, hTmem, hTpos⟩ := hexists
  refine ⟨T, ?_⟩
  rw [mem_deficientRootCuts]
  exact ⟨mem_properRootCuts.mp hTmem, hTpos⟩

omit [DecidableEq ι] in
/-- **Existence of a maximal deficient root cut.** When the potential is positive there is a
deficient proper root cut `T*` such that no deficient proper root cut strictly contains it.
This is the inclusion-maximal set the Frank uncrossing argument acts on. -/
theorem exists_maximal_deficientRootCut {e : ι → Finset V} (O : HeadOrientation e)
    {r : V} {k : ℕ} (hpos : 0 < totalRootDeficiency O r k) :
    ∃ T ∈ deficientRootCuts O r k,
      ∀ T' ∈ deficientRootCuts O r k, T ⊆ T' → T' ⊆ T := by
  classical
  obtain ⟨T, hTmem, hTmax⟩ :=
    (deficientRootCuts O r k).exists_maximal (deficientRootCuts_nonempty_of_pos O hpos)
  exact ⟨T, hTmem, fun T' hT' hsub => hTmax hT' hsub⟩

omit [DecidableEq ι] in
/-- **A maximal deficient root cut has a crossing edge whose head lies outside it.** This is
the WPC cut supply (`exists_border_head_outside_of_positive_deficiency`) applied at the
maximal cut; the maximal cut together with this edge are exactly the inputs of the Frank
uncrossing step. -/
theorem exists_maximal_deficientRootCut_crossing_edge {e : ι → Finset V}
    (O : HeadOrientation e) {r : V} {k : ℕ}
    (hwpc : WeaklyPartitionConnected k (Finset.univ : Finset V) e)
    (hpos : 0 < totalRootDeficiency O r k) :
    ∃ T : Finset V, (r ∈ T ∧ T ≠ Finset.univ) ∧ 0 < cutDeficiency O T k ∧
      (∀ T' ∈ deficientRootCuts O r k, T ⊆ T' → T' ⊆ T) ∧
      ∃ i, (e i ∩ T).Nonempty ∧ ¬ e i ⊆ T ∧ O.head i ∉ T := by
  classical
  obtain ⟨T, hTmem, hTmax⟩ := exists_maximal_deficientRootCut O hpos
  rw [mem_deficientRootCuts] at hTmem
  obtain ⟨⟨hrT, hTne⟩, hTdef⟩ := hTmem
  have hTpos : T.Nonempty := ⟨r, hrT⟩
  obtain ⟨i, hi₁, hi₂, hi₃⟩ :=
    exists_border_head_outside_of_positive_deficiency O T hTpos hTne hwpc hTdef
  exact ⟨T, ⟨hrT, hTne⟩, hTdef, hTmax, i, hi₁, hi₂, hi₃⟩

end AGL24

namespace AGL24

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The family-uniform Frank uncrossing decrease step: for every `t ≥ 1`, every nonempty-edge
family on `Fin (t+1)` that is `k`-weakly-partition-connected, every root `r`, and every
positive-potential orientation, there is an orientation of strictly smaller total root
deficiency. This is the published Lovász/Frank maximal-tight-set uncrossing argument, stated
as a single named residual. Its ingredients (cut supply, one-cut decrease, union/intersection
uncrossing corollary) are proven in `AGL24CutSupply`/`AGL24Submodular`. -/
def FrankUncrossingResidual (k : ℕ) : Prop :=
  ∀ {t : ℕ}, 1 ≤ t → ∀ e : ι → Finset (Fin (t + 1)),
    (∀ i, (e i).Nonempty) →
    WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
    ∀ (r : Fin (t + 1)) (O : HeadOrientation e),
      0 < totalRootDeficiency O r k →
      ∃ O' : HeadOrientation e,
        totalRootDeficiency O' r k < totalRootDeficiency O r k

omit [DecidableEq ι] in
/-- **Frank's rooted out-cut theorem, reduced to the uncrossing decrease residual.** The
descent assembly (well-founded recursion on the potential + base case + the out-cut bridge),
together with the single named uncrossing step, proves `FrankRootedOutCutTheorem`. Every
other ingredient is a proven theorem of this campaign. -/
theorem frankRootedOutCutTheorem_of_uncrossingResidual {k : ℕ}
    (hres : FrankUncrossingResidual ι k) :
    FrankRootedOutCutTheorem (ι := ι) k := by
  classical
  intro t ht e hne hwpc
  -- The per-family uncrossing step from the family-uniform residual.
  have hstep : FrankUncrossingStep (e := e) (0 : Fin (t + 1)) k := by
    intro O hpos
    exact hres ht e hne hwpc (0 : Fin (t + 1)) O hpos
  -- Descend from the canonical initial orientation to a zero-potential one.
  obtain ⟨O, hO⟩ :=
    exists_zero_totalRootDeficiency_of_uncrossingStep hstep (initOrientation hne)
  exact ⟨O, (0 : Fin (t + 1)), rootedOutCut_of_totalRootDeficiency_zero O (0 : Fin (t + 1)) k hO⟩

omit [DecidableEq ι] in
/-- **End-to-end: the uncrossing decrease residual discharges Frank's orientation interface.**
Composing the descent (`frankRootedOutCutTheorem_of_uncrossingResidual`) with the in-tree
out-cut glue (`frankOrientationResidual_of_rootedOutCutTheorem`) shows the single named
`FrankUncrossingResidual` is sufficient for the `FrankOrientationResidual` import consumed by
`symbolicFullRank_of_classical_imports`. -/
theorem frankOrientationResidual_of_uncrossingResidual {k : ℕ}
    (hres : FrankUncrossingResidual ι k) :
    FrankOrientationResidual ι k :=
  frankOrientationResidual_of_rootedOutCutTheorem
    (frankRootedOutCutTheorem_of_uncrossingResidual ι hres)

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.rootedOutCut_of_totalRootDeficiency_zero
#print axioms AGL24.exists_zero_totalRootDeficiency_of_uncrossingStep
#print axioms AGL24.exists_maximal_deficientRootCut
#print axioms AGL24.exists_maximal_deficientRootCut_crossing_edge
#print axioms AGL24.frankRootedOutCutTheorem_of_uncrossingResidual
#print axioms AGL24.frankOrientationResidual_of_uncrossingResidual
