/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorSecantLines

/-!
# P1 rate-quarter predecessor: spread structure of the forced core system

The forced-secant matching argument shows that an over-budget selected family
(`N < |G|` at `N = 2^30`, `K = 2^28`, `T = 592794966`) carries at least
`2^29 - 2` pairwise-disjoint scalar pairs, each riding a secant line whose
joint core has at least `K` coordinates.  This file pins the *spread* of that
core system — how the matched pairs distribute over distinct polynomial lines
— by two new unconditional rungs plus exact numeric anchors:

* **Near-saturated core cap (`no_six_nearSaturated_cores` /
  `nearSaturated_lines_card_le_five`).**  Six pairwise-distinct polynomial
  lines with components of degree `< K` cannot all have joint cores of size
  at least `T - 2 = 592794964`.  This is the *first Plotkin-active* bound on
  the core system: cores overlap pairwise in at most `K - 1` coordinates, and
  the constant-weight Plotkin denominator `w^2 - N*(K-1)` turns positive
  exactly at `w = 2K - 1 = 536870911 < T - 2`.  Six sets of weight `T - 2`
  would force `6 * ((T-2)^2 - N*(K-1)) = 379052965594748256`
  `<= N * (T-2-(K-1)) = 348278370825404416`, which is false.  Exact onset:
  six such cores are impossible iff their common weight is at least
  `587673607` (`six_core_plotkin_onset_holds` / `_fails`).  In particular at
  most `5` distinct lines can simultaneously have near-saturated
  (`>= T - 2`), and a fortiori saturation-violating (`>= T - 1`), cores.

* **Four-line collapse forces saturation
  (`saturated_secant_core_of_four_matched_lines`).**  If the canonical secant
  parameters of a forced matching of size `>= 2^29 - 2` take at most four
  distinct values, pigeonhole puts `>= 2^27` disjoint pairs on one line, so
  that line carries `>= 2^28` distinct selected scalars, and the per-line
  packing inequality `L * max 1 (T - z) + z <= N` forces its core to size
  `z >= T - 1`: with `z <= T - 2` one gets
  `2^28 * (T - z) + z >= 2^28 * 2 + (T - 2) = 1129665876 > N`.  Contrapositive
  (`five_matched_lines_or_saturated_core`): either some matched secant core is
  saturation-violating (`z + 2 > T`), or the matching spreads over at least
  five distinct pencils — strictly more than the four the residual extraction
  is allowed.

* **Averaging anchor (`triple_average_below_dimension`).**  The convexity
  floor on mean triple agreement overlap is `T^3 / N^2`, and
  `T^3 = 208311631775458904263020696 < K * N^2 = 309485009821345068724781056`
  (ratio `0.673`): third-moment averaging cannot force `K` commonly covered
  coordinates, so absorption-by-averaging is numerically dead.  (Probe:
  `scripts/probes/probe_fsmc_sunflower_forced_core_spread.py`; the same probe
  records that the matched-core mean pairwise overlap floor is `~K/4`, and
  that the count of weight-`K` cores with pairwise overlap `<= K - 1` is
  unbounded — the Plotkin denominator vanishes at `w = K` — so pure
  set-system statistics provably cannot finish the consolidation.)

The rigidity input `jointCore_inter_card_le_of_ne` is restated locally (same
proof as in `_P1RateQuarterForcedSecantMatching`, whose compiled interface is
not yet available) to keep this file's build footprint on already-built
substrate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.FSMCForcedCoreSpread

open ConstantWeightPlotkinBound
open HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLineCoreGeometry
open HalfPredecessorSecantLines

attribute [local instance] Classical.propDecidable

/-- Prize length. -/
abbrev N : Nat := 2 ^ 30

/-- Rate-quarter Reed--Solomon dimension. -/
abbrev K : Nat := 2 ^ 28

/-- Agreement threshold at the lattice predecessor of the saturated
common-factor endpoint. -/
abbrev T : Nat := 592794966

/-! ## Numeric anchors -/

/-- **Third-moment averaging is dead.**  The convexity floor on the mean
triple overlap of agreement sets of size `>= T` in `N` coordinates is
`T^3 / N^2 < K`: averaging over triples cannot force `K` commonly covered
coordinates, hence cannot trigger the pencil-absorption mechanism. -/
theorem triple_average_below_dimension : T ^ 3 < K * N ^ 2 := by
  norm_num [N, K, T]

/-- Exact onset of the six-core Plotkin impossibility: at common core weight
`587673607` the strict Plotkin violation holds. -/
theorem six_core_plotkin_onset_holds :
    N * (587673607 - (K - 1)) < 6 * (587673607 ^ 2 - N * (K - 1)) := by
  norm_num [N, K]

/-- One below the onset the six-core Plotkin count is still satisfiable:
`587673607` is exact. -/
theorem six_core_plotkin_onset_fails :
    ¬ N * (587673606 - (K - 1)) < 6 * (587673606 ^ 2 - N * (K - 1)) := by
  norm_num [N, K]

/-! ## Six near-saturated cores are impossible -/

/-- **Abstract six-core cap.**  Six subsets of the P1 coordinate set, each of
size at least `T - 2` and pairwise intersecting in at most `K - 1`
coordinates, cannot coexist: the constant-weight Plotkin bound is active
because `T - 2 > 2K - 1`. -/
theorem no_six_nearSaturated_cores
    (D : Fin 6 → Finset (Fin N))
    (hsize : ∀ i, T - 2 ≤ (D i).card)
    (hpair : ∀ i j, i ≠ j → (D i ∩ D j).card ≤ K - 1) : False := by
  classical
  choose D' hsub hcard using fun i => Finset.exists_subset_card_eq (hsize i)
  have hpair' : ∀ i j, i ≠ j → (D' i ∩ D' j).card ≤ K - 1 := by
    intro i j hij
    exact le_trans
      (Finset.card_le_card (Finset.inter_subset_inter (hsub i) (hsub j)))
      (hpair i j hij)
  have hplot := constantWeight_plotkin D' (T - 2) (K - 1) hcard hpair'
  simp only [Fintype.card_fin] at hplot
  norm_num [N, K, T] at hplot

/-! ## Distinct-line core rigidity (local restatement) -/

section Rigidity

variable {ι F : Type} [Fintype ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **Distinct-line core cap.**  Two polynomial lines that differ in intercept
or slope, with all components of degree `< k`, have joint cores meeting in at
most `k - 1` coordinates.  (Local restatement of the rigidity pin from the
forced-secant-matching development.) -/
theorem jointCore_inter_card_le_of_ne
    (dom : ι ↪ F) (u₀ u₁ : ι → F) {k : ℕ} (hk : 1 ≤ k)
    {a r a' r' : F[X]}
    (hadeg : a.natDegree < k) (hrdeg : r.natDegree < k)
    (hadeg' : a'.natDegree < k) (hrdeg' : r'.natDegree < k)
    (hne : a ≠ a' ∨ r ≠ r') :
    (jointCore dom u₀ u₁ a r ∩ jointCore dom u₀ u₁ a' r').card ≤ k - 1 := by
  rcases hne with hne | hne
  · have hp0 : a - a' ≠ 0 := sub_ne_zero.mpr hne
    have hpdeg : (a - a').natDegree < k :=
      lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hadeg hadeg')
    refine le_trans (Finset.card_le_card ?_)
      (domain_root_card_le_pred dom hk _ hp0 hpdeg)
    intro i hi
    simp only [Finset.mem_inter, jointCore, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_sub]
    rw [hi.1.1, hi.2.1, sub_self]
  · have hp0 : r - r' ≠ 0 := sub_ne_zero.mpr hne
    have hpdeg : (r - r').natDegree < k :=
      lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hrdeg hrdeg')
    refine le_trans (Finset.card_le_card ?_)
      (domain_root_card_le_pred dom hk _ hp0 hpdeg)
    intro i hi
    simp only [Finset.mem_inter, jointCore, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_sub]
    rw [hi.1.2, hi.2.2, sub_self]

end Rigidity

/-! ## At most five near-saturated lines -/

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Six-line impossibility.**  Six pairwise-distinct polynomial lines with
components of degree `< K` cannot all have joint cores of size `>= T - 2` on
the P1 coordinate set. -/
theorem no_six_nearSaturated_lines
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (lines : Fin 6 → F[X] × F[X])
    (hdeg : ∀ i, (lines i).1.natDegree < K ∧ (lines i).2.natDegree < K)
    (hinj : Function.Injective lines)
    (hcore : ∀ i,
      T - 2 ≤ (jointCore dom u₀ u₁ (lines i).1 (lines i).2).card) :
    False := by
  refine no_six_nearSaturated_cores
    (fun i => jointCore dom u₀ u₁ (lines i).1 (lines i).2) hcore ?_
  intro i j hij
  have hne : (lines i).1 ≠ (lines j).1 ∨ (lines i).2 ≠ (lines j).2 := by
    by_contra hboth
    push_neg at hboth
    exact hij (hinj (Prod.ext hboth.1 hboth.2))
  exact jointCore_inter_card_le_of_ne dom u₀ u₁
    (k := K) (by norm_num [K]) (hdeg i).1 (hdeg i).2 (hdeg j).1 (hdeg j).2 hne

/-- **Near-saturated line cap.**  Any finite set of polynomial lines with
components of degree `< K` and joint cores of size `>= T - 2` has at most
five members.  In particular at most five distinct pencils can carry
saturation-violating cores (`z + 2 > T`). -/
theorem nearSaturated_lines_card_le_five
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (S : Finset (F[X] × F[X]))
    (hdeg : ∀ l ∈ S, l.1.natDegree < K ∧ l.2.natDegree < K)
    (hcore : ∀ l ∈ S, T - 2 ≤ (jointCore dom u₀ u₁ l.1 l.2).card) :
    S.card ≤ 5 := by
  by_contra hgt
  have hsix : 6 ≤ S.card := by omega
  obtain ⟨S6, hS6sub, hS6card⟩ := Finset.exists_subset_card_eq hsix
  have he : S6 ≃ Fin 6 := by
    rw [← hS6card]
    exact S6.equivFin
  let lines : Fin 6 → F[X] × F[X] := fun i => (he.symm i : F[X] × F[X])
  have hinj : Function.Injective lines := by
    intro i j hij
    apply he.symm.injective
    exact Subtype.ext hij
  have hmem : ∀ i, lines i ∈ S := fun i => hS6sub (he.symm i).2
  exact no_six_nearSaturated_lines dom u₀ u₁ lines
    (fun i => hdeg _ (hmem i)) hinj (fun i => hcore _ (hmem i))

/-- Restriction to saturation-violating cores (`T - 1 <= z`, i.e.
`z + 2 > T`): still at most five lines. -/
theorem saturationViolating_lines_card_le_five
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (S : Finset (F[X] × F[X]))
    (hdeg : ∀ l ∈ S, l.1.natDegree < K ∧ l.2.natDegree < K)
    (hcore : ∀ l ∈ S, T - 1 ≤ (jointCore dom u₀ u₁ l.1 l.2).card) :
    S.card ≤ 5 :=
  nearSaturated_lines_card_le_five dom u₀ u₁ S hdeg
    (fun l hl => le_trans (by norm_num [T]) (hcore l hl))

/-! ## Four matched lines force a saturated core -/

/-- Shorthand for the joint core of the canonical secant through two selected
scalars.  (Local restatement.) -/
noncomputable def secantCore
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (gamma beta : F) : Finset (Fin N) :=
  jointCore dom (u 0) (u 1)
    (secantParameter family gamma beta).1
    (secantParameter family gamma beta).2

/-- A forced secant matching inside a scalar set `S`: pairwise-disjoint pairs
of distinct members of `S`, each with a `K`-core canonical secant.  (Local
restatement of the predicate from the forced-secant-matching development.) -/
def ForcedSecantMatching
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (S : Finset F) (M : Finset (F × F)) : Prop :=
  (∀ p ∈ M, p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2 ∧
    K ≤ (secantCore family p.1 p.2).card) ∧
  ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
    p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

/-- **Four-line collapse.**  If the canonical secants of a forced matching of
size `>= 2^29 - 2` take at most four distinct parameter values, then some
matched pair rides a *saturation-violating* pencil: its secant core has at
least `T - 1` coordinates, i.e. `z + 2 > T`.

Pigeonhole puts `2^27` disjoint pairs on one line; their `2^28` distinct
endpoints all lie on that line; the per-line packing inequality then forces
the core past `T - 2`. -/
theorem saturated_secant_core_of_four_matched_lines
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hthr : T ≤ ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {M : Finset (F × F)}
    (hM : ForcedSecantMatching family family.G M)
    (hMcard : 2 ^ 29 - 2 ≤ M.card)
    (himg : (M.image fun p => secantParameter family p.1 p.2).card ≤ 4) :
    ∃ gamma beta : F, (gamma, beta) ∈ M ∧
      T - 1 ≤ (secantCore family gamma beta).card := by
  classical
  have hMcard' : 536870910 ≤ M.card := by
    have h29 : (2 : ℕ) ^ 29 - 2 = 536870910 := by norm_num
    omega
  -- Pigeonhole: some secant-parameter fiber holds at least 2^27 pairs.
  have hfiber : ∃ l ∈ M.image fun p => secantParameter family p.1 p.2,
      134217728 ≤
        (M.filter fun p => secantParameter family p.1 p.2 = l).card := by
    by_contra hnot
    push_neg at hnot
    have hsum : M.card =
        ∑ l ∈ M.image fun p => secantParameter family p.1 p.2,
          (M.filter fun p => secantParameter family p.1 p.2 = l).card :=
      Finset.card_eq_sum_card_fiberwise
        (fun p hp => Finset.mem_image_of_mem _ hp)
    have hle : ∑ l ∈ M.image fun p => secantParameter family p.1 p.2,
        (M.filter fun p => secantParameter family p.1 p.2 = l).card ≤
          (M.image fun p => secantParameter family p.1 p.2).card *
            134217727 := by
      calc ∑ l ∈ M.image fun p => secantParameter family p.1 p.2,
            (M.filter fun p => secantParameter family p.1 p.2 = l).card
          ≤ ∑ _l ∈ M.image fun p => secantParameter family p.1 p.2,
              134217727 := by
            apply Finset.sum_le_sum
            intro l hl
            have := hnot l hl
            omega
        _ = (M.image fun p => secantParameter family p.1 p.2).card *
              134217727 := by
            simp [Finset.sum_const, smul_eq_mul]
    have hcap : (M.image fun p => secantParameter family p.1 p.2).card *
        134217727 ≤ 4 * 134217727 :=
      Nat.mul_le_mul_right _ himg
    omega
  obtain ⟨l, hlmem, hlbig⟩ := hfiber
  have hMlM : (M.filter fun p => secantParameter family p.1 p.2 = l) ⊆ M :=
    Finset.filter_subset _ _
  have hMlpos :
      (M.filter fun p => secantParameter family p.1 p.2 = l).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨p0, hp0⟩ := hMlpos
  have hp0M : p0 ∈ M := hMlM hp0
  have hp0f : secantParameter family p0.1 p0.2 = l :=
    (Finset.mem_filter.mp hp0).2
  obtain ⟨hp01G, hp02G, hp0ne, _⟩ := hM.1 p0 hp0M
  have hlLP : l ∈ lineParameters family := by
    rw [← hp0f]
    exact secantParameter_mem_lineParameters family hp01G hp02G hp0ne
  -- The 2 * 2^27 endpoints of the fiber are distinct points on the line.
  have hdisj : ∀ p ∈ (M.filter fun p => secantParameter family p.1 p.2 = l),
      ∀ q ∈ (M.filter fun p => secantParameter family p.1 p.2 = l), p ≠ q →
        Disjoint ({p.1, p.2} : Finset F) ({q.1, q.2} : Finset F) := by
    intro p hp q hq hpq
    obtain ⟨h11, h12, h21, h22⟩ := hM.2 p (hMlM hp) q (hMlM hq) hpq
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ha'
    rcases ha with rfl | rfl
    · rcases ha' with h | h
      · exact h11 h
      · exact h12 h
    · rcases ha' with h | h
      · exact h21 h
      · exact h22 h
  have hEcard :
      ((M.filter fun p => secantParameter family p.1 p.2 = l).biUnion
          fun p => ({p.1, p.2} : Finset F)).card =
        2 * (M.filter fun p => secantParameter family p.1 p.2 = l).card := by
    rw [Finset.card_biUnion hdisj]
    have hpair2 : ∀ p ∈ (M.filter fun p => secantParameter family p.1 p.2 = l),
        ({p.1, p.2} : Finset F).card = 2 := by
      intro p hp
      obtain ⟨_, _, hne, _⟩ := hM.1 p (hMlM hp)
      exact Finset.card_pair hne
    rw [Finset.sum_congr rfl hpair2]
    simp [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hEsub :
      ((M.filter fun p => secantParameter family p.1 p.2 = l).biUnion
          fun p => ({p.1, p.2} : Finset F)) ⊆ pointsOn family l := by
    refine Finset.biUnion_subset.mpr ?_
    intro p hp
    obtain ⟨h1G, h2G, hne, _⟩ := hM.1 p (hMlM hp)
    have hpf : secantParameter family p.1 p.2 = l :=
      (Finset.mem_filter.mp hp).2
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · rw [← hpf]
      exact first_point_mem_pointsOn_secant family (beta := p.2) h1G
    · rw [← hpf]
      exact second_point_mem_pointsOn_secant family (gamma := p.1) h2G hne
  have hL : 268435456 ≤ (pointsOn family l).card := by
    have hcardle := Finset.card_le_card hEsub
    omega
  -- Packing forces the core past T - 2.
  have hpack := pointsOn_card_mul_max_add_core_le family hlLP
  rw [Fintype.card_fin] at hpack hthr
  have hzbound : T - 1 ≤ (jointCore dom (u 0) (u 1) l.1 l.2).card := by
    by_contra hlt
    push_neg at hlt
    have hz2 : (jointCore dom (u 0) (u 1) l.1 l.2).card ≤ T - 2 := by
      have hT : T = 592794966 := by norm_num [T]
      omega
    have hmax : max 1 (⌈(1 - delta) * ((N : ℕ) : NNReal)⌉₊ -
        (jointCore dom (u 0) (u 1) l.1 l.2).card) =
          ⌈(1 - delta) * ((N : ℕ) : NNReal)⌉₊ -
            (jointCore dom (u 0) (u 1) l.1 l.2).card := by
      apply max_eq_right
      have hT : T = 592794966 := by norm_num [T]
      omega
    rw [hmax] at hpack
    have hmono : (pointsOn family l).card *
        (T - (jointCore dom (u 0) (u 1) l.1 l.2).card) ≤
          (pointsOn family l).card *
            (⌈(1 - delta) * ((N : ℕ) : NNReal)⌉₊ -
              (jointCore dom (u 0) (u 1) l.1 l.2).card) := by
      apply Nat.mul_le_mul_left
      omega
    have hLmono : 268435456 *
        (T - (jointCore dom (u 0) (u 1) l.1 l.2).card) ≤
          (pointsOn family l).card *
            (T - (jointCore dom (u 0) (u 1) l.1 l.2).card) :=
      Nat.mul_le_mul_right _ hL
    have hfin : 268435456 *
        (T - (jointCore dom (u 0) (u 1) l.1 l.2).card) +
          (jointCore dom (u 0) (u 1) l.1 l.2).card ≤ N :=
      le_trans (Nat.add_le_add_right (le_trans hLmono hmono) _) hpack
    have hT : T = 592794966 := by norm_num [T]
    have hN : N = 1073741824 := by norm_num [N]
    omega
  refine ⟨p0.1, p0.2, ?_, ?_⟩
  · rw [Prod.mk.eta]
    exact hp0M
  · show T - 1 ≤ (jointCore dom (u 0) (u 1)
      (secantParameter family p0.1 p0.2).1
      (secantParameter family p0.1 p0.2).2).card
    rw [hp0f]
    exact hzbound

/-- **Spread dichotomy.**  A forced matching of over-budget size either
spreads over at least five distinct pencils — one more than the four-pencil
extraction budget — or already exhibits a saturation-violating secant core
(`z + 2 > T`).  Together with `saturationViolating_lines_card_le_five`, the
open kernel of the residual is confined to exactly these two configuration
classes. -/
theorem five_matched_lines_or_saturated_core
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hthr : T ≤ ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {M : Finset (F × F)}
    (hM : ForcedSecantMatching family family.G M)
    (hMcard : 2 ^ 29 - 2 ≤ M.card) :
    5 ≤ (M.image fun p => secantParameter family p.1 p.2).card ∨
      ∃ gamma beta : F, (gamma, beta) ∈ M ∧
        T - 1 ≤ (secantCore family gamma beta).card := by
  by_cases himg : (M.image fun p => secantParameter family p.1 p.2).card ≤ 4
  · exact Or.inr
      (saturated_secant_core_of_four_matched_lines family hthr hM hMcard himg)
  · exact Or.inl (by omega)

end ArkLib.ProximityGap.Frontier.FSMCForcedCoreSpread

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.FSMCForcedCoreSpread.triple_average_below_dimension
#print axioms
  ArkLib.ProximityGap.Frontier.FSMCForcedCoreSpread.six_core_plotkin_onset_holds
#print axioms
  ArkLib.ProximityGap.Frontier.FSMCForcedCoreSpread.six_core_plotkin_onset_fails
#print axioms
  ArkLib.ProximityGap.Frontier.FSMCForcedCoreSpread.no_six_nearSaturated_cores
#print axioms
  ArkLib.ProximityGap.Frontier.FSMCForcedCoreSpread.jointCore_inter_card_le_of_ne
#print axioms
  ArkLib.ProximityGap.Frontier.FSMCForcedCoreSpread.no_six_nearSaturated_lines
#print axioms
  ArkLib.ProximityGap.Frontier.FSMCForcedCoreSpread.nearSaturated_lines_card_le_five
#print axioms
  ArkLib.ProximityGap.Frontier.FSMCForcedCoreSpread.saturationViolating_lines_card_le_five
#print axioms
  ArkLib.ProximityGap.Frontier.FSMCForcedCoreSpread.saturated_secant_core_of_four_matched_lines
#print axioms
  ArkLib.ProximityGap.Frontier.FSMCForcedCoreSpread.five_matched_lines_or_saturated_core
