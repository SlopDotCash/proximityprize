/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorSecantLines

/-!
# Core absorption and the integral five-core cap at the P1 predecessor

Two new bricks for the P1 rate-quarter predecessor pin
(`N = 2^30`, `K = 2^28`, `T = 592794966`).

## 1. Core absorption

If a selected polynomial point agrees with the received stack on at least `k`
coordinates of a polynomial line's joint core, the point *is* on that line:
`q = a + C gamma * r` identically.  This is the contrapositive of the off-line
core cap `fullAgreement_inter_jointCore_card_le`, packaged in the forms the
consolidation argument needs (raw, subset-witness, secant-pair, and
`pointsOn`-membership for a `BadScalarRichPointFamily`).  It upgrades the
forced-matching rigidity from *pairs* to *arbitrary scalars*: any scalar whose
agreement set captures `K` core coordinates of a pencil is absorbed into it.

## 2. Integral (Jensen) five-core cap

Core-core rigidity: two *distinct* degree-`<k` lines have joint cores meeting
in at most `k-1` coordinates (a nonzero degree-`<k` difference polynomial
vanishes on the intersection).

The new counting input is the exact multiplicity identity
`sum_i sum_j |Z_i inter Z_j| = sum_x deg(x)^2` together with the integer
convex minorant `5*m <= m^2 + 6` (tight at `m = 2, 3`; equivalent to
`(m-2)*(m-3) >= 0`).  For five sets this gives

`4 * (sum_j |Z_j|) <= 6*N + (ordered off-diagonal overlap mass)`,

which at the P1 numbers **beats the fractional Johnson bound**: five cores of
weight `>= 590558003` with pairwise intersections `<= K - 1 = 268435455` are
impossible in `N = 2^30` coordinates (margin `16` in the ordered count), even
though `constantWeight_johnson` alone admits five cores of weight `T`.
Since a saturated pencil core has `z >= T - 2 = 592794964 >= 590558003`
(headroom `2236962`), **at most four distinct saturated pencils can coexist**
— the census number matches the four-pencil extraction target exactly.

Numerics cross-checked by `scripts/probes/probe_fsmb_absorption_ladder.py`:
* `5*590558003 = 2952790015`; `4*S - 6*N = 5368709116 > 20*(K-1) = 5368709100`;
* four cores of weight `T` remain feasible (Jensen threshold `603979775 > T`),
  so the five-to-four gap is the exact residual left for geometry.

Everything below is axiom-clean (no `sorry`, no new axioms).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open _root_.ProximityGap Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines

namespace ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder

variable {ι F : Type} [Fintype ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. Core absorption -/

/-- **Core absorption.**  A degree-`<k` point whose agreement set meets a
degree-`<k` line's joint core in at least `k` coordinates lies on that line
identically.  Contrapositive of the off-line core cap. -/
theorem absorbed_of_core_overlap
    (dom : ι ↪ F) (u₀ u₁ : ι → F) {k : ℕ} (hk : 1 ≤ k)
    {gamma : F} {q a r : F[X]}
    (hqdeg : q.natDegree < k) (hadeg : a.natDegree < k) (hrdeg : r.natDegree < k)
    (hcard : k ≤
      (fullAgreement dom u₀ u₁ gamma q ∩ jointCore dom u₀ u₁ a r).card) :
    q = a + C gamma * r := by
  by_contra hoff
  have hcap :=
    fullAgreement_inter_jointCore_card_le dom u₀ u₁ hk hqdeg hadeg hrdeg hoff
  omega

/-- Subset-witness form: any `k` coordinates lying simultaneously in the
agreement set and in the joint core force absorption. -/
theorem absorbed_of_subset_core
    (dom : ι ↪ F) (u₀ u₁ : ι → F) {k : ℕ} (hk : 1 ≤ k)
    {gamma : F} {q a r : F[X]} {S : Finset ι}
    (hqdeg : q.natDegree < k) (hadeg : a.natDegree < k) (hrdeg : r.natDegree < k)
    (hS₁ : S ⊆ fullAgreement dom u₀ u₁ gamma q)
    (hS₂ : S ⊆ jointCore dom u₀ u₁ a r)
    (hcard : k ≤ S.card) :
    q = a + C gamma * r :=
  absorbed_of_core_overlap dom u₀ u₁ hk hqdeg hadeg hrdeg
    (le_trans hcard (Finset.card_le_card (Finset.subset_inter hS₁ hS₂)))

/-- **Secant-pair absorption.**  A third scalar whose agreement set meets the
*common agreement* of two distinct on-line points in at least `k` coordinates
is itself on the line.  (The pair intersection is exactly the joint core by
`fullAgreement_inter_eq_jointCore`.) -/
theorem absorbed_of_secant_pair_overlap
    (dom : ι ↪ F) (u₀ u₁ : ι → F) {k : ℕ} (hk : 1 ≤ k)
    {gamma beta theta : F} (hne : gamma ≠ beta)
    {q a r : F[X]}
    (hqdeg : q.natDegree < k) (hadeg : a.natDegree < k) (hrdeg : r.natDegree < k)
    (hcard : k ≤ (fullAgreement dom u₀ u₁ theta q ∩
      (fullAgreement dom u₀ u₁ gamma (a + C gamma * r) ∩
        fullAgreement dom u₀ u₁ beta (a + C beta * r))).card) :
    q = a + C theta * r := by
  rw [fullAgreement_inter_eq_jointCore dom u₀ u₁ a r hne] at hcard
  exact absorbed_of_core_overlap dom u₀ u₁ hk hqdeg hadeg hrdeg hcard

/-- Family form: a bad scalar whose agreement set captures `k` core
coordinates of a relevant secant line is a member of that pencil. -/
theorem mem_pointsOn_of_core_overlap [Nonempty ι]
    {dom : ι ↪ F} {k : ℕ} {delta : NNReal} {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) (hk : 1 ≤ k)
    {gamma : F} (hgamma : gamma ∈ family.G)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcard : k ≤ ((fullAgreement dom (u 0) (u 1) gamma (family.q gamma)) ∩
      jointCore dom (u 0) (u 1) line.1 line.2).card) :
    gamma ∈ pointsOn family line := by
  have hdeg := lineParameter_degree_lt family hline
  rw [mem_pointsOn_iff]
  exact ⟨hgamma, absorbed_of_core_overlap dom (u 0) (u 1) hk
    (family.degree_lt gamma hgamma) hdeg.1 hdeg.2 hcard⟩

/-! ## 2. Core-core rigidity -/

/-- **Core-core rigidity.**  The joint cores of two lines that differ in the
intercept or in the slope meet in at most `k-1` coordinates. -/
theorem jointCore_inter_jointCore_card_le
    (dom : ι ↪ F) (u₀ u₁ : ι → F) {k : ℕ} (hk : 1 ≤ k)
    {a₁ r₁ a₂ r₂ : F[X]}
    (ha₁ : a₁.natDegree < k) (hr₁ : r₁.natDegree < k)
    (ha₂ : a₂.natDegree < k) (hr₂ : r₂.natDegree < k)
    (hne : a₁ ≠ a₂ ∨ r₁ ≠ r₂) :
    (jointCore dom u₀ u₁ a₁ r₁ ∩ jointCore dom u₀ u₁ a₂ r₂).card ≤ k - 1 := by
  classical
  rcases hne with h | h
  · have hp0 : a₁ - a₂ ≠ 0 := sub_ne_zero.mpr h
    have hpdeg : (a₁ - a₂).natDegree < k :=
      lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ha₁ ha₂)
    refine le_trans (Finset.card_le_card ?_)
      (domain_root_card_le_pred dom hk _ hp0 hpdeg)
    intro i hi
    simp only [Finset.mem_inter, jointCore, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_sub]
    rw [hi.1.1, hi.2.1, sub_self]
  · have hp0 : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr h
    have hpdeg : (r₁ - r₂).natDegree < k :=
      lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hr₁ hr₂)
    refine le_trans (Finset.card_le_card ?_)
      (domain_root_card_le_pred dom hk _ hp0 hpdeg)
    intro i hi
    simp only [Finset.mem_inter, jointCore, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_sub]
    rw [hi.1.2, hi.2.2, sub_self]

/-! ## 3. The integral multiplicity bound -/

/-- Integer convex minorant of the square, tight at `m = 2, 3`:
`(m-2)*(m-3) >= 0` for every natural `m`. -/
theorem five_mul_le_sq_add_six (m : ℕ) : 5 * m ≤ m ^ 2 + 6 := by
  by_cases h : m ≤ 4
  · interval_cases m <;> norm_num
  · have hmul : 5 * m ≤ m * m := Nat.mul_le_mul (by omega) (le_refl m)
    rw [pow_two]
    omega

/-- **Exact multiplicity identity.**  The ordered total intersection mass of a
finite family equals the second moment of the coordinate degree function. -/
theorem sum_inter_card_eq_sum_degree_sq
    {κ : Type} [Fintype κ] (Z : κ → Finset ι) :
    (∑ i, ∑ j, (Z i ∩ Z j).card) =
      ∑ x : ι, ((Finset.univ.filter fun i => x ∈ Z i).card) ^ 2 := by
  classical
  set deg : ι → ℕ := fun x => (Finset.univ.filter (fun i => x ∈ Z i)).card
    with hdeg
  have hf : ∀ x : ι, deg x = ∑ i, (if x ∈ Z i then (1 : ℕ) else 0) := by
    intro x
    change (Finset.univ.filter (fun i => x ∈ Z i)).card = _
    rw [Finset.card_filter]
  have hinter : ∀ i j : κ, (Z i ∩ Z j).card
      = ∑ x : ι, (if x ∈ Z i then (1 : ℕ) else 0) *
          (if x ∈ Z j then 1 else 0) := by
    intro i j
    calc
      (Z i ∩ Z j).card
          = (Finset.univ.filter (fun x : ι => x ∈ Z i ∩ Z j)).card := by
              congr 1
              ext x
              simp
      _ = ∑ x : ι, (if x ∈ Z i ∩ Z j then (1 : ℕ) else 0) := by
              rw [Finset.card_filter]
      _ = ∑ x : ι, (if x ∈ Z i then (1 : ℕ) else 0) *
            (if x ∈ Z j then 1 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              by_cases hi : x ∈ Z i <;> by_cases hj : x ∈ Z j <;>
                simp [hi, hj, Finset.mem_inter]
  have step1 : (∑ i, ∑ j, ∑ x : ι, (if x ∈ Z i then (1 : ℕ) else 0) *
        (if x ∈ Z j then 1 else 0))
      = ∑ i, ∑ x : ι, ∑ j, (if x ∈ Z i then (1 : ℕ) else 0) *
        (if x ∈ Z j then 1 else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  have step2 : (∑ i, ∑ x : ι, ∑ j, (if x ∈ Z i then (1 : ℕ) else 0) *
        (if x ∈ Z j then 1 else 0))
      = ∑ x : ι, ∑ i, ∑ j, (if x ∈ Z i then (1 : ℕ) else 0) *
        (if x ∈ Z j then 1 else 0) := by
    exact Finset.sum_comm
  simp_rw [hinter]
  rw [step1, step2]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul_sum]
  simp only [← hf x]
  rw [sq]

/-- **Integral Jensen inequality for coverage.**  For any finite family,
`5 * total weight <= second intersection moment + 6 * (number of coordinates)`.
This is the summed form of `5*m <= m^2 + 6` and is strictly stronger than the
Cauchy-Schwarz (Johnson) bound in the P1 regime. -/
theorem five_mul_sum_card_le_sum_inter_add
    {κ : Type} [Fintype κ] (Z : κ → Finset ι) :
    5 * (∑ i, (Z i).card) ≤
      (∑ i, ∑ j, (Z i ∩ Z j).card) + 6 * Fintype.card ι := by
  classical
  rw [ArkLib.Coverage.sum_card_eq_sum_degree, sum_inter_card_eq_sum_degree_sq]
  calc 5 * ∑ x : ι, (Finset.univ.filter fun i => x ∈ Z i).card
      = ∑ x : ι, 5 * (Finset.univ.filter fun i => x ∈ Z i).card := by
        rw [Finset.mul_sum]
    _ ≤ ∑ x : ι, (((Finset.univ.filter fun i => x ∈ Z i).card) ^ 2 + 6) :=
        Finset.sum_le_sum fun x _ => five_mul_le_sq_add_six _
    _ = (∑ x : ι, ((Finset.univ.filter fun i => x ∈ Z i).card) ^ 2) +
          6 * Fintype.card ι := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          smul_eq_mul, mul_comm]

/-- **Integral five-core cap (abstract P1 numerics).**  In `N = 2^30`
coordinates, five subsets of size at least `590558003` with pairwise
intersections at most `K - 1 = 268435455` cannot coexist.
`constantWeight_johnson` alone cannot see this (it admits five sets of size
`T = 592794966`); the integer minorant closes it with margin `16`. -/
theorem no_five_saturated_cores
    (hN : Fintype.card ι = 1073741824)
    (Z : Fin 5 → Finset ι)
    (hbig : ∀ j, 590558003 ≤ (Z j).card)
    (hpair : ∀ i j, i ≠ j → (Z i ∩ Z j).card ≤ 268435455) :
    False := by
  classical
  have hS : 5 * 590558003 ≤ ∑ j, (Z j).card := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5)))
      fun j _ => hbig j
    simpa using h
  have hinner : ∀ i : Fin 5,
      (∑ j, (Z i ∩ Z j).card) ≤ (Z i).card + 4 * 268435455 := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ (fun j => (Z i ∩ Z j).card)
      (Finset.mem_univ i)]
    apply Nat.add_le_add
    · simp
    · calc ∑ j ∈ Finset.univ.erase i, (Z i ∩ Z j).card
          ≤ ∑ _j ∈ Finset.univ.erase i, 268435455 :=
            Finset.sum_le_sum fun j hj =>
              hpair i j (Finset.mem_erase.mp hj).1.symm
        _ = 4 * 268435455 := by
            simp [Finset.card_erase_of_mem]
  have hupper : (∑ i, ∑ j, (Z i ∩ Z j).card) ≤
      (∑ i, (Z i).card) + 20 * 268435455 := by
    calc (∑ i, ∑ j, (Z i ∩ Z j).card)
        ≤ ∑ i, ((Z i).card + 4 * 268435455) :=
          Finset.sum_le_sum fun i _ => hinner i
      _ = (∑ i, (Z i).card) + 20 * 268435455 := by
          rw [Finset.sum_add_distrib]
          simp
  have hJ := five_mul_sum_card_le_sum_inter_add Z
  rw [hN] at hJ
  omega

/-! ## 4. The P1 saturated-pencil census -/

/-- **No five distinct near-saturated pencils at P1.**  Five degree-`<K`
lines that pairwise differ, each with joint core of size at least
`590558003`, are impossible in `N = 2^30` coordinates.  Rigidity supplies
the pairwise `<= K - 1` cap; the integral five-core bound finishes. -/
theorem no_five_distinct_saturated_pencils
    (dom : ι ↪ F) (u₀ u₁ : ι → F)
    (hN : Fintype.card ι = 1073741824)
    (line : Fin 5 → F[X] × F[X])
    (hdeg : ∀ j, (line j).1.natDegree < 268435456 ∧
      (line j).2.natDegree < 268435456)
    (hinj : Function.Injective line)
    (hcore : ∀ j, 590558003 ≤
      (jointCore dom u₀ u₁ (line j).1 (line j).2).card) :
    False := by
  refine no_five_saturated_cores hN
    (fun j => jointCore dom u₀ u₁ (line j).1 (line j).2) hcore ?_
  intro i j hij
  have hne : (line i).1 ≠ (line j).1 ∨ (line i).2 ≠ (line j).2 := by
    by_contra hcon
    push_neg at hcon
    exact hij (hinj (Prod.ext hcon.1 hcon.2))
  have hcap := jointCore_inter_jointCore_card_le dom u₀ u₁
    (k := 268435456) (by norm_num) (hdeg i).1 (hdeg i).2
    (hdeg j).1 (hdeg j).2 hne
  omega

/-- **Saturated-pencil census `<= 4`.**  Any finite set of distinct
degree-`<K` lines whose joint cores all have size at least `590558003`
(in particular all *saturated* cores `z >= T - 2 = 592794964`) has at most
four members.  This is exactly the pencil count targeted by the four-pencil
extraction residual. -/
theorem saturated_pencil_census_le_four
    (dom : ι ↪ F) (u₀ u₁ : ι → F)
    (hN : Fintype.card ι = 1073741824)
    (lines : Finset (F[X] × F[X]))
    (hdeg : ∀ l ∈ lines, l.1.natDegree < 268435456 ∧
      l.2.natDegree < 268435456)
    (hcore : ∀ l ∈ lines,
      590558003 ≤ (jointCore dom u₀ u₁ l.1 l.2).card) :
    lines.card ≤ 4 := by
  classical
  by_contra hfive
  obtain ⟨s, hs_sub, hs_card⟩ :=
    Finset.exists_subset_card_eq (show 5 ≤ lines.card by omega)
  have e0 := s.equivFin
  rw [hs_card] at e0
  refine no_five_distinct_saturated_pencils dom u₀ u₁ hN
    (fun j => ((e0.symm j : s) : F[X] × F[X])) ?_ ?_ ?_
  · intro j
    exact hdeg _ (hs_sub (e0.symm j).2)
  · intro i j hij
    exact e0.symm.injective (Subtype.coe_injective hij)
  · intro j
    exact hcore _ (hs_sub (e0.symm j).2)

/-- Saturated form at the exact predecessor saturation level `z >= T - 2`. -/
theorem saturated_pencil_census_le_four_at_T_sub_two
    (dom : ι ↪ F) (u₀ u₁ : ι → F)
    (hN : Fintype.card ι = 1073741824)
    (lines : Finset (F[X] × F[X]))
    (hdeg : ∀ l ∈ lines, l.1.natDegree < 268435456 ∧
      l.2.natDegree < 268435456)
    (hcore : ∀ l ∈ lines,
      592794964 ≤ (jointCore dom u₀ u₁ l.1 l.2).card) :
    lines.card ≤ 4 :=
  saturated_pencil_census_le_four dom u₀ u₁ hN lines hdeg
    fun l hl => le_trans (by norm_num) (hcore l hl)

/-- Family consumer: in a P1 bad-scalar family (`k = K = 2^28`), at most four
relevant secant lines carry a near-saturated joint core. -/
theorem family_saturatedLines_card_le_four [Nonempty ι]
    {dom : ι ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom 268435456 delta u)
    (hN : Fintype.card ι = 1073741824) :
    ((lineParameters family).filter fun line =>
      590558003 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card).card ≤ 4 := by
  classical
  apply saturated_pencil_census_le_four dom (u 0) (u 1) hN
  · intro l hl
    exact lineParameter_degree_lt family (Finset.mem_filter.mp hl).1
  · intro l hl
    exact (Finset.mem_filter.mp hl).2

end ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder

#print axioms
  ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.absorbed_of_core_overlap
#print axioms
  ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.absorbed_of_subset_core
#print axioms
  ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.absorbed_of_secant_pair_overlap
#print axioms
  ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.mem_pointsOn_of_core_overlap
#print axioms
  ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.jointCore_inter_jointCore_card_le
#print axioms
  ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.five_mul_le_sq_add_six
#print axioms
  ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.sum_inter_card_eq_sum_degree_sq
#print axioms
  ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.five_mul_sum_card_le_sum_inter_add
#print axioms
  ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.no_five_saturated_cores
#print axioms
  ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.no_five_distinct_saturated_pencils
#print axioms
  ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.saturated_pencil_census_le_four
#print axioms
  ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.saturated_pencil_census_le_four_at_T_sub_two
#print axioms
  ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.family_saturatedLines_card_le_four
