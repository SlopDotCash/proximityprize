/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.RateHalfRichHeadCensus
import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-! # Saturated intersections in a large near-Johnson agreement list

At the first integer step below strict Johnson in production rate one eighth,
a list exceeding one block length forces four members with all pairwise
overlaps saturated. A list exceeding two block lengths forces six such members.
-/

namespace ProximityGap.SaturatedListCliques

open Finset SimpleGraph
open ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder (sum_inter_card_eq_sum_degree_sq)

variable {I : Type} [Fintype I] [DecidableEq I] {M : ℕ}

/-- Two distinct vertices are adjacent when their agreement sets attain the intersection cap. -/
def fullGraph (S : Fin M → Finset I) (d : ℕ) : SimpleGraph (Fin M) where
  Adj i j := i ≠ j ∧ d ≤ (S i ∩ S j).card
  symm := ⟨fun i j h => ⟨h.1.symm, by simpa only [inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem tangent (x a : ℕ) : (2*a+1)*x ≤ x^2+a*(a+1) := by
  rcases le_or_gt x a with h | h
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le h
    nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) r]
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le (show a+1 ≤ x by omega)
    nlinarith

/-- Integer tangent bound with the actual off-diagonal intersections. -/
theorem pair_incidence (S : Fin M → Finset I) {t : ℕ}
    (hsize : ∀ i, t ≤ (S i).card) (a : ℕ) :
    2*a*(M*t) ≤ (∑ i, ∑ j ∈ univ.erase i, (S i ∩ S j).card) + a*(a+1)*Fintype.card I := by
  classical
  have hS : M*t ≤ ∑ i, (S i).card := by
    simpa using Finset.sum_le_sum (s := (univ : Finset (Fin M))) (fun i _ => hsize i)
  have htan : (2*a+1)*(∑ i, (S i).card) ≤
      (∑ i, ∑ j, (S i ∩ S j).card) + a*(a+1)*Fintype.card I := by
    rw [ArkLib.Coverage.sum_card_eq_sum_degree, sum_inter_card_eq_sum_degree_sq, Finset.mul_sum]
    apply le_trans (Finset.sum_le_sum (fun x _ => tangent ((univ.filter (fun i => x ∈ S i)).card) a))
    simp only [Finset.sum_add_distrib, Finset.sum_const, card_univ, nsmul_eq_mul, Nat.mul_comm]
    exact le_rfl
  have row (i) : ∑ j, (S i ∩ S j).card =
      (S i).card + ∑ j ∈ univ.erase i, (S i ∩ S j).card := by
    rw [← add_sum_erase univ (fun j => (S i ∩ S j).card) (mem_univ i), inter_self]
  simp only [row, sum_add_distrib, Nat.add_mul, one_mul] at htan
  have hlo := Nat.mul_le_mul_left (2*a) hS
  omega

/-- The integer tangent to the pair moment bounds every family with uniform
pair-intersection cap, including punctured families on a complementary domain. -/
theorem uniform_pair_incidence (S : Fin M → Finset I) {t d : ℕ}
    (hsize : ∀ i, t ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ d) (a : ℕ) :
    2*a*(M*t) ≤ M*((M-1)*d) + a*(a+1)*Fintype.card I := by
  classical
  have h := pair_incidence S hsize a
  have row (i : Fin M) : (∑ j ∈ univ.erase i, (S i ∩ S j).card) ≤ (M-1)*d := by
    calc
      _ ≤ ∑ _j ∈ univ.erase i, d :=
        sum_le_sum fun j hj => hpair i j (mem_erase.mp hj).1.symm
      _ = _ := by simp
  exact h.trans (Nat.add_le_add_right (by simpa using sum_le_sum (s := univ) (fun i _ => row i)) _)

open Classical in
/-- Count pairs having more than the baseline number of common agreements. -/
theorem forced_edges_above (S : Fin M → Finset I) {t b c : ℕ}
    (hsize : ∀ i, t ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ b+c) (a : ℕ) :
    2*a*(M*t) ≤ M*((M-1)*b) + c*(2*(fullGraph S (b+1)).edgeFinset.card) +
      a*(a+1)*Fintype.card I := by
  classical
  let G := fullGraph S (b+1)
  have row (i) : ∑ j ∈ univ.erase i, (S i ∩ S j).card ≤ (M-1)*b + c*G.degree i := by
    have he : ((univ.erase i).filter (G.Adj i)) = G.neighborFinset i := by
      ext j
      simp only [mem_filter, mem_erase, mem_univ, and_true, mem_neighborFinset]
      exact ⟨And.right, fun h => ⟨h.ne.symm, h⟩⟩
    calc ∑ j ∈ univ.erase i, (S i ∩ S j).card
        ≤ ∑ j ∈ univ.erase i, (b + c*(if G.Adj i j then 1 else 0)) := by
          apply sum_le_sum
          intro j hj
          have hn := (mem_erase.mp hj).1.symm
          have hi := hpair i j hn
          by_cases h : G.Adj i j
          · rw [ite_eq_left h]; omega
          · have hl : ¬b+1 ≤ (S i ∩ S j).card := fun hb => h ⟨hn,hb⟩
            rw [ite_eq_right h]; omega
      _ = (M-1)*b + c*G.degree i := by
          rw [sum_add_distrib, ← Finset.mul_sum, ← card_filter, he, G.card_neighborFinset_eq_degree]
          simp [card_erase_of_mem]
  have hu := Finset.sum_le_sum (s := (univ : Finset (Fin M))) (fun i _ => row i)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, G.sum_degrees_eq_twice_card_edges, Nat.cast_id] at hu
  exact (pair_incidence S hsize a).trans (Nat.add_le_add_right hu _)

open Classical in
/-- Integer multiplicities force edges of the saturated-overlap graph. -/
theorem forced_edges (S : Fin M → Finset I) {t d : ℕ} (hd : 0 < d)
    (hsize : ∀ i, t ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ d) (a : ℕ) :
    2*a*(M*t) ≤ M*((M-1)*(d-1)) + 2*(fullGraph S d).edgeFinset.card +
      a*(a+1)*Fintype.card I := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  simpa only [Nat.succ_sub_one, one_mul] using forced_edges_above (b := b) (c := 1) S hsize hpair a

open Classical in
/-- A numerical certificate applying Turán to saturated intersections. -/
theorem forced_clique (S : Fin M → Finset I) {t d r : ℕ} (hd : 0 < d)
    (hsize : ∀ i, t ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ d) (a : ℕ)
    (hbound : M*((M-1)*(d-1)) + 2*SimpleGraph.turanNumber M r +
      a*(a+1)*Fintype.card I < 2*a*(M*t)) : ¬ (fullGraph S d).CliqueFree (r+1) := by
  classical
  intro h
  have hn : (fullGraph S d).edgeFinset.card ≤ SimpleGraph.turanNumber M r := by
    simpa only [Fintype.card_fin] using h.card_edgeFinset_le
  have hedges := forced_edges S hd hsize hpair a
  omega

/-- The two named-budget overflows at the first agreement count below Johnson. -/
theorem first_budget (S : Fin 1073741825 → Finset I)
    (hn : Fintype.card I = 1073741824) (ht : ∀ i, 379625061 ≤ (S i).card)
    (hp : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 134217727) :
    ¬ (fullGraph S 134217727).CliqueFree 4 := by
  apply forced_clique S (r := 3) (by decide) ht hp 379625061
  rw [hn, SimpleGraph.turanNumber_three]
  decide

theorem second_budget (S : Fin 2147483649 → Finset I)
    (hn : Fintype.card I = 1073741824) (ht : ∀ i, 379625061 ≤ (S i).card)
    (hp : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 134217727) :
    ¬ (fullGraph S 134217727).CliqueFree 6 := by
  apply forced_clique S (r := 5) (by decide) ht hp 759250122
  rw [hn, SimpleGraph.turanNumber_eq, Nat.choose_two_right]
  decide

open Code Polynomial

/-- A worst-center scalar list exceeding B produces actual distinct message
polynomials and exactly t selected agreements per word. Pairwise overlaps satisfy the degree bound. -/
theorem from_list_family {F : Type} [Field F] (D : I ↪ F) {k t B : ℕ} (hk : 0 < k)
    (htn : t ≤ Fintype.card I) (hn : 0 < Fintype.card I)
    (hlist : (B : ℕ∞) < Lambda (ReedSolomon.code D k : Set (I → F))
      (((Fintype.card I-t : ℕ) : ℝ)/Fintype.card I)) :
    ∃ (y : I → F) (P : Fin (B+1) → F[X]) (S : Fin (B+1) → Finset I),
      Function.Injective P ∧ (∀ i, (P i).natDegree < k) ∧ (∀ i, (S i).card=t) ∧
      (∀ i x, x ∈ S i → (P i).eval (D x) = y x) ∧
      (∀ i j, i ≠ j → (S i ∩ S j).card ≤ k-1) := by
  classical
  let _ : NeZero k := ⟨hk.ne'⟩
  let C := (ReedSolomon.code D k : Set (I → F))
  let δ := (((Fintype.card I-t : ℕ) : ℝ)/Fintype.card I)
  obtain ⟨y,W,hW,hlarge⟩ : ∃ (y : I → F) (W : Finset (I → F)),
      (∀ w ∈ W, w ∈ closeCodewordsRel C y δ) ∧ B < W.card := by
    by_contra! h
    exact (not_le_of_gt hlist) (Lambda_le_of_forall_finset_card_le fun y W hw => h y W hw)
  obtain ⟨V,hsub,hV⟩ := exists_subset_card_eq (show B+1 ≤ W.card by omega)
  let eqv := V.equivFin
  rw [hV] at eqv
  let w (i : Fin (B+1)) := (eqv.symm i).val
  have hin : Function.Injective w := fun _ _ h => eqv.symm.injective (Subtype.ext h)
  have hclose (i) := mem_closeCodewordsRel_iff.mp (hW (w i) (hsub (eqv.symm i).property))
  have hex (i) := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hclose i).1
  choose P hdeg heval using hex
  have hinP : Function.Injective P := by
    intro i j he
    apply hin
    exact funext fun x => ((heval i x).symm.trans (congrArg (eval (D x)) he)).trans (heval j x)
  have hδ : δ = 1-(t : ℝ)/Fintype.card I := by
    dsimp [δ]
    rw [Nat.cast_sub htn, sub_div, div_self (by exact_mod_cast hn.ne')]
  let A (i : Fin (B+1)) := univ.filter fun x => w i x = y x
  have hA (i) : t ≤ (A i).card := by
    have hd := (hclose i).2
    rw [hδ] at hd
    exact_mod_cast (relHammingDist_le_one_sub_div_iff hn).mp hd
  choose S hs hc using fun i => exists_subset_card_eq (hA i)
  refine ⟨y,P,S,hinP,hdeg,hc,?_,?_⟩
  · intro i x hx
    exact (heval i x).trans (mem_filter.mp (hs i hx)).2
  · intro i j hij
    have hfit : (S i ∩ S j).card ≤ agree (w i) (w j) := by
      apply card_le_card
      intro x hx
      obtain ⟨hi,hj⟩ := mem_inter.mp hx
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (hs i hi)).2.trans
        (mem_filter.mp (hs j hj)).2.symm⟩
    have hpair := ReedSolomon.agree_lt_of_mem_code (hclose i).1 (hclose j).1 (hin.ne hij)
    omega

/-- A worst-center scalar list exceeding B produces actual distinct message
polynomials and exactly t selected agreements per word. The pair overlaps still satisfy the degree bound when a looser clique threshold is used. -/
theorem from_list_at_overlap {F : Type} [Field F] (D : I ↪ F) {k t B r s : ℕ} (hk : 0 < k)
    (htn : t ≤ Fintype.card I) (hn : 0 < Fintype.card I)
    (hforce : ∀ S : Fin (B+1) → Finset I, (∀ i, (S i).card = t) →
      (∀ i j, i ≠ j → (S i ∩ S j).card ≤ k-1) → ¬(fullGraph S s).CliqueFree r)
    (hlist : (B : ℕ∞) < Lambda (ReedSolomon.code D k : Set (I → F))
      (((Fintype.card I-t : ℕ) : ℝ)/Fintype.card I)) :
    ∃ (y : I → F) (P : Fin (B+1) → F[X]) (S : Fin (B+1) → Finset I),
      Function.Injective P ∧ (∀ i, (P i).natDegree < k) ∧ (∀ i, (S i).card=t) ∧
      (∀ i x, x ∈ S i → (P i).eval (D x) = y x) ∧ ¬(fullGraph S s).CliqueFree r := by
  obtain ⟨y,P,S,hinP,hdeg,hc,he,hpair⟩ := from_list_family D hk htn hn hlist
  exact ⟨y,P,S,hinP,hdeg,hc,he,hforce S hc hpair⟩

/-- A worst-center scalar list exceeding B produces actual distinct message
polynomials and exactly t selected agreements per word. Any clique provided by
the set-family theorem consists of fully split polynomial differences. -/
theorem from_list {F : Type} [Field F] (D : I ↪ F) {k t B r : ℕ} (hk : 0 < k)
    (htn : t ≤ Fintype.card I) (hn : 0 < Fintype.card I)
    (hforce : ∀ S : Fin (B+1) → Finset I, (∀ i, (S i).card = t) →
      (∀ i j, i ≠ j → (S i ∩ S j).card ≤ k-1) → ¬(fullGraph S (k-1)).CliqueFree r)
    (hlist : (B : ℕ∞) < Lambda (ReedSolomon.code D k : Set (I → F))
      (((Fintype.card I-t : ℕ) : ℝ)/Fintype.card I)) :
    ∃ (y : I → F) (P : Fin (B+1) → F[X]) (S : Fin (B+1) → Finset I),
      Function.Injective P ∧ (∀ i, (P i).natDegree < k) ∧ (∀ i, (S i).card=t) ∧
      (∀ i x, x ∈ S i → (P i).eval (D x) = y x) ∧ ¬(fullGraph S (k-1)).CliqueFree r := by
  exact from_list_at_overlap D hk htn hn hforce hlist

#print axioms from_list

#print axioms forced_edges
#print axioms first_budget
#print axioms second_budget

end ProximityGap.SaturatedListCliques
