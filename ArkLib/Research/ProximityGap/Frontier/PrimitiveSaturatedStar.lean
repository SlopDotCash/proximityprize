/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SaturatedSplitTriangle
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection
import ArkLib.Research.ProximityGap.Frontier.SharedSiteListBound
import Mathlib.Algebra.Polynomial.Splits

/-! # A primitive saturated star at the first eighth-rate list frontier

At length 2^30, an overflowing scalar list at 694,116,763 errors contains one
head with 765,474,164 fully saturated neighbors. Every sufficiently large
subset of these neighbors has polynomial differences with unit common gcd.
-/

set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
namespace ProximityGap.PrimitiveSaturatedStar

variable {I F : Type} [Fintype I] [DecidableEq I] [Field F]

/-- The integer pair moment forces this many neighbors at one vertex. -/
theorem star (S : Fin 1073741825 → Finset I)
    (hn : Fintype.card I = 1073741824) (hs : ∀ i, (S i).card = 379625061)
    (hp : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 134217727) :
    ∃ (h : Fin 1073741825) (N : Finset (Fin 1073741825)), N.card = 765474164 ∧
      ∀ i ∈ N, h ≠ i ∧ (S h ∩ S i).card = 134217727 := by
  classical
  let G := SaturatedListCliques.fullGraph S 134217727
  have lower := SaturatedListCliques.forced_edges S (by decide : 0 < 134217727)
    (fun i => (hs i).ge) hp 379625061
  rw [hn] at lower
  have edges : 821921624952514482 ≤ 2*G.edgeFinset.card := by dsimp [G]; omega
  rw [← G.sum_degrees_eq_twice_card_edges] at edges
  have rich : ∃ h, 765474164 ≤ G.degree h := by
    by_contra! small
    have bound : (∑ h, G.degree h) ≤ ∑ _h : Fin 1073741825, 765474163 :=
      sum_le_sum fun i _ => by have := small i; omega
    simp at bound
    omega
  obtain ⟨h, hh⟩ := rich
  obtain ⟨N, sub, card⟩ := exists_subset_card_eq
    ((G.card_neighborFinset_eq_degree h).symm ▸ hh)
  refine ⟨h, N, card, ?_⟩
  intro i hi
  have e : h ≠ i ∧ 134217727 ≤ (S h ∩ S i).card := (G.mem_neighborFinset h i).mp (sub hi)
  exact ⟨e.1, le_antisymm (hp h i e.1) e.2⟩

/-- The punctured second moment bounds the number of supports through any one site. -/
theorem site_capacity {J : Type} (S : J → Finset I) (T : Finset J) (x : I)
    (hn : Fintype.card I = 1073741824) (hs : ∀ i ∈ T, (S i).card = 379625061)
    (hp : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → (S i ∩ S j).card ≤ 134217727)
    (hx : ∀ i ∈ T, x ∈ S i) : T.card ≤ 682920127 := by
  classical
  by_contra! large
  obtain ⟨U, sub, card⟩ := exists_subset_card_eq (show 682920128 ≤ T.card by omega)
  let fixed : Finset I := {x}
  let R (i : J) := (S i).subtype fun u => u ∈ fixedᶜ
  have size (i) (hi : i ∈ U) : (R i).card = 379625060 := by
    have incl : fixed ⊆ S i := by simpa [fixed] using hx i (sub hi)
    change ((S i).subtype _).card = _
    rw [SharedSiteListBound.card_on_complement, card_sdiff_of_subset incl, hs i (sub hi)]
    simp [fixed]
  have pair (i) (hi : i ∈ U) (j) (hj : j ∈ U) (ne : i ≠ j) :
      (R i ∩ R j).card ≤ 134217726 := by
    have eq : R i ∩ R j = (S i ∩ S j).subtype (fun u => u ∈ fixedᶜ) := by ext; simp [R]
    have incl : fixed ⊆ S i ∩ S j := by
      simpa [fixed] using And.intro (hx i (sub hi)) (hx j (sub hj))
    rw [eq, SharedSiteListBound.card_on_complement, card_sdiff_of_subset incl]
    have bound := hp i (sub hi) j (sub hj) ne
    have one : fixed.card = 1 := by simp [fixed]
    omega
  let e := U.equivFin
  rw [card] at e
  let W (i : Fin 682920128) := R (e.symm i).val
  have estimate := SaturatedListCliques.uniform_pair_incidence W
    (fun i => (size (e.symm i).val (e.symm i).property).ge)
    (fun i j ne => pair _ (e.symm i).property _ (e.symm j).property
      (fun eq => ne (e.symm.injective (Subtype.ext eq)))) 241448725
  rw [Fintype.card_coe, card_compl, hn, show fixed.card = 1 from by simp [fixed]] at estimate
  exact (by decide : ¬ (2*241448725*(682920128*379625060) ≤ 682920128*((682920128-1)*134217726) +
    241448725*(241448725+1)*(1073741824-1))) estimate

/-- Every eligible subfamily of this star has only constant common divisors.
The factorization specifies the entire root set of each difference. -/
def ContainsStar (D : I ↪ F) : Prop :=
    ∃ (y : I → F) (P : Fin 1073741825 → F[X]) (S : Fin 1073741825 → Finset I)
      (h : Fin 1073741825) (N : Finset (Fin 1073741825)),
      Function.Injective P ∧ (∀ i, (P i).natDegree < 134217728) ∧
      (∀ i, (S i).card = 379625061) ∧ (∀ i x, x ∈ S i → (P i).eval (D x) = y x) ∧
      N.card = 765474164 ∧ (∀ i ∈ N, (S h ∩ S i).card = 134217727 ∧
        ∃ c : F, c ≠ 0 ∧ P i - P h = C c * Lagrange.nodal (S h ∩ S i) D) ∧
      (∀ U ⊆ N, 682920126 < U.card → ∀ q : F[X], (∀ i ∈ U, q ∣ P i - P h) → IsUnit q)

/-- An overflowing scalar Reed–Solomon list supplies the full star and its divisibility bound. -/
theorem production (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (overflow : (1073741824 : ℕ∞) < Lambda (ReedSolomon.code D 134217728 : Set (I → F))
      ((694116763 : ℝ) / 1073741824)) :
    ContainsStar D := by
  classical
  have he : (1073741824 : ℕ∞) < Lambda (ReedSolomon.code D 134217728 : Set (I → F))
      (((Fintype.card I - 379625061 : ℕ) : ℝ) / Fintype.card I) := by
    simpa only [hn, Nat.reduceSub, Nat.cast_ofNat] using overflow
  obtain ⟨y, P, S, hinj, hd, hs, hy, hp⟩ :=
    SaturatedListCliques.from_list_family D (by decide : 0 < 134217728)
      (by rw [hn]; decide) (by rw [hn]; decide) he
  obtain ⟨h, N, hN, neighbor⟩ := star S hn hs hp
  have factor (i) (hi : i ∈ N) : ∃ c : F, c ≠ 0 ∧
      P i - P h = C c * Lagrange.nodal (S h ∩ S i) D := by
    obtain ⟨ne, eq⟩ := neighbor i hi
    apply SaturatedSplitTriangle.saturated_factor D _ (sub_ne_zero.mpr (hinj.ne ne.symm))
    · rw [eq]
      exact (natDegree_sub_le _ _).trans (max_le (by have := hd i; omega) (by have := hd h; omega))
    · intro x hx
      rw [eval_sub, hy i x (mem_inter.mp hx).2, hy h x (mem_inter.mp hx).1, sub_self]
  refine ⟨y,P,S,h,N,hinj,hd,hs,hy,hN,fun i hi => ⟨(neighbor i hi).2, factor i hi⟩,?_⟩
  intro U sub enough q divides
  obtain ⟨i, hi⟩ := card_pos.mp (show 0 < U.card by omega)
  obtain ⟨a, ha, eq⟩ := factor i (sub hi)
  have split : (P i - P h).Splits := by
    rw [eq]
    exact (Splits.prod (fun j _ => Splits.X_sub_C (D j))).C_mul a
  have hq := split.of_dvd (sub_ne_zero.mpr (hinj.ne (neighbor i (sub hi)).1.symm)) (divides i hi)
  by_contra unit
  obtain ⟨z, hz⟩ := hq.exists_eval_eq_zero (fun deg => unit (isUnit_iff_degree_eq_zero.mpr deg))
  have root (j) (hj : j ∈ U) : ∃ x ∈ S h ∩ S j, z = D x := by
    obtain ⟨b, hb, eb⟩ := factor j (sub hj)
    have van := eval_eq_zero_of_dvd_of_eval_eq_zero (divides j hj) hz
    rw [eb, eval_mul, eval_C] at van
    by_contra! off
    exact Lagrange.eval_nodal_not_at_node off ((mul_eq_zero.mp van).resolve_left hb)
  obtain ⟨x, _, rfl⟩ := root i hi
  have shared (j) (hj : j ∈ U) : x ∈ S j := by
    obtain ⟨w, hw, heq⟩ := root j hj
    exact D.injective heq ▸ (mem_inter.mp hw).2
  have headOut : h ∉ U := fun hh => (neighbor h (sub hh)).1 rfl
  obtain ⟨w, hw, eqw⟩ := root i hi
  have headHit : x ∈ S h := D.injective eqw ▸ (mem_inter.mp hw).1
  have cap := site_capacity S (insert h U) x hn (fun j _ => hs j) (fun a _ b _ => hp a b)
    (fun j hj => (mem_insert.mp hj).elim (fun eq => eq ▸ headHit) (shared j))
  rw [card_insert_of_notMem headOut] at cap
  omega

/-- The scalar star is also necessary for an overflowing interleaving when the
field supplies a separating projection for one over-budget sublist. -/
theorem of_interleaved (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hfield : Nat.choose 1073741825 2 ≤ Nat.card F) (w : ℕ)
    (overflow : (1073741824 : ℕ∞) < Lambda
      (interleavedCodeSet (κ := Fin w) (ReedSolomon.code D 134217728 : Set (I → F)))
      ((694116763 : ℝ) / 1073741824)) : ContainsStar D := by
  have : Nonempty I := Fintype.card_pos_iff.mp (hn ▸ by decide)
  have : Finite F := Nat.finite_of_card_ne_zero (ne_of_gt
    ((Nat.choose_pos (by decide : 2 ≤ 1073741825)).trans_le hfield))
  let := Fintype.ofFinite F
  apply production D hn
  apply lt_of_not_ge
  intro safe
  exact (not_le_of_gt overflow)
    (InterleavedListProjection.interleaved_le_of_scalar_le _ _ _ hfield safe)

#print axioms production
#print axioms of_interleaved
end ProximityGap.PrimitiveSaturatedStar
