/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DenseOddRedundancy

/-! # A sparse prescribed domain with at most one quadratic pair

A greedy weak Sidon set rules out all degree-two polynomial pairing maps
at once, in every finite field large enough for the indicated length.
-/
set_option autoImplicit false
namespace ProximityGap.QuadraticPairObstruction
open Polynomial Finset
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private def UniquePairSums (S : Finset F) := ∀ a∈S, ∀ b∈S, ∀ c∈S, ∀ d∈S,
  a ≠ b → c ≠ d → a+b=c+d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)

private theorem exists_set (n : ℕ) (room : n^3+n < Fintype.card F) :
    ∃ S : Finset F, S.card=n ∧ UniquePairSums S := by
  classical
  induction n with
  | zero => exact ⟨∅,by simp,by simp [UniquePairSums]⟩
  | succ n ih =>
    obtain ⟨S,hS,unique⟩ := ih (by nlinarith)
    let blocked := S ∪ (((S ×ˢ S) ×ˢ S).image fun z => z.1.1+z.1.2-z.2)
    have card : blocked.card ≤ n+n^3 := calc
      _ ≤ S.card+(((S ×ˢ S) ×ˢ S).image fun z => z.1.1+z.1.2-z.2).card := card_union_le ..
      _ ≤ S.card+((S ×ˢ S) ×ˢ S).card := Nat.add_le_add_left card_image_le _
      _ = _ := by simp [hS,pow_succ]
    obtain ⟨x,fresh⟩ : ∃ x : F, x ∉ blocked := by
      by_contra! all
      rw [eq_univ_of_forall all,card_univ] at card
      nlinarith
    have new : x ∉ S := fun hx => fresh (mem_union_left _ hx)
    have avoid {a b c : F} (ha : a∈S) (hb : b∈S) (hc : c∈S) (e : x+a=b+c) : False := by
      apply fresh
      apply mem_union_right _
      exact mem_image.mpr ⟨((b,c),a),mem_product.mpr ⟨mem_product.mpr ⟨hb,hc⟩,ha⟩,
        by change b+c-a=x;linear_combination -e⟩
    have with_new {a b c : F} (ha : a∈S) (hb : b∈insert x S) (hc : c∈insert x S)
        (sum : x+a=b+c) : (x=b ∧ a=c) ∨ (x=c ∧ a=b) := by
      rcases mem_insert.mp hb with rfl|hb
      · exact Or.inl ⟨rfl,add_left_cancel sum⟩
      rcases mem_insert.mp hc with rfl|hc
      · exact Or.inr ⟨rfl,by linear_combination sum⟩
      exact (avoid ha hb hc sum).elim
    refine ⟨insert x S,by simp [new,hS],?_⟩
    intro a ha b hb c hc d hd ab cd eq
    rcases mem_insert.mp ha with rfl|haS
    · exact with_new ((mem_insert.mp hb).resolve_left ab.symm) hc hd eq
    rcases mem_insert.mp hb with rfl|hbS
    · rcases with_new haS hc hd ((add_comm ..).trans eq) with res|res
      · exact Or.inr ⟨res.2,res.1⟩
      · exact Or.inl ⟨res.2,res.1⟩
    rcases mem_insert.mp hc with rfl|hcS
    · exact (avoid ((mem_insert.mp hd).resolve_left cd.symm) haS hbS eq.symm).elim
    rcases mem_insert.mp hd with rfl|hdS
    · exact (avoid hcS haS hbS ((add_comm ..).trans eq.symm)).elim
    exact unique a haS b hbS c hcS d hdS ab cd eq

/-- Some prescribed n-site domain has at most two ordered off-diagonal
collisions for every degree-two polynomial, corresponding to a single unordered pair. -/
theorem exists_domain (n : ℕ) (room : n^3+n < Fintype.card F) :
    ∃ x : Fin n ↪ F, ∀ P : F[X], P.natDegree=2 →
      ((univ : Finset (Fin n)).offDiag.filter fun w => P.eval (x w.1)=P.eval (x w.2)).card ≤ 2 := by
  classical
  obtain ⟨S,hS,sidon⟩ := exists_set n room
  let e := (S.equivFinOfCardEq hS).symm
  let x := e.toEmbedding.trans (Function.Embedding.subtype (·∈S))
  have mem (i : Fin n) : x i∈S := (e i).property
  refine ⟨x,?_⟩
  intro P hp
  let H := (univ : Finset (Fin n)).offDiag.filter fun w => P.eval (x w.1)=P.eval (x w.2)
  change H.card ≤ 2
  rcases H.eq_empty_or_nonempty with empty|⟨w,hw⟩
  · simp [empty]
  have lead : P.coeff 2 ≠ 0 := hp ▸ leadingCoeff_ne_zero.mpr (by intro zero;simp [zero] at hp)
  have ev (z : F) : P.eval z=P.coeff 0+P.coeff 1*z+P.coeff 2*z^2 := by
    rw [eval_eq_sum_range' (n:=3) (by omega : P.natDegree < 3)]
    simp [sum_range_succ]
  have distinct {z : Fin n × Fin n} (h : z∈H) := (mem_offDiag.mp (mem_filter.mp h).1).2.2
  have relation {z : Fin n × Fin n} (hz : z∈H) : P.coeff 2*(x z.1+x z.2)+P.coeff 1=0 := by
    have h := (mem_filter.mp hz).2
    change P.eval (x z.1)=P.eval (x z.2) at h
    rw [ev,ev] at h
    have prod : (x z.1-x z.2)*(P.coeff 2*(x z.1+x z.2)+P.coeff 1)=0 := by linear_combination h
    exact (mul_eq_zero.mp prod).resolve_left (sub_ne_zero.mpr (x.injective.ne (distinct hz)))
  have cover : H ⊆ {w,(w.2,w.1)} := by
    intro z hz
    have sum := mul_left_cancel₀ lead (add_right_cancel ((relation hz).trans (relation hw).symm))
    rcases sidon _ (mem _) _ (mem _) _ (mem _) _ (mem _)
      (x.injective.ne (distinct hz)) (x.injective.ne (distinct hw)) sum with eq|eq
    · exact mem_insert.mpr (Or.inl (Prod.ext (x.injective eq.1) (x.injective eq.2)))
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (Prod.ext (x.injective eq.1) (x.injective eq.2))))
  exact (card_le_card cover).trans ((card_insert_le ..).trans (by simp))

end ProximityGap.QuadraticPairObstruction
#print axioms ProximityGap.QuadraticPairObstruction.exists_domain
