/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergyDiagonalFloor

/-!
# The universal swap floor for the `r`-fold additive energy (#444, #389)

This file extends the just-landed universal **diagonal** floor `rEnergy G r ≥ |G|^r`
(`REnergyDiagonalFloor.rEnergy_ge_card_pow`) to a strictly larger, still **hypothesis-free**,
**char-free** closed-form lower bound for every `r ≥ 2`:

> **`rEnergy_ge_swap_floor`.**  `2·|G|^(m+2) − |G|^(m+1) ≤ rEnergy G (m+2)`, any finite `G`, any `m`.

The mechanism is the **adjacent transposition** on the first two coordinates: for every tuple
`v ∈ (Fin r → G)`, the swapped tuple `w = v ∘ swap 0 1` has the same coordinate multiset, hence
`∑ w = ∑ v`, so the inner indicator sum is `≥ 2` whenever `v 0 ≠ v 1` (the diagonal `w = v` and
the distinct swap `w = swap v` are two different solutions) and `≥ 1` otherwise.  Summing the
per-`v` lower bound `if v 0 = v 1 then 1 else 2` gives

  `∑_v (if v 0 = v 1 then 1 else 2) = 2·|G|^r − #{v : v 0 = v 1} = 2·|G|^r − |G|^(r-1)`.

This is the all-`r` generalization of the `r = 2` char-free swap floor `2n² − n`
(`E2CharFree`'s `T1 ∪ T2` diagonal+swap part).  Unlike the **antipodal** floor `3n² − 3n`
(which needs negation-closure `∀ x ∈ G, −x ∈ G`), the swap floor is a pure **permutation**
symmetry, so it needs **no** hypothesis on `G` at all.

We parametrize `r = m + 2` so that the two distinguished coordinates `0, 1` always exist and the
overlap count `|G|^(r-1) = |G|^(m+1)` is manifest.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  No CORE closure, no char-p transfer, no
capacity / beyond-Johnson / growth-law claim.  Issues #444, #389.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The adjacent transposition on the first two coordinates of a tuple `v : Fin (m+2) → F`. -/
def swap01 {m : ℕ} (v : Fin (m + 2) → F) : Fin (m + 2) → F :=
  fun i => v (Equiv.swap (0 : Fin (m + 2)) 1 i)

/-- `swap01` preserves the coordinate sum (it permutes the index set). -/
theorem sum_swap01 {m : ℕ} (v : Fin (m + 2) → F) :
    ∑ i, (swap01 v) i = ∑ i, v i := by
  unfold swap01
  exact Equiv.sum_comp (Equiv.swap (0 : Fin (m + 2)) 1) v

/-- `swap01 v` lands in the same product finset as `v`. -/
theorem swap01_mem {m : ℕ} {G : Finset F} {v : Fin (m + 2) → F}
    (hv : v ∈ Fintype.piFinset (fun _ : Fin (m + 2) => G)) :
    swap01 v ∈ Fintype.piFinset (fun _ : Fin (m + 2) => G) := by
  rw [Fintype.mem_piFinset] at hv ⊢
  intro i; exact hv _

/-- If `v 0 ≠ v 1` then `swap01 v ≠ v`. -/
theorem swap01_ne {m : ℕ} {v : Fin (m + 2) → F} (hne : v 0 ≠ v 1) :
    swap01 v ≠ v := by
  intro h
  apply hne
  have h0 : (swap01 v) 0 = v 0 := by rw [h]
  unfold swap01 at h0
  rw [Equiv.swap_apply_left] at h0
  exact h0.symm
  -- swap 0 1 sends 0 ↦ 1, so (swap01 v) 0 = v 1, contradicting = v 0

/-- The number of tuples `v : Fin (m+2) → G` with `v 0 = v 1` is `|G|^(m+1)`.
Proved by peeling coordinate `0` (`consEquiv`): after fixing `v 0 = a`, the predicate becomes
`(tail v) 0 = a`, leaving the first tail coordinate forced and the remaining `m` free. -/
theorem eqPair_count (G : Finset F) (m : ℕ) :
    ((Fintype.piFinset (fun _ : Fin (m + 2) => G)).filter
        (fun v => v 0 = v 1)).card = G.card ^ (m + 1) := by
  classical
  -- Bijection `{v : Fin (m+2)→G | v 0 = v 1}  ↔  Fin (m+1) → G`, dropping coordinate `1`.
  -- forward `f v = cons (v 0) (fun j => v j.succ.succ)`; inverse `g t = cons (t 0) (cons (t 0) (t ∘ succ))`.
  rw [← Fintype.card_piFinset_const G (m + 1)]
  refine Finset.card_nbij'
      (fun v => Fin.cons (v 0) (fun j : Fin m => v j.succ.succ))
      (fun t => Fin.cons (t 0) (Fin.cons (t 0) (fun j : Fin m => t j.succ)))
      ?_ ?_ ?_ ?_
  · -- maps into piFinset (Fin (m+1))
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hv
    simp only [Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa using hv.1 0
    · simpa using hv.1 k.succ.succ
  · -- inverse maps into the filtered set
    intro t ht
    simp only [Finset.mem_coe, Fintype.mem_piFinset] at ht
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun k => ?_) i
      · simpa using ht 0
      · refine Fin.cases ?_ (fun l => ?_) k
        · simpa using ht 0
        · simpa using ht l.succ
    · -- `(g t) 0 = (g t) 1`
      simp only [Fin.cons_zero, Fin.cons_one]
  · -- left inverse: `g (f v) = v` on the set
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hv
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [Fin.cons_zero]
    · refine Fin.cases ?_ (fun l => ?_) k
      · -- coordinate 1 = Fin.succ 0:  g(f v) 1 = (f v) 0 = v 0,  RHS = v 1
        simp only [Fin.cons_succ, Fin.cons_zero]
        rw [Fin.succ_zero_eq_one]
        exact hv.2
      · simp [Fin.cons_succ]
  · -- right inverse: `f (g t) = t`
    intro t _
    funext j
    refine Fin.cases ?_ (fun l => ?_) j
    · simp [Fin.cons_zero]
    · simp [Fin.cons_zero, Fin.cons_succ]

/-- **The universal swap floor.**  `2·|G|^(m+2) − |G|^(m+1) ≤ rEnergy G (m+2)` for any finite `G`
and any `m`, via the diagonal `w = v` together with the adjacent transposition `w = swap01 v`
(hypothesis-free, char-free).  Strictly improves `rEnergy_ge_card_pow` for `r = m + 2`. -/
theorem rEnergy_ge_swap_floor (G : Finset F) (m : ℕ) :
    2 * G.card ^ (m + 2) - G.card ^ (m + 1) ≤ rEnergy G (m + 2) := by
  classical
  unfold rEnergy
  -- Per-`v` inner lower bound:  ≥ 2 when `v 0 ≠ v 1`, ≥ 1 always.
  have hinner : ∀ v ∈ Fintype.piFinset (fun _ : Fin (m + 2) => G),
      (if v 0 = v 1 then (1 : ℕ) else 2) ≤
        ∑ w ∈ Fintype.piFinset (fun _ : Fin (m + 2) => G),
          (if ∑ i, v i = ∑ i, w i then 1 else 0) := by
    intro v hv
    by_cases heq : v 0 = v 1
    · -- diagonal alone gives ≥ 1
      simp only [heq, if_true]
      calc (1 : ℕ)
          = (if ∑ i, v i = ∑ i, v i then 1 else 0) := by simp
        _ ≤ _ := Finset.single_le_sum
              (f := fun w => if ∑ i, v i = ∑ i, w i then (1 : ℕ) else 0)
              (fun w _ => by positivity) hv
    · -- diagonal `v` and swap `swap01 v` are two distinct solutions
      simp only [heq, if_false]
      have hsw_mem : swap01 v ∈ Fintype.piFinset (fun _ : Fin (m + 2) => G) := swap01_mem hv
      have hsw_ne : swap01 v ≠ v := swap01_ne heq
      have hsum_sw : ∑ i, v i = ∑ i, (swap01 v) i := (sum_swap01 v).symm
      have hpair : ({v, swap01 v} : Finset (Fin (m + 2) → F)) ⊆
          Fintype.piFinset (fun _ : Fin (m + 2) => G) := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hv
        · exact hsw_mem
      calc (2 : ℕ)
          = ∑ w ∈ ({v, swap01 v} : Finset (Fin (m + 2) → F)),
              (if ∑ i, v i = ∑ i, w i then 1 else 0) := by
            rw [Finset.sum_insert (by simp [Ne.symm hsw_ne]), Finset.sum_singleton]
            simp [← hsum_sw]
        _ ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin (m + 2) => G),
              (if ∑ i, v i = ∑ i, w i then 1 else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg hpair (fun w _ _ => by positivity)
  -- Sum the per-`v` lower bound; evaluate the LHS sum to the closed form.
  have hsum_lhs : ∑ v ∈ Fintype.piFinset (fun _ : Fin (m + 2) => G),
      (if v 0 = v 1 then (1 : ℕ) else 2)
      = 2 * G.card ^ (m + 2) - G.card ^ (m + 1) := by
    have hcard_pi : (Fintype.piFinset (fun _ : Fin (m + 2) => G)).card = G.card ^ (m + 2) := by
      rw [Fintype.card_piFinset_const]
    have hpoint : ∀ v : Fin (m + 2) → F, (if v 0 = v 1 then (1 : ℕ) else 2)
        = 2 - (if v 0 = v 1 then 1 else 0) := by
      intro v; by_cases h : v 0 = v 1 <;> simp [h]
    simp_rw [hpoint]
    rw [Finset.sum_tsub_distrib _ (fun v _ => by
          by_cases h : v 0 = v 1 <;> simp [h])]
    rw [Finset.sum_const, hcard_pi, smul_eq_mul]
    have hcount : ∑ v ∈ Fintype.piFinset (fun _ : Fin (m + 2) => G),
        (if v 0 = v 1 then (1 : ℕ) else 0) = G.card ^ (m + 1) := by
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      exact eqPair_count G m
    rw [hcount, Nat.mul_comm]
  rw [← hsum_lhs]
  exact Finset.sum_le_sum hinner

end ArkLib.ProximityGap.SubgroupGaussSumMoment

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no sorryAx).
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_ge_swap_floor
