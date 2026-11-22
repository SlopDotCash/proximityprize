/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AgreementSlicePacking
import ArkLib.Research.ProximityGap.Frontier.SharedSiteListBound
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! # Lower bounds on the affine dimension of over-budget lists -/

set_option autoImplicit false
noncomputable section
open Finset Classical
namespace ProximityGap.AffineRankMoment

variable {F I V : Type} [Field F] [Fintype I] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- Affine dimension of a finite family of scalar or interleaved words. -/
def rank (F : Type) [Field F] [Module F V] (T : Finset (I → V)) : ℕ :=
  Module.finrank F (vectorSpan F (T : Set (I → V)))

/-- A cardinality bound for every center and every family with the indicated
affine dimension, agreement count, and pairwise agreement cap. -/
def Bound (F I V : Type) [Field F] [Fintype I] [AddCommGroup V] [Module F V]
    (t d r L : ℕ) : Prop :=
  ∀ (T : Finset (I → V)) (y : I → V),
    (∀ u ∈ T, t ≤ (univ.filter (fun i => u i = y i)).card) →
    (∀ u ∈ T, ∀ v ∈ T, u ≠ v → (univ.filter (fun i => u i = v i)).card ≤ d) →
    rank F T ≤ r → T.card ≤ L

/-- Every affine zero-flat contains at most one member of the list. -/
theorem zero (t d : ℕ) : Bound F I V t d 0 1 := by
  intro T _ _ _ hr
  apply Finset.card_le_one_iff_subsingleton.mpr
  apply (vectorSpan_eq_bot_iff_subsingleton (k := F)).mp
  exact Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hr)

private theorem mono {S T : Finset (I → V)} (h : S ⊆ T) : rank F S ≤ rank F T :=
  Submodule.finrank_mono (vectorSpan_mono F h)

private theorem drop {T : Finset (I → V)} (i : I) (v : V)
    (nonconst : ¬ ∀ a ∈ T, ∀ b ∈ T, a i = b i)
    (nonempty : (T.filter (fun a => a i = v)).Nonempty) :
    rank F (T.filter (fun a => a i = v)) < rank F T := by
  let U := T.filter (fun a => a i = v)
  let slice := (affineSpan F ({v} : Set V)).comap (LinearMap.proj i : (I → V) →ₗ[F] V).toAffineMap
  have in_slice : affineSpan F (U : Set (I → V)) ≤ slice := by
    apply affineSpan_le.mpr
    intro a ha
    apply (AffineSubspace.mem_affineSpan_singleton F V).mpr
    exact (mem_filter.mp ha).2
  have proper : affineSpan F (U : Set (I → V)) < affineSpan F (T : Set (I → V)) := by
    apply lt_of_le_of_ne (affineSpan_mono F (filter_subset _ _))
    intro eq
    have all (a : I → V) (ha : a ∈ T) : a i = v := by
      have hs : a ∈ slice := in_slice (eq.symm ▸ subset_affineSpan F _ ha)
      exact (AffineSubspace.mem_affineSpan_singleton F V).mp hs
    exact nonconst (fun a ha b hb => (all a ha).trans (all b hb).symm)
  have smaller := AffineSubspace.direction_lt_of_nonempty proper (nonempty.to_set.affineSpan F)
  rw [direction_affineSpan, direction_affineSpan] at smaller
  exact Submodule.finrank_lt_finrank_of_lt smaller

omit [AddCommGroup V] in
private theorem shortened (T : Finset (I → V)) (y : I → V) (J : Finset I) (t d : ℕ)
    (large : ∀ u ∈ T, t ≤ (univ.filter (fun i => u i = y i)).card)
    (pair : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (univ.filter (fun i => u i = v i)).card ≤ d)
    (shared : ∀ i ∈ J, ∀ u ∈ T, ∀ v ∈ T, u i = v i) :
    T.card * (t - J.card) ^ 2 ≤ (Fintype.card I - J.card) *
      ((t - J.card) + (T.card - 1) * (d - J.card)) := by
  let supp (w : ↥T) := univ.filter fun i => w.val i = y i
  let outside (w : ↥T) := (supp w).subtype (fun i => i ∈ Jᶜ)
  have enough (w : ↥T) : t - J.card ≤ (outside w).card := by
    dsimp only [outside]
    rw [SharedSiteListBound.card_on_complement]
    exact (Nat.sub_le_sub_right (large _ w.property) _).trans (le_card_sdiff _ _)
  choose S subset size using fun w => exists_subset_card_eq (enough w)
  have bound (u v : ↥T) (ne : u ≠ v) : (S u ∩ S v).card ≤ d - J.card := by
    let E := univ.filter fun i => u.val i = v.val i
    have incl : J ⊆ E := fun i hi => mem_filter.mpr ⟨mem_univ _, shared _ hi _ u.property _ v.property⟩
    have small := pair _ u.property _ v.property (fun h => ne (Subtype.ext h))
    have h : S u ∩ S v ⊆ E.subtype (fun i => i ∈ Jᶜ) := by
      intro i hi
      obtain ⟨a, b⟩ := mem_inter.mp hi
      have ei : u.val i.val = y i.val := (mem_filter.mp (mem_subtype.mp (subset _ a))).2
      have ej : v.val i.val = y i.val := (mem_filter.mp (mem_subtype.mp (subset _ b))).2
      exact mem_subtype.mpr (mem_filter.mpr ⟨mem_univ _, ei.trans ej.symm⟩)
    have z := card_le_card h
    rw [SharedSiteListBound.card_on_complement, card_sdiff_of_subset incl] at z
    exact z.trans (Nat.sub_le_sub_right small _)
  have h := AgreementSlicePacking.plotkin (univ : Finset ↥T) S (t - J.card) (d - J.card)
    (fun w _ => size w) (fun u _ v _ => bound u v)
  simpa only [card_univ, Fintype.card_coe, card_compl] using h

/-- Test one rank step by forcing a common set of coordinates, then applying
the finite second moment after deleting that set. -/
theorem step {n t d r L M b : ℕ} (hn : Fintype.card I = n) (prev : Bound F I V t d r L)
    (hL : L < M) (two : 1 < M) (bn : b ≤ n)
    (force : b = 0 ∨ (b - 1) * M + (n - (b - 1)) * L < M * t)
    (reject : d < b ∨ (n - b) * (t - b + (M - 1) * (d - b)) < M * (t - b) ^ 2) :
    Bound F I V t d (r + 1) (M - 1) := by
  intro T₀ y large₀ pair₀ dim₀
  by_contra! bad
  obtain ⟨T, subset, count⟩ := exists_subset_card_eq (show M ≤ T₀.card by omega)
  have large (u) (hu : u ∈ T) := large₀ u (subset hu)
  have pair (u) (hu : u ∈ T) (v) (hv : v ∈ T) := pair₀ u (subset hu) v (subset hv)
  let common := univ.filter (fun i => ∀ u ∈ T, ∀ v ∈ T, u i = v i)
  let slice (i : I) := T.filter (fun u => u i = y i)
  have cap (i : I) (hi : i ∉ common) : (slice i).card ≤ L := by
    obtain he | hp := (slice i).eq_empty_or_nonempty
    · simp [he]
    apply prev _ y (fun u hu => large u (mem_filter.mp hu).1)
      (fun u hu v hv => pair u (mem_filter.mp hu).1 v (mem_filter.mp hv).1)
    have h := drop (F := F) i (y i) (fun h => hi (mem_filter.mpr ⟨mem_univ _, h⟩)) hp
    have hm := (mono (F := F) subset).trans dim₀
    omega
  have hits : M * t ≤ ∑ i, (slice i).card := by
    calc
      M * t = ∑ _ ∈ T, t := by simp [count]
      _ ≤ ∑ u ∈ T, (univ.filter (fun i => u i = y i)).card := sum_le_sum large
      _ = _ := by simp only [slice, Finset.card_filter]; rw [sum_comm]
  have capsum : (∑ i, (slice i).card) ≤ common.card * M + (n - common.card) * L := by
    rw [← sum_add_sum_compl common]
    apply Nat.add_le_add
    · calc
        _ ≤ ∑ _ ∈ common, M := sum_le_sum fun i _ => (card_filter_le ..).trans_eq count
        _ = _ := by simp
    · calc
        _ ≤ ∑ _ ∈ commonᶜ, L := sum_le_sum fun i hi => cap i (mem_compl.mp hi)
        _ = _ := by simp [card_compl, hn]
  have at_least : b ≤ common.card := by
    rcases force with h | h
    · omega
    by_contra! fewer
    have c := hits.trans capsum
    let q := b - 1 - common.card
    have extra : b - 1 = common.card + q := by dsimp [q]; omega
    have rest : n - common.card = n - (b - 1) + q := by dsimp [q]; omega
    have adjust : common.card * M + (n - common.card) * L ≤ (b - 1) * M + (n - (b - 1)) * L := by
      calc
        _ = common.card * M + (n - (b - 1)) * L + q * L := by rw [rest, add_mul]; omega
        _ ≤ common.card * M + (n - (b - 1)) * L + q * M := Nat.add_le_add_left (Nat.mul_le_mul_left q hL.le) _
        _ = _ := by
          have h := congrArg (· * M) extra
          rw [add_mul] at h
          omega
    omega
  obtain ⟨J, sub, jc⟩ := exists_subset_card_eq at_least
  have shared (i) (hi : i ∈ J) := (mem_filter.mp (sub hi)).2
  rcases reject with h | h
  · obtain ⟨u, hu, v, hv, ne⟩ := one_lt_card.mp (by omega : 1 < T.card)
    have incl : J ⊆ univ.filter (fun i => u i = v i) :=
      fun i hi => mem_filter.mpr ⟨mem_univ _, shared i hi u hu v hv⟩
    have := (card_le_card incl).trans (pair _ hu _ hv ne)
    omega
  · have result := shortened T y J t d large pair shared
    rw [count, jc, hn] at result
    omega

/-- Lower bound on the number of coordinates constant across the selected sublist. -/
def forced (n t L M : ℕ) : ℕ := (M * t - L * n + (M - L - 1)) / (M - L)

/-- All integer hypotheses of the one-step argument. -/
abbrev ValidStep (n t d L next : ℕ) : Prop :=
  let M := next + 1
  let b := forced n t L M
  L < M ∧ 1 < M ∧ b ≤ n ∧
  (b = 0 ∨ (b - 1) * M + (n - (b - 1)) * L < M * t) ∧
  (d < b ∨ (n - b) * (t - b + (M - 1) * (d - b)) < M * (t - b) ^ 2)

/-- Check a proposed sequence of rank caps, starting from the preceding cap. -/
def check (n t d : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | L, v :: vs => decide (ValidStep n t d L v) && check n t d v vs

/-- The last cap in the sequence, using the starting cap for an empty sequence. -/
def lastCap : ℕ → List ℕ → ℕ
  | L, [] => L
  | _, v :: vs => lastCap v vs

/-- Each row of a valid integer certificate raises the dimension by one. -/
theorem check_sound {n t d : ℕ} (hn : Fintype.card I = n) (caps : List ℕ) {r L : ℕ}
    (prev : Bound F I V t d r L) (verified : check n t d L caps = true) :
    Bound F I V t d (r + caps.length) (lastCap L caps) := by
  induction caps generalizing r L with
  | nil => simpa [lastCap] using prev
  | cons v vs ih =>
    rcases Bool.and_eq_true_iff.mp verified with ⟨row, tail⟩
    obtain ⟨hl, two, bn, force, reject⟩ := (of_decide_eq_true row : ValidStep n t d L v)
    have next := step hn prev hl two bn force reject
    change Bound F I V t d (r + 1) v at next
    simpa [lastCap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih next tail

/-- A cardinality violation for actual interleaved Reed–Solomon words gives an
affine-dimension lower bound over the alphabet field. -/
theorem interleaved_rank {k width t r L : ℕ} (D : I ↪ F)
    (T : Finset (I → Fin width → F)) (y : I → Fin width → F)
    (mem : ∀ u ∈ T, u ∈ Code.interleavedCodeSet (κ := Fin width) (ReedSolomon.code D k : Set (I → F)))
    (large : ∀ u ∈ T, t ≤ (univ.filter (fun i => u i = y i)).card)
    (bound : Bound F I (Fin width → F) t (k - 1) r L) (excess : L < T.card) : r < rank F T := by
  by_contra! small
  have h : T.card ≤ L := by
    apply bound T y _ _ small
    · intro u hu
      convert large u hu using 2
      ext x
      simp
    · intro u hu v hv ne
      have pair := ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet (mem u hu) (mem v hv) ne
      change (univ.filter (fun i => u i = v i)).card < k at pair
      have le := Nat.le_pred_of_lt pair
      convert le using 2
      ext x
      simp
  omega

#print axioms check_sound
#print axioms interleaved_rank
#print axioms step
end ProximityGap.AffineRankMoment
