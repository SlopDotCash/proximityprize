/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CorePartitionLemma

/-!
# The pointwise pencil bound (#389, the pencil-sum decomposition)

The pencil decomposition of the reformulated supply core splits the target into a
provable pointwise half and the open mean half.  This file lands the pointwise half:

> **`pencil_family_card_le`** — a family of sets through a common point `x`, pairwise
> meeting exactly at `{x}`, each with `≥ r` points besides `x`, has at most
> `(n−1)/r` members (`S.card · r ≤ n − 1`): the remainders are disjoint.

> **`agreement_pencil_card_le`** — instantiated at `k = 2` RS agreement sets: the
> large agreement sets (`≥ t` points) of a word through a common domain point number
> at most `(n−1)/(t−1)` (`d_x · (t−1) ≤ n−1`) — the measured pencil degrees (max `3`
> at the extremal witness, bound `6`) sit inside it.

The open half is the MEAN pencil degree (`Σ_x d_x = Σ_c a_c ≈ 2n` measured): the
linear configuration law.  Pointwise bounds alone give the quadratic set-system
optimum; the mean requires the word coupling.  Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The abstract pencil bound**: sets through `x`, pairwise meeting exactly at `{x}`,
each with `≥ r` further points, number at most `(n−1)/r` (`card·r ≤ n−1`). -/
theorem pencil_family_card_le {S : Finset (Finset (Fin n))} {x : Fin n} {r : ℕ}
    (hmem : ∀ A ∈ S, x ∈ A ∧ r + 1 ≤ A.card)
    (hpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = {x}) :
    S.card * r ≤ n - 1 := by
  classical
  have hdisj : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → Disjoint (A.erase x) (B.erase x) := by
    intro A hA B hB hne
    rw [Finset.disjoint_left]
    intro i hiA hiB
    have hi : i ∈ A ∩ B := Finset.mem_inter.mpr
      ⟨Finset.mem_of_mem_erase hiA, Finset.mem_of_mem_erase hiB⟩
    rw [hpair A hA B hB hne] at hi
    exact (Finset.mem_erase.mp hiA).1 (Finset.mem_singleton.mp hi)
  have hcard : ∀ A ∈ S, r ≤ (A.erase x).card := by
    intro A hA
    obtain ⟨hx, hr⟩ := hmem A hA
    rw [Finset.card_erase_of_mem hx]
    omega
  calc S.card * r = ∑ _A ∈ S, r := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  _ ≤ ∑ A ∈ S, (A.erase x).card := Finset.sum_le_sum hcard
  _ = (S.biUnion (fun A => A.erase x)).card := (Finset.card_biUnion hdisj).symm
  _ ≤ ((Finset.univ : Finset (Fin n)).erase x).card := by
      refine Finset.card_le_card ?_
      intro i hi
      obtain ⟨A, hA, hiA⟩ := Finset.mem_biUnion.mp hi
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hiA).1, Finset.mem_univ _⟩
  _ = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
        Fintype.card_fin]

open Classical in
/-- **The RS pencil bound at `k = 2`**: the number of codewords whose agreement set
with `w` has `≥ t ≥ 3` points and passes through a fixed domain point `x` satisfies
`d_x · (t − 1) ≤ n − 1` — large agreement sets through a point have pairwise
intersection exactly `{x}` (codewords of `rsCode dom 2` agree pairwise on `≤ 1`
point unless equal), so their remainders are disjoint. -/
theorem agreement_pencil_card_le (dom : Fin n ↪ F) {m : ℕ} {w : Fin n → F}
    (x : Fin n) {C : Finset (Fin n → F)}
    (hC : ∀ c ∈ C, c ∈ (rsCode dom 2 : Submodule F (Fin n → F)))
    (hinj : ∀ c ∈ C, ∀ c' ∈ C,
      (agreeSet c w ∩ agreeSet c' w).card ≥ 2 → c = c')
    (hCx : ∀ c ∈ C, x ∈ agreeSet c w ∧ m + 3 ≤ (agreeSet c w).card)
    (hCinj : Set.InjOn (fun c => agreeSet c w) ↑C) :
    C.card * (m + 2) ≤ n - 1 := by
  classical
  set Sfam := C.image (fun c => agreeSet c w) with hSfam
  have hcardim : Sfam.card = C.card := Finset.card_image_of_injOn hCinj
  rw [← hcardim]
  refine pencil_family_card_le (x := x) (r := m + 2) ?_ ?_
  · intro A hA
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hx, hcard⟩ := hCx c hc
    exact ⟨hx, by omega⟩
  · intro A hA B hB hne
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hB
    refine Finset.Subset.antisymm ?_ ?_
    · intro i hi
      by_contra hix
      have h2 : 2 ≤ (agreeSet c w ∩ agreeSet c' w).card := by
        refine Finset.one_lt_card.mpr ?_
        exact ⟨i, hi, x, Finset.mem_inter.mpr
          ⟨(hCx c hc).1, (hCx c' hc').1⟩, fun h => hix (h ▸ Finset.mem_singleton_self x)⟩
      exact hne (by rw [hinj c hc c' hc' h2])
    · intro i hi
      rw [Finset.mem_singleton.mp hi]
      exact Finset.mem_inter.mpr ⟨(hCx c hc).1, (hCx c' hc').1⟩

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.pencil_family_card_le
#print axioms ProximityGap.PairRank.agreement_pencil_card_le
