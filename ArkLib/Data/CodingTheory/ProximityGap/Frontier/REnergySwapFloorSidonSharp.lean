/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergySwapFloor

/-!
# The swap floor is SHARP exactly for Sidon sets at `r = 2` (#444, #389, §0)

The just-landed universal swap floor `rEnergy G (m+2) ≥ 2·|G|^(m+2) − |G|^(m+1)`
(`REnergySwapFloor.rEnergy_ge_swap_floor`) is an inequality holding for every finite `G`.  This
file characterizes **equality at `r = 2`**: the floor is attained iff `G` is a **Sidon set**
(`B_2` set), i.e. the only additive coincidences `a + b = c + d` in `G` are the two *swap-trivial*
ones `(c,d) = (a,b)` or `(c,d) = (b,a)`.

> **`rEnergy_two_eq_swap_floor_of_sidon`.**  `IsSidonSet G → rEnergy G 2 = 2·|G|² − |G|`.

This is the **hypothesis-free / char-free** sharpness companion to the negation-closed
`AdditiveEnergySidonModNeg.additiveEnergy_eq_of_sidonModNeg` (which gives `3n² − 3n` under
*Sidon-modulo-negation*).  Here no negation-closure is assumed; the floor `2n² − n` is the *plain*
Sidon minimum of the `r = 2` moment object `rEnergy G 2 = #{(v,w) ∈ (Fin 2 → G)² : ∑v = ∑w}`.

The mechanism: for each `v = (v 0, v 1)`, under Sidon the fiber `{w : ∑ w = ∑ v}` is exactly
`{v, swap01 v}` (size `2` when `v 0 ≠ v 1`, size `1` otherwise), so the inner count equals the
per-`v` bound `if v 0 = v 1 then 1 else 2`, whose sum is `2|G|² − |G|` (`= 2|G|^(m+2) − |G|^(m+1)`
at `m = 0`).  For **nondegenerate** Sidon sets (`|G| ≥ 2`), `r = 2` is the only sharp depth: the
probe `probe_rEnergy_sidon_equality.py` shows that at `r ≥ 3`, even Sidon sets of size `≥ 2` acquire
genuine `r`-fold excess (the `B_2` condition controls only *pairwise* sums), which is precisely why
the depth-ℓ Sidon bootstrap (§0) is the open core.  (This `r ≥ 3` non-sharpness is a probe
observation, NOT formalized here; the singleton `|G| = 1` is sharp at every `r` since both sides
are `1`.)

Axiom-clean (`propext, Classical.choice, Quot.sound`).  No CORE closure, no char-p transfer, no
capacity / beyond-Johnson / growth-law claim.  Issues #444, #389.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Plain Sidon (`B_2`) set:** every additive coincidence `a + b = c + d` in `G` is
*swap-trivial*, i.e. `(c, d) = (a, b)` or `(c, d) = (b, a)`.  (No negation-closure assumed —
contrast `AdditiveEnergySidonModNeg.SidonModNeg`, which also permits the zero-sum class.) -/
def IsSidonSet (G : Finset F) : Prop :=
  ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ d ∈ G, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Under Sidon, the energy fiber over `v : Fin 2 → G` is exactly `{v, swap01 v}`. -/
private theorem sidon_fiber_eq {G : Finset F} (hS : IsSidonSet G) {v : Fin 2 → F}
    (hv : v ∈ Fintype.piFinset (fun _ : Fin 2 => G)) :
    (Fintype.piFinset (fun _ : Fin 2 => G)).filter (fun w => ∑ i, v i = ∑ i, w i)
      = {v, swap01 v} := by
  classical
  rw [Fintype.mem_piFinset] at hv
  have hv0 : v 0 ∈ G := hv 0
  have hv1 : v 1 ∈ G := hv 1
  apply Finset.Subset.antisymm
  · intro w hw
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hw
    obtain ⟨hwmem, hsum⟩ := hw
    have hw0 : w 0 ∈ G := hwmem 0
    have hw1 : w 1 ∈ G := hwmem 1
    -- ∑ over Fin 2 = first + second
    have hsum' : v 0 + v 1 = w 0 + w 1 := by
      simpa [Fin.sum_univ_two] using hsum
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases hS (v 0) hv0 (v 1) hv1 (w 0) hw0 (w 1) hw1 hsum' with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · -- w = v
      left; funext i; fin_cases i <;> simp [hc, hd]
    · -- w = swap01 v
      right; funext i
      fin_cases i
      · -- w 0 = v 1 = (swap01 v) 0
        show w 0 = swap01 v 0
        unfold swap01; rw [Equiv.swap_apply_left]; exact hd.symm
      · -- w 1 = v 0 = (swap01 v) 1
        show w 1 = swap01 v 1
        unfold swap01; rw [Equiv.swap_apply_right]; exact hc.symm
  · intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    rcases hw with rfl | rfl
    · exact ⟨fun i => hv i, rfl⟩
    · refine ⟨?_, ?_⟩
      · intro i
        show swap01 v i ∈ G
        unfold swap01
        exact hv _
      · exact (sum_swap01 v).symm

/-- **The swap floor is sharp for Sidon sets at `r = 2`.**  If `G` is a Sidon (`B_2`) set then
the `r = 2` additive energy equals the swap floor exactly:  `rEnergy G 2 = 2·|G|² − |G|`.
Hypothesis-free in characteristic; char-free.  (`r = 2` is the *only* sharp depth.) -/
theorem rEnergy_two_eq_swap_floor_of_sidon {G : Finset F} (hS : IsSidonSet G) :
    rEnergy G 2 = 2 * G.card ^ 2 - G.card := by
  classical
  -- Each inner fiber sum equals `card {v, swap01 v} = if v 0 = v 1 then 1 else 2`.
  have hinner : ∀ v ∈ Fintype.piFinset (fun _ : Fin 2 => G),
      (∑ w ∈ Fintype.piFinset (fun _ : Fin 2 => G),
        (if ∑ i, v i = ∑ i, w i then (1 : ℕ) else 0))
        = (if v 0 = v 1 then 1 else 2) := by
    intro v hv
    -- inner sum = card of the filtered fiber
    rw [Finset.sum_boole]
    rw [sidon_fiber_eq hS hv]
    by_cases heq : v 0 = v 1
    · -- swap01 v = v, so the pair is a singleton
      have : swap01 v = v := by
        funext i; fin_cases i
        · show swap01 v 0 = v 0
          unfold swap01; rw [Equiv.swap_apply_left]; exact heq.symm
        · show swap01 v 1 = v 1
          unfold swap01; rw [Equiv.swap_apply_right]; exact heq
      rw [this, if_pos heq]
      simp
    · -- swap01 v ≠ v, two distinct elements
      have hne : swap01 v ≠ v := swap01_ne heq
      rw [if_neg heq, Finset.card_pair (Ne.symm hne)]
      norm_num
  -- Sum the per-`v` value; this is the swap-floor LHS sum already evaluated in REnergySwapFloor.
  unfold rEnergy
  rw [Finset.sum_congr rfl hinner]
  -- ∑_v (if v 0 = v 1 then 1 else 2) = 2|G|^2 - |G|   (the m = 0 swap-floor count)
  have hcard_pi : (Fintype.piFinset (fun _ : Fin 2 => G)).card = G.card ^ 2 := by
    rw [Fintype.card_piFinset_const]
  have hpoint : ∀ v : Fin 2 → F, (if v 0 = v 1 then (1 : ℕ) else 2)
      = 2 - (if v 0 = v 1 then 1 else 0) := by
    intro v; by_cases h : v 0 = v 1 <;> simp [h]
  simp_rw [hpoint]
  rw [Finset.sum_tsub_distrib _ (fun v _ => by by_cases h : v 0 = v 1 <;> simp [h])]
  rw [Finset.sum_const, hcard_pi, smul_eq_mul]
  have hcount : ∑ v ∈ Fintype.piFinset (fun _ : Fin 2 => G),
      (if v 0 = v 1 then (1 : ℕ) else 0) = G.card := by
    rw [Finset.sum_boole]; simp only [Nat.cast_id]
    have := eqPair_count G 0
    simpa using this
  rw [hcount, Nat.mul_comm]

end ArkLib.ProximityGap.SubgroupGaussSumMoment

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no sorryAx).
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_two_eq_swap_floor_of_sidon
