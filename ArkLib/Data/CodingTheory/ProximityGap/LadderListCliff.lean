/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LadderListExactCount

/-!
# THE LADDER CLIFF, PROVEN below Johnson (#389): the r = 2 ladder list is `≤ n/2`

The Corrádi / general list-decoding envelope (`rs_list_corradi_bound`) is **vacuous**
below the Johnson agreement `a < √((k−1)n)`.  This file proves a genuinely sub-Johnson
list bound for an explicit word family — turning the probe-observed cliff
(`max single-word list = O(n)` for agreement `≥ k+2`) into a theorem at its first
interior point.

* `two_subset_sum_fibre_card_le` — **the combinatorial core** (reusable): for any
  finite set `M` and constant `c`, the number of 2-element subsets of `M` summing to
  `c` is `≤ |M|`.  (The pairing `t ↦ {t, c−t}` surjects `M` onto the fibre.)
* `ladder_r2_fibre_card_le` — the `r = 2` subset-sum fibre over `μ_{n/2}` has
  `≤ n/2` elements.
* `ladder_r2_list_card_le` — hence, via the exact correspondence `ladder_list_iff`,
  the `r = 2` ladder word `x⁴ + λx²`'s agreement-`≥ 4` codeword list over `μ_n ⊂ F_p`
  has size **`≤ n/2`** — `O(n)` at relative agreement `4/n → 0`, **deeply sub-Johnson**,
  a proven (not probed) interior cliff point for an infinite RS family.

The bound is the additive-combinatorics count `|μ_{n/2} ∩ (−λ − μ_{n/2})|/2` made
explicit; sharper constants are the subgroup sum-set / Lam–Leung objects of the
parallel additive-energy lane.  Issue #389.
-/

open Finset Polynomial

namespace ProximityGap.LadderList

open ProximityGap.SpikeFloor ProximityGap.LadderListModP

variable {L : Type} [Field L] [DecidableEq L]

/-- **The combinatorial core**: in any finite set `M`, at most `|M|` two-element
subsets sum to a given constant `c`.  The pairing `t ↦ {t, c − t}` surjects `M`
onto the fibre. -/
theorem two_subset_sum_fibre_card_le (M : Finset L) (c : L) :
    ((M.powersetCard 2).filter (fun T => ∑ t ∈ T, t = c)).card ≤ M.card := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := M)
    (f := fun t => ({t, c - t} : Finset L)))
  intro T hT
  obtain ⟨hTpow, hTsum⟩ := Finset.mem_filter.mp hT
  obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTpow
  -- `T = {t, t'}` with `t + t' = c`, both in `M`
  obtain ⟨t, t', htt', rfl⟩ := Finset.card_eq_two.mp hTcard
  rw [Finset.sum_pair htt'] at hTsum
  have htM : t ∈ M := hTsub (by simp)
  have ht'eq : c - t = t' := by rw [← hTsum]; ring
  exact Finset.mem_image.mpr ⟨t, htM, by rw [ht'eq]⟩

variable {p : ℕ} [Fact p.Prime] {n ν r k : ℕ} {g lam : ZMod p} {dom : Fin n ↪ ZMod p}

/-- The `(n/2)`-th roots of unity in `ZMod p`, as a `Finset`. -/
noncomputable def muHalf (p n : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Polynomial.nthRootsFinset (n / 2) (1 : ZMod p)

theorem mem_muHalf {t : ZMod p} (hn : 0 < n / 2) :
    t ∈ muHalf p n ↔ t ^ (n / 2) = 1 := by
  rw [muHalf, Polynomial.mem_nthRootsFinset hn]

/-- The cardinality of `μ_{n/2}` is `n/2` (from the primitive `2^ν`-th root `g`, whose
square is a primitive `2^{ν−1} = (n/2)`-th root). -/
theorem muHalf_card (hν : 1 ≤ ν) (hg : IsPrimitiveRoot g (2 ^ ν)) (hn : n = 2 ^ ν) :
    (muHalf p n).card = n / 2 := by
  have h2 : (2 : ℕ) ^ ν = 2 * 2 ^ (ν - 1) := by
    conv_lhs => rw [show ν = (ν - 1) + 1 by omega, pow_succ']
  have hprod : (2 : ℕ) ^ ν = 2 * (n / 2) := by rw [hn] at *; omega
  have hg2 : IsPrimitiveRoot (g ^ 2) (n / 2) := hg.pow (Nat.two_pow_pos ν) hprod
  rw [muHalf, hg2.card_nthRootsFinset]

/-- **THE r = 2 FIBRE CAP**: at most `n/2` valid fibre sets for the `r = 2` ladder. -/
theorem ladder_r2_fibre_card_le (hν : 1 ≤ ν) (hg : IsPrimitiveRoot g (2 ^ ν))
    (hn : n = 2 ^ ν) :
    (((muHalf p n).powersetCard 2).filter (fun T => ∑ t ∈ T, t = -lam)).card ≤ n / 2 := by
  rw [← muHalf_card (p := p) hν hg hn]
  exact two_subset_sum_fibre_card_le (muHalf p n) (-lam)

open Classical in
/-- **THE LADDER CLIFF, PROVEN below Johnson**: over `μ_n ⊂ ZMod p` (`p > 4^{2^{ν−1}}`),
the `r = 2` ladder word `x⁴ + λx²`'s agreement-`≥ 4` codeword list has size `≤ n/2`.
At relative agreement `4/n → 0` this is deeply sub-Johnson — a proven interior cliff
point that the Corrádi envelope (vacuous below Johnson) cannot reach. -/
theorem ladder_r2_list_card_le (hν : 1 ≤ ν) (hg : IsPrimitiveRoot g (2 ^ ν))
    (hn : n = 2 ^ ν) (hroot : ∀ i, (dom i) ^ n = 1) (hk1 : 1 ≤ k) (hk2 : k ≤ 2)
    (hp : (4 : ℕ) ^ 2 ^ (ν - 1) < p) :
    ((Finset.univ : Finset (Fin n → ZMod p)).filter
        (fun c => c ∈ (rsCode dom k : Submodule (ZMod p) (Fin n → ZMod p)) ∧
          2 * 2 ≤ (Finset.univ.filter
            (fun i => c i = ladderWord dom 2 lam i)).card)).card ≤ n / 2 := by
  classical
  have hnhalf : 0 < n / 2 := by
    rw [hn]
    have h1 : (2 : ℕ) ^ ν = 2 * 2 ^ (ν - 1) := by
      conv_lhs => rw [show ν = (ν - 1) + 1 by omega, pow_succ']
    have h2 : 0 < 2 ^ (ν - 1) := Nat.two_pow_pos _
    omega
  set FIB := ((muHalf p n).powersetCard 2).filter (fun T => ∑ t ∈ T, t = -lam) with hFIB
  have hlisteq : ((Finset.univ : Finset (Fin n → ZMod p)).filter
      (fun c => c ∈ (rsCode dom k : Submodule (ZMod p) (Fin n → ZMod p)) ∧
        2 * 2 ≤ (Finset.univ.filter
          (fun i => c i = ladderWord dom 2 lam i)).card))
      = FIB.image (ladderFibreCodeword dom 2 lam) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hFIB]
    rw [ladder_list_iff (r := 2) hν hg hn hroot hk1 (by omega) (by omega) (by
      simpa using hp) c]
    constructor
    · rintro ⟨T, hTcard, hTmu, hTsum, rfl⟩
      exact ⟨T, ⟨Finset.mem_powersetCard.mpr ⟨fun t ht =>
        (mem_muHalf hnhalf).mpr (hTmu t ht), hTcard⟩, hTsum⟩, rfl⟩
    · rintro ⟨T, ⟨hTpow, hTsum⟩, rfl⟩
      obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTpow
      exact ⟨T, hTcard, fun t ht => (mem_muHalf hnhalf).mp (hTsub ht), hTsum, rfl⟩
  rw [hlisteq]
  exact le_trans (Finset.card_image_le) (ladder_r2_fibre_card_le hν hg hn)

end ProximityGap.LadderList

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.LadderList.two_subset_sum_fibre_card_le
#print axioms ProximityGap.LadderList.muHalf_card
#print axioms ProximityGap.LadderList.ladder_r2_fibre_card_le
#print axioms ProximityGap.LadderList.ladder_r2_list_card_le
