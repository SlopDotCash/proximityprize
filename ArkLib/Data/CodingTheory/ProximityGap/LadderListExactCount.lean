/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LadderListModP
import ArkLib.Data.CodingTheory.ProximityGap.LadderSupplyExact

/-!
# THE LADDER EXACT LIST: the fibre correspondence in production fields (#389)

Welds the rigidity half (`ladder_explainer_fiber_modp`) and the supply half
(`ladderFibreCodeword_mem` / `ladder_fibre_agreement_card`) into a single
**exact correspondence**, over a production prime field above the resultant
threshold:

> **`ladder_list_iff`** — a function `c` is a codeword of `rsCode dom k`
> (`2r − 3 ≤ k ≤ 2r − 2`) agreeing with the ladder word `x^{2r} + λx^{2r−2}`
> on `≥ 2r` of the `μ_n` domain points **if and only if** `c = w − ∏_{t∈T}(x²−t)`
> for an `r`-subset `T ⊆ μ_{n/2}` with `Σ T = −λ`.

So the agreement-`≥ 2r` single-word list is in bijection with the subset-sum
fibre `{T ⊆ μ_{n/2} : |T| = r, Σ T = −λ}`, and its size is exactly `N_fib` — the
first exact sub-Johnson single-word list size for an infinite Reed–Solomon family,
both directions, in production fields.  Issue #389.
-/

open Finset Polynomial

namespace ProximityGap.LadderList

open ProximityGap.SpikeFloor ProximityGap.LadderListModP

variable {p : ℕ} [Fact p.Prime] {n ν r k : ℕ} {g lam : ZMod p} {dom : Fin n ↪ ZMod p}

/-- **THE EXACT FIBRE CORRESPONDENCE** (production fields): the agreement-`≥ 2r`
single-word list of the ladder word is exactly the set of fibre codewords. -/
theorem ladder_list_iff (hν : 1 ≤ ν) (hg : IsPrimitiveRoot g (2 ^ ν)) (hn : n = 2 ^ ν)
    (hroot : ∀ i, (dom i) ^ n = 1) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * r - 2)
    (hk3 : 2 * r - 3 ≤ k) (hp : (2 * r) ^ 2 ^ (ν - 1) < p)
    (c : Fin n → ZMod p) :
    (c ∈ (rsCode dom k : Submodule (ZMod p) (Fin n → ZMod p)) ∧
        2 * r ≤ (Finset.univ.filter (fun i => c i = ladderWord dom r lam i)).card)
      ↔ ∃ T : Finset (ZMod p), T.card = r ∧ (∀ t ∈ T, t ^ (n / 2) = 1) ∧
          (∑ t ∈ T, t = -lam) ∧ c = ladderFibreCodeword dom r lam T := by
  classical
  have hr : 1 ≤ r := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h2'
    have hp2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2')
    have hr3 : 3 ≤ 2 * r := by omega
    have : 3 ≤ (2 * r) ^ 2 ^ (ν - 1) :=
      le_trans hr3 (Nat.le_self_pow (Nat.two_pow_pos (ν - 1)).ne' _)
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
    omega
  constructor
  · rintro ⟨hc, hagr⟩
    obtain ⟨T, hTcard, hTmu, hTsum, hTform⟩ :=
      ladder_explainer_fiber_modp hν hg hn hroot hk1 hk2 hp hc hagr
    exact ⟨T, hTcard, hTmu, hTsum, funext hTform⟩
  · rintro ⟨T, hTcard, hTmu, hTsum, rfl⟩
    refine ⟨ladderFibreCodeword_mem hr hk1 hk3 hTcard hTsum, ?_⟩
    -- the agreement set is the squaring-preimage of `T`, of size `2r ≥ 2r`
    have hfilter : (Finset.univ.filter
        (fun i => ladderFibreCodeword dom r lam T i = ladderWord dom r lam i))
        = Finset.univ.filter (fun i => (dom i) ^ 2 ∈ T) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ladderFibreCodeword_agree_iff i
    rw [hfilter]
    have hcard := ladder_fibre_agreement_card hν hg hn h2 hroot hTmu
    rw [hTcard] at hcard
    convert hcard.ge using 2
    exact (Finset.filter_congr_decidable _ _ _).symm

end ProximityGap.LadderList

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.LadderList.ladder_list_iff
