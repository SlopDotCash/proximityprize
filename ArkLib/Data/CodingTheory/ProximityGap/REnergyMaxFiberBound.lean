/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# The trivial max-fiber bound on the `r`-fold additive energy, and the deep-moment corollary (#407)

The #407 meta-theorem reduces the prize to the char-`p` **deep-moment** bound
`(DM_r): q·E_r(μ_n) ≤ m·(2r−1)‼·n^r` at depth `r ≍ log m`, where `E_r(G) = rEnergy G r` is the
`r`-fold additive energy.  This file proves the **trivial max-fiber bound**

  `rEnergy G (s+1) ≤ |G|^{2s+1}`   (i.e. `E_r ≤ |G|^{2r−1}` for `r ≥ 1`),

which is the engine behind the **unconditional deep-regime** half of `(DM_r)`: combined with Stirling
it discharges `(DM_r)` *unconditionally* for `r ≳ e·n/2 ≈ 1.36 n` (the "free deep tail" of the T4
recursion).  The prize depth `r ≍ log m = β·log n ≪ n/2` sits *below* that threshold, in the gap
`[β log n, 1.36 n]` where the bound is too weak — so this is **not** a closure, but it is the exact,
axiom-clean statement of where the trivial bound runs out and the genuine deep-moment difficulty begins.

Proof of the max-fiber bound: `E_r = Σ_t N_r(t)²` with `N_r(t) = #{v ∈ G^r : Σv = t}`, and the
truncation `v ↦ Fin.init v` (drop the last coordinate) is **injective** on each fixed-sum fiber
`{v : Σv = t}` — the last coordinate is forced by `Σv = t` once the first `r−1` are fixed.  Hence
`N_r(t) ≤ |G|^{r−1}`, and `E_r = Σ_v N_r(Σv) ≤ |G|^r · |G|^{r−1} = |G|^{2r−1}`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.REnergyMaxFiberBound

open ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The fixed-sum fiber has at most `|G|^s` tuples.**  For `r = s+1 ≥ 1`, the number of `r`-tuples
from `G` summing to a fixed target `t` is `≤ |G|^{r−1}`, because dropping the last coordinate is
injective on the fiber (the last coordinate is determined by the sum constraint). -/
theorem card_fiber_le (G : Finset F) (s : ℕ) (t : F) :
    ((Fintype.piFinset (fun _ : Fin (s + 1) => G)).filter (fun v => ∑ i, v i = t)).card
      ≤ G.card ^ s := by
  classical
  have hcard : (Fintype.piFinset (fun _ : Fin s => G)).card = G.card ^ s := by
    rw [Fintype.card_piFinset]; simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun v => Fin.init v) ?_ ?_
  · -- maps into the (s)-fold piFinset
    intro v hv
    have hv' : v ∈ (Fintype.piFinset (fun _ : Fin (s + 1) => G)).filter
        (fun v => ∑ i, v i = t) := hv
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hv'
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    simpa [Fin.init] using hv'.1 i.castSucc
  · -- injective on the fiber: last coordinate forced by the sum
    intro v hv w hw hinit
    have hv' : v ∈ (Fintype.piFinset (fun _ : Fin (s + 1) => G)).filter
        (fun v => ∑ i, v i = t) := hv
    have hw' : w ∈ (Fintype.piFinset (fun _ : Fin (s + 1) => G)).filter
        (fun v => ∑ i, v i = t) := hw
    rw [Finset.mem_filter] at hv' hw'
    have hsum : (∑ i, v i) = ∑ i, w i := by rw [hv'.2, hw'.2]
    -- split off the last coordinate
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hsum
    have hpart : (∑ i : Fin s, v i.castSucc) = ∑ i : Fin s, w i.castSucc := by
      apply Finset.sum_congr rfl
      intro i _
      have := congrFun hinit i
      simpa [Fin.init] using this
    have hlast : v (Fin.last s) = w (Fin.last s) := by
      have := hsum
      rw [hpart] at this
      exact add_left_cancel this
    -- v and w agree on castSucc (from init) and on last ⟹ equal
    funext j
    refine Fin.lastCases ?_ ?_ j
    · exact hlast
    · intro i
      have := congrFun hinit i
      simpa [Fin.init] using this

/-- **The trivial max-fiber bound on the `r`-fold additive energy.**  `E_r(G) ≤ |G|^{2r−1}` for
`r = s+1 ≥ 1`.  Proof: `rEnergy = Σ_v #{w : Σw = Σv} ≤ Σ_v |G|^s = |G|^{s+1} · |G|^s`. -/
theorem rEnergy_le_card_pow (G : Finset F) (s : ℕ) :
    rEnergy G (s + 1) ≤ G.card ^ (2 * s + 1) := by
  classical
  unfold rEnergy
  -- inner sum over w = card of the fixed-sum fiber {w : ∑ w = ∑ v}
  have hinner : ∀ v : Fin (s + 1) → F,
      (∑ w ∈ Fintype.piFinset (fun _ : Fin (s + 1) => G),
          (if ∑ i, v i = ∑ i, w i then 1 else 0))
        ≤ G.card ^ s := by
    intro v
    have hcf : (∑ w ∈ Fintype.piFinset (fun _ : Fin (s + 1) => G),
        (if ∑ i, v i = ∑ i, w i then 1 else 0))
        = ((Fintype.piFinset (fun _ : Fin (s + 1) => G)).filter
            (fun w => ∑ i, w i = ∑ i, v i)).card := by
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro w _
      by_cases h : ∑ i, v i = ∑ i, w i
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    rw [hcf]
    exact card_fiber_le G s (∑ i, v i)
  have hpi : (Fintype.piFinset (fun _ : Fin (s + 1) => G)).card = G.card ^ (s + 1) := by
    rw [Fintype.card_piFinset]; simp
  calc (∑ v ∈ Fintype.piFinset (fun _ : Fin (s + 1) => G),
            ∑ w ∈ Fintype.piFinset (fun _ : Fin (s + 1) => G),
              (if ∑ i, v i = ∑ i, w i then 1 else 0))
        ≤ ∑ _v ∈ Fintype.piFinset (fun _ : Fin (s + 1) => G), G.card ^ s :=
        Finset.sum_le_sum (fun v _ => hinner v)
    _ = G.card ^ (s + 1) * G.card ^ s := by rw [Finset.sum_const, hpi, smul_eq_mul]
    _ = G.card ^ (2 * s + 1) := by rw [← pow_add]; ring_nf

end ArkLib.ProximityGap.REnergyMaxFiberBound
