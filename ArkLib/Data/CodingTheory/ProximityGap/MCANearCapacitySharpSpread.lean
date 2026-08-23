/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCANearCapacityQuadratic

/-!
# The sharp maximal near-capacity MCA spread on the arithmetic domain (Proximity Prize, #232)

`MCANearCapacityQuadratic.lean` realized a quadratic `Θ(k(n-k))` witness spread, but only a *sub*-range
of the `(k+1)`-subset sums (its single-tail staircase has gaps near the top, and it needs `n ≥ 2k+1`).
This file proves the **exact maximal** arithmetic-domain spread promised in
`MCANearCapacityGeneralRate.lean`'s docstring:

`ε_mca(C, 1-(k+1)/n) ≥ ((k+1)(n-k-1) + 1) / |F|`  for every `1 ≤ k < n`,

the largest spread any `(k+1)`-window family on the arithmetic node set `{0,…,n-1}` can give, because
the set of `(k+1)`-subset sums of `{0,…,n-1}` is *exactly* the contiguous integer interval `[T, T']`
with `T = 0+1+⋯+k` and `T' = (n-k-1)+⋯+(n-1)`, of size `T'-T+1 = (k+1)(n-k-1)+1`.

## The construction (water-filling / complement gaps)

A `(k+1)`-subset `{a₀<⋯<a_k} ⊆ {0,…,n-1}` is encoded by its **gaps** `c_j = a_j - j ∈ {0,…,m}`
(`m = n-1-k`), a weakly-increasing sequence, with `∑aⱼ = T + ∑cⱼ`. Conversely, every offset
`s ∈ [0, (k+1)m]` is realized by the *water-filled* gap profile

`c_j = min m (max 0 (s - (k-j)·m))`  (pour `s` units into `k+1` columns of height `m`, top-first),

whose total is exactly `s` (`gapProfile_sum`, via the water-filling identity `waterfill_sum`). Setting
`a_j = c_j + j` gives a strictly increasing window (`aProfile_strictMono`) of `k+1` nodes `< n`, with
node-sum `T + s`. The `(k+1)m + 1` windows for `s = 0,…,(k+1)m` have distinct sums, hence (feeding
`MCANearCapacityGK.epsMCA_ge_of_window_family`) distinct bad scalars, giving the sharp bound.

## What this does and does not do (candidate analysis for #232)

* It is the **tight** arithmetic-domain realization — no `(k+1)`-window family on `{0,…,n-1}` beats
  `(k+1)(n-k-1)+1`, since that is the full subset-sum interval length. Removes the `n ≥ 2k+1`
  restriction of the staircase: holds for every `1 ≤ k < n`.
* It is still `O(n²)/|F| < ε* = 2⁻¹²⁸` for the prize's large fields, so it does **not** pin `δ*`
  (which needs an *exponential* spread). It is the ceiling of the *single-line, single-domain* method;
  the open prize lives beyond it (multiplicity / Guruswami–Sudan).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232 / #141.
-/

open Polynomial BigOperators
open scoped NNReal ENNReal

namespace ProximityGap.MCANearCapacitySharpSpread

open ProximityGap Code ProximityGap.MCANearCapacityGK ProximityGap.MCANearCapacityQuadratic

/-! ## The water-filling identity -/

/-- **Water-filling.** Pouring `s` units of water into `K` columns of height `m` (top-first, each
column `i` receiving `min m (max 0 (s - i·m))`) holds `min s (K·m)` units in total. -/
theorem waterfill_sum (m s : ℕ) :
    ∀ K, (∑ i ∈ Finset.range K, min m (max 0 (s - i * m))) = min s (K * m) := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.lt_or_ge s (K * m) with hsKm | hsKm
    · have h1 : min s (K * m) = s := by omega
      have h2 : s - K * m = 0 := by omega
      have h3 : min s ((K + 1) * m) = s := by
        have : K * m ≤ (K + 1) * m := Nat.mul_le_mul_right _ (by omega)
        omega
      rw [h1, h2, h3]; simp
    · have h1 : min s (K * m) = K * m := by omega
      rcases Nat.lt_or_ge s ((K + 1) * m) with hs1 | hs1
      · have hlt : s - K * m < m := by
          have : (K + 1) * m = K * m + m := by ring
          omega
        have h2 : min m (max 0 (s - K * m)) = s - K * m := by omega
        have h3 : min s ((K + 1) * m) = s := by omega
        rw [h1, h2, h3]; omega
      · have hge : m ≤ s - K * m := by
          have : (K + 1) * m = K * m + m := by ring
          omega
        have h2 : min m (max 0 (s - K * m)) = m := by omega
        have h3 : min s ((K + 1) * m) = (K + 1) * m := by omega
        rw [h1, h2, h3]; ring

/-! ## The gap profile and window for a given offset -/

variable {p : ℕ} [Fact p.Prime] {n k : ℕ} [NeZero n]

/-- The water-filled gap of node `j` (`0 ≤ j ≤ k`) for total offset `s`, into columns of height
`m = n-1-k`. -/
def gap (m k s j : ℕ) : ℕ := min m (max 0 (s - (k - j) * m))

/-- The window node `aⱼ = cⱼ + j`. -/
def aNode (m k s j : ℕ) : ℕ := gap m k s j + j

/-- The gap profile sums to the offset `s`, provided `s ≤ (k+1)·m`. -/
theorem gapProfile_sum (m k s : ℕ) (hs : s ≤ (k + 1) * m) :
    (∑ j ∈ Finset.range (k + 1), gap m k s j) = s := by
  have hreflect :
      (∑ j ∈ Finset.range (k + 1), min m (max 0 (s - (k - j) * m)))
        = ∑ i ∈ Finset.range (k + 1), min m (max 0 (s - i * m)) := by
    rw [← Finset.sum_range_reflect (fun i => min m (max 0 (s - i * m))) (k + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hkj : k - j = k + 1 - 1 - j := by omega
    rw [hkj]
  have hunfold : (∑ j ∈ Finset.range (k + 1), gap m k s j)
      = ∑ j ∈ Finset.range (k + 1), min m (max 0 (s - (k - j) * m)) := by
    simp only [gap]
  rw [hunfold, hreflect, waterfill_sum m s (k + 1)]
  omega

/-- The gap profile is weakly increasing in `j`. -/
theorem gap_mono (m k s : ℕ) {j j' : ℕ} (hj : j ≤ j') (hj'k : j' ≤ k) :
    gap m k s j ≤ gap m k s j' := by
  rw [gap, gap]
  have hsub : (k - j') * m ≤ (k - j) * m := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The window nodes are strictly increasing, hence injective. -/
theorem aNode_strictMono (m k s : ℕ) {j j' : ℕ} (hj : j < j') (hj'k : j' ≤ k) :
    aNode m k s j < aNode m k s j' := by
  have hmono : gap m k s j ≤ gap m k s j' := gap_mono m k s (by omega) hj'k
  rw [aNode, aNode]; omega

omit [Fact p.Prime] [NeZero n] in
/-- Every window node is `< n` (the top gap is `≤ m = n-1-k`, the top index is `k`). -/
theorem aNode_lt (k s : ℕ) {j : ℕ} (hj : j ≤ k) (hkn : k + 1 ≤ n) :
    aNode (n - 1 - k) k s j < n := by
  have hgle : gap (n - 1 - k) k s j ≤ n - 1 - k := min_le_left _ _
  rw [aNode]; omega

/-! ## The window for an offset and its `ZMod p` sum -/

/-- The `(k+1)`-node window realizing offset `s`: nodes `aⱼ = cⱼ + j`, `j = 0,…,k`. -/
def Wsharp (n k s : ℕ) [NeZero n] : Finset (Fin n) :=
  (Finset.range (k + 1)).image (fun j => node (aNode (n - 1 - k) k s j))

/-- The window node-index map is injective on `{0,…,k}` (strict monotonicity + nodes `< n`). -/
theorem aNode_node_injOn (k s : ℕ) (hkn : k + 1 ≤ n) :
    Set.InjOn (fun j => node (aNode (n - 1 - k) k s j) : ℕ → Fin n)
      (Finset.range (k + 1) : Set ℕ) := by
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp only at hab
  have hva : ((node (aNode (n - 1 - k) k s a) : Fin n) : ℕ) = aNode (n - 1 - k) k s a :=
    node_val_of_lt (aNode_lt k s (by omega) hkn)
  have hvb : ((node (aNode (n - 1 - k) k s b) : Fin n) : ℕ) = aNode (n - 1 - k) k s b :=
    node_val_of_lt (aNode_lt k s (by omega) hkn)
  have hval : aNode (n - 1 - k) k s a = aNode (n - 1 - k) k s b := by rw [← hva, ← hvb, hab]
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd hval (Nat.ne_of_lt (aNode_strictMono _ k s h (by omega)))
  · exact h
  · exact absurd hval.symm (Nat.ne_of_lt (aNode_strictMono _ k s h (by omega)))

/-- The window has exactly `k+1` nodes. -/
theorem Wsharp_card (k s : ℕ) (hkn : k + 1 ≤ n) : (Wsharp n k s).card = k + 1 := by
  rw [Wsharp, Finset.card_image_of_injOn (aNode_node_injOn k s hkn), Finset.card_range]

/-- The integer node-sum of the window is `s + T`, where `T = ∑_{j≤k} j`. -/
theorem Wsharp_natsum (k s : ℕ) (hkn : k + 1 ≤ n) (hs : s ≤ (k + 1) * (n - 1 - k)) :
    (∑ i ∈ Wsharp n k s, (i : ℕ)) = s + ∑ j ∈ Finset.range (k + 1), j := by
  rw [Wsharp, Finset.sum_image (aNode_node_injOn k s hkn)]
  have hnode : ∀ j ∈ Finset.range (k + 1),
      ((node (aNode (n - 1 - k) k s j) : Fin n) : ℕ) = aNode (n - 1 - k) k s j := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact node_val_of_lt (aNode_lt k s (by omega) hkn)
  rw [Finset.sum_congr rfl hnode]
  simp only [aNode]
  rw [Finset.sum_add_distrib, gapProfile_sum (n - 1 - k) k s hs]

omit [Fact p.Prime] in
/-- The window node-sum is `< n²`, hence `< p`. -/
theorem Wsharp_natsum_lt (hp : n * n ≤ p) (k s : ℕ) (hkn : k + 1 ≤ n) :
    (∑ i ∈ Wsharp n k s, (i : ℕ)) < p := by
  have hle : (∑ i ∈ Wsharp n k s, (i : ℕ)) ≤ (Wsharp n k s).card • (n - 1) :=
    Finset.sum_le_card_nsmul _ _ _ (fun i _ => by have := i.isLt; omega)
  rw [Wsharp_card k s hkn, smul_eq_mul] at hle
  have hnpos : 0 < n := NeZero.pos n
  have hstep : (k + 1) * (n - 1) < n * n :=
    calc (k + 1) * (n - 1) ≤ n * (n - 1) := Nat.mul_le_mul_right _ (by omega)
      _ < n * n := mul_lt_mul_of_pos_left (by omega) hnpos
  omega

/-! ## The sharp maximal spread lower bound -/

/-- **Sharp maximal near-capacity MCA lower bound on the arithmetic domain.**
For the Reed–Solomon code of dimension `k` on the arithmetic domain `i ↦ (i : ZMod p)` over a prime
field with `n² ≤ p`, with `1 ≤ k` and `k+1 ≤ n`, at radius `δ = 1-(k+1)/n` (capacity minus `1/n`):
`ε_mca(C, δ) ≥ ((k+1)(n-k-1) + 1) / |F|`.
The `(k+1)(n-k-1)+1` water-filled windows for `s = 0,…,(k+1)(n-1-k)` have node-sums `T + s` covering
the **entire** `(k+1)`-subset-sum interval of `{0,…,n-1}`, hence distinct bad scalars. This is the
tight ceiling of the single-line arithmetic-domain method (no window family on `{0,…,n-1}` beats it),
strengthening the staircase bound `MCANearCapacityQuadratic.epsMCA_quadratic_ge` and removing its
`n ≥ 2k+1` restriction. -/
theorem epsMCA_sharp_ge (hp : n * n ≤ p) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    (((k + 1) * (n - 1 - k) + 1 : ℕ) : ℝ≥0∞) / (Fintype.card (ZMod p) : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (A := ZMod p)
          (ReedSolomon.code
              (domain := dom (p := p) (n := n) (by have := NeZero.pos n; nlinarith [hp])) k : Set (Fin n → ZMod p))
          (1 - ((k + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0)) := by
  have hnp : n ≤ p := by have := NeZero.pos n; nlinarith [hp]
  -- dom-sum of a window = cast of its integer node-sum
  have hcastsum : ∀ s, (∑ i ∈ Wsharp n k s, dom (p := p) hnp i)
      = (((∑ i ∈ Wsharp n k s, (i : ℕ)) : ℕ) : ZMod p) := by
    intro s; rw [Nat.cast_sum]; rfl
  -- dom-sum = cast (s + T) on the valid offset range
  have hdomsum : ∀ s, s ≤ (k + 1) * (n - 1 - k) →
      (∑ i ∈ Wsharp n k s, dom (p := p) hnp i)
        = (((s + ∑ j ∈ Finset.range (k + 1), j) : ℕ) : ZMod p) := by
    intro s hs; rw [hcastsum s, Wsharp_natsum k s hkn hs]
  -- the offset determines the window (distinct sums in `ZMod p`)
  have key : ∀ s ∈ Finset.range ((k + 1) * (n - 1 - k) + 1),
      ∀ s' ∈ Finset.range ((k + 1) * (n - 1 - k) + 1),
      (∑ i ∈ Wsharp n k s, dom (p := p) hnp i) = (∑ i ∈ Wsharp n k s', dom (p := p) hnp i) →
        s = s' := by
    intro s hs s' hs' hsum
    rw [Finset.mem_range] at hs hs'
    rw [hdomsum s (by omega), hdomsum s' (by omega)] at hsum
    have hsp : s + ∑ j ∈ Finset.range (k + 1), j < p := by
      rw [← Wsharp_natsum k s hkn (by omega)]; exact Wsharp_natsum_lt hp k s hkn
    have hsp' : s' + ∑ j ∈ Finset.range (k + 1), j < p := by
      rw [← Wsharp_natsum k s' hkn (by omega)]; exact Wsharp_natsum_lt hp k s' hkn
    have hcast := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hsum
    rw [Nat.mod_eq_of_lt hsp, Nat.mod_eq_of_lt hsp'] at hcast
    omega
  -- the window family
  set 𝒮 : Finset (Finset (Fin n)) :=
    (Finset.range ((k + 1) * (n - 1 - k) + 1)).image (fun s => Wsharp n k s) with h𝒮
  have hwinInj : Set.InjOn (fun s => Wsharp n k s)
      (Finset.range ((k + 1) * (n - 1 - k) + 1) : Set ℕ) := by
    intro s hs s' hs' hss'
    exact key s (by simpa using hs) s' (by simpa using hs') (by simp only at hss'; rw [hss'])
  have h𝒮card : 𝒮.card = (k + 1) * (n - 1 - k) + 1 := by
    rw [h𝒮, Finset.card_image_of_injOn hwinInj, Finset.card_range]
  have hcard : ∀ S ∈ 𝒮, S.card = k + 1 := by
    intro S hS
    rw [h𝒮, Finset.mem_image] at hS
    obtain ⟨s, _, rfl⟩ := hS
    exact Wsharp_card k s hkn
  have hinj : Set.InjOn (fun S => -(∑ i ∈ S, dom (p := p) hnp i)) (𝒮 : Set (Finset (Fin n))) := by
    intro S hS S' hS' hSS'
    rw [Finset.mem_coe, h𝒮, Finset.mem_image] at hS hS'
    obtain ⟨s, hs, rfl⟩ := hS
    obtain ⟨s', hs', rfl⟩ := hS'
    simp only at hSS'
    have hs2 := key s (by simpa using hs) s' (by simpa using hs') (neg_injective hSS')
    rw [hs2]
  have hbound := epsMCA_ge_of_window_family (F := ZMod p) (dom (p := p) hnp) k hk
    𝒮 hcard hinj
  rwa [h𝒮card] at hbound

#print axioms epsMCA_sharp_ge

end ProximityGap.MCANearCapacitySharpSpread
