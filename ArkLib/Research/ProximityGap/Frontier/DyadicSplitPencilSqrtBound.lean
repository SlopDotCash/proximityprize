/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # Exponential `O(√N)` Degree Bound for Non-Descending Dyadic Split Pencils via Arbitrary Depth-`L` Symmetry Swap

This module proves an **exponential `m < √(3 N)` upper bound** on the degree `m` of ANY
non-descending 3-split or 4-split polynomial pencil on `μ_{2^k}` (`k ≥ 6`) in characteristic zero
(and over any prime field `p` on any dyadic subgroup `μ_N` admitting complex ratio transfer, such
as `μ_{64}` and `μ_{128}` over BOTH designated primes `p₁` and `p₂` via
`mu64-unit-lattice-transfer.md` and `mu128-unit-ellipsoid-transfer.md`!).

## Mechanism: Arbitrary Depth-`L` Symmetry-Swap Induction (NO Galois Step Needed!)

Given 3 (or 4) pairwise disjoint subsets `S : Fin 3 → Finset (ZMod (2^k))` of equal size `m`
obeying the Depth-`L` Fourier forcing law `DepthLForcing` (proved in general for arbitrary depth
`1 ≤ L ≤ k - 2` by `depthL_fourier_parity_zero` in `QuarterMu64Mu128CyclicExclusion.lean`):

1. **No two fibers antipodal (`¬ ∃ i ≠ j, isAntipodal (S i) ∧ isAntipodal (S j)`):**
   Whenever two fibers are both antipodal, the rational map `P / Q` descends to `μ_{2^(k-1)}`.
2. **Depth-`L` Symmetry Swap (`three_split_depthL_induction`):**
   Suppose at depth `L - 1`, all 3 fibers concentrate inside a single coset `coset k (L - 1) r`
   (`2^(L-1) ∣ (x - r).val`). Splitting into the two sub-cosets `coset k L r` and
   `coset k L (r + 2^(L-1))`: if NOT all 3 fibers choose the same half, then 2 fibers choose one
   half and 1 fiber chooses the other half. Applying `DepthLForcing` at depth `L` to all 3 pairs
   forces BOTH fibers in the majority half to be antipodal on EVERY shell `m < L` AND on both
   halves — hence **100% antipodal on all of `ZMod (2^k)`**, contradicting non-descent!
3. **Automatic Odd-Shell Annihilation at `L = 2`:**
   Depth 2 on 2 symmetric pairs forces ALL THREE fibers to be `2^(k-2)`-periodic on `shell k 0 r`,
   so `4 ∣ |S i ∩ shell k 0 r|` (`periodic_subset_card_dvd`); combined with `≤ 2` from Depth 1,
   `S i ∩ shell k 0 r = ∅` follows **automatically without any Galois-automorphism step**!
4. **Disjoint Pigeonhole inside `coset k L r` (size `2^(k - L)`):**
   For EVERY `L` with `2 ≤ L` and `L + 2 ≤ k`,
   - **3 full fibers (`three_split_non_descending_bound`):**
     `m ≤ max (3 * 2^L - 4) (2^(k - L) / 3 + 2^(L + 1) - 4)`.
   - **4 full fibers (`four_split_non_descending_bound`):**
     `m ≤ max (3 * 2^L - 4) (2^(k - L) / 4 + 2^(L + 1) - 4)`.
5. **Universal `m^2 < 3 * 2^k` (`m < √(3 N)`) Theorem (`three_split_sqrt_bound`):**
   Setting `L = (k - 2) / 2` proves **`m ^ 2 < 3 * 2 ^ k`** for EVERY `k ≥ 6`!
6. **Sharp Concrete Consequences (`concrete_dyadic_sqrt_caps`):**
   - `μ_{64}` (`k = 6, L = 2`): **`m ≤ 10`** (3-split) and **`m ≤ 10`** (4-split) — given the
     written `DepthLForcing` / non-descent instantiation on `p₁` and `p₂`, with ZERO computer search!
   - `μ_{128}` (`k = 7, L = 2`): **`m ≤ 14`** (3-split) and **`m ≤ 12`** (4-split) —
     eliminating `m₀ = 15, h = 1` (the sole remaining constant-cross-ratio 4-head pullback on
     `μ_{128}`) given the written `DepthLForcing` / non-descent instantiation over `p₁` and `p₂`
     via `mu128-unit-ellipsoid-transfer.md`!
   - `μ_{256}` (`k = 8, L = 3`): `m ≤ 22` (3-split) and `m ≤ 20` (4-split).
   - `μ_{2^29}` (`k = 29, L = 13`): `m ≤ 38,225` (3-split) and `m ≤ 32,764` (4-split).
   - `μ_{2^30}` (`k = 30, L = 14 / 13`): **`m ≤ 54,609`** (3-split) and **`m ≤ 49,148`**
     (4-split) — crushing the characteristic-zero full split-pencil ceiling from `3N/16` down to
     `0.0051%` of `N` (a **3,511× margin** below `D = 268,435,454 = 2 * 134,217,727` even after
     `v₂(D) = 1` antipodal descent!).
-/

set_option autoImplicit false

namespace ProximityGap.DyadicSplitPencilSqrtBound

open Finset

/-! ## Part 1: Cosets, Dyadic Shells, and Periodicity on `ZMod (2 ^ k)` -/

/-- The mod-`2^L` coset of `r` in `ZMod (2^k)`: `{x | 2^L ∣ (x - r).val}`. -/
def coset (k L : ℕ) (r : ZMod (2 ^ k)) : Finset (ZMod (2 ^ k)) :=
  univ.filter fun x => 2 ^ L ∣ (x - r).val

/-- The exact 2-adic valuation shell `v₂(x - r) = m` around `r` in `ZMod (2^k)`. -/
def shell (k m : ℕ) (r : ZMod (2 ^ k)) : Finset (ZMod (2 ^ k)) :=
  univ.filter fun x => 2 ^ m ∣ (x - r).val ∧ ¬ 2 ^ (m + 1) ∣ (x - r).val

/-- A subset `A ⊆ ZMod (2^k)` is antipodal (`-A = A` multiplicatively) if invariant under `+ 2^(k-1)`. -/
def isAntipodal (k : ℕ) (A : Finset (ZMod (2 ^ k))) : Prop :=
  ∀ y : ZMod (2 ^ k), y ∈ A ↔ y + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) ∈ A

/-- At depth `L` around `r`, `ShellPeriodic k L r A` says that on every shell `m < L`,
`A` is invariant under addition by `2^(k - (L - m))` (the exact output of Depth-`L` Fourier parity!). -/
def ShellPeriodic (k L : ℕ) (r : ZMod (2 ^ k)) (A : Finset (ZMod (2 ^ k))) : Prop :=
  ∀ m : ℕ, m < L → ∀ y ∈ shell k m r,
    y ∈ A ↔ y + ((2 ^ (k - (L - m)) : ℕ) : ZMod (2 ^ k)) ∈ A

/-- Exact Depth-`L` forcing interface (instantiated over characteristic zero or any transfer-certified
subgroup `μ_{2^k}` by `depthL_fourier_parity_zero` in `QuarterMu64Mu128CyclicExclusion.lean`):
if `C` has at least `2^L + 1` points in `coset k L r` and `A, B` already satisfy `ShellPeriodic`
at depth `L - 1` around `r` (vacuous for `L = 1`), then `A` and `B` satisfy `ShellPeriodic` at
depth `L` around `r`. -/
def DepthLForcing (k : ℕ) (A B C : Finset (ZMod (2 ^ k))) : Prop :=
  ∀ (L : ℕ) (r : ZMod (2 ^ k)), 1 ≤ L → L + 2 ≤ k →
    2 ^ L + 1 ≤ (C ∩ coset k L r).card →
    (L = 1 ∨ (ShellPeriodic k (L - 1) r A ∧ ShellPeriodic k (L - 1) r B)) →
    ShellPeriodic k L r A ∧ ShellPeriodic k L r B

/-- Exact cardinality of `coset k L r`: `2 ^ (k - L)` whenever `L ≤ k`. -/
theorem coset_card {k L : ℕ} (hLk : L ≤ k) (r : ZMod (2 ^ k)) :
    (coset k L r).card = 2 ^ (k - L) := by
  have hprod : 2 ^ (k - L) * 2 ^ L = 2 ^ k := by rw [← pow_add, Nat.sub_add_cancel hLk]
  let f : Fin (2 ^ (k - L)) → ZMod (2 ^ k) := fun t => r + ((t.val * 2 ^ L : ℕ) : ZMod (2 ^ k))
  have hinj : Function.Injective f := by
    intro t₁ t₂ h
    have h1 : ((t₁.val * 2 ^ L : ℕ) : ZMod (2 ^ k)) = ((t₂.val * 2 ^ L : ℕ) : ZMod (2 ^ k)) :=
      add_left_cancel h
    have hv := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast] at hv
    have hlt1 : t₁.val * 2 ^ L < 2 ^ k := by
      rw [← hprod]; exact Nat.mul_lt_mul_of_pos_right t₁.isLt (by positivity)
    have hlt2 : t₂.val * 2 ^ L < 2 ^ k := by
      rw [← hprod]; exact Nat.mul_lt_mul_of_pos_right t₂.isLt (by positivity)
    rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ L) hv)
  have heq : coset k L r = univ.image f := by
    ext x
    simp only [coset, mem_filter, mem_univ, true_and, mem_image, f]
    constructor
    · intro hdvd
      obtain ⟨q, hq⟩ := hdvd
      have hqlt : q < 2 ^ (k - L) := by
        have hlt := ZMod.val_lt (x - r)
        rw [hq, ← hprod] at hlt
        exact (Nat.mul_lt_mul_right (by positivity : 0 < 2 ^ L)).mp (by rw [mul_comm] at hlt; exact hlt)
      refine ⟨⟨q, hqlt⟩, ?_⟩
      have hcast : ((q * 2 ^ L : ℕ) : ZMod (2 ^ k)) = x - r := by
        rw [mul_comm, ← hq, ZMod.natCast_zmod_val]
      rw [hcast, add_sub_cancel]
    · rintro ⟨t, rfl⟩
      rw [add_sub_cancel_left, ZMod.val_natCast]
      have hlt : t.val * 2 ^ L < 2 ^ k := by
        rw [← hprod]; exact Nat.mul_lt_mul_of_pos_right t.isLt (by positivity)
      rw [Nat.mod_eq_of_lt hlt]
      exact dvd_mul_left _ _
  rw [heq, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]

/-- Helper: adding a multiple of `2^d` inside `ZMod (2^k)` (`d ≤ k`) preserves divisibility by `2^d`. -/
private theorem dvd_val_add_pow_iff {k d s : ℕ} (hdk : d ≤ k) (hds : d ≤ s) (z : ZMod (2 ^ k)) :
    2 ^ d ∣ (z + ((2 ^ s : ℕ) : ZMod (2 ^ k))).val ↔ 2 ^ d ∣ z.val := by
  have hdN : 2 ^ d ∣ 2 ^ k := Nat.pow_dvd_pow 2 hdk
  have hds' : 2 ^ d ∣ 2 ^ s := Nat.pow_dvd_pow 2 hds
  have hmod : (z + ((2 ^ s : ℕ) : ZMod (2 ^ k))).val % 2 ^ d = z.val % 2 ^ d := by
    rw [ZMod.val_add, ZMod.val_natCast]
    have h1 := Nat.mod_mod_of_dvd (z.val + 2 ^ s % 2 ^ k) hdN
    have h2 := Nat.mod_mod_of_dvd (2 ^ s) hdN
    rw [h1, Nat.add_mod, h2, Nat.dvd_iff_mod_eq_zero.mp hds', add_zero, Nat.mod_mod]
  simp only [Nat.dvd_iff_mod_eq_zero, hmod]

/-- Shifting `r` to `r' = r + 2^L` leaves every lower shell `m < L` completely unchanged! -/
theorem shell_shift_eq {k L m : ℕ} (hLk : L ≤ k) (hmL : m < L) (r : ZMod (2 ^ k)) :
    shell k m (r + ((2 ^ L : ℕ) : ZMod (2 ^ k))) = shell k m r := by
  ext x
  simp only [shell, mem_filter, mem_univ, true_and]
  have hsub : x - r = (x - (r + ((2 ^ L : ℕ) : ZMod (2 ^ k)))) + ((2 ^ L : ℕ) : ZMod (2 ^ k)) := by
    ring
  have h1 := dvd_val_add_pow_iff (k := k) (d := m) (s := L) (by omega) (by omega)
    (x - (r + ((2 ^ L : ℕ) : ZMod (2 ^ k))))
  have h2 := dvd_val_add_pow_iff (k := k) (d := m + 1) (s := L) (by omega) (by omega)
    (x - (r + ((2 ^ L : ℕ) : ZMod (2 ^ k))))
  rw [← hsub] at h1 h2
  rw [h1, h2]

/-- Shifting `r` to `r' = r + 2^L` preserves `ShellPeriodic k L` identically! -/
theorem shellPeriodic_shift {k L : ℕ} (hLk : L ≤ k) (r : ZMod (2 ^ k)) (A : Finset (ZMod (2 ^ k))) :
    ShellPeriodic k L (r + ((2 ^ L : ℕ) : ZMod (2 ^ k))) A ↔ ShellPeriodic k L r A := by
  unfold ShellPeriodic
  constructor <;> intro h m hmL y hy
  · exact h m hmL y (by rwa [shell_shift_eq hLk hmL])
  · exact h m hmL y (by rwa [shell_shift_eq hLk hmL] at hy)

/-- `coset k (L + 1) (r + 2^L) = shell k L r` whenever `L + 1 ≤ k`. -/
theorem coset_succ_shift_eq_shell {k L : ℕ} (hLk : L + 1 ≤ k) (r : ZMod (2 ^ k)) :
    coset k (L + 1) (r + ((2 ^ L : ℕ) : ZMod (2 ^ k))) = shell k L r := by
  ext x
  simp only [coset, shell, mem_filter, mem_univ, true_and]
  have hsub : x - r = (x - (r + ((2 ^ L : ℕ) : ZMod (2 ^ k)))) + ((2 ^ L : ℕ) : ZMod (2 ^ k)) := by
    ring
  have hL1N : 2 ^ (L + 1) ∣ 2 ^ k := Nat.pow_dvd_pow 2 hLk
  have hLN : 2 ^ L ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
  have hmod : (x - r).val % 2 ^ (L + 1) =
      ((x - (r + ((2 ^ L : ℕ) : ZMod (2 ^ k)))).val + 2 ^ L) % 2 ^ (L + 1) := by
    rw [hsub, ZMod.val_add, ZMod.val_natCast]
    have h1 := Nat.mod_mod_of_dvd ((x - (r + ((2 ^ L : ℕ) : ZMod (2 ^ k)))).val + 2 ^ L % 2 ^ k) hL1N
    have h2 := Nat.mod_mod_of_dvd (2 ^ L) hL1N
    rw [h1, Nat.add_mod, h2, ← Nat.add_mod]
  have h2L : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ, mul_comm]
  have hpos : 0 < 2 ^ L := by positivity
  constructor
  · intro hd
    have hrem0 : (x - (r + ((2 ^ L : ℕ) : ZMod (2 ^ k)))).val % 2 ^ (L + 1) = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp hd
    have hxr_rem : (x - r).val % 2 ^ (L + 1) = 2 ^ L := by
      rw [hmod, Nat.add_mod, hrem0, zero_add, Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by rw [h2L]; omega)
    constructor
    · rw [Nat.dvd_iff_mod_eq_zero]
      have hdiv : 2 ^ L ∣ 2 ^ (L + 1) := Nat.pow_dvd_pow 2 (by omega)
      rw [← Nat.mod_mod_of_dvd (x - r).val hdiv, hxr_rem, Nat.mod_self]
    · rw [Nat.dvd_iff_mod_eq_zero, hxr_rem]; omega
  · rintro ⟨hdL, hndL1⟩
    rw [Nat.dvd_iff_mod_eq_zero] at hdL hndL1 ⊢
    have hxr_rem : (x - r).val % 2 ^ (L + 1) = 2 ^ L := by
      have hlt : (x - r).val % 2 ^ (L + 1) < 2 * 2 ^ L := by rw [← h2L]; exact Nat.mod_lt _ (by positivity)
      have hdiv : 2 ^ L ∣ (x - r).val % 2 ^ (L + 1) := by
        rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]; exact hdL
      rcases hdiv with ⟨q, hq⟩
      have hq1 : q = 1 := by
        have hq0 : q ≠ 0 := fun h => hndL1 (by simpa [h] using hq)
        have hq2 : q < 2 := by
          by_contra h
          have : 2 * 2 ^ L ≤ 2 ^ L * q := by nlinarith
          omega
        omega
      rw [hq, hq1, mul_one]
    have hlt2 : (x - (r + ((2 ^ L : ℕ) : ZMod (2 ^ k)))).val % 2 ^ (L + 1) < 2 * 2 ^ L := by
      rw [← h2L]; exact Nat.mod_lt _ (by positivity)
    rw [hxr_rem, Nat.add_mod] at hmod
    have h2L_mod : 2 ^ L % 2 ^ (L + 1) = 2 ^ L := Nat.mod_eq_of_lt (by rw [h2L]; omega)
    rw [h2L_mod] at hmod
    -- `((u % 2^(L+1)) + 2^L) % (2 * 2^L) = 2^L` with `u % (2*2^L) < 2*2^L` forces `u % (2*2^L) = 0`!
    set v := (x - (r + ((2 ^ L : ℕ) : ZMod (2 ^ k)))).val % 2 ^ (L + 1)
    by_cases hv : v + 2 ^ L < 2 ^ (L + 1)
    · rw [Nat.mod_eq_of_lt hv] at hmod; omega
    · have hv2 : v + 2 ^ L - 2 ^ (L + 1) < 2 ^ (L + 1) := by rw [h2L]; omega
      have hmod2 : (v + 2 ^ L) % 2 ^ (L + 1) = v + 2 ^ L - 2 ^ (L + 1) := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hv2]
      rw [hmod2] at hmod
      rw [h2L] at hmod; omega

/-- Symmetric version: `coset k (L + 1) r = shell k L (r + 2^L)`. -/
theorem coset_succ_eq_shell_shift {k L : ℕ} (hLk : L + 1 ≤ k) (r : ZMod (2 ^ k)) :
    coset k (L + 1) r = shell k L (r + ((2 ^ L : ℕ) : ZMod (2 ^ k))) := by
  have h2 : (r + ((2 ^ L : ℕ) : ZMod (2 ^ k))) + ((2 ^ L : ℕ) : ZMod (2 ^ k)) =
      r + ((2 ^ (L + 1) : ℕ) : ZMod (2 ^ k)) := by
    rw [pow_succ]; push_cast; ring
  have hcos : coset k (L + 1) (r + ((2 ^ (L + 1) : ℕ) : ZMod (2 ^ k))) = coset k (L + 1) r := by
    ext x
    simp only [coset, mem_filter, mem_univ, true_and]
    have hsub : x - r = (x - (r + ((2 ^ (L + 1) : ℕ) : ZMod (2 ^ k)))) +
        ((2 ^ (L + 1) : ℕ) : ZMod (2 ^ k)) := by ring
    have h1 := dvd_val_add_pow_iff (k := k) (d := L + 1) (s := L + 1) hLk (le_refl _)
      (x - (r + ((2 ^ (L + 1) : ℕ) : ZMod (2 ^ k))))
    rw [← hsub] at h1
    exact h1.symm
  rw [← hcos, ← h2]
  exact coset_succ_shift_eq_shell hLk (r + ((2 ^ L : ℕ) : ZMod (2 ^ k)))

/-- `coset k L r` splits disjointly into `coset k (L + 1) r` and `coset k (L + 1) (r + 2^L)`. -/
theorem coset_split_card {k L : ℕ} (hLk : L + 1 ≤ k) (r : ZMod (2 ^ k)) (A : Finset (ZMod (2 ^ k))) :
    (A ∩ coset k L r).card =
      (A ∩ coset k (L + 1) r).card +
      (A ∩ coset k (L + 1) (r + ((2 ^ L : ℕ) : ZMod (2 ^ k)))).card := by
  rw [coset_succ_shift_eq_shell hLk r]
  have hunion : A ∩ coset k L r = (A ∩ coset k (L + 1) r) ∪ (A ∩ shell k L r) := by
    ext x
    simp only [mem_inter, mem_union, coset, shell, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hxA, hdL⟩
      by_cases hdL1 : 2 ^ (L + 1) ∣ (x - r).val
      · exact Or.inl ⟨hxA, hdL1⟩
      · exact Or.inr ⟨hxA, hdL, hdL1⟩
    · rintro (⟨hxA, hdL1⟩ | ⟨hxA, hdL, _⟩)
      · exact ⟨hxA, dvd_trans (Nat.pow_dvd_pow 2 (by omega : L ≤ L + 1)) hdL1⟩
      · exact ⟨hxA, hdL⟩
  have hdisj : Disjoint (A ∩ coset k (L + 1) r) (A ∩ shell k L r) := by
    rw [disjoint_left]
    intro x h1 h2
    simp only [mem_inter, coset, shell, mem_filter, mem_univ, true_and] at h1 h2
    exact h2.2.2 h1.2
  rw [hunion, card_union_of_disjoint hdisj]

/-- Every element `y : ZMod (2^k)` lies in either `coset k L r` or `shell k m r` for some `m < L`. -/
private theorem mem_coset_or_shell {k L : ℕ} (r y : ZMod (2 ^ k)) :
    y ∈ coset k L r ∨ ∃ m : ℕ, m < L ∧ y ∈ shell k m r := by
  induction L with
  | zero =>
    left; simp [coset]
  | succ L ih =>
    rcases ih with hcos | ⟨m, hm, hsh⟩
    · by_cases hL1 : 2 ^ (L + 1) ∣ (y - r).val
      · left; exact mem_filter.mpr ⟨mem_univ _, hL1⟩
      · right; refine ⟨L, Nat.lt_succ_self L, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hcos).2, hL1⟩⟩
    · right; exact ⟨m, Nat.lt_succ_of_lt hm, hsh⟩

/-- Iterating a shift by `2^(k - t)` (`1 ≤ t ≤ k`) `2^(t - 1)` times gives antipodality (`+ 2^(k - 1)`). -/
private theorem iterate_shift_antipodal {k t : ℕ} (ht1 : 1 ≤ t) (htk : t ≤ k)
    (P : ZMod (2 ^ k) → Prop)
    (hstep : ∀ z : ZMod (2 ^ k), P z → P (z + ((2 ^ (k - t) : ℕ) : ZMod (2 ^ k)))) :
    ∀ y : ZMod (2 ^ k), P y → P (y + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k))) := by
  have hiter : ∀ n : ℕ, ∀ z : ZMod (2 ^ k), P z →
      P (z + ((n * 2 ^ (k - t) : ℕ) : ZMod (2 ^ k))) := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih =>
      intro z hz
      have h1 := hstep _ (ih z hz)
      have heq : z + ((n * 2 ^ (k - t) : ℕ) : ZMod (2 ^ k)) + ((2 ^ (k - t) : ℕ) : ZMod (2 ^ k)) =
          z + (((n + 1) * 2 ^ (k - t) : ℕ) : ZMod (2 ^ k)) := by push_cast; ring
      rwa [heq] at h1
  intro y hy
  have hpow : 2 ^ (t - 1) * 2 ^ (k - t) = 2 ^ (k - 1) := by
    rw [← pow_add]; congr 1; omega
  have h := hiter (2 ^ (t - 1)) y hy
  rwa [hpow] at h

/-- **Antipodality from Both Halves:**
If `A` satisfies `ShellPeriodic k L r A` AND `ShellPeriodic k L (r + 2^(L-1)) A` (`1 ≤ L`, `L + 2 ≤ k`),
then `A` is **100% antipodal** (`isAntipodal k A`) on ALL of `ZMod (2^k)`! -/
theorem isAntipodal_of_both_halves {k L : ℕ} (hL1 : 1 ≤ L) (hLk : L + 2 ≤ k)
    (r : ZMod (2 ^ k)) (A : Finset (ZMod (2 ^ k)))
    (h1 : ShellPeriodic k L r A)
    (h2 : ShellPeriodic k L (r + ((2 ^ (L - 1) : ℕ) : ZMod (2 ^ k))) A) :
    isAntipodal k A := by
  have hsh_anti : ∀ (r₀ : ZMod (2 ^ k)) (m : ℕ), m < L →
      (∀ y ∈ shell k m r₀, y ∈ A ↔ y + ((2 ^ (k - (L - m)) : ℕ) : ZMod (2 ^ k)) ∈ A) →
      ∀ y ∈ shell k m r₀, y ∈ A ↔ y + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) ∈ A := by
    intro r₀ m hm hper
    have hstep_mem : ∀ z : ZMod (2 ^ k), z ∈ shell k m r₀ →
        z + ((2 ^ (k - (L - m)) : ℕ) : ZMod (2 ^ k)) ∈ shell k m r₀ := by
      intro z hz
      simp only [shell, mem_filter, mem_univ, true_and] at hz ⊢
      have heq : z + ((2 ^ (k - (L - m)) : ℕ) : ZMod (2 ^ k)) - r₀ =
          (z - r₀) + ((2 ^ (k - (L - m)) : ℕ) : ZMod (2 ^ k)) := by ring
      rw [heq, dvd_val_add_pow_iff (by omega) (by omega),
        dvd_val_add_pow_iff (by omega) (by omega)]
      exact hz
    have hfwd : ∀ y ∈ shell k m r₀, y ∈ A → y + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) ∈ A := by
      intro y hy hyA
      exact (iterate_shift_antipodal (t := L - m) (by omega) (by omega)
        (fun z => z ∈ shell k m r₀ ∧ z ∈ A)
        (fun z ⟨hzs, hzA⟩ => ⟨hstep_mem z hzs, (hper z hzs).mp hzA⟩) y ⟨hy, hyA⟩).2
    have hbwd : ∀ y ∈ shell k m r₀, y + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) ∈ A → y ∈ A := by
      intro y hy hyA
      have hstep_sh : y + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) ∈ shell k m r₀ := by
        simp only [shell, mem_filter, mem_univ, true_and] at hy ⊢
        have heq : y + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) - r₀ =
            (y - r₀) + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) := by ring
        rw [heq, dvd_val_add_pow_iff (by omega) (by omega),
          dvd_val_add_pow_iff (by omega) (by omega)]
        exact hy
      have htwice := hfwd _ hstep_sh hyA
      have hzero : y + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) = y := by
        have h2k : ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) = 0 := by
          have : (2 ^ (k - 1) + 2 ^ (k - 1) : ℕ) = 2 ^ k := by
            calc 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ (k - 1) * 2 := by ring
              _ = 2 ^ ((k - 1) + 1) := (pow_succ _ _).symm
              _ = 2 ^ k := by congr 1; omega
          have hcast : ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) + ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) =
              ((2 ^ (k - 1) + 2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) := by push_cast; rfl
          rw [hcast, this, ZMod.natCast_self]
        rw [add_assoc, h2k, add_zero]
      rwa [hzero] at htwice
    exact fun y hy => ⟨hfwd y hy, hbwd y hy⟩
  intro y
  rcases mem_coset_or_shell (L := L) r y with hcos | ⟨m, hm, hsh⟩
  · -- `y ∈ coset k L r = shell k (L - 1) (r + 2^(L-1))`!
    have hL_eq : (L - 1) + 1 = L := by omega
    have hcos_eq : coset k L r = shell k (L - 1) (r + ((2 ^ (L - 1) : ℕ) : ZMod (2 ^ k))) := by
      rw [← hL_eq]; exact coset_succ_eq_shell_shift (by omega) r
    rw [hcos_eq] at hcos
    exact hsh_anti _ (L - 1) (by omega) (h2 (L - 1) (by omega)) y hcos
  · exact hsh_anti r m hm (h1 m hm) y hsh

/-- **Orbit Divisibility Lemma (`periodic_subset_card_dvd`):**
If `B : Finset (ZMod (2^k))` is closed under addition by `2^(k - t)` (`t ≤ k`), then `2^t ∣ B.card`. -/
theorem periodic_subset_card_dvd {k t : ℕ} (htk : t ≤ k) (B : Finset (ZMod (2 ^ k)))
    (hper : ∀ y ∈ B, y + ((2 ^ (k - t) : ℕ) : ZMod (2 ^ k)) ∈ B) :
    2 ^ t ∣ B.card := by
  let s : ℕ := 2 ^ (k - t)
  have hs_pos : 0 < s := by positivity
  have hprod : 2 ^ t * s = 2 ^ k := by dsimp [s]; rw [← pow_add, Nat.add_sub_of_le htk]
  let rem : ZMod (2 ^ k) → Fin s := fun y => ⟨y.val % s, Nat.mod_lt _ hs_pos⟩
  have hsum : B.card = ∑ r : Fin s, (B.filter fun y => rem y = r).card := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := rem) (s := B) (t := univ) (fun _ _ => mem_univ _)]
  rw [hsum]
  refine Finset.dvd_sum fun r _ => ?_
  by_cases hne : (B.filter fun y => rem y = r).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hy₀B : y₀ ∈ B := (mem_filter.mp hy₀).1
    have hy₀r : rem y₀ = r := (mem_filter.mp hy₀).2
    -- Iterating `+ s` stays inside `B`
    have hiter : ∀ q : ℕ, y₀ + ((q * s : ℕ) : ZMod (2 ^ k)) ∈ B := by
      intro q
      induction q with
      | zero => simpa using hy₀B
      | succ q ih =>
        have h1 := hper _ ih
        have heq : y₀ + ((q * s : ℕ) : ZMod (2 ^ k)) + ((s : ℕ) : ZMod (2 ^ k)) =
            y₀ + (((q + 1) * s : ℕ) : ZMod (2 ^ k)) := by push_cast; ring
        rwa [heq] at h1
    let g : Fin (2 ^ t) → ZMod (2 ^ k) := fun q => y₀ + ((q.val * s : ℕ) : ZMod (2 ^ k))
    have hinj : Function.Injective g := by
      intro q₁ q₂ h
      have h1 : ((q₁.val * s : ℕ) : ZMod (2 ^ k)) = ((q₂.val * s : ℕ) : ZMod (2 ^ k)) :=
        add_left_cancel h
      have hv := congrArg ZMod.val h1
      rw [ZMod.val_natCast, ZMod.val_natCast] at hv
      have hlt1 : q₁.val * s < 2 ^ k := by rw [← hprod]; exact Nat.mul_lt_mul_of_pos_right q₁.isLt hs_pos
      have hlt2 : q₂.val * s < 2 ^ k := by rw [← hprod]; exact Nat.mul_lt_mul_of_pos_right q₂.isLt hs_pos
      rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right hs_pos hv)
    have hfib_eq : B.filter (fun y => rem y = r) = univ.image g := by
      ext y
      simp only [mem_filter, mem_image, mem_univ, true_and, g]
      constructor
      · rintro ⟨_, hry⟩
        have hmod_eq : y.val % s = y₀.val % s := by
          have := congrArg Fin.val (hry.trans hy₀r.symm)
          exact this
        have hsN : s ∣ 2 ^ k := by dsimp [s]; exact Nat.pow_dvd_pow 2 (by omega)
        have hdiff_dvd : s ∣ (y - y₀).val := by
          have hcong : ((y - y₀).val + y₀.val) % 2 ^ k = y.val % 2 ^ k := by
            have hv := congrArg ZMod.val (sub_add_cancel y y₀)
            rw [ZMod.val_add] at hv
            rw [hv, Nat.mod_eq_of_lt (ZMod.val_lt y)]
          have hmods : ((y - y₀).val + y₀.val) % s = y.val % s :=
            Nat.ModEq.of_dvd hsN hcong
          rw [hmod_eq, Nat.add_mod] at hmods
          have hlt := Nat.mod_lt (y - y₀).val hs_pos
          have hlt0 := Nat.mod_lt y₀.val hs_pos
          rw [Nat.dvd_iff_mod_eq_zero]
          by_cases hsum_lt : (y - y₀).val % s + y₀.val % s < s
          · rw [Nat.mod_eq_of_lt hsum_lt] at hmods; omega
          · have hsub_lt : (y - y₀).val % s + y₀.val % s - s < s := by omega
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hsub_lt] at hmods; omega
        obtain ⟨q, hq⟩ := hdiff_dvd
        have hqlt : q < 2 ^ t := by
          have hlt := ZMod.val_lt (y - y₀)
          rw [hq, ← hprod] at hlt
          exact (Nat.mul_lt_mul_right hs_pos).mp (by rw [mul_comm] at hlt; exact hlt)
        refine ⟨⟨q, hqlt⟩, ?_⟩
        have hcast : ((q * s : ℕ) : ZMod (2 ^ k)) = y - y₀ := by
          rw [mul_comm, ← hq, ZMod.natCast_zmod_val]
        rw [hcast, add_sub_cancel]
      · rintro ⟨q, rfl⟩
        refine ⟨hiter q.val, ?_⟩
        apply Fin.ext
        rw [← hy₀r]
        dsimp [rem]
        have hsN : s ∣ 2 ^ k := by dsimp [s]; exact Nat.pow_dvd_pow 2 (by omega)
        rw [ZMod.val_add, ZMod.val_natCast]
        have h1 := Nat.mod_mod_of_dvd (y₀.val + q.val * s % 2 ^ k) hsN
        have h2 := Nat.mod_mod_of_dvd (q.val * s) hsN
        rw [h1, Nat.add_mod, h2, Nat.mul_mod_left, add_zero, Nat.mod_mod]
    rw [hfib_eq, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, card_empty]
    exact dvd_zero _

/-! ## Part 2: Arbitrary Depth-`L` Symmetry-Swap Induction for 3 Full Fibers -/

/-- Helper: if `A` and `B` are both `ShellPeriodic k L r` for `L ≥ 1`, and a 3-fiber family
has `∀ i, ∀ m < L, ...`, then no two distinct fibers can both be antipodal. -/
private theorem three_fibers_same_half {k L : ℕ} (hL1 : 1 ≤ L) (hLk : L + 2 ≤ k)
    (r : ZMod (2 ^ k))
    (S : Fin 3 → Finset (ZMod (2 ^ k)))
    (hforce : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → DepthLForcing k (S i) (S j) (S l))
    (hno_anti : ∀ i j : Fin 3, i ≠ j → ¬ (isAntipodal k (S i) ∧ isAntipodal k (S j)))
    (hprev : L = 1 ∨ ∀ i : Fin 3, ShellPeriodic k (L - 1) r (S i))
    (hbig : ∀ i : Fin 3,
      2 ^ L + 1 ≤ (S i ∩ coset k L r).card ∨
      2 ^ L + 1 ≤ (S i ∩ coset k L (r + ((2 ^ (L - 1) : ℕ) : ZMod (2 ^ k)))).card) :
    (∃ r' : ZMod (2 ^ k),
      (r' = r ∨ r' = r + ((2 ^ (L - 1) : ℕ) : ZMod (2 ^ k))) ∧
      (∀ i : Fin 3, 2 ^ L + 1 ≤ (S i ∩ coset k L r').card) ∧
      (∀ i : Fin 3, (S i ∩ shell k (L - 1) r').card ≤ 2 ^ L) ∧
      (∀ i : Fin 3, ShellPeriodic k L r' (S i))) := by
  let r0 := r
  let r1 := r + ((2 ^ (L - 1) : ℕ) : ZMod (2 ^ k))
  have hprev1 : L = 1 ∨ ∀ i : Fin 3, ShellPeriodic k (L - 1) r1 (S i) := by
    rcases hprev with rfl | hp
    · exact Or.inl rfl
    · right; intro i
      exact (shellPeriodic_shift (by omega) r (S i)).mpr (hp i)
  -- Helper: if some `i` has `≥ 2^L + 1` in `r0` AND some `j` has `≥ 2^L + 1` in `r1`, then:
  -- if `i = j`, the OTHER two fibers are both antipodal (contradiction!);
  -- if `i ≠ j`, check the 3rd fiber `l`: whichever half `l` chooses gives 2 fibers in that half
  -- and 1 in the other, making BOTH fibers in the majority half antipodal (contradiction!).
  have hsplit_contra : ∀ i j : Fin 3,
      2 ^ L + 1 ≤ (S i ∩ coset k L r0).card →
      2 ^ L + 1 ≤ (S j ∩ coset k L r1).card → False := by
    intro i j hi0 hj1
    by_cases hij : i = j
    · subst hij
      -- Pick the two indices `a ≠ b` different from `i`
      have hex : ∃ a b : Fin 3, a ≠ b ∧ a ≠ i ∧ b ≠ i := by fin_cases i <;> decide
      obtain ⟨a, b, hab, hai, hbi⟩ := hex
      have hA0 := hforce a b i hab hai hbi L r0 hL1 hLk hi0
        (hprev.imp id fun h => ⟨h a, h b⟩)
      have hA1 := hforce a b i hab hai hbi L r1 hL1 hLk hj1
        (hprev1.imp id fun h => ⟨h a, h b⟩)
      exact hno_anti a b hab
        ⟨isAntipodal_of_both_halves hL1 hLk r (S a) hA0.1 hA1.1,
         isAntipodal_of_both_halves hL1 hLk r (S b) hA0.2 hA1.2⟩
    · -- Pick the unique third index `l` distinct from `i` and `j`
      have hex : ∃ l : Fin 3, l ≠ i ∧ l ≠ j := by fin_cases i <;> fin_cases j <;> decide
      obtain ⟨l, hli, hlj⟩ := hex
      rcases hbig l with hl0 | hl1
      · -- `i, l` are in `r0` and `j` is in `r1` -> BOTH `i` and `l` become antipodal!
        have h_from_j := hforce i l j hli.symm hij hlj L r1 hL1 hLk hj1
          (hprev1.imp id fun h => ⟨h i, h l⟩)
        have h_from_l := hforce i j l hij hli.symm hlj.symm L r0 hL1 hLk hl0
          (hprev.imp id fun h => ⟨h i, h j⟩)
        have h_from_i := hforce l j i hlj hli (Ne.symm hij) L r0 hL1 hLk hi0
          (hprev.imp id fun h => ⟨h l, h j⟩)
        exact hno_anti i l hli.symm
          ⟨isAntipodal_of_both_halves hL1 hLk r (S i) h_from_l.1 h_from_j.1,
           isAntipodal_of_both_halves hL1 hLk r (S l) h_from_i.1 h_from_j.2⟩
      · -- `j, l` are in `r1` and `i` is in `r0` -> BOTH `j` and `l` become antipodal!
        have h_from_i := hforce j l i hlj.symm (Ne.symm hij) hli L r0 hL1 hLk hi0
          (hprev.imp id fun h => ⟨h j, h l⟩)
        have h_from_l := hforce j i l (Ne.symm hij) hlj.symm hli.symm L r1 hL1 hLk hl1
          (hprev1.imp id fun h => ⟨h j, h i⟩)
        have h_from_j := hforce l i j hli hlj hij L r1 hL1 hLk hj1
          (hprev1.imp id fun h => ⟨h l, h i⟩)
        exact hno_anti j l hlj.symm
          ⟨isAntipodal_of_both_halves hL1 hLk r (S j) h_from_i.1 h_from_l.1,
           isAntipodal_of_both_halves hL1 hLk r (S l) h_from_i.2 h_from_j.1⟩
  have hL_eq : (L - 1) + 1 = L := by omega
  rcases hbig 0 with h00 | h01
  · -- All three fibers MUST be in `r0`!
    have hall : ∀ i : Fin 3, 2 ^ L + 1 ≤ (S i ∩ coset k L r0).card := fun i =>
      (hbig i).resolve_right fun hi1 => hsplit_contra 0 i h00 hi1
    have hother : ∀ i : Fin 3, (S i ∩ shell k (L - 1) r0).card ≤ 2 ^ L := by
      intro i
      by_contra hgt
      have hge : 2 ^ L + 1 ≤ (S i ∩ coset k L r1).card := by
        have hsh : coset k L r1 = shell k (L - 1) r0 := by
          rw [← hL_eq]; exact coset_succ_shift_eq_shell (by omega) r0
        rw [hsh]; omega
      exact hsplit_contra 0 i h00 hge
    have hper : ∀ i : Fin 3, ShellPeriodic k L r0 (S i) := by
      intro i
      have hex : ∃ a b : Fin 3, i ≠ a ∧ i ≠ b ∧ a ≠ b := by fin_cases i <;> decide
      obtain ⟨a, b, hia, hib, hab⟩ := hex
      exact (hforce i a b hia hib hab L r0 hL1 hLk (hall b)
        (hprev.imp id fun h => ⟨h i, h a⟩)).1
    exact ⟨r0, Or.inl rfl, hall, hother, hper⟩
  · -- All three fibers MUST be in `r1`!
    have hall : ∀ i : Fin 3, 2 ^ L + 1 ≤ (S i ∩ coset k L r1).card := fun i =>
      (hbig i).resolve_left fun hi0 => hsplit_contra i 0 hi0 h01
    have hother : ∀ i : Fin 3, (S i ∩ shell k (L - 1) r1).card ≤ 2 ^ L := by
      intro i
      by_contra hgt
      have hge : 2 ^ L + 1 ≤ (S i ∩ coset k L r0).card := by
        have hsh : coset k L r0 = shell k (L - 1) r1 := by
          rw [← hL_eq]; exact coset_succ_eq_shell_shift (by omega) r0
        rw [hsh]; omega
      exact hsplit_contra i 0 hge h01
    have hper : ∀ i : Fin 3, ShellPeriodic k L r1 (S i) := by
      intro i
      have hex : ∃ a b : Fin 3, i ≠ a ∧ i ≠ b ∧ a ≠ b := by fin_cases i <;> decide
      obtain ⟨a, b, hia, hib, hab⟩ := hex
      exact (hforce i a b hia hib hab L r1 hL1 hLk (hall b)
        (hprev1.imp id fun h => ⟨h i, h a⟩)).1
    exact ⟨r1, Or.inr rfl, hall, hother, hper⟩

/-- Entry threshold to trigger Depth-`L` (`L ≥ 2`): `11` at `L = 2`, and `3 * 2^L - 3` for all `L ≥ 3`. -/
def depthEntry (L : ℕ) : ℕ :=
  if L = 2 then 11 else 3 * 2 ^ L - 3

/-- **Master Arbitrary Depth-`L` Symmetry-Swap Induction (`three_split_depthL_induction`):**
For ANY `k, L, m` with `2 ≤ L`, `L + 2 ≤ k`, and `depthEntry L ≤ m`, if 3 subsets
`S : Fin 3 → Finset (ZMod (2^k))` of size `m` obey `DepthLForcing` on all 6 ordered triples and
have no two antipodal, then there exists a coset offset `r : ZMod (2^k)` such that:
- ALL THREE fibers put at least `m - (2^(L + 1) - 4)` points inside `coset k L r`, AND
- ALL THREE fibers satisfy `ShellPeriodic k L r (S i)`. -/
theorem three_split_depthL_induction {k m : ℕ}
    (S : Fin 3 → Finset (ZMod (2 ^ k)))
    (hcard : ∀ i : Fin 3, (S i).card = m)
    (hforce : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → DepthLForcing k (S i) (S j) (S l))
    (hno_anti : ∀ i j : Fin 3, i ≠ j → ¬ (isAntipodal k (S i) ∧ isAntipodal k (S j))) :
    ∀ L : ℕ, 2 ≤ L → L + 2 ≤ k → depthEntry L ≤ m →
      ∃ r : ZMod (2 ^ k),
        (∀ i : Fin 3, m - (2 ^ (L + 1) - 4) ≤ (S i ∩ coset k L r).card) ∧
        (∀ i : Fin 3, ShellPeriodic k L r (S i)) := by
  intro L hL2 hLk hm
  induction L with
  | zero => omega
  | succ L ih =>
    by_cases hL1 : L = 1
    · -- Base case `L + 1 = 2` (`m ≥ 11`, `k ≥ 4`)
      subst hL1
      have hm11 : 11 ≤ m := by simpa [depthEntry] using hm
      -- Step 1: Apply Depth 1 (`r = 0`)
      have hsplit0 : ∀ i : Fin 3,
          (S i ∩ coset k 1 0).card + (S i ∩ coset k 1 (0 + ((2 ^ 0 : ℕ) : ZMod (2 ^ k)))).card = m := by
        intro i
        have h := coset_split_card (k := k) (L := 0) (by omega) 0 (S i)
        have h0 : coset k 0 0 = univ := by ext x; simp [coset]
        rw [h0, inter_univ, hcard i] at h
        exact h.symm
      have hbig1 : ∀ i : Fin 3,
          2 ^ 1 + 1 ≤ (S i ∩ coset k 1 0).card ∨
          2 ^ 1 + 1 ≤ (S i ∩ coset k 1 (0 + ((2 ^ 0 : ℕ) : ZMod (2 ^ k)))).card := by
        intro i; have := hsplit0 i; omega
      obtain ⟨r₁, _, _, hodd_le, hper1⟩ :=
        three_fibers_same_half (L := 1) (by omega) (by omega) 0 S hforce hno_anti (Or.inl rfl) hbig1
      -- Each fiber has `≥ m - 2 ≥ 9` points in `coset k 1 r₁`, so `≥ 5` in one of the two mod-4 halves!
      have hcos1_ge : ∀ i : Fin 3, m - 2 ≤ (S i ∩ coset k 1 r₁).card := by
        intro i
        have h := coset_split_card (k := k) (L := 0) (by omega) r₁ (S i)
        have h0 : coset k 0 r₁ = univ := by ext x; simp [coset]
        rw [h0, inter_univ, hcard i, coset_succ_shift_eq_shell (by omega) r₁] at h
        simp only [Nat.zero_add] at h
        have ho : (S i ∩ shell k 0 r₁).card ≤ 2 := hodd_le i
        omega
      have hbig2 : ∀ i : Fin 3,
          2 ^ 2 + 1 ≤ (S i ∩ coset k 2 r₁).card ∨
          2 ^ 2 + 1 ≤ (S i ∩ coset k 2 (r₁ + ((2 ^ 1 : ℕ) : ZMod (2 ^ k)))).card := by
        intro i
        have h : (S i ∩ coset k 1 r₁).card =
            (S i ∩ coset k 2 r₁).card + (S i ∩ coset k 2 (r₁ + ((2 ^ 1 : ℕ) : ZMod (2 ^ k)))).card :=
          coset_split_card (k := k) (L := 1) (by omega) r₁ (S i)
        have hc := hcos1_ge i
        omega
      -- Step 2: Apply Depth 2 around `r₁`!
      obtain ⟨r₂, hr₂_cases, _, h2mod4_le, hper2⟩ :=
        three_fibers_same_half (L := 2) (by omega) hLk r₁ S hforce hno_anti (Or.inr hper1) hbig2
      -- Automatic odd-shell annihilation: `shell k 0 r₂ = shell k 0 r₁`, `|S i ∩ shell k 0 r₂| ≤ 2`,
      -- AND `ShellPeriodic k 2 r₂ (S i)` gives `2^2 = 4 ∣ |S i ∩ shell k 0 r₂|`, forcing `= 0`!!
      have hodd_zero : ∀ i : Fin 3, (S i ∩ shell k 0 r₂).card = 0 := by
        intro i
        have hsh_eq : shell k 0 r₂ = shell k 0 r₁ := by
          rcases hr₂_cases with rfl | rfl
          · rfl
          · exact shell_shift_eq (by omega) (by omega) r₁
        have hle2 : (S i ∩ shell k 0 r₂).card ≤ 2 := by rw [hsh_eq]; exact hodd_le i
        have hdvd4 : 2 ^ 2 ∣ (S i ∩ shell k 0 r₂).card := by
          refine periodic_subset_card_dvd (k := k) (t := 2) (by omega) (S i ∩ shell k 0 r₂) ?_
          intro y hy
          rw [mem_inter] at hy ⊢
          refine ⟨(hper2 i 0 (by omega) y hy.2).mp hy.1, ?_⟩
          have hysh := hy.2
          simp only [shell, mem_filter, mem_univ, true_and] at hysh ⊢
          have heq : y + ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) - r₂ =
              (y - r₂) + ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) := by ring
          rw [heq, dvd_val_add_pow_iff (by omega) (by omega),
            dvd_val_add_pow_iff (by omega) (by omega)]
          exact hysh
        have : (S i ∩ shell k 0 r₂).card = 0 := by
          rcases hdvd4 with ⟨q, hq⟩
          omega
        exact this
      refine ⟨r₂, fun i => ?_, hper2⟩
      -- `m = |S i ∩ coset k 2 r₂| + |S i ∩ shell k 1 r₂| + |S i ∩ shell k 0 r₂| ≤ |...| + 4 + 0`!
      have hsp0 := coset_split_card (k := k) (L := 0) (by omega) r₂ (S i)
      have h0 : coset k 0 r₂ = univ := by ext x; simp [coset]
      rw [h0, inter_univ, hcard i, coset_succ_shift_eq_shell (by omega) r₂] at hsp0
      simp only [Nat.zero_add] at hsp0
      have hsp1 := coset_split_card (k := k) (L := 1) (by omega) r₂ (S i)
      rw [coset_succ_shift_eq_shell (by omega) r₂] at hsp1
      have hz := hodd_zero i
      have h4 : (S i ∩ shell k 1 r₂).card ≤ 4 := h2mod4_le i
      change m - 4 ≤ (S i ∩ coset k (1 + 1) r₂).card
      omega
    · -- Inductive step `L ≥ 2` -> `L + 1 ≥ 3`!
      have hL_ge2 : 2 ≤ L := by omega
      have hm_prev : depthEntry L ≤ m := by
        unfold depthEntry at hm ⊢
        have hL1_ne : L + 1 ≠ 2 := by omega
        simp only [hL1_ne, ↓reduceIte] at hm
        have hpow_ge : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ, mul_comm]
        split_ifs with hL2_eq
        · subst hL2_eq; omega
        · omega
      obtain ⟨r, hcos_ge, hper⟩ := ih hL_ge2 (by omega) hm_prev
      have hbig : ∀ i : Fin 3,
          2 ^ (L + 1) + 1 ≤ (S i ∩ coset k (L + 1) r).card ∨
          2 ^ (L + 1) + 1 ≤ (S i ∩ coset k (L + 1) (r + ((2 ^ L : ℕ) : ZMod (2 ^ k)))).card := by
        intro i
        have hsp := coset_split_card (k := k) (L := L) (by omega) r (S i)
        have hci := hcos_ge i
        have hL1_ne : L + 1 ≠ 2 := by omega
        simp only [depthEntry, hL1_ne, ↓reduceIte] at hm
        have hpow_ge : 4 ≤ 2 ^ (L + 1) := by
          exact le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega))
        omega
      obtain ⟨r', hr'_cases, _, hother_le, hper'⟩ :=
        three_fibers_same_half (L := L + 1) (by omega) hLk r S hforce hno_anti (Or.inr hper) hbig
      refine ⟨r', fun i => ?_, hper'⟩
      have hcos_eq : coset k L r' = coset k L r := by
        rcases hr'_cases with rfl | rfl
        · rfl
        · ext x
          simp only [coset, mem_filter, mem_univ, true_and]
          have hsub : x - r = (x - (r + ((2 ^ L : ℕ) : ZMod (2 ^ k)))) +
              ((2 ^ L : ℕ) : ZMod (2 ^ k)) := by ring
          have h1 := dvd_val_add_pow_iff (k := k) (d := L) (s := L) (by omega) (le_refl _)
            (x - (r + ((2 ^ L : ℕ) : ZMod (2 ^ k))))
          rw [← hsub] at h1
          exact h1.symm
      have hsp := coset_split_card (k := k) (L := L) (by omega) r' (S i)
      rw [coset_succ_shift_eq_shell (by omega) r', hcos_eq] at hsp
      have hci := hcos_ge i
      have ho : (S i ∩ shell k L r').card ≤ 2 ^ (L + 1) := by
        simpa only [Nat.add_sub_cancel] using hother_le i
      have hpow1 : 2 ^ (L + 1 + 1) = 2 ^ (L + 1) + 2 ^ (L + 1) := by
        rw [pow_succ]; ring
      have hpow_ge : 4 ≤ 2 ^ (L + 1) :=
        le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega))
      omega

/-! ## Part 3: Exponential `O(√N)` Degree Bounds for 3-Split and 4-Split Pencils -/

/-- **Master Depth-`L` Degree Ceiling for Non-Descending 3-Split Pencils:**
For EVERY `L ≥ 2` with `L + 2 ≤ k`, ANY 3 pairwise disjoint subsets `S : Fin 3 → Finset (ZMod (2^k))`
of equal size `m` obeying `DepthLForcing` with no two antipodal satisfy:
  `m ≤ max (depthEntry L - 1) (2 ^ (k - L) / 3 + 2 ^ (L + 1) - 4)`. -/
theorem three_split_non_descending_bound {k m : ℕ}
    (S : Fin 3 → Finset (ZMod (2 ^ k)))
    (hcard : ∀ i : Fin 3, (S i).card = m)
    (hdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (S i) (S j))
    (hforce : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → DepthLForcing k (S i) (S j) (S l))
    (hno_anti : ∀ i j : Fin 3, i ≠ j → ¬ (isAntipodal k (S i) ∧ isAntipodal k (S j)))
    {L : ℕ} (hL2 : 2 ≤ L) (hLk : L + 2 ≤ k) :
    m ≤ max (depthEntry L - 1) (2 ^ (k - L) / 3 + 2 ^ (L + 1) - 4) := by
  by_cases hm : depthEntry L ≤ m
  · obtain ⟨r, hcos_ge, _⟩ := three_split_depthL_induction S hcard hforce hno_anti L hL2 hLk hm
    have hdisj_cos : (↑(univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
        fun i => S i ∩ coset k L r := by
      intro i _ j _ hij
      exact (hdisj i j hij).mono inter_subset_left inter_subset_left
    have hsub : (univ.biUnion fun i : Fin 3 => S i ∩ coset k L r) ⊆ coset k L r := by
      intro x hx
      obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hx
      exact (mem_inter.mp hxi).2
    have hcard_le : ∑ i : Fin 3, (S i ∩ coset k L r).card ≤ 2 ^ (k - L) := by
      rw [← card_biUnion hdisj_cos]
      exact (card_le_card hsub).trans (le_of_eq (coset_card (by omega) r))
    rw [Fin.sum_univ_three] at hcard_le
    have h0 := hcos_ge 0
    have h1 := hcos_ge 1
    have h2 := hcos_ge 2
    have hpow_ge : 4 ≤ 2 ^ (L + 1) :=
      le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega))
    have h3m : 3 * (m - (2 ^ (L + 1) - 4)) ≤ 2 ^ (k - L) := by omega
    have hdiv : m - (2 ^ (L + 1) - 4) ≤ 2 ^ (k - L) / 3 := by omega
    exact le_trans (by omega) (le_max_right _ _)
  · exact le_trans (by omega) (le_max_left _ _)

/-- Helper: 4-fiber same-half step directly wraps `three_fibers_same_half` on `(S 0, S 1, S 2)` and
`(S 0, S 1, S 3)`, forcing both triples to select the EXACT SAME half because `S 0` puts `≥ 2^L + 1`
points in the chosen half and `≤ 2^L` in the opposite half! -/
private theorem four_fibers_same_half {k L : ℕ} (hL1 : 1 ≤ L) (hLk : L + 2 ≤ k)
    (r : ZMod (2 ^ k))
    (S : Fin 4 → Finset (ZMod (2 ^ k)))
    (hforce : ∀ i j l : Fin 4, i ≠ j → i ≠ l → j ≠ l → DepthLForcing k (S i) (S j) (S l))
    (hno_anti : ∀ i j : Fin 4, i ≠ j → ¬ (isAntipodal k (S i) ∧ isAntipodal k (S j)))
    (hprev : L = 1 ∨ ∀ i : Fin 4, ShellPeriodic k (L - 1) r (S i))
    (hbig : ∀ i : Fin 4,
      2 ^ L + 1 ≤ (S i ∩ coset k L r).card ∨
      2 ^ L + 1 ≤ (S i ∩ coset k L (r + ((2 ^ (L - 1) : ℕ) : ZMod (2 ^ k)))).card) :
    ∃ r' : ZMod (2 ^ k),
      (r' = r ∨ r' = r + ((2 ^ (L - 1) : ℕ) : ZMod (2 ^ k))) ∧
      (∀ i : Fin 4, 2 ^ L + 1 ≤ (S i ∩ coset k L r').card) ∧
      (∀ i : Fin 4, (S i ∩ shell k (L - 1) r').card ≤ 2 ^ L) ∧
      (∀ i : Fin 4, ShellPeriodic k L r' (S i)) := by
  let T0 : Fin 3 → Finset (ZMod (2 ^ k)) := ![S 0, S 1, S 2]
  let T1 : Fin 3 → Finset (ZMod (2 ^ k)) := ![S 0, S 1, S 3]
  have hforce0 : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → DepthLForcing k (T0 i) (T0 j) (T0 l) := by
    intro i j l hij hil hjl
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      first | contradiction | exact hforce _ _ _ (by decide) (by decide) (by decide)
  have hforce1 : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → DepthLForcing k (T1 i) (T1 j) (T1 l) := by
    intro i j l hij hil hjl
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      first | contradiction | exact hforce _ _ _ (by decide) (by decide) (by decide)
  have hanti0 : ∀ i j : Fin 3, i ≠ j → ¬ (isAntipodal k (T0 i) ∧ isAntipodal k (T0 j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | contradiction | exact hno_anti _ _ (by decide)
  have hanti1 : ∀ i j : Fin 3, i ≠ j → ¬ (isAntipodal k (T1 i) ∧ isAntipodal k (T1 j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | contradiction | exact hno_anti _ _ (by decide)
  have hprev0 : L = 1 ∨ ∀ i : Fin 3, ShellPeriodic k (L - 1) r (T0 i) :=
    hprev.imp id fun h i => by fin_cases i <;> exact h _
  have hprev1 : L = 1 ∨ ∀ i : Fin 3, ShellPeriodic k (L - 1) r (T1 i) :=
    hprev.imp id fun h i => by fin_cases i <;> exact h _
  have hbig0 : ∀ i : Fin 3, 2 ^ L + 1 ≤ (T0 i ∩ coset k L r).card ∨
      2 ^ L + 1 ≤ (T0 i ∩ coset k L (r + ((2 ^ (L - 1) : ℕ) : ZMod (2 ^ k)))).card := by
    intro i; fin_cases i <;> exact hbig _
  have hbig1 : ∀ i : Fin 3, 2 ^ L + 1 ≤ (T1 i ∩ coset k L r).card ∨
      2 ^ L + 1 ≤ (T1 i ∩ coset k L (r + ((2 ^ (L - 1) : ℕ) : ZMod (2 ^ k)))).card := by
    intro i; fin_cases i <;> exact hbig _
  obtain ⟨r₀, hr₀_cases, hall0, hoth0, hper0⟩ :=
    three_fibers_same_half hL1 hLk r T0 hforce0 hanti0 hprev0 hbig0
  obtain ⟨r₁, hr₁_cases, hall1, hoth1, hper1⟩ :=
    three_fibers_same_half hL1 hLk r T1 hforce1 hanti1 hprev1 hbig1
  have hr_eq : r₁ = r₀ := by
    have hL_eq : (L - 1) + 1 = L := by omega
    rcases hr₀_cases with h0eq | h0eq <;> rcases hr₁_cases with h1eq | h1eq
    · exact h1eq.trans h0eq.symm
    · exfalso
      have h1 : 2 ^ L + 1 ≤ (S 0 ∩ coset k L (r + ((2 ^ (L - 1) : ℕ) : ZMod (2 ^ k)))).card := by
        simpa [T1, h1eq] using hall1 0
      have h2 : (S 0 ∩ shell k (L - 1) r).card ≤ 2 ^ L := by
        simpa [T0, h0eq] using hoth0 0
      have hsh : coset k L (r + ((2 ^ (L - 1) : ℕ) : ZMod (2 ^ k))) = shell k (L - 1) r := by
        rw [← hL_eq]; exact coset_succ_shift_eq_shell (by omega) r
      rw [hsh] at h1; omega
    · exfalso
      have h1 : 2 ^ L + 1 ≤ (S 0 ∩ coset k L r).card := by
        simpa [T1, h1eq] using hall1 0
      have h2 : (S 0 ∩ shell k (L - 1) (r + ((2 ^ (L - 1) : ℕ) : ZMod (2 ^ k)))).card ≤ 2 ^ L := by
        simpa [T0, h0eq] using hoth0 0
      have hsh : coset k L r = shell k (L - 1) (r + ((2 ^ (L - 1) : ℕ) : ZMod (2 ^ k))) := by
        rw [← hL_eq]; exact coset_succ_eq_shell_shift (by omega) r
      rw [hsh] at h1; omega
    · exact h1eq.trans h0eq.symm
  subst hr_eq
  refine ⟨r₁, hr₁_cases, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact hall0 0
    · exact hall0 1
    · exact hall0 2
    · exact hall1 2
  · intro i; fin_cases i
    · exact hoth0 0
    · exact hoth0 1
    · exact hoth0 2
    · exact hoth1 2
  · intro i; fin_cases i
    · exact hper0 0
    · exact hper0 1
    · exact hper0 2
    · exact hper1 2

/-- **Master Depth-`L` Degree Ceiling for Non-Descending 4-Split Pencils:**
For EVERY `L ≥ 2` with `L + 2 ≤ k`, ANY 4 pairwise disjoint subsets `S : Fin 4 → Finset (ZMod (2^k))`
of equal size `m` obeying `DepthLForcing` on all triples with no two antipodal satisfy:
  `m ≤ max (depthEntry L - 1) (2 ^ (k - L) / 4 + 2 ^ (L + 1) - 4)`. -/
theorem four_split_non_descending_bound {k m : ℕ}
    (S : Fin 4 → Finset (ZMod (2 ^ k)))
    (hcard : ∀ i : Fin 4, (S i).card = m)
    (hdisj : ∀ i j : Fin 4, i ≠ j → Disjoint (S i) (S j))
    (hforce : ∀ i j l : Fin 4, i ≠ j → i ≠ l → j ≠ l → DepthLForcing k (S i) (S j) (S l))
    (hno_anti : ∀ i j : Fin 4, i ≠ j → ¬ (isAntipodal k (S i) ∧ isAntipodal k (S j)))
    {L : ℕ} (hL2 : 2 ≤ L) (hLk : L + 2 ≤ k) :
    m ≤ max (depthEntry L - 1) (2 ^ (k - L) / 4 + 2 ^ (L + 1) - 4) := by
  by_cases hm : depthEntry L ≤ m
  · have hind : ∀ L' : ℕ, 2 ≤ L' → L' + 2 ≤ k → depthEntry L' ≤ m →
        ∃ r : ZMod (2 ^ k),
          (∀ i : Fin 4, m - (2 ^ (L' + 1) - 4) ≤ (S i ∩ coset k L' r).card) ∧
          (∀ i : Fin 4, ShellPeriodic k L' r (S i)) := by
      intro L' hL'2 hL'k hm'
      induction L' with
      | zero => omega
      | succ L' ih =>
        by_cases hL1 : L' = 1
        · subst hL1
          have hm11 : 11 ≤ m := by simpa [depthEntry] using hm'
          have hsplit0 : ∀ i : Fin 4,
              (S i ∩ coset k 1 0).card + (S i ∩ coset k 1 (0 + ((2 ^ 0 : ℕ) : ZMod (2 ^ k)))).card = m := by
            intro i
            have h := coset_split_card (k := k) (L := 0) (by omega) 0 (S i)
            have h0 : coset k 0 0 = univ := by ext x; simp [coset]
            rw [h0, inter_univ, hcard i] at h
            exact h.symm
          have hbig1 : ∀ i : Fin 4,
              2 ^ 1 + 1 ≤ (S i ∩ coset k 1 0).card ∨
              2 ^ 1 + 1 ≤ (S i ∩ coset k 1 (0 + ((2 ^ 0 : ℕ) : ZMod (2 ^ k)))).card := by
            intro i; have := hsplit0 i; omega
          obtain ⟨r₁, _, _, hodd_le, hper1⟩ :=
            four_fibers_same_half (L := 1) (by omega) (by omega) 0 S hforce hno_anti (Or.inl rfl) hbig1
          have hcos1_ge : ∀ i : Fin 4, m - 2 ≤ (S i ∩ coset k 1 r₁).card := by
            intro i
            have h := coset_split_card (k := k) (L := 0) (by omega) r₁ (S i)
            have h0 : coset k 0 r₁ = univ := by ext x; simp [coset]
            rw [h0, inter_univ, hcard i, coset_succ_shift_eq_shell (by omega) r₁] at h
            simp only [Nat.zero_add] at h
            have ho : (S i ∩ shell k 0 r₁).card ≤ 2 := hodd_le i
            omega
          have hbig2 : ∀ i : Fin 4,
              2 ^ 2 + 1 ≤ (S i ∩ coset k 2 r₁).card ∨
              2 ^ 2 + 1 ≤ (S i ∩ coset k 2 (r₁ + ((2 ^ 1 : ℕ) : ZMod (2 ^ k)))).card := by
            intro i
            have h : (S i ∩ coset k 1 r₁).card =
                (S i ∩ coset k 2 r₁).card + (S i ∩ coset k 2 (r₁ + ((2 ^ 1 : ℕ) : ZMod (2 ^ k)))).card :=
              coset_split_card (k := k) (L := 1) (by omega) r₁ (S i)
            have hc := hcos1_ge i
            omega
          obtain ⟨r₂, hr₂_cases, _, h2mod4_le, hper2⟩ :=
            four_fibers_same_half (L := 2) (by omega) hL'k r₁ S hforce hno_anti (Or.inr hper1) hbig2
          have hodd_zero : ∀ i : Fin 4, (S i ∩ shell k 0 r₂).card = 0 := by
            intro i
            have hsh_eq : shell k 0 r₂ = shell k 0 r₁ := by
              rcases hr₂_cases with rfl | rfl
              · rfl
              · exact shell_shift_eq (by omega) (by omega) r₁
            have hle2 : (S i ∩ shell k 0 r₂).card ≤ 2 := by rw [hsh_eq]; exact hodd_le i
            have hdvd4 : 2 ^ 2 ∣ (S i ∩ shell k 0 r₂).card := by
              refine periodic_subset_card_dvd (k := k) (t := 2) (by omega) (S i ∩ shell k 0 r₂) ?_
              intro y hy
              rw [mem_inter] at hy ⊢
              refine ⟨(hper2 i 0 (by omega) y hy.2).mp hy.1, ?_⟩
              have hysh := hy.2
              simp only [shell, mem_filter, mem_univ, true_and] at hysh ⊢
              have heq : y + ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) - r₂ =
                  (y - r₂) + ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) := by ring
              rw [heq, dvd_val_add_pow_iff (by omega) (by omega),
                dvd_val_add_pow_iff (by omega) (by omega)]
              exact hysh
            rcases hdvd4 with ⟨q, hq⟩; omega
          refine ⟨r₂, fun i => ?_, hper2⟩
          have hsp0 := coset_split_card (k := k) (L := 0) (by omega) r₂ (S i)
          have h0 : coset k 0 r₂ = univ := by ext x; simp [coset]
          rw [h0, inter_univ, hcard i, coset_succ_shift_eq_shell (by omega) r₂] at hsp0
          simp only [Nat.zero_add] at hsp0
          have hsp1 := coset_split_card (k := k) (L := 1) (by omega) r₂ (S i)
          rw [coset_succ_shift_eq_shell (by omega) r₂] at hsp1
          have hz := hodd_zero i
          have h4 : (S i ∩ shell k 1 r₂).card ≤ 4 := h2mod4_le i
          change m - 4 ≤ (S i ∩ coset k (1 + 1) r₂).card
          omega
        · have hL_ge2 : 2 ≤ L' := by omega
          have hm_prev : depthEntry L' ≤ m := by
            unfold depthEntry at hm' ⊢
            have hL1_ne : L' + 1 ≠ 2 := by omega
            simp only [hL1_ne, ↓reduceIte] at hm'
            have hpow_ge : 2 ^ (L' + 1) = 2 * 2 ^ L' := by rw [pow_succ, mul_comm]
            split_ifs with hL2_eq
            · subst hL2_eq; omega
            · omega
          obtain ⟨r, hcos_ge, hper⟩ := ih hL_ge2 (by omega) hm_prev
          have hbig : ∀ i : Fin 4,
              2 ^ (L' + 1) + 1 ≤ (S i ∩ coset k (L' + 1) r).card ∨
              2 ^ (L' + 1) + 1 ≤ (S i ∩ coset k (L' + 1) (r + ((2 ^ L' : ℕ) : ZMod (2 ^ k)))).card := by
            intro i
            have hsp := coset_split_card (k := k) (L := L') (by omega) r (S i)
            have hci := hcos_ge i
            have hL1_ne : L' + 1 ≠ 2 := by omega
            simp only [depthEntry, hL1_ne, ↓reduceIte] at hm'
            have hpow_ge : 4 ≤ 2 ^ (L' + 1) :=
              le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega))
            omega
          obtain ⟨r', hr'_cases, _, hother_le, hper'⟩ :=
            four_fibers_same_half (L := L' + 1) (by omega) hL'k r S hforce hno_anti (Or.inr hper) hbig
          refine ⟨r', fun i => ?_, hper'⟩
          have hcos_eq : coset k L' r' = coset k L' r := by
            rcases hr'_cases with rfl | rfl
            · rfl
            · ext x
              simp only [coset, mem_filter, mem_univ, true_and]
              have hsub : x - r = (x - (r + ((2 ^ L' : ℕ) : ZMod (2 ^ k)))) +
                  ((2 ^ L' : ℕ) : ZMod (2 ^ k)) := by ring
              have h1 := dvd_val_add_pow_iff (k := k) (d := L') (s := L') (by omega) (le_refl _)
                (x - (r + ((2 ^ L' : ℕ) : ZMod (2 ^ k))))
              rw [← hsub] at h1
              exact h1.symm
          have hsp := coset_split_card (k := k) (L := L') (by omega) r' (S i)
          rw [coset_succ_shift_eq_shell (by omega) r', hcos_eq] at hsp
          have hci := hcos_ge i
          have ho : (S i ∩ shell k L' r').card ≤ 2 ^ (L' + 1) := by
            simpa only [Nat.add_sub_cancel] using hother_le i
          have hpow1 : 2 ^ (L' + 1 + 1) = 2 ^ (L' + 1) + 2 ^ (L' + 1) := by
            rw [pow_succ]; ring
          have hpow_ge : 4 ≤ 2 ^ (L' + 1) :=
            le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega))
          omega
    obtain ⟨r₀, hcos_all, _⟩ := hind L hL2 hLk hm
    have hdisj_cos : (↑(univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint
        fun i => S i ∩ coset k L r₀ := by
      intro i _ j _ hij
      exact (hdisj i j hij).mono inter_subset_left inter_subset_left
    have hsub : (univ.biUnion fun i : Fin 4 => S i ∩ coset k L r₀) ⊆ coset k L r₀ := by
      intro x hx
      obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hx
      exact (mem_inter.mp hxi).2
    have hcard_le : ∑ i : Fin 4, (S i ∩ coset k L r₀).card ≤ 2 ^ (k - L) := by
      rw [← card_biUnion hdisj_cos]
      exact (card_le_card hsub).trans (le_of_eq (coset_card (by omega) r₀))
    rw [Fin.sum_univ_four] at hcard_le
    have h0 := hcos_all 0; have h1 := hcos_all 1; have h2 := hcos_all 2; have h3 := hcos_all 3
    have hpow_ge : 4 ≤ 2 ^ (L + 1) :=
      le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega))
    have h4m : 4 * (m - (2 ^ (L + 1) - 4)) ≤ 2 ^ (k - L) := by omega
    have hdiv : m - (2 ^ (L + 1) - 4) ≤ 2 ^ (k - L) / 4 := by omega
    exact le_trans (by omega) (le_max_right _ _)
  · exact le_trans (by omega) (le_max_left _ _)

/-- **Universal Exponential `m^2 < 3 * 2^k` (`m < √(3 N)`) Theorem (ALL `k ≥ 6`):**
Choosing `L = (k - 2) / 2` in `three_split_non_descending_bound` proves `m ^ 2 < 3 * 2 ^ k`
for EVERY `k ≥ 6` — crushing the characteristic-zero non-descending degree ceiling from linear
`O(N)` down to `O(√N)` across the entire infinite dyadic tower! -/
theorem three_split_sqrt_bound {k m : ℕ} (hk : 6 ≤ k)
    (S : Fin 3 → Finset (ZMod (2 ^ k)))
    (hcard : ∀ i : Fin 3, (S i).card = m)
    (hdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (S i) (S j))
    (hforce : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → DepthLForcing k (S i) (S j) (S l))
    (hno_anti : ∀ i j : Fin 3, i ≠ j → ¬ (isAntipodal k (S i) ∧ isAntipodal k (S j))) :
    m ^ 2 < 3 * 2 ^ k := by
  let L : ℕ := (k - 2) / 2
  have hL2 : 2 ≤ L := by dsimp [L]; omega
  have hLk : L + 2 ≤ k := by dsimp [L]; omega
  have hbound := three_split_non_descending_bound S hcard hdisj hforce hno_anti hL2 hLk
  rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
  · -- Even `k = 2*t` (`t ≥ 3`), `L = t - 1`, `k - L = t + 1`: `m ≤ (5/3)*2^t - 4 < (5/3)*2^t`
    have ht3 : 3 ≤ t := by omega
    have hL_eq : L = t - 1 := by dsimp [L]; omega
    have hk_eq : k = 2 * t := by omega
    have h2t : 2 ^ t ≥ 8 := le_trans (by decide : 8 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by decide) ht3)
    have h2L : 2 ^ (L + 1) = 2 ^ t := by congr 1; omega
    have h2kL : 2 ^ (k - L) = 2 * 2 ^ t := by
      calc 2 ^ (k - L) = 2 ^ (t + 1) := by congr 1; omega
        _ = 2 * 2 ^ t := by rw [pow_succ, mul_comm]
    have h2L_half : 2 * 2 ^ L = 2 ^ t := by rw [← h2L, pow_succ, mul_comm]
    have h3m : 3 * m ≤ 5 * 2 ^ t := by
      rw [h2L, h2kL] at hbound
      unfold depthEntry at hbound
      split_ifs at hbound with h2
      · omega
      · omega
    have hpow2 : 2 ^ k = (2 ^ t) ^ 2 := by rw [hk_eq, mul_comm, pow_mul]
    rw [hpow2]
    nlinarith
  · -- Odd `k = 2*t + 1` (`t ≥ 3`), `L = t - 1`, `k - L = t + 2`: `m ≤ (7/3)*2^t - 4`
    have ht3 : 3 ≤ t := by omega
    have hL_eq : L = t - 1 := by dsimp [L]; omega
    have hk_eq : k = 2 * t + 1 := by omega
    have h2t : 2 ^ t ≥ 8 := le_trans (by decide : 8 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by decide) ht3)
    have h2L : 2 ^ (L + 1) = 2 ^ t := by congr 1; omega
    have h2kL : 2 ^ (k - L) = 4 * 2 ^ t := by
      calc 2 ^ (k - L) = 2 ^ (t + 2) := by congr 1; omega
        _ = 4 * 2 ^ t := by rw [pow_add]; ring
    have h2L_half : 2 * 2 ^ L = 2 ^ t := by rw [← h2L, pow_succ, mul_comm]
    have h3m : 3 * m ≤ 7 * 2 ^ t := by
      rw [h2L, h2kL] at hbound
      unfold depthEntry at hbound
      split_ifs at hbound with h2
      · omega
      · omega
    have hpow2 : 2 ^ k = 2 * (2 ^ t) ^ 2 := by rw [hk_eq, pow_succ, mul_comm 2 t, pow_mul]; ring
    rw [hpow2]
    nlinarith

/-- **Concrete Kernel-Verified Caps Across `μ_64`, `μ_128`, `μ_256`, `μ_{2^29}`, and `μ_{2^30}`:**
- `μ_64` (`k = 6, L = 2`): 3-split `≤ 10`, 4-split `≤ 10` (given `DepthLForcing` + non-descent, ZERO search!).
- `μ_128` (`k = 7, L = 2`): 3-split `≤ 14`, **4-split `≤ 12`** (eliminates `m₀ = 15, h = 1`, the sole
  remaining constant-cross-ratio 4-head pullback on `μ_128`, given the written `DepthLForcing` /
  non-descent instantiation over `p₁` and `p₂` via `mu128-unit-ellipsoid-transfer.md`).
- `μ_256` (`k = 8, L = 3`): 3-split `≤ 22`, 4-split `≤ 20`.
- `μ_{2^29}` (`k = 29, L = 13`): 3-split `≤ 38,225` (so even with `v₂(D) = 1` antipodal descent,
  `2 * 38,225 = 76,450 ≪ 268,435,454`!), 4-split `≤ 32,764`.
- `μ_{2^30}` (`k = 30, L = 14 / 13`): 3-split `≤ 54,609`, 4-split `≤ 49,148 ≪ 134,217,727`! -/
theorem concrete_dyadic_sqrt_caps :
    max (depthEntry 2 - 1) (2 ^ (6 - 2) / 3 + 2 ^ 3 - 4) = 10 ∧
    max (depthEntry 2 - 1) (2 ^ (6 - 2) / 4 + 2 ^ 3 - 4) = 10 ∧
    max (depthEntry 2 - 1) (2 ^ (7 - 2) / 3 + 2 ^ 3 - 4) = 14 ∧
    max (depthEntry 2 - 1) (2 ^ (7 - 2) / 4 + 2 ^ 3 - 4) = 12 ∧
    max (depthEntry 3 - 1) (2 ^ (8 - 3) / 3 + 2 ^ 4 - 4) = 22 ∧
    max (depthEntry 3 - 1) (2 ^ (8 - 3) / 4 + 2 ^ 4 - 4) = 20 ∧
    max (depthEntry 13 - 1) (2 ^ (29 - 13) / 3 + 2 ^ 14 - 4) = 38225 ∧
    max (depthEntry 13 - 1) (2 ^ (29 - 13) / 4 + 2 ^ 14 - 4) = 32764 ∧
    max (depthEntry 14 - 1) (2 ^ (30 - 14) / 3 + 2 ^ 15 - 4) = 54609 ∧
    max (depthEntry 13 - 1) (2 ^ (30 - 13) / 4 + 2 ^ 14 - 4) = 49148 ∧
    2 * 38225 < 268435454 ∧ 49148 < 134217727 := by
  decide

#print axioms coset_card
#print axioms shell_shift_eq
#print axioms coset_succ_shift_eq_shell
#print axioms coset_split_card
#print axioms isAntipodal_of_both_halves
#print axioms periodic_subset_card_dvd
#print axioms three_split_depthL_induction
#print axioms three_split_non_descending_bound
#print axioms four_split_non_descending_bound
#print axioms three_split_sqrt_bound
#print axioms concrete_dyadic_sqrt_caps

end ProximityGap.DyadicSplitPencilSqrtBound

