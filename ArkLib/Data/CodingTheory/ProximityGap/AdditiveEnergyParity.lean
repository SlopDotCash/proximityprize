/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyResultant

/-!
# Parity of the BGK prize kernel via the inversion involution (#232)

A new structural constraint on the open additive-energy intersection count
`M = bgkCount n = #{u ∈ μ_n : -(1+u) ∈ μ_n}` (for even `n`): **its parity is completely
determined**, namely `M` is odd iff `(2:F)^n = 1`.

The mechanism is the involution `u ↦ u⁻¹`. The key observations:

* `bgkSet_inv_closed` — the kernel set is closed under `u ↦ u⁻¹`. Indeed `u ∈ μ_n ⟹ u⁻¹ ∈ μ_n`,
  and `-(1+u⁻¹) = -(1+u)·u⁻¹` is a product of two elements of `μ_n`, hence in `μ_n`.
* The only possible fixed point of `u ↦ u⁻¹` in the kernel is `u = 1`: `u⁻¹ = u ⟹ u² = 1 ⟹
  u ∈ {1, -1}`, and `u = -1` would force `-(1+(-1)) = 0 ∈ μ_n`, impossible. And `u = 1` lies in the
  kernel iff `-(1+1) = -2 ∈ μ_n`, i.e. iff `(2:F)^n = 1`.

Since the non-fixed points pair into 2-cycles, `M ≡ #{fixed points} [MOD 2]`, giving
`odd_bgkCount_iff`. The general counting principle is isolated as `card_filter_fixed_modEq_card_of_involutive`.

**Consequence (sharpens the prize cartography).** Combined with `AdditiveEnergyChar0` (M = 0 in
characteristic 0) and `AdditiveEnergyFermat` (over prime characteristic `p`, `(2:F)^n = 1` for
`n = 2^k` iff `p` divides a Fermat number `F_j`, `j < k`):

* in characteristic `p` with `n = 2^k`, **`M` is odd iff `p` divides one of `F_0, …, F_{k−1}`** — so
  whenever a "Fermat-bad" prime is the characteristic, the additive energy is forced **odd**, hence
  **nonzero**, and the prize cell provably breaks;
* for every **other** characteristic, `M` is **even** — so the kernel cannot be exactly `1`; the
  obstruction, if present at all, comes in pairs `{u, u⁻¹}`.

Axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyKernel

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Involution parity on a Finset.** If `f` is an involution mapping `s` into itself, then the
number of its fixed points in `s` has the same parity as `|s|`: the non-fixed points pair up into
2-cycles `{x, f x}`. Proved by strong induction, peeling a fixed point (both counts drop by one) or
a 2-cycle (`|s|` drops by two, the fixed count is unchanged). -/
theorem card_filter_fixed_modEq_card_of_involutive {α : Type*} [DecidableEq α] (f : α → α)
    (hinv : Function.Involutive f) :
    ∀ s : Finset α, (∀ x ∈ s, f x ∈ s) →
      (s.filter fun x => f x = x).card ≡ s.card [MOD 2] := by
  intro s
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro hmem
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · rfl
    by_cases hfx : f x = x
    · -- `x` is a fixed point: erase it, both sides drop by one
      have hsub : s.erase x ⊂ s := Finset.erase_ssubset hx
      have hmem' : ∀ y ∈ s.erase x, f y ∈ s.erase x := by
        intro y hy
        rw [Finset.mem_erase] at hy ⊢
        refine ⟨fun h => hy.1 (by rw [← hinv y, h, hfx]), hmem y hy.2⟩
      have IH := ih (s.erase x) hsub hmem'
      have hxmem : x ∈ s.filter (fun z => f z = z) := Finset.mem_filter.mpr ⟨hx, hfx⟩
      have hfe : (s.filter fun z => f z = z)
          = insert x ((s.erase x).filter fun z => f z = z) := by
        rw [Finset.filter_erase]; exact (Finset.insert_erase hxmem).symm
      have hxnm : x ∉ (s.erase x).filter fun z => f z = z := by
        rw [Finset.mem_filter, Finset.mem_erase]; rintro ⟨⟨h, _⟩, _⟩; exact h rfl
      have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨x, hx⟩
      have hcard : s.card = (s.erase x).card + 1 := by
        rw [Finset.card_erase_of_mem hx]; omega
      rw [hfe, Finset.card_insert_of_notMem hxnm, hcard]
      exact Nat.ModEq.add_right 1 IH
    · -- `x` is not fixed: erase the 2-cycle `{x, f x}`, `|s|` drops by two, fixed count unchanged
      have hfxs : f x ∈ s := hmem x hx
      have hffx : f (f x) = x := hinv x
      set s' := (s.erase x).erase (f x) with hs'
      have hfxe : f x ∈ s.erase x := Finset.mem_erase.mpr ⟨hfx, hfxs⟩
      have hsub : s' ⊂ s :=
        Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset _ _) (Finset.erase_ssubset hx)
      have hmem' : ∀ y ∈ s', f y ∈ s' := by
        intro y hy
        rw [hs', Finset.mem_erase, Finset.mem_erase] at hy ⊢
        obtain ⟨hyfx, hyx, hys⟩ := hy
        refine ⟨fun h => hyx (by rw [← hinv y, h, hinv]), fun h => hyfx (by rw [← hinv y, h]),
          hmem y hys⟩
      have IH := ih s' hsub hmem'
      have hxnm2 : x ∉ s.filter (fun z => f z = z) := by
        rw [Finset.mem_filter]; rintro ⟨_, h⟩; exact hfx h
      have hfxnm : f x ∉ (s.filter (fun z => f z = z)).erase x := by
        rw [Finset.mem_erase, Finset.mem_filter]; rintro ⟨_, _, h⟩; rw [hffx] at h; exact hfx h.symm
      have hfilt : (s.filter fun z => f z = z) = s'.filter fun z => f z = z := by
        rw [hs', Finset.filter_erase, Finset.filter_erase,
          Finset.erase_eq_of_notMem hfxnm, Finset.erase_eq_of_notMem hxnm2]
      have hcard : s.card = s'.card + 2 := by
        rw [hs', Finset.card_erase_of_mem hfxe, Finset.card_erase_of_mem hx]
        have h2 : 2 ≤ s.card := Finset.one_lt_card.mpr ⟨f x, hfxs, x, hx, hfx⟩
        omega
      rw [hfilt, hcard]
      calc (s'.filter fun z => f z = z).card
          ≡ s'.card [MOD 2] := IH
        _ ≡ s'.card + 2 [MOD 2] := (Nat.modEq_iff_dvd' (by omega)).mpr ⟨1, by omega⟩

/-- **The BGK kernel is closed under inversion.** If `u ∈ μ_n` and `-(1+u) ∈ μ_n`, then `u⁻¹ ∈ μ_n`
and `-(1+u⁻¹) ∈ μ_n` (using `-(1+u⁻¹) = -(1+u)·u⁻¹`, a product of two `μ_n` elements). -/
theorem bgkSet_inv_closed {n : ℕ} (hn : 0 < n) :
    ∀ u ∈ (nthRootsFinset n (1:F)).filter (fun u => -(1+u) ∈ nthRootsFinset n (1:F)),
      u⁻¹ ∈ (nthRootsFinset n (1:F)).filter (fun u => -(1+u) ∈ nthRootsFinset n (1:F)) := by
  intro u hu
  rw [Finset.mem_filter] at hu ⊢
  obtain ⟨hu1, hu2⟩ := hu
  rw [mem_nthRootsFinset hn] at hu1 hu2
  have hune : u ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hu1; exact zero_ne_one hu1
  refine ⟨?_, ?_⟩
  · rw [mem_nthRootsFinset hn, inv_pow, hu1, inv_one]
  · rw [mem_nthRootsFinset hn]
    have hkey : -(1 + u⁻¹) = -(1 + u) * u⁻¹ := by field_simp; ring
    rw [hkey, mul_pow, hu2, inv_pow, hu1, inv_one, mul_one]

/-- **Parity of the BGK kernel count.** For even `n > 0`, the additive-energy intersection count
`M = bgkCount n` is **odd iff `(2:F)^n = 1`** (i.e. iff `char F ∣ 2^n − 1`). The involution
`u ↦ u⁻¹` fixes the kernel set (`bgkSet_inv_closed`) and its only possible fixed point is `u = 1`
(present iff `(2:F)^n = 1`, since `u = -1` would force `0 ∈ μ_n`); the non-fixed points pair into
2-cycles, so the parity of `M` is exactly the indicator of the `u = 1` solution. -/
theorem odd_bgkCount_iff {n : ℕ} (hn : 0 < n) (hne : Even n) :
    Odd (bgkCount (F := F) n) ↔ (2 : F) ^ n = 1 := by
  set S := (nthRootsFinset n (1:F)).filter (fun u => -(1+u) ∈ nthRootsFinset n (1:F)) with hS
  have hbgk : bgkCount (F := F) n = S.card := rfl
  have hpar : (S.filter (fun u => u⁻¹ = u)).card ≡ S.card [MOD 2] :=
    card_filter_fixed_modEq_card_of_involutive (fun u : F => u⁻¹) (fun u => inv_inv u) S
      (by intro u hu; rw [hS] at hu ⊢; exact bgkSet_inv_closed hn u hu)
  -- the inverse-fixed subset is contained in `{1}`
  have hsub1 : S.filter (fun u => u⁻¹ = u) ⊆ {1} := by
    intro u hu
    rw [Finset.mem_filter, hS, Finset.mem_filter] at hu
    obtain ⟨⟨huμ, huS⟩, hinveq⟩ := hu
    rw [mem_nthRootsFinset hn] at huμ huS
    have hune : u ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at huμ; exact zero_ne_one huμ
    have husq : u * u = 1 := by have := mul_inv_cancel₀ hune; rwa [hinveq] at this
    have hfac : (u - 1) * (u + 1) = 0 := by linear_combination husq
    rcases mul_eq_zero.mp hfac with h | h
    · rw [Finset.mem_singleton]; linear_combination h
    · exfalso
      have h0 : -(1 + u) = 0 := by linear_combination -h
      rw [h0, zero_pow hn.ne'] at huS
      exact zero_ne_one huS
  -- `1` lies in the inverse-fixed subset iff `(2:F)^n = 1`
  have h1iff : (1:F) ∈ S.filter (fun u => u⁻¹ = u) ↔ (2:F)^n = 1 := by
    rw [Finset.mem_filter, inv_one, and_iff_left (rfl : (1:F) = 1), hS, Finset.mem_filter,
      mem_nthRootsFinset hn, mem_nthRootsFinset hn, one_pow, and_iff_right (rfl : (1:F) = 1),
      show -(1 + 1 : F) = -(2:F) by norm_num, neg_pow, hne.neg_one_pow, one_mul]
  -- parity of the fixed-point count
  have hoddfix : Odd (S.filter (fun u => u⁻¹ = u)).card ↔ (2:F)^n = 1 := by
    rcases Finset.subset_singleton_iff.mp hsub1 with h | h
    · rw [h, Finset.card_empty]
      refine ⟨fun hc => absurd hc (by decide), fun h2 => ?_⟩
      exact absurd (h ▸ h1iff.mpr h2) (Finset.notMem_empty _)
    · rw [h, Finset.card_singleton]
      exact ⟨fun _ => h1iff.mp (h ▸ Finset.mem_singleton_self 1), fun _ => odd_one⟩
  rw [hbgk, ← hoddfix, Nat.odd_iff, Nat.odd_iff, (hpar : _ % 2 = _ % 2)]

/-- **Even-characteristic-free survival pairing.** If `(2:F)^n ≠ 1` (the characteristic is not a
"Mersenne/Fermat-bad" prime), then `bgkCount n` is even — the kernel solutions, if any, come in
inverse pairs `{u, u⁻¹}`. -/
theorem even_bgkCount_of_two_pow_ne_one {n : ℕ} (hn : 0 < n) (hne : Even n)
    (h2 : (2 : F) ^ n ≠ 1) : Even (bgkCount (F := F) n) := by
  rcases Nat.even_or_odd (bgkCount (F := F) n) with he | ho
  · exact he
  · exact absurd ((odd_bgkCount_iff hn hne).mp ho) h2

end ArkLib.ProximityGap.AdditiveEnergyKernel

#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.odd_bgkCount_iff
#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.even_bgkCount_of_two_pow_ne_one
