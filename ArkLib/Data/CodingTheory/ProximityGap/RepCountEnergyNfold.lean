/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetInvariance
import ArkLib.Data.CodingTheory.ProximityGap.SmoothCubicSupplyBound

/-!
# THE ADDITIVE ENERGY IS `n`-FOLD STRUCTURED OFF THE DIAGONAL (#389)

The coset-invariance `repCount_mul_mem_eq` (r is constant on multiplicative cosets `c·μ_n`)
forces the additive energy to be `n`-fold structured away from `c = 0`:

> **`n_dvd_energy_offDiag`** — `n ∣ (E(G) − r(0)²)`, i.e. the `c ≠ 0` part of the energy
> `Σ_{c≠0} r(c)²` is divisible by `n`.

Proof: group `F^×` by the `n`-th power map `s ↦ sⁿ`.  Each nonempty fibre is a full
multiplicative coset `s₀·μ_n` of size `n` (bijection `ζ ↦ s₀ζ`), on which `r²` is constant
(coset-invariance) — so each fibre contributes `n·(value)`, and the whole `c≠0` sum is
`n·Σ_{fibres} (value)`.

Concretely: the Garcia–Voloch energy `E(μ_n) = Σ_c r(c)²` — the object the δ* supply wall
reduces to — needs only its `(|F|−1)/n` coset values, and they enter with multiplicity
exactly `n`.  This is the `n`-fold reduction of the GV obligation made into a divisibility
theorem.  Issue #389.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- For `h` in the image of the `n`-th power map over `F^×`, the fibre
`{s ≠ 0 : sⁿ = h}` is a coset of `G = μ_n`, hence has cardinality `n`, and `r²` is constant
on it — so the fibre sum is `n · r(s₀)²`. -/
theorem fiber_sum_repCount_sq {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hGcard : G.card = n) (h : F) :
    n ∣ ∑ s ∈ (Finset.univ.filter (fun s : F => s ≠ 0 ∧ s ^ n = h)),
      repCount G s ^ 2 := by
  classical
  rcases Finset.eq_empty_or_nonempty
    (Finset.univ.filter (fun s : F => s ≠ 0 ∧ s ^ n = h)) with he | ⟨s₀, hs₀⟩
  · rw [he, Finset.sum_empty]; exact dvd_zero n
  · obtain ⟨hs₀0, hs₀n⟩ := Finset.mem_filter.mp hs₀ |>.2
    -- the fibre is exactly the coset `s₀·G`
    have hfib : (Finset.univ.filter (fun s : F => s ≠ 0 ∧ s ^ n = h))
        = G.image (fun ζ => s₀ * ζ) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨hs0, hsn⟩
        have hh0 : h ≠ 0 := hs₀n ▸ pow_ne_zero n hs₀0
        refine ⟨s * s₀⁻¹, ?_, by field_simp⟩
        rw [hGmem, mul_pow, inv_pow, hsn, hs₀n]
        exact mul_inv_cancel₀ hh0
      · rintro ⟨ζ, hζ, rfl⟩
        have hζn : ζ ^ n = 1 := (hGmem ζ).mp hζ
        have hζ0 : ζ ≠ 0 := by
          intro h0; rw [h0, zero_pow (by omega : n ≠ 0)] at hζn; exact zero_ne_one hζn
        exact ⟨mul_ne_zero hs₀0 hζ0, by rw [mul_pow, hζn, mul_one, hs₀n]⟩
    rw [hfib]
    -- `r²` constant on the coset (coset-invariance), and `|s₀·G| = n`
    rw [Finset.sum_image (fun a _ b _ hab => mul_left_cancel₀ hs₀0 hab)]
    have hconst : ∀ ζ ∈ G, repCount G (s₀ * ζ) ^ 2 = repCount G s₀ ^ 2 := by
      intro ζ hζ; rw [repCount_mul_mem_eq hn hGmem s₀ hζ]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hGcard, smul_eq_mul]
    exact Dvd.intro _ rfl

/-- **THE `n`-FOLD STRUCTURE**: `n ∣ Σ_{s ≠ 0} r(s)²` — the off-diagonal additive energy
of `G = μ_n` is divisible by `n`. -/
theorem n_dvd_sum_repCount_sq_offDiag {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hGcard : G.card = n) :
    n ∣ ∑ s ∈ (Finset.univ.filter (fun s : F => s ≠ 0)), repCount G s ^ 2 := by
  classical
  -- group `F^×` by the `n`-th power map; each fibre sum is divisible by `n`
  set s₀ := Finset.univ.filter (fun s : F => s ≠ 0) with hs0
  set t := s₀.image (fun s => s ^ n) with ht
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun s => s ^ n) (t := t)
    (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.dvd_sum (fun h _ => ?_)
  have hsub : (s₀.filter (fun s => s ^ n = h))
      = Finset.univ.filter (fun s : F => s ≠ 0 ∧ s ^ n = h) := by
    ext s; simp only [hs0, Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
  rw [hsub]
  exact fiber_sum_repCount_sq hn hGmem hGcard h

/-- **The energy off-diagonal is `n`-fold** (energy form): `n ∣ (E(G) − r(0)²)`. -/
theorem n_dvd_energy_offDiag {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hGcard : G.card = n) :
    n ∣ (additiveEnergy G - repCount G 0 ^ 2) := by
  classical
  have hsplit : additiveEnergy G
      = repCount G 0 ^ 2 + ∑ s ∈ (Finset.univ.filter (fun s : F => s ≠ 0)),
          repCount G s ^ 2 := by
    rw [additiveEnergy_eq_sum_repCount_sq,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : F => s = 0)
        (fun s => repCount G s ^ 2)]
    congr 1
    rw [Finset.filter_eq' Finset.univ (0 : F), if_pos (Finset.mem_univ 0),
      Finset.sum_singleton]
  rw [hsplit, Nat.add_sub_cancel_left]
  exact n_dvd_sum_repCount_sq_offDiag hn hGmem hGcard

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.fiber_sum_repCount_sq
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.n_dvd_energy_offDiag
