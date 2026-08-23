/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G206DyadicCrossOrbitClassCap
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G209TailFloorPartitionEngine

/-!
# G215: the SHARP dyadic depth-two wall floor — G209/G210 partition floor wired onto the CORE object

G206 (`crossOrbitTail_two_floor`) lower-bounds the depth-`2` cross-orbit tail by the
Cauchy–Schwarz constant `2·n·(n-1)²`, and feeds it into G88's orbit-class Parseval to get the
wall floor `q·(n² + 2(n-1)²) − n⁴ ≤ centeredShadowMass` (`dyadic_wall_floor_two_with_tail`).
G206's own docstring flags that the SHARP integer-partition floor `n²(2n-3)` from G209/G210 is
`~1%` larger but was NOT wired in, because it needs the finer quantisation `S_γ = n·k_γ`.

This file supplies exactly that missing consumer.  Using the mass quantisation
`orbitClassMass g n 2 γ = n · repRF g n 2 (rep γ)` (`orbitClassMass_eq_card_mul`, G88) together
with the G206 class-count cap `card ≤ m`, the occupied depth-`2` masses form the natural profile
`S_γ = n·k_γ` with `k_γ ≥ 1` a positive partition of `n-1`.  Feeding that partition into G209's
`tail_floor_scaled` gives the SHARP cross-orbit tail floor

```text
n²(2n-3) ≤ Σ_γ S_γ²     (`crossOrbitTail_two_floor_sharp`)
```

which is strictly above G206's `2n(n-1)²` for every even `n ≥ 4` (`sharp_gt_cauchy_schwarz`).
Substituting into G88's Parseval (which divides the tail by `n`: the tail enters the wall floor
as `Σ_γ S_γ² / n`) upgrades the wall floor to

```text
q·(n² + n(2n-3)) − n⁴ ≤ centeredShadowMass
```

(`dyadic_wall_floor_two_sharp`), whose cross-orbit contribution `q·n(2n-3)` strictly exceeds
G206's `q·2(n-1)²` for every even `n ≥ 4`; it is the strongest depth-`2` lower bound from the fully
pinned kernel+tail support theory (G182 kernel `S₀=n`, G206 cap, G209 floor, G210 rigidity,
G213 defect).

THINNESS-ESSENTIAL. The `card ≤ n/2` cap is the dyadic `d ↦ n-d` involution (G206), unavailable
to odd-order subgroups; the sharp constant `2n-3` genuinely needs it (without the cap the floor
collapses to the non-realized `n-1`).

SCOPE / no prize claim. This sharpens the depth-`2` wall floor by exactly the G209/G210 partition
constant.  It does NOT bound the signed simultaneous `r=5,6` cyclotomic-class covariance (the
literal BGK object, G214 shows intrinsically two-dimensional), does NOT bound higher-depth `S₀`,
and does NOT close the prize.  CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G215

open Multiset Finset
open ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence
open ArkLib.ProximityGap.Frontier.G206DyadicCrossOrbitClassCap
open ArkLib.ProximityGap.Frontier.G209
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R365CenteredShadowMassWeld
open ArkLib.ProximityGap.Frontier.G182DyadicKernelCeiling

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A canonical nonzero representative of an occupied depth-`2` class.  Membership in
`orbitClassSet` gives some nonkernel `c` with `c^n = γ`; we choose one. -/
noncomputable def classRep (g : F) (n : ℕ) (γ : F) : F :=
  if h : γ ∈ orbitClassSet F n then
    Classical.choose (by
      have := h
      simp only [orbitClassSet, Finset.mem_image] at this
      exact this)
  else 0

theorem classRep_spec (g : F) (n : ℕ) {γ : F} (hγ : γ ∈ orbitClassSet F n) :
    classRep g n γ ∈ nonkernelValues F ∧ (classRep g n γ) ^ n = γ := by
  unfold classRep
  rw [dif_pos hγ]
  have hex : ∃ c ∈ nonkernelValues F, c ^ n = γ := by
    have := hγ
    simp only [orbitClassSet, Finset.mem_image] at this
    obtain ⟨c, hc, hcn⟩ := this
    exact ⟨c, hc, hcn⟩
  exact Classical.choose_spec (by
    have := hγ
    simp only [orbitClassSet, Finset.mem_image] at this
    exact this)

theorem classRep_ne_zero (g : F) (n : ℕ) {γ : F} (hγ : γ ∈ orbitClassSet F n) :
    classRep g n γ ≠ 0 := by
  have h := (classRep_spec g n hγ).1
  simp only [nonkernelValues, Finset.mem_filter] at h
  exact h.2

/-- The natural depth-`2` multiplicity of an occupied class: `S_γ = n · natMult γ`. -/
noncomputable def natMult (g : F) (n : ℕ) (γ : F) : ℕ := repRF g n 2 (classRep g n γ)

/-- Mass quantisation on an occupied class: `orbitClassMass g n 2 γ = n · natMult γ`. -/
theorem orbitClassMass_eq_natMult (g : F) (n : ℕ) (hg0 : g ≠ 0) (hn : 0 < n)
    (hord : orderOf g = n) {γ : F} (hγ : γ ∈ orbitClassSet F n) :
    orbitClassMass g n 2 γ = (n : ℝ) * (natMult g n γ : ℝ) := by
  have hspec := classRep_spec g n hγ
  have hc0 : classRep g n γ ≠ 0 := classRep_ne_zero g n hγ
  have hcn : (classRep g n γ) ^ n = γ := hspec.2
  have := orbitClassMass_eq_card_mul g n 2 hg0 hn hord hc0
  rw [hcn] at this
  rw [this]
  rfl

/-- On an occupied class the natural multiplicity is positive (`k_γ ≥ 1`). -/
theorem natMult_pos (g : F) (n : ℕ) (hg0 : g ≠ 0) (hn : 0 < n) (hord : orderOf g = n)
    {γ : F} (hγ : γ ∈ occupiedDepth2Classes g n) : 1 ≤ natMult g n γ := by
  simp only [occupiedDepth2Classes, Finset.mem_filter] at hγ
  obtain ⟨hset, hpos⟩ := hγ
  have hmass := orbitClassMass_eq_natMult g n hg0 hn hord hset
  rw [hmass] at hpos
  rcases Nat.eq_zero_or_pos (natMult g n γ) with h0 | hpos'
  · rw [h0] at hpos; simp at hpos
  · exact hpos'

/-- The natural depth-`2` profile of the occupied classes, as a `Multiset ℕ`. -/
noncomputable def natProfile (g : F) (n : ℕ) : Multiset ℕ :=
  (occupiedDepth2Classes g n).val.map (natMult g n)

theorem natProfile_card (g : F) (n : ℕ) :
    (natProfile g n).card = (occupiedDepth2Classes g n).card := by
  unfold natProfile
  rw [Multiset.card_map, Finset.card_def]

/-- Every part of the natural profile is positive. -/
theorem natProfile_pos (g : F) (n : ℕ) (hg0 : g ≠ 0) (hn : 0 < n) (hord : orderOf g = n) :
    ∀ k ∈ natProfile g n, 1 ≤ k := by
  intro k hk
  unfold natProfile at hk
  rw [Multiset.mem_map] at hk
  obtain ⟨γ, hγ, rfl⟩ := hk
  have hγ' : γ ∈ occupiedDepth2Classes g n := by
    rwa [← Finset.mem_def] at hγ
  exact natMult_pos g n hg0 hn hord hγ'

/-- The natural profile sums to `n - 1`.  Follows from the real mass identity
`Σ_γ n·k_γ = n² - n = n·(n-1)` by cancelling `n`. -/
theorem natProfile_sum (g : F) (n m : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (natProfile g n).sum = n - 1 := by
  have hn0 : 0 < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  -- Real mass sum over occupied classes = n² - n.
  have hmass := sum_occupied_orbitClassMass_two g n m hm hn hg hord
  -- Rewrite each occupied mass as n · natMult.
  have hrw : ∑ γ ∈ occupiedDepth2Classes g n, orbitClassMass g n 2 γ
      = ∑ γ ∈ occupiedDepth2Classes g n, (n : ℝ) * (natMult g n γ : ℝ) := by
    refine Finset.sum_congr rfl (fun γ hγ => ?_)
    have hset : γ ∈ orbitClassSet F n := by
      simp only [occupiedDepth2Classes, Finset.mem_filter] at hγ
      exact hγ.1
    exact orbitClassMass_eq_natMult g n hg0 hn0 hord hset
  rw [hrw, ← Finset.mul_sum] at hmass
  -- So n · (Σ natMult) = n² - n = n·(n-1), cancel n.
  have hnat : (∑ γ ∈ occupiedDepth2Classes g n, (natMult g n γ : ℝ))
      = ((n : ℝ) - 1) := by
    have hfac : (n : ℝ) ^ 2 - (n : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by ring
    rw [hfac] at hmass
    exact (mul_left_cancel₀ (ne_of_gt hnpos) hmass)
  -- Transfer the real class-sum to the multiset natural sum.
  have hprofsum : (natProfile g n).sum = ∑ γ ∈ occupiedDepth2Classes g n, natMult g n γ := by
    unfold natProfile Finset.sum
    rfl
  have hsumcast : ((natProfile g n).sum : ℝ)
      = ∑ γ ∈ occupiedDepth2Classes g n, (natMult g n γ : ℝ) := by
    rw [hprofsum, Nat.cast_sum]
  have hn1 : ((natProfile g n).sum : ℝ) = ((n - 1 : ℕ) : ℝ) := by
    rw [hsumcast, hnat]
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]
  exact_mod_cast hn1

/-- Cardinality cap on the natural profile (G206). -/
theorem natProfile_card_le (g : F) (n m : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (natProfile g n).card ≤ n / 2 := by
  rw [natProfile_card]
  have hc := occupiedDepth2Classes_card_le_half g n m hg0 hord hm hn hg
  have : n / 2 = m := by omega
  rw [this]; exact hc

/-- The natural sum of squares of the profile, as a `ℕ`. -/
noncomputable def natProfileSumSq (g : F) (n : ℕ) : ℕ := ((natProfile g n).map (· ^ 2)).sum

theorem natProfileSumSq_eq (g : F) (n : ℕ) :
    natProfileSumSq g n = ∑ γ ∈ occupiedDepth2Classes g n, (natMult g n γ) ^ 2 := by
  unfold natProfileSumSq natProfile Finset.sum
  rw [Multiset.map_map]
  rfl

/-- The real cross-orbit sq-sum equals `n² · (Σ k²)` over the natural profile. -/
theorem sum_sq_eq_natProfile (g : F) (n : ℕ) (hg0 : g ≠ 0) (hn : 0 < n) (hord : orderOf g = n) :
    ∑ γ ∈ orbitClassSet F n, orbitClassMass g n 2 γ ^ 2
      = (n : ℝ) ^ 2 * ((natProfileSumSq g n : ℕ) : ℝ) := by
  -- Restrict to occupied classes (zero-mass terms drop).
  have hsplit : ∑ γ ∈ orbitClassSet F n, orbitClassMass g n 2 γ ^ 2
      = ∑ γ ∈ occupiedDepth2Classes g n, orbitClassMass g n 2 γ ^ 2 := by
    unfold occupiedDepth2Classes
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    by_cases hpos : 0 < orbitClassMass g n 2 γ
    · rw [if_pos hpos]
    · rw [if_neg hpos]
      have hnonneg : 0 ≤ orbitClassMass g n 2 γ := by
        unfold orbitClassMass
        exact Finset.sum_nonneg fun c _ => by positivity
      have hz : orbitClassMass g n 2 γ = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
      rw [hz]; ring
  rw [hsplit]
  -- Rewrite each occupied mass square as (n·k_γ)² = n²·k_γ².
  have hrw : ∑ γ ∈ occupiedDepth2Classes g n, orbitClassMass g n 2 γ ^ 2
      = ∑ γ ∈ occupiedDepth2Classes g n, (n : ℝ) ^ 2 * ((natMult g n γ : ℝ) ^ 2) := by
    refine Finset.sum_congr rfl (fun γ hγ => ?_)
    have hset : γ ∈ orbitClassSet F n := by
      simp only [occupiedDepth2Classes, Finset.mem_filter] at hγ
      exact hγ.1
    rw [orbitClassMass_eq_natMult g n hg0 hn hord hset]
    ring
  rw [hrw, ← Finset.mul_sum]
  -- Real form of the RHS: n² * (cast of the nat map-sum).
  congr 1
  rw [natProfileSumSq_eq]
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  push_cast
  ring

/-- **SHARP depth-`2` cross-orbit tail floor.**  Using the mass quantisation `S_γ = n·k_γ` and
the G206 class-count cap, the occupied natural profile is a positive partition of `n-1` with at
most `m = n/2` parts, so G209's `tail_floor_scaled` gives the sharp integer-partition floor
`n²(2n-3) ≤ Σ_γ S_γ²`, strictly above G206's Cauchy–Schwarz constant `2n(n-1)²`. -/
theorem crossOrbitTail_two_floor_sharp (g : F) (n m : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (n : ℝ) ^ 2 * (2 * (n : ℝ) - 3) ≤
      ∑ γ ∈ orbitClassSet F n, orbitClassMass g n 2 γ ^ 2 := by
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  have heven : Even n := ⟨m, by omega⟩
  -- Pure-ℕ floor from G209 on the natural profile.
  have hfloor : n ^ 2 * (2 * n) ≤ n ^ 2 * natProfileSumSq g n + 3 * n ^ 2 :=
    tail_floor_scaled n hn2 heven (natProfile g n)
      (natProfile_pos g n hg0 hn0 hord)
      (natProfile_sum g n m hg0 hord hm hn hg)
      (natProfile_card_le g n m hg0 hord hm hn hg)
  -- Cast the pure-ℕ floor to ℝ and reshape to n²(2n-3) ≤ n² * Q.
  have hfloorR : (n : ℝ) ^ 2 * (2 * (n : ℝ))
      ≤ (n : ℝ) ^ 2 * ((natProfileSumSq g n : ℕ) : ℝ) + 3 * (n : ℝ) ^ 2 := by
    have hc : ((n ^ 2 * (2 * n) : ℕ) : ℝ)
        ≤ ((n ^ 2 * natProfileSumSq g n + 3 * n ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hfloor
    push_cast at hc
    linarith
  rw [sum_sq_eq_natProfile g n hg0 hn0 hord]
  nlinarith [hfloorR]

/-- The sharp floor is strictly larger than G206's Cauchy–Schwarz floor for every even `n ≥ 4`:
`2n(n-1)² < n²(2n-3)`  ⟺  `n < n²` (true for `n ≥ 2`), the `~1%` gap. -/
theorem sharp_gt_cauchy_schwarz (n : ℕ) (hn : 4 ≤ n) :
    (2 : ℝ) * (n : ℝ) * ((n : ℝ) - 1) ^ 2 < (n : ℝ) ^ 2 * (2 * (n : ℝ) - 3) := by
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [hnR]

/-- **SHARP dyadic depth-`2` wall floor.**  Feeding `S₀ = n` (G182) and the SHARP cross-orbit
tail floor `n²(2n-3)` into G88's orbit-class Parseval yields the strongest depth-`2` wall floor
available from the pinned support theory: the cross classes contribute `q·n²(2n-3)` instead of
G206's weaker `q·2(n-1)²`. -/
theorem dyadic_wall_floor_two_sharp (g : F) (n m : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (Fintype.card F : ℝ) * ((n : ℝ) ^ 2 + (n : ℝ) * (2 * (n : ℝ) - 3)) - (n : ℝ) ^ 4 ≤
      centeredShadowMass g n m 2 := by
  have hn0 : 0 < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hpar := centeredShadowMass_orbitClassParseval g n m 2 hg0 hord hm hn hg
  have hS0 : (repRF g n 2 0 : ℝ) = (n : ℝ) := by
    have := repRF_two_zero_eq g n m hm hn hg hord
    exact_mod_cast this
  rw [hS0] at hpar
  have htail := crossOrbitTail_two_floor_sharp g n m hg0 hord hm hn hg
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  have hpow : (n : ℝ) ^ (2 * 2) = (n : ℝ) ^ 4 := by norm_num
  rw [hpow] at hpar
  have hqtail : (Fintype.card F : ℝ) * ((n : ℝ) ^ 2 * (2 * (n : ℝ) - 3))
      ≤ (Fintype.card F : ℝ) * ∑ γ ∈ orbitClassSet F n, orbitClassMass g n 2 γ ^ 2 :=
    mul_le_mul_of_nonneg_left htail hq
  have hkey : (n : ℝ) * ((Fintype.card F : ℝ) * ((n : ℝ) ^ 2 + (n : ℝ) * (2 * (n : ℝ) - 3))
        - (n : ℝ) ^ 4) ≤ (n : ℝ) * centeredShadowMass g n m 2 := by
    rw [hpar]
    nlinarith [hqtail, hnpos, hq]
  exact le_of_mul_le_mul_left hkey hnpos

#print axioms orbitClassMass_eq_natMult
#print axioms crossOrbitTail_two_floor_sharp
#print axioms sharp_gt_cauchy_schwarz
#print axioms dyadic_wall_floor_two_sharp

end ArkLib.ProximityGap.Frontier.G215
