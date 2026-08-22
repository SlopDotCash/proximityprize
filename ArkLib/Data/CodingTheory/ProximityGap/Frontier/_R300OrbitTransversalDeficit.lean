/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R55Depth3VarianceReformulation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R57Depth3DeviationOrbitBound

/-!
# LANE B2 (#466 round 300): MULTI-ORBIT TRANSVERSAL BOUND + ORBIT-LEVEL CHEBYSHEV
  (strengthening the r57 single-orbit capstone to families)

Round 57 proved the flatness deficit `∑_c d(c)²` dominates `|G|·d(b)²` for a SINGLE
nonzero frequency `b`.  This brick strengthens it to any FAMILY of pairwise
`G`-inequivalent nonzero frequencies (a partial transversal of the orbit quotient
`F^× / G`), and extracts the counting consequence:

* **`deficit_ge_orbit_family`** :  if `R` is a finite set of nonzero frequencies no two of
  which lie on the same multiplicative `G`-orbit, then
  `|G| · ∑_{b∈R} d(b)² ≤ ∑_c d(c)²`  — the orbits are pairwise disjoint, each of exact
  size `|G|`, and `d` is constant on each.
* **`orbit_count_chebyshev`** :  hence at most `(∑_c d(c)²) / (|G|·T²)` orbits can carry a
  period-deviation of magnitude `≥ T`:  `|R| · |G| · T² ≤ ∑_c d(c)²` for any such
  transversal family `R` of `T`-large frequencies.
* **`orbit_count_chebyshev_energy`** :  the same with the round-55 `variance_identity`
  substituted — `|R| · |G| · T² ≤ q·(q·E₃ − |G|⁶)` — the level-set count of large Gauss
  periods pays only the `(q−1)/|G|` effective degrees of freedom, in usable counting form.

This is the standard moment→level-set step of the moment method, machine-checked WITH the
`/|G|` orbit saving (which a naive per-point Chebyshev over `F` loses).  It does not break
the wall (the deficit itself is still the open Paley/BGK object at prize depth), but it is
the correct downstream consumer shape: any future sub-Wick bound on `q·E₃ − |G|⁶` now
converts directly into a large-period orbit count.  Issue #466, round 300, LANE B2.
Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R300OrbitTransversalDeficit

open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment
open ArkLib.ProximityGap.Frontier.R55Depth3VarianceReformulation
open ArkLib.ProximityGap.Frontier.R56RepThreeMultiplicativeInvariance
open ArkLib.ProximityGap.Frontier.R57Depth3DeviationOrbitBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Local re-derivation of the round-56 `rep3_smul`, kept here so this brick does not
depend on the R56/R57 oleans' (toolchain-drifted) instance names. -/
private theorem rep3_smul_local (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a : F} (ha : a ∈ G) (c : F) :
    rep3 G (a * c) = rep3 G c := by
  classical
  have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
  have hainv : a⁻¹ ∈ G := hinv ha
  have hmemA : ∀ x : F, a * x ∈ G ↔ x ∈ G := by
    intro x
    constructor
    · intro hx
      have : a⁻¹ * (a * x) ∈ G := hmul hainv hx
      rwa [← mul_assoc, inv_mul_cancel₀ ha0, one_mul] at this
    · intro hx; exact hmul ha hx
  have hreindex : ∀ f : F → ℕ, ∑ y ∈ G, f (a * y) = ∑ y ∈ G, f y := by
    intro f
    refine Finset.sum_nbij' (i := fun y => a * y) (j := fun y => a⁻¹ * y)
      (fun y hy => (hmemA y).mpr hy) (fun y hy => hmul hainv hy)
      (fun y _ => inv_mul_cancel_left₀ ha0 y)
      (fun y _ => mul_inv_cancel_left₀ ha0 y)
      (fun y _ => rfl)
  unfold rep3
  rw [← hreindex (fun y₁ => ∑ y₂ ∈ G, ∑ y₃ ∈ G, if y₁ + y₂ + y₃ = a * c then 1 else 0)]
  refine Finset.sum_congr rfl (fun y₁ _ => ?_)
  rw [← hreindex (fun y₂ => ∑ y₃ ∈ G, if a * y₁ + y₂ + y₃ = a * c then 1 else 0)]
  refine Finset.sum_congr rfl (fun y₂ _ => ?_)
  rw [← hreindex (fun y₃ => if a * y₁ + a * y₂ + y₃ = a * c then 1 else 0)]
  refine Finset.sum_congr rfl (fun y₃ _ => ?_)
  rw [show a * y₁ + a * y₂ + a * y₃ = a * (y₁ + y₂ + y₃) by ring]
  simp only [mul_right_inj' ha0]

/-- Local re-derivation of the round-57 `deviation_smul` (from `rep3_smul_local`). -/
private theorem deviation_smul_local (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    {a : F} (ha : a ∈ G) (c : F) :
    deviation G (a * c) = deviation G c := by
  unfold deviation
  rw [rep3_smul_local G hmul hinv h0 ha c]

/-- **The multi-orbit transversal bound.**  For a multiplicative subgroup `G` and a family
`R` of nonzero frequencies that are pairwise `G`-inequivalent (no `b' = a·b` with `a ∈ G`),
the flatness deficit dominates `|G|` times the family's total squared deviation: the orbits
`G·b`, `b ∈ R`, are pairwise disjoint, each has exactly `|G|` elements, and the deviation is
constant on each. -/
theorem deficit_ge_orbit_family (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (R : Finset F)
    (hR0 : ∀ b ∈ R, b ≠ 0)
    (hdisj : ∀ b ∈ R, ∀ b' ∈ R, b ≠ b' → ∀ a ∈ G, a * b ≠ b') :
    (G.card : ℝ) * ∑ b ∈ R, (deviation G b) ^ 2 ≤ ∑ c : F, (deviation G c) ^ 2 := by
  classical
  -- each orbit as an image
  set orb : F → Finset F := fun b => G.image (fun a => a * b) with horb
  -- orbits are pairwise disjoint on ↑R
  have hpd : Set.PairwiseDisjoint (↑R : Set F) orb := by
    intro b hb b' hb' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [horb, Finset.mem_image] at hc hc'
    obtain ⟨a, ha, rfl⟩ := hc
    obtain ⟨a', ha', heq⟩ := hc'
    -- a·b = a'·b'  ⟹  b' = (a'⁻¹·a)·b, with a'⁻¹·a ∈ G — contradicting hdisj
    have hmem : a'⁻¹ * a ∈ G := hmul (hinv ha') ha
    have : (a'⁻¹ * a) * b = b' := by
      have ha'0 : a' ≠ 0 := fun h => h0 (h ▸ ha')
      field_simp
      rw [mul_comm a' b', ← heq]; ring
    exact hdisj b hb b' hb' hne (a'⁻¹ * a) hmem this
  -- sum over the union of the orbits
  have hsplit :
      ∑ c ∈ R.biUnion orb, (deviation G c) ^ 2
        = ∑ b ∈ R, ∑ c ∈ orb b, (deviation G c) ^ 2 :=
    Finset.sum_biUnion hpd
  -- each orbit sum equals |G| · d(b)²
  have horbsum : ∀ b ∈ R, ∑ c ∈ orb b, (deviation G c) ^ 2
      = (G.card : ℝ) * (deviation G b) ^ 2 := by
    intro b hb
    have hb0 : b ≠ 0 := hR0 b hb
    have hconst : ∀ c ∈ orb b, (deviation G c) ^ 2 = (deviation G b) ^ 2 := by
      intro c hc
      simp only [horb, Finset.mem_image] at hc
      obtain ⟨a, ha, rfl⟩ := hc
      rw [deviation_smul_local G hmul hinv h0 ha b]
    have hcard : (orb b).card = G.card := by
      rw [horb]
      exact Finset.card_image_of_injective _ (mul_left_injective₀ hb0)
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, nsmul_eq_mul]
  calc (G.card : ℝ) * ∑ b ∈ R, (deviation G b) ^ 2
      = ∑ b ∈ R, (G.card : ℝ) * (deviation G b) ^ 2 := by rw [Finset.mul_sum]
    _ = ∑ b ∈ R, ∑ c ∈ orb b, (deviation G c) ^ 2 :=
        Finset.sum_congr rfl (fun b hb => (horbsum b hb).symm)
    _ = ∑ c ∈ R.biUnion orb, (deviation G c) ^ 2 := hsplit.symm
    _ ≤ ∑ c : F, (deviation G c) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun c _ _ => sq_nonneg _)

/-- **Orbit-level Chebyshev.**  If every frequency in the transversal family `R` carries a
period-deviation of magnitude at least `T`, then `|R| · |G| · T² ≤ ∑_c d(c)²`: the number of
`G`-orbits with `T`-large deviation is at most `(∑_c d(c)²)/(|G|·T²)`. -/
theorem orbit_count_chebyshev (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (R : Finset F)
    (hR0 : ∀ b ∈ R, b ≠ 0)
    (hdisj : ∀ b ∈ R, ∀ b' ∈ R, b ≠ b' → ∀ a ∈ G, a * b ≠ b')
    {T : ℝ} (hT : 0 ≤ T)
    (hbig : ∀ b ∈ R, T ≤ |deviation G b|) :
    (R.card : ℝ) * ((G.card : ℝ) * T ^ 2) ≤ ∑ c : F, (deviation G c) ^ 2 := by
  have hfam := deficit_ge_orbit_family G hmul hinv h0 R hR0 hdisj
  have hlower : (R.card : ℝ) * T ^ 2 ≤ ∑ b ∈ R, (deviation G b) ^ 2 := by
    calc (R.card : ℝ) * T ^ 2 = ∑ _b ∈ R, T ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ R, (deviation G b) ^ 2 := by
          refine Finset.sum_le_sum (fun b hb => ?_)
          have := hbig b hb
          calc T ^ 2 ≤ |deviation G b| ^ 2 := by
                exact pow_le_pow_left₀ hT this 2
            _ = (deviation G b) ^ 2 := sq_abs _
  calc (R.card : ℝ) * ((G.card : ℝ) * T ^ 2)
      = (G.card : ℝ) * ((R.card : ℝ) * T ^ 2) := by ring
    _ ≤ (G.card : ℝ) * ∑ b ∈ R, (deviation G b) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hlower (by positivity)
    _ ≤ ∑ c : F, (deviation G c) ^ 2 := hfam

/-- **Orbit-level Chebyshev, energy form.**  Substituting the round-55 variance identity:
the count of `T`-large-deviation orbits pays only the DC-subtracted depth-3 energy —
`|R| · |G| · T² ≤ q·(q·E₃ − |G|⁶)`. -/
theorem orbit_count_chebyshev_energy (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (R : Finset F)
    (hR0 : ∀ b ∈ R, b ≠ 0)
    (hdisj : ∀ b ∈ R, ∀ b' ∈ R, b ≠ b' → ∀ a ∈ G, a * b ≠ b')
    {T : ℝ} (hT : 0 ≤ T)
    (hbig : ∀ b ∈ R, T ≤ |deviation G b|) :
    (R.card : ℝ) * ((G.card : ℝ) * T ^ 2)
      ≤ (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) * (addEnergy3 G : ℝ) - (G.card : ℝ) ^ 6) := by
  have h := orbit_count_chebyshev G hmul hinv h0 R hR0 hdisj hT hbig
  rwa [show (∑ c : F, (deviation G c) ^ 2)
      = ∑ c : F, ((Fintype.card F : ℝ) * (rep3 G c : ℝ) - (G.card : ℝ) ^ 3) ^ 2 from rfl,
    variance_identity G] at h

end ArkLib.ProximityGap.Frontier.R300OrbitTransversalDeficit

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R300OrbitTransversalDeficit.deficit_ge_orbit_family
#print axioms ArkLib.ProximityGap.Frontier.R300OrbitTransversalDeficit.orbit_count_chebyshev
#print axioms
  ArkLib.ProximityGap.Frontier.R300OrbitTransversalDeficit.orbit_count_chebyshev_energy
