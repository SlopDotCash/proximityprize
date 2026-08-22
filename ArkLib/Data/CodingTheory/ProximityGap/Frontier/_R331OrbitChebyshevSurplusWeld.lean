/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R303GeneralROrbitChebyshev
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R310ShadowFloorToRFoldEnergy

/-!
# LANE B2 (#466 round 331): ORBIT CHEBYSHEV × SHADOW SURPLUS — the level-set count pays
  only the collision mass

Weld of the two landed arcs:

* R303 (`orbit_count_chebyshev_energy`): for any pairwise `G`-inequivalent family `R` of
  `T`-large depth-`r` deviations, `|R|·|G|·T² ≤ q·(q·E_r − |G|^{2r})`;
* R310 (`shadowEnergy_le_rEnergy_real_of_repIdentifies`): `E_r = shadowEnergy + surplus`,
  where `shadowEnergy n m r` is the EXACT char-0 quantity (computable, prime-independent)
  and the surplus is the mod-`p` collision mass (the r312–r321 kernel-relation object).

Composition: **the count of `T`-large-deviation orbits is controlled by the char-0 shadow
energy plus ANY bound `S` on the collision surplus** —

```text
|R| · |G| · T²  ≤  q·(q·(shadowEnergy n m r + S) − |G|^{2r}).
```

The char-0 term is a closed-form constant of `(n, r)`; every prime-dependent unknown in the
depth-`r` level-set count is now formally isolated in the single scalar `S` — exactly the
quantity the kernel-relation mass arc (r312–r321) decomposes and the census (r305)
computes at small `n`.  Does not touch the wall (bounding `S` uniformly at prize depth IS
the wall); it is the final consumer weld of the shadow programme.  Issue #466, round 331,
LANE B2.  Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R331OrbitChebyshevSurplusWeld

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance
open ArkLib.ProximityGap.Frontier.R303GeneralROrbitChebyshev
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The abstract weld**: an orbit-level Chebyshev count in which the depth-`r` energy has
been replaced by `char-0 shadow + surplus bound S`.  All prime-dependence of the level-set
count is isolated in `S`. -/
theorem orbit_count_le_shadow_plus_surplus (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (n m r : ℕ) (S : ℝ)
    (hsurplus : (rEnergy G r : ℝ) ≤ (shadowEnergy n m r : ℝ) + S)
    (Rset : Finset F)
    (hR0 : ∀ b ∈ Rset, b ≠ 0)
    (hdisj : ∀ b ∈ Rset, ∀ b' ∈ Rset, b ≠ b' → ∀ a ∈ G, a * b ≠ b')
    {T : ℝ} (hT : 0 ≤ T)
    (hbig : ∀ b ∈ Rset, T ≤ |R303GeneralROrbitChebyshev.deviationR G r b|) :
    (Rset.card : ℝ) * ((G.card : ℝ) * T ^ 2)
      ≤ (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) * ((shadowEnergy n m r : ℝ) + S)
            - (G.card : ℝ) ^ (2 * r)) := by
  have h := orbit_count_chebyshev_energy G hmul hinv h0 r Rset hR0 hdisj hT hbig
  refine le_trans h ?_
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hq
  have := mul_le_mul_of_nonneg_left hsurplus hq
  linarith

/-- **The concrete weld** (power-root instantiation): with `g` of order `n = 2m`,
`g^m = -1`, and the R310 representation identification, the SAME bound holds with the
surplus hypothesis stated directly as a bound on the collision mass
`E_r − shadowEnergy`. -/
theorem orbit_count_le_shadow_plus_surplus_of_repIdentifies
    (g : F) (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (n m r : ℕ) (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (hrep : PowerShadowRepIdentifies g G n r)
    (S : ℝ)
    (hS : (rEnergy G r : ℝ) - (shadowEnergy n m r : ℝ) ≤ S)
    (Rset : Finset F)
    (hR0 : ∀ b ∈ Rset, b ≠ 0)
    (hdisj : ∀ b ∈ Rset, ∀ b' ∈ Rset, b ≠ b' → ∀ a ∈ G, a * b ≠ b')
    {T : ℝ} (hT : 0 ≤ T)
    (hbig : ∀ b ∈ Rset, T ≤ |R303GeneralROrbitChebyshev.deviationR G r b|) :
    (Rset.card : ℝ) * ((G.card : ℝ) * T ^ 2)
      ≤ (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) * ((shadowEnergy n m r : ℝ) + S)
            - (G.card : ℝ) ^ (2 * r)) := by
  have hfloor : (shadowEnergy n m r : ℝ) ≤ (rEnergy G r : ℝ) :=
    shadowEnergy_le_rEnergy_real_of_repIdentifies g G n m r hm hn hg hrep
  exact orbit_count_le_shadow_plus_surplus G hmul hinv h0 n m r S
    (by linarith) Rset hR0 hdisj hT hbig

/-- **Shadow-injective specialization**: on a shadow-injective prime (the census good-prime
criterion), `S = 0` — the level-set count is bounded by the CHAR-0 CONSTANT alone. -/
theorem orbit_count_le_shadow_of_injective
    (g : F) (G : Finset F)
    (hmul : ∀ {x y : F}, x ∈ G → y ∈ G → x * y ∈ G)
    (hinv : ∀ {x : F}, x ∈ G → x⁻¹ ∈ G)
    (h0 : (0 : F) ∉ G)
    (n m r : ℕ) (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (hrep : PowerShadowRepIdentifies g G n r)
    (heq : rEnergy G r = shadowEnergy n m r)
    (Rset : Finset F)
    (hR0 : ∀ b ∈ Rset, b ≠ 0)
    (hdisj : ∀ b ∈ Rset, ∀ b' ∈ Rset, b ≠ b' → ∀ a ∈ G, a * b ≠ b')
    {T : ℝ} (hT : 0 ≤ T)
    (hbig : ∀ b ∈ Rset, T ≤ |R303GeneralROrbitChebyshev.deviationR G r b|) :
    (Rset.card : ℝ) * ((G.card : ℝ) * T ^ 2)
      ≤ (Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) * (shadowEnergy n m r : ℝ)
            - (G.card : ℝ) ^ (2 * r)) := by
  have h := orbit_count_le_shadow_plus_surplus_of_repIdentifies g G hmul hinv h0
    n m r hm hn hg hrep 0 (by rw [heq]; simp) Rset hR0 hdisj hT hbig
  simpa using h

end ArkLib.ProximityGap.Frontier.R331OrbitChebyshevSurplusWeld

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R331OrbitChebyshevSurplusWeld.orbit_count_le_shadow_plus_surplus
#print axioms
  ArkLib.ProximityGap.Frontier.R331OrbitChebyshevSurplusWeld.orbit_count_le_shadow_plus_surplus_of_repIdentifies
#print axioms
  ArkLib.ProximityGap.Frontier.R331OrbitChebyshevSurplusWeld.orbit_count_le_shadow_of_injective
