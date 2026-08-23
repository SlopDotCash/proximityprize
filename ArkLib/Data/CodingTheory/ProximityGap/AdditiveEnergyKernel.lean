/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The first truly-open interior cell is the BGK additive-energy kernel (#232)

`SmoothMomentBridgeOnLattice` pins the interior `(k,t)` grid exactly through `a = t+1` (the coset
boundary of rigidity). The FIRST genuinely-open cell is `t=1, a=3`: 3-subsets of `μ_n` with
`∑x = 0` (at `a=t+2=3` the rigidity boundary is crossed — `e_2,e_3` are free). Here we identify its
count EXACTLY with the **Bourgain–Glibichuk–Konyagin additive-energy quantity** of the multiplicative
subgroup:

  `tripleZero n  =  |μ_n| · M`,   `M = bgkCount n = #{u ∈ μ_n : -(1+u) ∈ μ_n} = |μ_n ∩ -(1+μ_n)|`.

Scaling by the unit `x∈μ_n` (`(x,y,z) ↦ y/x`) makes the inner count `x`-independent. This is the
precise, concrete NAME of the open prize core for the smooth domain `μ_{2^k}`: the magnitude of the
additive energy / `μ ∩ (μ-1)` intersection of a power-of-2 multiplicative subgroup in the regime
`|μ| = 2^k ≪ √q`, where full Weil gives no cancellation (Bourgain territory; no Mathlib input). The
prize is open iff this `M` is not controlled. Axiom-clean.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyKernel

variable {F : Type*} [Field F] [DecidableEq F]

/-- The **additive-energy ordered-triple count**: ordered `(x,y,z) ∈ μ_n³` with `x+y+z=0`. -/
noncomputable def tripleZero (n : ℕ) : ℕ :=
  ((nthRootsFinset n (1 : F) ×ˢ nthRootsFinset n (1 : F) ×ˢ nthRootsFinset n (1 : F)).filter
    (fun p => p.1 + p.2.1 + p.2.2 = 0)).card

/-- The **BGK intersection count** `M = #{u ∈ μ_n : -(1+u) ∈ μ_n}` — equivalently
`|μ_n ∩ -(1 + μ_n)|`, the additive-combinatorics quantity governing whether `μ_n` is additively
structured. -/
noncomputable def bgkCount (n : ℕ) : ℕ :=
  ((nthRootsFinset n (1 : F)).filter (fun u => -(1 + u) ∈ nthRootsFinset n (1 : F))).card

/-- **The first open interior cell is exactly `|μ_n|·M`.** The additive energy `#{(x,y,z)∈μ_n³ :
x+y+z=0}` equals `n` times the BGK intersection count `M = #{u∈μ_n : -(1+u)∈μ_n}`. Scaling by the
unit `x∈μ_n` (`y=x·u`, `z=-x(1+u)`) makes the inner count independent of `x`. This pins the
prize-deciding `t=1, a=3` open cell EXACTLY to the BGK / Bourgain–Glibichuk–Konyagin additive-energy
quantity for the multiplicative subgroup `μ_{2^k}` — the precise, concrete name of the open core. -/
theorem tripleZero_eq_card_mul_bgk (n : ℕ) (hn : 0 < n) :
    tripleZero (F := F) n = (nthRootsFinset n (1 : F)).card * bgkCount (F := F) n := by
  classical
  set G := nthRootsFinset n (1 : F) with hG
  -- partition the triples by the first coordinate x
  rw [tripleZero, bgkCount, ← hG]
  rw [Finset.card_filter]
  -- ∑ over the product of the indicator
  rw [Finset.sum_product]
  have hunit : ∀ x ∈ G, x ≠ 0 := by
    intro x hx; rw [hG, mem_nthRootsFinset hn] at hx
    intro h0; rw [h0, zero_pow hn.ne'] at hx; exact one_ne_zero hx.symm
  -- for each x ∈ G, the inner count equals bgkCount
  have hinner : ∀ x ∈ G,
      ∑ yz ∈ G ×ˢ G, (if x + yz.1 + yz.2 = 0 then 1 else 0)
        = ((G.filter (fun u => -(1 + u) ∈ G)).card) := by
    intro x hx
    have hx0 := hunit x hx
    -- bijection (y,z) ↦ y/x onto {u : -(1+u) ∈ G}, picking up z = -x(1+ y/x)
    rw [← Finset.card_filter]
    -- count pairs (y,z)∈G×G with x+y+z=0  via  y∈G, z=-x-y∈G
    have step1 : ((G ×ˢ G).filter (fun yz => x + yz.1 + yz.2 = 0)).card
        = (G.filter (fun y => -x - y ∈ G)).card := by
      apply Finset.card_nbij' (fun yz => yz.1) (fun y => (y, -x - y))
      · rintro ⟨y, z⟩ hyz
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hyz
        simp only [Finset.mem_coe, Finset.mem_filter]
        refine ⟨hyz.1.1, ?_⟩
        have : z = -x - y := by linear_combination hyz.2
        rw [← this]; exact hyz.1.2
      · intro y hy
        simp only [Finset.mem_coe, Finset.mem_filter] at hy
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hy.1, hy.2⟩, by ring⟩
      · rintro ⟨y, z⟩ hyz
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hyz
        have : z = -x - y := by linear_combination hyz.2
        simp [this]
      · intro y hy; rfl
    rw [step1]
    -- now reindex y = x*u : {y∈G : -x-y∈G} ≃ {u∈G : -(1+u)∈G}
    apply Finset.card_nbij' (fun y => y * x⁻¹) (fun u => u * x)
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
      refine ⟨?_, ?_⟩
      · -- y*x⁻¹ ∈ G
        rw [hG, mem_nthRootsFinset hn] at hy ⊢
        rw [mul_pow, hy.1, inv_pow, (mem_nthRootsFinset hn _).mp hx, inv_one, mul_one]
      · -- -(1 + y*x⁻¹) ∈ G : equals (-x-y)*x⁻¹
        have heq : -(1 + y * x⁻¹) = (-x - y) * x⁻¹ := by field_simp; ring
        rw [heq, hG, mem_nthRootsFinset hn]
        rw [hG, mem_nthRootsFinset hn] at hx
        rw [mul_pow, inv_pow, hx, inv_one, mul_one]
        exact (mem_nthRootsFinset hn _).mp hy.2
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter] at hu ⊢
      refine ⟨?_, ?_⟩
      · rw [hG, mem_nthRootsFinset hn] at hu ⊢
        rw [mul_pow, hu.1, (mem_nthRootsFinset hn _).mp hx, mul_one]
      · have heq : -x - u * x = (-(1 + u)) * x := by ring
        rw [heq, hG, mem_nthRootsFinset hn]
        rw [hG, mem_nthRootsFinset hn] at hx
        rw [mul_pow, hx, mul_one]
        exact (mem_nthRootsFinset hn _).mp hu.2
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter] at hy
      field_simp
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter] at hu
      field_simp
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]

end ArkLib.ProximityGap.AdditiveEnergyKernel

#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.tripleZero_eq_card_mul_bgk
