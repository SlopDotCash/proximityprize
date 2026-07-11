/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G136LawfulCount
import ArkLib.Data.CodingTheory.ProximityGap.SidonLiftDevacuated

/-!
# G136 (production instantiation): the concrete rung-2 accident equivalence at `μ_{2^30}`

Instantiates the abstract capstone `rung2_anchor_iff_accidents` at the actual production
subgroup: `H = {ω^k : k < 2^30}` for a primitive `2^30`-th root of unity `ω` in a finite
field of size `> 2^90` (both certified prize primes qualify, with room to spare).  All the
closure hypotheses (multiplicative closure, inverses, `1`, negation-closure via
`ω^{2^29} = −1`, `0 ∉ H`, cardinality `2^30`) are discharged from `IsPrimitiveRoot` alone.

```text
q·E₂(μ_{2^30}) ≤ 3·q·(2^30)² + (2^30)⁴   ⟺   #accidents(μ_{2^30}) ≤ 3.
```

The production rung-2 anchor is now literally a finite Diophantine statement about the
certified prime.  **Honest scope.**  The accident count itself is the wall.  CORE remains
OPEN.  Issue #466 (G136).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G136ProductionInstantiation

open Finset
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.Frontier.G136EnergySolutionBijection
open ArkLib.ProximityGap.Frontier.G136LawfulCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The production roots-of-unity subgroup as a Finset. -/
noncomputable def rootsFinset (ω : F) (n : ℕ) : Finset F :=
  (Finset.range n).image (ω ^ ·)

section Closure

variable {ω : F} {n : ℕ} (hn0 : n ≠ 0) (hω : IsPrimitiveRoot ω n)

theorem mem_rootsFinset_iff {x : F} :
    x ∈ rootsFinset ω n ↔ ∃ k < n, ω ^ k = x := by
  unfold rootsFinset
  simp [Finset.mem_image]

include hn0 hω

theorem pow_mem_rootsFinset (k : ℕ) : ω ^ k ∈ rootsFinset ω n := by
  refine mem_rootsFinset_iff.mpr ⟨k % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn0), ?_⟩
  exact (primitiveRoot_pow_eq_iff hn0 hω (k % n) k).mpr (Nat.mod_modEq k n)

theorem one_mem_rootsFinset : (1 : F) ∈ rootsFinset ω n := by
  have := pow_mem_rootsFinset hn0 hω 0
  simpa using this

theorem zero_notMem_rootsFinset : (0 : F) ∉ rootsFinset ω n := by
  intro h
  obtain ⟨k, _, hk⟩ := mem_rootsFinset_iff.mp h
  have hω0 : ω ≠ 0 := by
    intro h0
    have := hω.pow_eq_one
    rw [h0, zero_pow hn0] at this
    exact zero_ne_one this
  exact pow_ne_zero k hω0 hk

theorem mul_mem_rootsFinset {x u : F}
    (hx : x ∈ rootsFinset ω n) (hu : u ∈ rootsFinset ω n) :
    x * u ∈ rootsFinset ω n := by
  obtain ⟨k, _, rfl⟩ := mem_rootsFinset_iff.mp hx
  obtain ⟨l, _, rfl⟩ := mem_rootsFinset_iff.mp hu
  rw [← pow_add]
  exact pow_mem_rootsFinset hn0 hω (k + l)

theorem inv_mem_rootsFinset {x : F} (hx : x ∈ rootsFinset ω n) :
    x⁻¹ ∈ rootsFinset ω n := by
  obtain ⟨k, hk, rfl⟩ := mem_rootsFinset_iff.mp hx
  have hone : ω ^ k * ω ^ (n * (k + 1) - k) = 1 := by
    have hkle : k ≤ n * (k + 1) := by
      calc
        k ≤ k + 1 := Nat.le_succ k
        _ ≤ n * (k + 1) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hn0)
    rw [← pow_add, show k + (n * (k + 1) - k) = n * (k + 1) from by omega,
      pow_mul]
    simp [hω.pow_eq_one]
  have : (ω ^ k)⁻¹ = ω ^ (n * (k + 1) - k) :=
    eq_inv_of_mul_eq_one_right hone |>.symm
  rw [this]
  exact pow_mem_rootsFinset hn0 hω _

theorem neg_mem_rootsFinset (hn2 : 2 ∣ n) {x : F}
    (hx : x ∈ rootsFinset ω n) :
    -x ∈ rootsFinset ω n := by
  obtain ⟨k, _, rfl⟩ := mem_rootsFinset_iff.mp hx
  have hhalf : ω ^ (n / 2) = -1 := primitiveRoot_pow_half hn2 hn0 hω
  have : -ω ^ k = ω ^ (n / 2 + k) := by
    rw [pow_add, hhalf]
    ring
  rw [this]
  exact pow_mem_rootsFinset hn0 hω _

theorem card_rootsFinset : (rootsFinset ω n).card = n := by
  unfold rootsFinset
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have h := (primitiveRoot_pow_eq_iff hn0 hω a b).mp hab
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

end Closure

/-- **The concrete production rung-2 equivalence.**  For a primitive `2^30`-th root of
unity `ω` in a finite field with more than `2^90` elements (both certified prize primes
qualify): the rung-2 anchor holds iff the accident count is at most three. -/
theorem production_rung2_anchor_iff_accidents
    {ω : F} (hω : IsPrimitiveRoot ω (2 ^ 30))
    (hq : 2 ^ 90 < Fintype.card F) (h2 : (2 : F) ≠ 0) :
    Fintype.card F * Finset.addREnergy 2 (rootsFinset ω (2 ^ 30))
        ≤ 3 * Fintype.card F * (2 ^ 30) ^ 2 + (2 ^ 30) ^ 4
      ↔ (accidents (rootsFinset ω (2 ^ 30))).card ≤ 3 := by
  have hn0 : (2 ^ 30 : ℕ) ≠ 0 := by positivity
  exact rung2_anchor_iff_accidents (rootsFinset ω (2 ^ 30)) hq
    (card_rootsFinset hn0 hω)
    (one_mem_rootsFinset hn0 hω)
    (fun x hx => neg_mem_rootsFinset hn0 hω ⟨2 ^ 29, by norm_num⟩ hx)
    (zero_notMem_rootsFinset hn0 hω) h2
    (fun x hx u hu => mul_mem_rootsFinset hn0 hω hx hu)
    (fun x hx => inv_mem_rootsFinset hn0 hω hx)

end ArkLib.ProximityGap.Frontier.G136ProductionInstantiation

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G136ProductionInstantiation.card_rootsFinset
#print axioms
  ArkLib.ProximityGap.Frontier.G136ProductionInstantiation.production_rung2_anchor_iff_accidents
