/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# The energy injection toward the proximity-prize core (#389)

The prize's optimality residual is the small-subgroup additive energy `E(μ_n)=n^{2+o(1)}`.
A genuine structural lever: the **additive** energy is controlled by the **multiplicative**
energy of the *shifted* subgroup `1+μ_n`. Concretely, with

* `M2 n G = #{(x,y)∈G² : (1+x)^n = (1+y)^n}`  (the `n`-th-power fibre count; `E(μ_n)=n·M2`),
* `M4 n G = #{(x₁,x₂,x₃,x₄)∈G⁴ : ((1+x₁)(1+x₂))^n = ((1+x₃)(1+x₄))^n}` (shifted mult. energy),

we prove `M2² ≤ M4` by the explicit injection `((x,y),(x',y')) ↦ ((x,x'),(y,y'))`: the two
fibre conditions multiply to the `M4` condition. This is honest, axiom-clean machinery — NOT a
closure of the prize (bounding `M4 ≤ n^{2+o(1)}` is the open core, recognized in the literature),
but the cleanest reduction of the additive energy to a multiplicative-energy object.  Issue #389.
-/

open Finset

namespace ProximityPrize

variable {F : Type*} [Field F] [DecidableEq F]

/-- The `n`-th-power fibre count `M2 n G = #{(x,y)∈G² : (1+x)^n = (1+y)^n}`.
For `G = μ_n` the additive energy is `E(μ_n) = n · M2`. -/
def M2 (n : ℕ) (G : Finset F) : ℕ :=
  ((G ×ˢ G).filter (fun p => (1 + p.1) ^ n = (1 + p.2) ^ n)).card

/-- The shifted multiplicative energy
`M4 n G = #{(x₁,x₂,x₃,x₄)∈G⁴ : ((1+x₁)(1+x₂))^n = ((1+x₃)(1+x₄))^n}`. -/
def M4 (n : ℕ) (G : Finset F) : ℕ :=
  (((G ×ˢ G) ×ˢ (G ×ˢ G)).filter
    (fun q => ((1 + q.1.1) * (1 + q.1.2)) ^ n = ((1 + q.2.1) * (1 + q.2.2)) ^ n)).card

/-- **The energy injection: `M2² ≤ M4`.**  The map `((x,y),(x',y')) ↦ ((x,x'),(y,y'))` sends
`M2-set × M2-set` into the `M4-set` injectively, because
`(1+x)^n=(1+y)^n ∧ (1+x')^n=(1+y')^n ⟹ ((1+x)(1+x'))^n = ((1+y)(1+y'))^n`
(multiply the two `n`-th-power equalities). Hence `(E(μ_n)/n)² ≤ M4`. -/
theorem M2_sq_le_M4 (n : ℕ) (G : Finset F) : M2 n G ^ 2 ≤ M4 n G := by
  classical
  set S : Finset (F × F) := (G ×ˢ G).filter (fun p => (1 + p.1) ^ n = (1 + p.2) ^ n) with hS
  -- `M2² = |S ×ˢ S|`
  have hcard : M2 n G ^ 2 = (S ×ˢ S).card := by
    rw [M2, ← hS, Finset.card_product, sq]
  rw [hcard, M4]
  -- the injection `i ((x,y),(x',y')) = ((x,x'),(y,y'))`
  refine Finset.card_le_card_of_injOn
    (fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))) ?_ ?_
  · -- maps `S ×ˢ S` into the M4-filter
    rintro ⟨⟨x, y⟩, ⟨x', y'⟩⟩ hq
    simp only [Finset.mem_coe, Finset.mem_product, hS, Finset.mem_filter] at hq
    obtain ⟨⟨⟨hxG, hyG⟩, hxy⟩, ⟨hx'G, hy'G⟩, hx'y'⟩ := hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨⟨hxG, hx'G⟩, hyG, hy'G⟩, ?_⟩
    -- ((1+x)(1+x'))^n = ((1+y)(1+y'))^n  from the two fibre equalities
    rw [mul_pow, mul_pow, hxy, hx'y']
  · -- injectivity: the 4 components are recoverable
    rintro ⟨⟨x, y⟩, ⟨x', y'⟩⟩ _ ⟨⟨a, b⟩, ⟨a', b'⟩⟩ _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨hx, hx'⟩, hy, hy'⟩ := heq
    simp [hx, hx', hy, hy']

end ProximityPrize

#print axioms ProximityPrize.M2_sq_le_M4
