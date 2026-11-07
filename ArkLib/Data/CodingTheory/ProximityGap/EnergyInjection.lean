/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The energy injection toward the proximity-prize core (#389)

The prize's optimality residual is the small-subgroup additive energy `E(μ_n)=n^{2+o(1)}`.
A structural lever: the **additive** energy is related to the **multiplicative** energy of the
*shifted* subgroup `1+μ_n`. Concretely, with

* `M2 n G = #{(x,y)∈G² : (1+x)^n = (1+y)^n}`  (the `n`-th-power fibre count),
* `M4 n G = #{(x₁,x₂,x₃,x₄)∈G⁴ : ((1+x₁)(1+x₂))^n = ((1+x₃)(1+x₄))^n}` (shifted mult. energy),

we prove `M2² ≤ M4` by the explicit injection `((x,y),(x',y')) ↦ ((x,x'),(y,y'))`: the two
fibre conditions multiply to the `M4` condition. This holds for every finite set `G`.

**Relation to additive energy — corrected, NOT formalized here.** It is *false* in general that
`E(μ_n) = n·M2`. For `G = μ_n` (all `n`-th roots of unity, `|G| = n`), splitting
`a+b = c+d` by whether the common sum is zero gives (informal derivation)
`E(μ_n) = n·M2 + (n² − n)·[−1 ∈ μ_n]`: when `−1 ∈ G` the pair `x = y = −1` is counted once by
`M2` (as `0 = 0`) but the zero-sum fibre `{a+b = 0 = c+d}` contributes `n²` quadruples, whereas a
nonzero common sum contributes `n` quadruples per counted pair. So `E(μ_n) = n·M2` holds only for
odd `n` / `−1 ∉ G`, and the correction is structural for every even-order subgroup. The
kernel-checked counterexample `addEnergy_ne_n_mul_M2_F5` (`F_5`, `n = 2`, `G = {1,4}`) has
`E = 6`, `M2 = 2`, `n·M2 = 4`, matching the corrected formula `6 = 4 + (4 − 2)`. The general
corrected identity is not proved in this file. Granting that informal formula, `M2² ≤ M4` would
bound `((E − (n² − n))/n)²` for even `n`, not `(E/n)²`.

This is honest, axiom-clean machinery — NOT a closure of the prize (bounding `M4 ≤ n^{2+o(1)}` is
the open core, recognized in the literature), and no claim is made that it discharges the
production upper/cancellation bound.  Issue #389.
-/

open Finset

namespace ProximityPrize

variable {F : Type*} [Field F] [DecidableEq F]

/-- The `n`-th-power fibre count `M2 n G = #{(x,y)∈G² : (1+x)^n = (1+y)^n}`.
For `G = μ_n` the additive energy is NOT `n · M2` in general: when `−1 ∈ μ_n` the zero-shift pair
contributes an extra `n² − n` (informal corrected formula `E(μ_n) = n·M2 + (n² − n)·[−1 ∈ μ_n]`,
not formalized; see the module docstring and `addEnergy_ne_n_mul_M2_F5`). -/
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
(multiply the two `n`-th-power equalities). This is a statement about `M2` only; it does not give
`(E(μ_n)/n)² ≤ M4`, since `E(μ_n) ≠ n·M2` when `−1 ∈ μ_n` (see the module docstring). -/
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

section Counterexample

local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **`E(μ_n) = n·M2` is false: kernel-checked counterexample.** Over `F_5` with `n = 2` and
`G = μ_2 = {1, 4}`, the additive energy `#{(a,b,c,d) ∈ G⁴ : a + b = c + d}` is `6`, while
`M2 2 G = 2`, so `n·M2 = 4 ≠ 6`. The missing `2 = n² − n` is the zero-shift contribution. -/
theorem addEnergy_ne_n_mul_M2_F5 :
    ((((({1, 4} : Finset (ZMod 5)) ×ˢ ({1, 4} : Finset (ZMod 5))) ×ˢ
        (({1, 4} : Finset (ZMod 5)) ×ˢ ({1, 4} : Finset (ZMod 5)))).filter
        (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card = 6) ∧
      M2 2 ({1, 4} : Finset (ZMod 5)) = 2 := by
  refine ⟨by decide, by decide⟩

end Counterexample

end ProximityPrize

#print axioms ProximityPrize.M2_sq_le_M4
#print axioms ProximityPrize.addEnergy_ne_n_mul_M2_F5
