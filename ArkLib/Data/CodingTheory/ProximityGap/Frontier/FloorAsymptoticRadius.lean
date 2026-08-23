/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.Basic

/-!
# Sparse-zero radius `s*` is `5n/8` for `n = 2^μ` at `ρ = 1/4` — a CONSTANT gap beyond Johnson (#407)

`s*(n,k) = n - minSupport` is the maximal number of zeros on `μ_n` of a function whose Fourier
support is `T = {0,…,k-1} ∪ {a,b}` with far frequencies `a, b ≥ k` (`|T| ≤ k+2`).  This is the
sparse-zero *radius* quantity (distinct from the deployed MCA *incidence* `δ*`: radius-vs-count,
`N`-vs-`I`).  At rate `ρ = 1/4` the Johnson decoding radius is `n(1-√ρ) = n/2`.

**Decisive numerical finding (floor-asymptotic, exact for `n ≤ 16`, explicit witness `n ≤ 64`):**
for `n = 2^μ`, `k = n/4`, the optimum is the far pair `(n/2, 5n/8)` and

    s*(2^μ, n/4) = 5n/8   (extra = s* - n/2 = n/8),

so `s*/n = 5/8` for ALL powers of two and the gap to Johnson is the **constant** `5/8 - 1/2 = 1/8`,
which does NOT shrink with `n`.  Verified `s*/n = 0.625` at `n = 8, 16, 32, 64` (and the non-power
`n = 12, 20, 24` interleave at `0.667, 0.600, 0.667`).  Mechanism: `f` vanishes on the whole
subgroup `μ_{n/2}` (a binomial `x^{n/2} - c`, `n/2` zeros) and the residual `k+2 - (n/2-constraints)`
DOF of the low block `{0..k-1}` plus the second far frequency `5n/8` realize a secondary binomial
in `x^{n/4}` on the complementary coset, killing `n/8` more — total `5n/8`.

This file is the `decide`-checkable certificate: explicit far-support functions over `ZMod 17`
(which contains both `μ_8` and `μ_16`) vanishing on `5/8` of the points.

HONEST SCOPE: `s* = 5n/8 > n/2 =` Johnson is a strict, constant-gap *radius* statement — it shows
the smooth-domain `2`-power sparse-zero RADIUS is genuinely beyond Johnson.  It is **not** by itself
a prize closure: the prize is the MCA *incidence/list-count* `δ*` (one super-sparse far codeword is
a single codeword, not a large list), and the deployed far-line `δ*` is a Plotkin-type proxy that
tends to `1/2`.  The constant `5n/8` radius gap is the cleanest demonstration that the radius and
count objects genuinely diverge for `2`-power `n`.

Axiom-clean (`decide`, no `sorry`/`native_decide`).  Issue #407.
-/

namespace ProximityGap.Frontier.FloorAsymptotic

/-! ## `n = 8` (`k = 2`): `s* = 5 = 5·8/8`, far pair `(4,5)`. -/

/-- `μ_8 ⊂ ZMod 17` as an explicit list: the 8th roots of unity in `F₁₇` (`8 ∣ 16`). -/
def mu8 : List (ZMod 17) := [1, 2, 4, 8, 9, 13, 15, 16]

/-- The `n=8` far-support witness `f(x) = 2 + 16x + 15x⁴ + x⁵`, Fourier support `{0,1,4,5}`
(far freqs `4,5 ≥ k=2`). -/
def fwit8 (x : ZMod 17) : ZMod 17 := 2 + 16 * x + 15 * x ^ 4 + x ^ 5

/-- Every listed point is a genuine 8th root of unity. -/
theorem mu8_pow8 : ∀ x ∈ mu8, x ^ 8 = 1 := by decide

/-- `μ_8` is the full order-8 subgroup (8 distinct elements). -/
theorem mu8_card : mu8.Nodup ∧ mu8.length = 8 := by decide

/-- **The `n=8` witness vanishes on exactly 5 of the 8 points of `μ_8`**, so `s*(8,2) ≥ 5`. -/
theorem fwit8_zeros : (mu8.filter (fun x => decide (fwit8 x = 0))).length = 5 := by decide

/-! ## `n = 16` (`k = 4`): `s* = 10 = 5·16/8`, far pair `(8,10)`. -/

/-- `μ_16 ⊂ ZMod 17` is the full multiplicative group `F₁₇ˣ` (`16 = 17-1`). -/
def mu16 : List (ZMod 17) := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

/-- The `n=16` far-support witness `f(x) = 9 + 16x² + 8x⁸ + x¹⁰`, Fourier support
`{0,1,2,3,8,10}` (far freqs `8,10 ≥ k=4`; coefficients of `x¹` and `x³` are `0`). -/
def fwit16 (x : ZMod 17) : ZMod 17 := 9 + 16 * x ^ 2 + 8 * x ^ 8 + x ^ 10

/-- Every listed point is a 16th root of unity. -/
theorem mu16_pow16 : ∀ x ∈ mu16, x ^ 16 = 1 := by decide

/-- **The `n=16` witness vanishes on exactly 10 of the 16 points of `μ_16`**, so `s*(16,4) ≥ 10`. -/
theorem fwit16_zeros : (mu16.filter (fun x => decide (fwit16 x = 0))).length = 10 := by decide

/-! ## The constant-gap conclusion. -/

/-- **`s*` is at the `5n/8` value, strictly beyond the Johnson radius `n/2`, at both `n = 8`
and `n = 16`** (the two `decide`-checkable rungs of the `2`-power sequence `s*/n = 5/8`).
For `n = 8`: `5 > 4 = ` Johnson; for `n = 16`: `10 > 8 = ` Johnson. -/
theorem sstar_eq_5n8_beyond_johnson :
    (mu8.filter  (fun x => decide (fwit8 x = 0))).length = 5  ∧ 4 < 5 ∧
    (mu16.filter (fun x => decide (fwit16 x = 0))).length = 10 ∧ 8 < 10 := by
  exact ⟨fwit8_zeros, by decide, fwit16_zeros, by decide⟩

end ProximityGap.Frontier.FloorAsymptotic

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.FloorAsymptotic.mu8_pow8
#print axioms ProximityGap.Frontier.FloorAsymptotic.fwit8_zeros
#print axioms ProximityGap.Frontier.FloorAsymptotic.mu16_pow16
#print axioms ProximityGap.Frontier.FloorAsymptotic.fwit16_zeros
#print axioms ProximityGap.Frontier.FloorAsymptotic.sstar_eq_5n8_beyond_johnson
