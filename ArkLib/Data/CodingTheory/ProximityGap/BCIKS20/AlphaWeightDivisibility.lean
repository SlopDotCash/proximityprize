/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ClearingProduct
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

/-!
# The monic-`H` specialization of the `AlphaGenuineRegularWeightLe` weight invariant (BCIKS20 A.4, #138)

`ClearingProduct.lean` reduces the genuine `(A.4)` weight invariant `AlphaGenuineRegularWeightLe`
to the `𝒪`-level divisibility-with-weight `DivWeightLe`: at every order `t`, the clearing product
`W𝒪^{t+1}·ξ^{2t−1}` must divide `βHensel t` in `𝒪 H`, with the quotient of `Λ_𝒪`-weight `≤ 1`.
The honest residual (the `WALL` note in `AlphaWeight.lean`) is that the weight-`≤-1` core is
genuinely irreducible: it is exactly the divisibility `W𝒪 ∣ βHensel 0` (and its higher-order
analogues), which the field embedding cannot manufacture.

This file isolates the **monic-`H` specialization**, where the `W` half of that obstruction
*collapses* and the order-zero invariant becomes provable outright.  When `H` is monic,
`W = H.leadingCoeff = 1`, so the `𝒪`-element `W𝒪 H = mk (C 1) = 1`:

* `W𝒪_eq_one_of_monic` — `W𝒪 H = 1` in `𝒪 H`.
* `embeddingOf𝒪Into𝕃_W𝒪_eq_one_of_monic` — its `𝕃`-embedding is `1`.
* `weight_Λ_over_𝒪_W𝒪_pow_le` — the genuine weight-arithmetic fact
  `Λ_𝒪(W𝒪^k) ≤ k·(lc H).natDegree`, valid for all `H` (combine `_pow_le` + `_W`).
* `weight_Λ_over_𝒪_W𝒪_pow_le_zero_of_monic` — its monic collapse `Λ_𝒪(W𝒪^k) ≤ 0`.
* `clearingProduct_eq_ξ_pow_of_monic` — the clearing product reduces to `ξ^{2t−1}`.
* `αGenuine_zero_eq_functionFieldT_of_monic` — the order-0 root is `α₀ = T/W = T` itself.
* `AlphaGenuineRegularWeightLe_zero_of_monic` — **hence the order-zero weight invariant is provable
  outright for monic `H`**: `βHensel 0 = mk X` is a weight-`≤ 1` regular preimage of
  `αGenuine 0 = T` directly (no `W`-clearing needed, since the `W𝒪 ∣ βHensel 0` obstruction is
  vacuous when `W𝒪 = 1`).  This is the precise sense in which the monic case dissolves the residual.

The general (non-monic) weight-`≤-1` core stays irreducible; this file lands the tractable
monic-collapse surrounding lemmas, honestly flagged as a *specialization*, not a resolution of the
general invariant.
-/

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ### 1. The `W𝒪 = 1` collapse under monicity -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **Monic collapse of `W𝒪`.**  When `H` is monic, `W = H.leadingCoeff = 1`, so the genuine
`W`-factor `W𝒪 H = mk (C W) = mk (C 1) = mk 1 = 1` in `𝒪 H`. -/
theorem W𝒪_eq_one_of_monic (hmonic : H.Monic) : W𝒪 H = 1 := by
  rw [W𝒪, hmonic, map_one, map_one]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The `𝕃`-embedding of `W𝒪 H` is `1` when `H` is monic (the lift identity's `W` factor is
trivial).  Routes through `embeddingOf𝒪Into𝕃_W𝒪` + `H.leadingCoeff = 1`. -/
theorem embeddingOf𝒪Into𝕃_W𝒪_eq_one_of_monic (hmonic : H.Monic) :
    embeddingOf𝒪Into𝕃 H (W𝒪 H) = 1 := by
  rw [embeddingOf𝒪Into𝕃_W𝒪, hmonic, map_one]

/-! ### 2. The `Λ_𝒪`-weight of `W𝒪`-powers (general `H`, then the monic collapse) -/

variable {D : ℕ}

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The `Λ_𝒪`-weight of `W𝒪`-powers (general `H`).**  `Λ_𝒪(W𝒪^k) ≤ k·(lc H).natDegree`: the
genuine weight-arithmetic fact for the clearing product's `W`-factor, valid for *all* `H`.  The
over-`𝒪` power bound `weight_Λ_over_𝒪_pow_le` gives `Λ_𝒪(W𝒪^k) ≤ k·Λ_𝒪(W𝒪)`, and the in-tree
`Λ(W)` bound `weight_Λ_over_𝒪_W` gives `Λ_𝒪(W𝒪) ≤ (lc H).natDegree`. -/
theorem weight_Λ_over_𝒪_W𝒪_pow_le (hH : 0 < H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D) (k : ℕ) :
    weight_Λ_over_𝒪 hH ((W𝒪 H) ^ k) D
      ≤ (WithBot.some (k * (H.leadingCoeff).natDegree) : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_pow_le H hH hDH (W𝒪 H) k).trans ?_
  exact nsmul_withBot_le k _ (weight_Λ_over_𝒪_W H hH hDH)

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The monic collapse of the `W𝒪`-power weight.**  When `H` is monic, `lc H = 1` has
`natDegree 0`, so `Λ_𝒪(W𝒪^k) ≤ k·0 = 0`: the `W`-factor contributes nothing to the weight of the
clearing product.  (Equivalently `W𝒪^k = 1` has weight `≤ 0`.) -/
theorem weight_Λ_over_𝒪_W𝒪_pow_le_zero_of_monic (hH : 0 < H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D) (hmonic : H.Monic) (k : ℕ) :
    weight_Λ_over_𝒪 hH ((W𝒪 H) ^ k) D ≤ (0 : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_W𝒪_pow_le H hH hDH k).trans ?_
  rw [hmonic, Polynomial.natDegree_one]
  simp

/-! ### 3. The clearing product collapses to a pure `ξ`-power -/

/-- **Monic collapse of the clearing product.**  When `H` is monic, the `(A.4)` clearing product
`W𝒪^{t+1}·ξ^{2t−1}` is just the `ξ`-power `ξ^{2t−1}` (the `W`-factor is `1`).  This is the
`𝒪`-level shadow of the denominator collapsing to `ξ^{2t−1}` in `𝕃`. -/
theorem clearingProduct_eq_ξ_pow_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hmonic : H.Monic) (t : ℕ) :
    (W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1)
      = (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1) := by
  rw [W𝒪_eq_one_of_monic H hmonic, one_pow, one_mul]

/-! ### 4. The order-0 root is `T` itself, and the order-0 weight invariant is provable -/

/-- **Monic collapse of the order-0 root.**  `αGenuine 0 = α₀ = T / W`; when `H` is monic, `W = 1`
so `α₀ = T / 1 = T = functionFieldT`.  This removes the single `W`-division that obstructs
`AlphaGenuineRegularWeightLe_zero` in the general case. -/
theorem αGenuine_zero_eq_functionFieldT_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hmonic : H.Monic) :
    αGenuine H x₀ R hHyp 0 = functionFieldT (H := H) := by
  rw [αGenuine_zero, α₀, hmonic, map_one, div_one]

/-- **The order-zero weight invariant holds outright for monic `H`.**  In the general case,
`AlphaGenuineRegularWeightLe_zero` is the irreducible residual: it asks for a regular weight-`≤ 1`
preimage of `αGenuine 0 = T/W`, equivalently the divisibility `W𝒪 ∣ βHensel 0` that the field
embedding cannot synthesize.  But when `H` is monic the `W`-clearing is *vacuous* (`W𝒪 = 1` divides
everything): `αGenuine 0 = T = embedding (βHensel 0)` directly (`βHensel 0 = mk X`,
`embeddingOf𝒪Into𝕃_βHensel_zero`), and `βHensel 0` has `Λ_𝒪`-weight `≤ 1` whenever
`2 ≤ deg H` and `D ≤ deg H` (`βHensel_zero_weight_le_one`).  Hence the witness `a := βHensel 0`
discharges the order-zero invariant with no carved hypothesis.  This is the precise, honest sense
in which the monic specialization dissolves the order-zero face of the A.4 residual. -/
theorem AlphaGenuineRegularWeightLe_zero_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hmonic : H.Monic)
    (hd : 2 ≤ H.natDegree) (hD : D ≤ H.natDegree) :
    AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D := by
  refine ⟨βHensel H x₀ R hHyp 0, ?_, βHensel_zero_weight_le_one H x₀ R hHyp hH hd hD⟩
  rw [embeddingOf𝒪Into𝕃_βHensel_zero, αGenuine_zero_eq_functionFieldT_of_monic H x₀ R hHyp hmonic]

/-- **The `t = 0` divisibility-with-weight (`DivWeightLe_zero`) holds outright for monic `H`.**  The
clearing-product face of the order-zero invariant: `βHensel 0 = a · W𝒪^{0+1} · ξ^{2·0−1}` with the
quotient of weight `≤ 1`.  Since `W𝒪 = 1` and `ξ^{0} = 1` collapse the clearing product, the witness
is `a := βHensel 0` itself.  This is `AlphaGenuineRegularWeightLe_zero_of_monic` transported to the
`𝒪`-divisibility world (it does not need the `t = 0` lift identity, only the monic `W`-collapse). -/
theorem DivWeightLe_zero_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hmonic : H.Monic)
    (hd : 2 ≤ H.natDegree) (hD : D ≤ H.natDegree) :
    DivWeightLe_zero H x₀ R hHyp hH D := by
  refine ⟨βHensel H x₀ R hHyp 0, ?_, βHensel_zero_weight_le_one H x₀ R hHyp hH hd hD⟩
  rw [W𝒪_eq_one_of_monic H hmonic]
  simp

end BCIKS20.HenselNumerator.AlphaWeight

#print axioms BCIKS20.HenselNumerator.AlphaWeight.W𝒪_eq_one_of_monic
#print axioms BCIKS20.HenselNumerator.AlphaWeight.embeddingOf𝒪Into𝕃_W𝒪_eq_one_of_monic
#print axioms BCIKS20.HenselNumerator.AlphaWeight.weight_Λ_over_𝒪_W𝒪_pow_le
#print axioms BCIKS20.HenselNumerator.AlphaWeight.weight_Λ_over_𝒪_W𝒪_pow_le_zero_of_monic
#print axioms BCIKS20.HenselNumerator.AlphaWeight.clearingProduct_eq_ξ_pow_of_monic
#print axioms BCIKS20.HenselNumerator.AlphaWeight.αGenuine_zero_eq_functionFieldT_of_monic
#print axioms BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe_zero_of_monic
#print axioms BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe_zero_of_monic
