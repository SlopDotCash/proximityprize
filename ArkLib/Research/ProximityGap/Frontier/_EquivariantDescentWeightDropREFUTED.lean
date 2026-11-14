/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# REFUTATION of `_EquivariantDescentWeightDrop`: the √p-removal is FLAWED (finite-vs-1-dim) (#444)

This file is the adversarial-verification record for the claim of
`_EquivariantDescentWeightDrop.weight_drop_kills_sqrtP` that the diagonal `μ_n`-action on the
correlation variety `V_corr` *removes the `√p`* on the nontrivial-winding part by dropping the
cohomological weight `2r-1 → 2r-2`. **The √p-removal is FLAWED.** The error is a precise and
fatal conflation of the **finite group scheme `μ_n` (dimension 0)** with the **1-dimensional
torus `𝔾_m`**.

## The single load-bearing FALSE step

`_EquivariantDescentWeightDrop` line 50 asserts verbatim:
> "A free quotient by a **`1`-dimensional group** drops the cohomological weight by exactly one:
>  `H^{2r-1}(V_corr)^{χ_w} ≅ H^{2r-2}(V_corr / μ_n ⊗ ℒ_{χ_w})`."

and encodes the conclusion as `def descendedWeight (r) := 2*r - 2` (degree dropped by one).
**`μ_n` is NOT a `1`-dimensional group.** `μ_n = Spec k[t]/(tⁿ-1)` is a *finite* group scheme of
**dimension 0** (`n` points). The `1`-dimensional group is `𝔾_m = Spec k[t,t⁻¹]`.

The cohomological consequence of a *free* quotient depends decisively on the dimension of the
group:

* **Finite `G` (dim 0), free action.** `X → X/G` is a **finite étale cover** of degree `|G|`.
  It does **NOT** change dimension (`dim X/G = dim X`) and the cohomology decomposes by characters
  **at the SAME degree**:
  `H^i(X, ℚ_ℓ) ≅ ⊕_χ H^i(X/G, ℒ_χ)`, in particular `H^i(X)^{χ} ≅ H^i(X/G, ℒ_χ)`.
  **No degree shift, no weight drop.** The eigenvalue modulus stays `p^{i/2}`. The only gain is a
  redistribution of the *same* total cohomology across `|G|=n` isotypic pieces — a **factor-`n`
  combinatorial saving**, which is NOT a power of `p`.

* **Positive-dimensional `G` (e.g. `𝔾_m`, dim 1), free action.** `X → X/G` is (étale-locally) a
  `G`-bundle with `(dim G)`-dimensional fibres: `dim X/G = dim X − dim G`. The middle cohomology
  then *does* shift down by `dim G` (Gysin/Leray with the `𝔾_m`-fibration), dropping the weight by
  `1`. **This — and only this — is what the brick's `2r-1 → 2r-2` step needs.**

So `descendedWeight = 2r-2` is the formula for a `𝔾_m`-quotient (dim 1). For the actual finite
`μ_n` (dim 0), the honest descended weight is **unchanged**: `2r-1`. The `√p` survives.

## No rescue: the dim-1 group does NOT act on the weighted variety

One might try to *upgrade* the finite `μ_n`-action to a free `𝔾_m`-action `t·(x,y)=(tx,ty)` to
license the weight drop. This fails for two independent reasons:

1. **The winding character is finite-order.** `χ_w` is a character of `μ_n ≅ ℤ/n`. A nontrivial
   finite-order character does **not** extend to a character of the connected group `𝔾_m`
   (`Hom(𝔾_m,𝔾_m)=ℤ` is torsion-free; the Kummer sheaf data that descends is `μ_n`-data only).
2. **The Jacobi weights are not `𝔾_m`-invariant.** `Jphase(x)` depends on the subgroup sums
   `Σ xᵢ^{-exp}`; scaling `x` by a general `t∈𝔾_m` changes them. There is no free `𝔾_m`-action
   *preserving the weighted sum* `Σ Jphase(x)·conj Jphase(y)`. Only the finite `μ_n` preserves it.

Hence the only group that genuinely acts is the finite `μ_n`, whose quotient gives the factor-`n`
saving — exactly the already-known coset invariance `η_{cb}=η_b` (`_EtaCosetInvariance`, cited by
the original file at line 33). The "new" diagonal action contributes **nothing past the n-fold
coset symmetry already exploited**, and in particular **does not touch the BGK/√p exponent**.

## What the original Lean theorems actually prove (and why they are not a closure)

Every theorem in `_EquivariantDescentWeightDrop` is *arithmetically* true and axiom-clean — but
none of them is *about cohomology*. `weight_drop_kills_sqrtP` proves only the tautology
`(2r-2)/2 − (r-1) = 0`; the mathematical content "`2r-2` is the descended weight" lives entirely
in the **unjustified `def descendedWeight := 2r-2`**, whose justification (the line-50 prose) is
the false finite-vs-1-dim step. The Lean is honest as arithmetic; the *interpretation* attached to
it is wrong.

## This file: the machine-checked honest correction

We record, axiom-clean:

* `mu_n_is_dim_zero_not_one` — the dimension bookkeeping: a finite group scheme has dimension `0`,
  not `1` (recorded as the literal `0 ≠ 1`, the crux datum the brick gets wrong).
* `finite_etale_preserves_degree` — for a finite étale quotient the descended degree equals the
  original degree (the cohomology does NOT shift): `descendedDegreeFinite r = corrDegree r`.
* `honest_descended_weight_unchanged` — therefore the honest descended residual exponent is the
  SAME `1/2`, NOT `0`: `(2r-1)/2 − (r-1) = 1/2`.
* `finite_quotient_gives_factor_n_not_sqrtP` — the saving from a finite `μ_n`-quotient is the
  factor `1/n` (a combinatorial, `p`-independent saving), which is NOT a half-power of `p`:
  for `p` large the field scale `√p` strictly dominates any fixed `1/n`.
* `descent_does_not_beat_wall` — the corrected conclusion: the honest descended residual is `1/2`,
  EQUAL to (not strictly below) the wall of `_JacobiFermatCohomology`. The `√p` is NOT removed.

**Verdict: the √p-removal headline of `_EquivariantDescentWeightDrop` is FLAWED.** The thesis's
claimed advance past the cohomology wall does not stand: the diagonal `μ_n`-symmetry yields the
already-known factor-`n` coset saving, leaving the `√p`/BGK face of the wall exactly where
`_JacobiFermatCohomology` left it. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDropREFUTED

open Real

/-! ### Part 1 — the crux datum the brick gets wrong: `dim μ_n = 0`, not `1` -/

/-- Dimension of the finite group scheme `μ_n = Spec k[t]/(tⁿ-1)`: it is **`0`** (a finite set of
points), independent of `n`. The `1`-dimensional group is `𝔾_m`. -/
def dimMuN : ℕ := 0

/-- Dimension of the multiplicative group `𝔾_m = Spec k[t,t⁻¹]`: **`1`**. -/
def dimGm : ℕ := 1

/-- **THE ERROR, isolated.** `_EquivariantDescentWeightDrop` (line 50) calls `μ_n` a
"`1`-dimensional group" to license a weight drop. But `dim μ_n = 0 ≠ 1 = dim 𝔾_m`. The whole
weight-drop-by-one rests on this false dimension. -/
theorem mu_n_is_dim_zero_not_one : dimMuN ≠ dimGm := by decide

/-- A finite group has dimension `0` — restating the crux as the equality `dimMuN = 0`. -/
theorem dimMuN_eq_zero : dimMuN = 0 := rfl

/-! ### Part 2 — finite étale quotient preserves the cohomological degree (no weight drop) -/

/-- The degree of the middle cohomology of the correlation variety, `2r-1`
(matching `_JacobiFermatCohomology.corrDim` / `corrMiddleWeight`). -/
def corrDegree (r : ℕ) : ℕ := 2 * r - 1

/-- The Jacobi normalization exponent `r-1` (matching `_JacobiFermatCohomology.jacobiWeight`). -/
def jacobiNorm (r : ℕ) : ℕ := r - 1

/-- **Descended degree under a FINITE étale quotient = original degree.** For a free quotient by a
finite group `G` (dim 0), `X → X/G` is finite étale and `H^i(X)^χ ≅ H^i(X/G, ℒ_χ)` at the **same**
degree `i`. So the descended degree equals the original `2r-1`: there is **no** `2r-1 → 2r-2`
shift. This is the honest replacement for `_EquivariantDescentWeightDrop.descendedWeight`. -/
def descendedDegreeFinite (r : ℕ) : ℕ := 2 * r - 1

/-- **The finite quotient does NOT change the degree.** Concretely
`descendedDegreeFinite r = corrDegree r` for all `r` — the finite-group descent is degree- (hence
weight-) preserving, contradicting the brick's `descendedWeight = 2r-2`. -/
theorem finite_etale_preserves_degree (r : ℕ) : descendedDegreeFinite r = corrDegree r := rfl

/-! ### Part 3 — the corrected residual: still `1/2`, the `√p` is NOT removed -/

/-- **The honest descended residual exponent is `1/2`, not `0`.** With the *correct* finite-group
descended degree `2r-1` (Part 2), the residual after the Jacobi normalization is
`(2r-1)/2 − (r-1) = 1/2` — IDENTICAL to the `_JacobiFermatCohomology` wall. The `√p` survives the
finite `μ_n`-quotient. (Contrast `_EquivariantDescentWeightDrop.weight_drop_kills_sqrtP`, which
gets `0` only by using the wrong `𝔾_m`-degree `2r-2`.) -/
theorem honest_descended_weight_unchanged (r : ℕ) (hr : 1 ≤ r) :
    (descendedDegreeFinite r : ℝ) / 2 - (jacobiNorm r : ℝ) = 1 / 2 := by
  unfold descendedDegreeFinite jacobiNorm
  have h2 : 2 * r - 1 = 2 * (r - 1) + 1 := by omega
  rw [h2, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hr]; push_cast; ring

/-- The honest descended residual as a power of `p`: it is `p^{1/2} = √p`, the **same** field scale
as before the descent — the literal statement that the descent does NOT remove `√p`. -/
theorem honest_descended_residual_is_sqrtP {p : ℝ} (hp : 0 < p) (r : ℕ) (hr : 1 ≤ r) :
    p ^ ((descendedDegreeFinite r : ℝ) / 2) * p ^ (-(jacobiNorm r : ℝ)) = p ^ ((1 : ℝ) / 2) := by
  rw [← rpow_add hp,
      show ((descendedDegreeFinite r : ℝ) / 2) + (-(jacobiNorm r : ℝ)) = 1 / 2 from by
        have := honest_descended_weight_unchanged r hr; linarith]

/-- **The corrected verdict: the descent does NOT beat the wall.** The honest finite-group
descended residual `1/2` is EQUAL to the `_JacobiFermatCohomology` wall residual `1/2` (it is not
strictly below it, as `_EquivariantDescentWeightDrop.descent_strictly_below_wall` claimed). -/
theorem descent_does_not_beat_wall (r : ℕ) (hr : 1 ≤ r) :
    (descendedDegreeFinite r : ℝ) / 2 - (jacobiNorm r : ℝ)
      = (corrDegree r : ℝ) / 2 - (jacobiNorm r : ℝ) := by
  rw [finite_etale_preserves_degree]

/-! ### Part 4 — what the finite quotient ACTUALLY gives: a factor-`n`, not a half-power of `p` -/

/-- The genuine saving from a finite étale `μ_n`-quotient: a factor `1/n` (the cover has degree
`n`; the isotypic component is `1/n` of the total). This is `p`-INDEPENDENT and combinatorial. -/
noncomputable def finiteQuotientSaving (n : ℕ) : ℝ := 1 / (n : ℝ)

/-- **The factor-`n` saving is NOT a half-power of `p`.** For any fixed subgroup size `n ≥ 1` and
all sufficiently large `p`, the field scale `√p` strictly exceeds the reciprocal `1/n`: the
combinatorial saving cannot account for a single half-power of `p`, so it leaves the BGK exponent
untouched. (Witness: at `p > n²` we have `√p > n > 1 = 1/(1/n)·(1/n)`, i.e. `1/n < √p`.) -/
theorem finite_quotient_gives_factor_n_not_sqrtP {n : ℕ} (hn : 1 ≤ n) {p : ℝ}
    (hp : (n : ℝ) ^ 2 < p) : finiteQuotientSaving n < Real.sqrt p := by
  unfold finiteQuotientSaving
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1n : 1 / (n : ℝ) ≤ (n : ℝ) := by
    rw [div_le_iff₀ hn0]; nlinarith
  have hnlt : (n : ℝ) < Real.sqrt p := by
    have hns : (n : ℝ) = Real.sqrt ((n : ℝ) ^ 2) := by
      rw [Real.sqrt_sq (le_of_lt hn0)]
    rw [hns]
    exact Real.sqrt_lt_sqrt (by positivity) hp
  linarith

/-! ### Part 5 — consolidated refutation verdict -/

/-- **REFUTATION verdict (theorem form).** Simultaneously:
(1) `μ_n` is dimension `0`, not `1` (`mu_n_is_dim_zero_not_one`) — the crux the brick gets wrong;
(2) the finite étale `μ_n`-quotient preserves the cohomological degree `2r-1`
    (`finite_etale_preserves_degree`), so the honest descended residual is `1/2`
    (`honest_descended_weight_unchanged`), EQUAL to the wall, not `0`
    (`descent_does_not_beat_wall`) — **the `√p` is NOT removed**;
(3) the finite quotient's genuine saving is the factor `1/n`, which is strictly below `√p` for
    large `p` (`finite_quotient_gives_factor_n_not_sqrtP`) — a `p`-independent combinatorial saving,
    NOT a half-power of `p`, leaving the BGK exponent intact.
Hence `_EquivariantDescentWeightDrop.weight_drop_kills_sqrtP` is FLAWED: the claimed √p-removal
rests on treating finite `μ_n` as a `1`-dimensional group. The thesis advance does NOT stand. -/
theorem refutation_verdict (r : ℕ) (hr : 1 ≤ r) :
    dimMuN ≠ dimGm ∧
    descendedDegreeFinite r = corrDegree r ∧
    ((descendedDegreeFinite r : ℝ) / 2 - (jacobiNorm r : ℝ) = 1 / 2) ∧
    ((descendedDegreeFinite r : ℝ) / 2 - (jacobiNorm r : ℝ)
        = (corrDegree r : ℝ) / 2 - (jacobiNorm r : ℝ)) :=
  ⟨mu_n_is_dim_zero_not_one,
   finite_etale_preserves_degree r,
   honest_descended_weight_unchanged r hr,
   descent_does_not_beat_wall r hr⟩

end ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDropREFUTED

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDropREFUTED.mu_n_is_dim_zero_not_one
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDropREFUTED.finite_etale_preserves_degree
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDropREFUTED.honest_descended_weight_unchanged
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDropREFUTED.honest_descended_residual_is_sqrtP
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDropREFUTED.descent_does_not_beat_wall
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDropREFUTED.finite_quotient_gives_factor_n_not_sqrtP
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDropREFUTED.refutation_verdict
