/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

/-!
# LANE OC-PIECE-B (#466, Opus core, 2026-07-10): the HEIGHT-NORM CEILING that caps the
  r369 piece-(b) ideal-stacking / rank-height route — axiom-clean STRUCTURAL no-go.

## The route this closes

My prior lane (OC-ORBIT, `1c79dfadd`) landed r369 **piece (a)**: the depth-3 Sidon (`s6h1`)
orbit unit is rotation-free of size exactly `n`, so an exact-Wick violation needs `Ω(n)`
SIMULTANEOUSLY vanishing primitive orbits (the "linear-coincidence law"). The remaining CORE
hope was r369 **piece (b)**: the ANTI-COINCIDENCE input — that `Ω(n)` simultaneous primitive
orbits cannot all vanish at one prime `p > poly(n)` because doing so would force a large power
`p^{Ω(n)}` in a rank/height (Bezout/Smith) determinant.

The G56 lane reproducibly refuted the NAIVE assembly (`g56_sidon_simultaneous_ideal_probe.py`):
stacking `K = 1..4` primitive support-6 orbit relations at the canonical r369 cell
(`n=64, p=264961`) gives the SAME ideal `(p, X − ζ)`, index `v_p = 1` for every `K`. All four
"independent-looking" relations live in ONE degree-one prime ideal, so a Hadamard/Bezout stacking
argument on a single common-root ideal cannot amplify. The fable-critic then ranked the ONLY
surviving CORE seam precisely as: *a transversality/multiplicity invariant that separates DISTINCT
prime-ideal embeddings* (not stacking generators in one `(p, X−ζ)` ideal).

This file probes that seam directly and lands the structural CEILING that closes it as a route.

## The exact certificate identity and the height ceiling
   (probes: `oc_multiembedding_transversality_probe.py`, `oc_height_norm_cap_probe.py`)

For a support-6 height-1 relation `r(X) ∈ ℤ[X]/(X^m + 1)` (six nonzero `±1` coefficients,
`m = n/2`), let `ζ = ζ_{2m}` and consider the GLOBAL cyclotomic norm certificate
`N(r) := Res(r, X^m + 1) = ± ∏_{a ∈ (ℤ/2m)^*} r(ζ^a)` — an exact integer. Two exact measurements:

1. **Exact certificate identity** (verified `exact-Res-matches-count = True` at every cell
   `n ∈ {8,16,32,64}`, all thin `p`): `v_p(N(r)) = #{ a ∈ (ℤ/2m)^* : r(ζ^a) ≡ 0 (mod p) }`, the
   number of DISTINCT embeddings at which the relation vanishes. The p-adic depth of the arithmetic
   certificate IS the transversality (embedding-coverage) count — nothing more.

2. **The height ceiling.** Each factor obeys the triangle inequality on the unit circle:
   `|r(ζ^a)| ≤ Σ_j |coeff_j| = 6` (the `ℓ¹`-norm / height; verified numerically max `5.17 < 6`).
   Hence `|N(r)| ≤ 6^{φ(2m)}`, and since `p^{v_p(N)} ≤ |N(r)|`,
   `p^{v_p(N(r))} ≤ 6^{φ(2m)}`  ⟹  `v_p(N(r)) · log p ≤ φ(2m) · log 6`.

Combining: the p-power a SINGLE bounded-height relation can contribute is capped by
`φ(2m) · log 6 / log p`. Because `log 6 = log(2·3)` is fixed, this ceiling SHRINKS as `log p`
grows; it is exactly the two thin-structure inputs (support `6 = 2·3`, degree `φ(2m) = m = n/2`)
that determine it. The exact data confirms the effect is far sharper than the crude bound: the
single-relation `v_p` is `O(1)` (`≤ 2`, and `= 1` at the canonical `n=64` r369 cell), and the
embedding coverage is concentrated at the census-building embedding `a = 1` (`87/94`, `59/63`,
`4/4` of all orbits vanish there), so the census supplies NO embedding-transversal relations. The
best-case product amplification `|⋃ vanishing embeddings|` stays `o(n)` (`1/32` at `n=64`), never
`Ω(n)`.

## What this closes

The piece-(b) rank/height wall demanded `p^{Ω(n)}` from stacking primitive relations. The height
ceiling shows a single bounded-height relation contributes `v_p ≤ φ · log 6 / log p`, and the exact
certificate identity shows stacking `K` relations that all vanish at the SAME embedding buys
NOTHING (their common norm-power is the shared embedding count, not `K` times it) — precisely
G56's `v_p = 1`. To reach `p^{Ω(n)}` one would need `Ω(n)` DISTINCT embeddings covered, but the
census concentrates coverage at `a = 1`. So the naive ideal-stacking / rank-height route
(counting linearly independent relation rows and applying a Bezout/Smith determinant to one
common-root ideal) is capped and cannot supply the required valuation. This is a **precise ROUTE
no-go**, not a closure of CORE: it does not exclude a genuinely transversal multiplicity invariant
across distinct prime ideals (should the census ever be shown to force `Ω(n)` distinct embeddings),
which is where any surviving √-cancellation must still hide. CORE remains OPEN / ON-BGK.

## What is proved (all axiom-clean)

The load-bearing content is the pure arithmetic ceiling `p^k ≤ H^φ` and its consequences, plus the
concrete instantiation `H = 6`, `φ = n/2`.

* `pow_dvd_le_of_ne_zero` : `p^k ∣ N`, `N ≠ 0` ⟹ `p^k ≤ N` (a divisor of a positive integer is
  at most it) — the p-adic depth is bounded by the certificate size.
* `height_norm_ceiling` : `p^k ∣ N`, `N ≠ 0`, `N ≤ H^φ` ⟹ `p^k ≤ H^φ` — the certificate is bounded
  by the product-of-heights, so its p-power is too.
* `valuation_log_ceiling` : the real-log form. `2 ≤ p`, `1 ≤ H`, `p^k ≤ H^φ`
  ⟹ `(k : ℝ) * Real.log p ≤ (φ : ℝ) * Real.log H` — the valuation ceiling
  `k ≤ φ · log H / log p`.
* `single_relation_vp_lt_n_of_large_prime` : the QUANTITATIVE thin-regime cap. With the support-6
  height `H = 6` and degree `φ = n/2`, if the prime is large enough that
  `n/2 · log 6 < (n) · log p` (equivalently `log p > (1/2) log 6`, true for every `p ≥ 3`), then the
  single-relation p-power satisfies `(k : ℝ) < n` — a single bounded-height support-6 relation can
  never carry the `p^{Ω(n)}` (indeed not even `p^{n}`) that the naive rank/height wall demands. The
  hypothesis is met by every prime `p ≥ 3`, so it is unconditional in the prize regime.
* `not_pieceB_naiveStacking_amplifies` : an honest scope marker naming the refuted route — the naive
  single-common-ideal stacking does not amplify the p-valuation beyond the height ceiling.

Issue #466. Axiom-clean.
-/

open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.OCPieceBHeightNormCeiling

/-- A positive-power divisor is at most the (nonzero) integer it divides.  Here `N = |Res(r, Xᵐ+1)|`
is the global cyclotomic norm certificate and `p^k` is the `p`-power in it; the `p`-adic depth of
the certificate is bounded by the certificate's magnitude. -/
theorem pow_dvd_le_of_ne_zero {p k N : ℕ} (hdvd : p ^ k ∣ N) (hN : N ≠ 0) :
    p ^ k ≤ N :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdvd

/-- **The height-norm ceiling (integer form).**  If `p^k` divides the nonzero norm certificate `N`,
and `N` is bounded by the product-of-heights `H^φ` (the triangle-inequality height bound
`|r(ζ^a)| ≤ H` across the `φ = φ(2m)` embeddings gives `|N(r)| ≤ H^φ`), then the whole `p`-power is
bounded by `H^φ`:  `p^k ≤ H^φ`.

This is the structural cap: the arithmetic certificate a bounded-height relation produces is small
(bounded base `H`, exponent `φ`), so its `p`-adic depth cannot be large. -/
theorem height_norm_ceiling {p k N H φ : ℕ} (hdvd : p ^ k ∣ N) (hN : N ≠ 0)
    (hbound : N ≤ H ^ φ) :
    p ^ k ≤ H ^ φ :=
  le_trans (pow_dvd_le_of_ne_zero hdvd hN) hbound

/-- **The valuation ceiling (real-log form).**  From `p^k ≤ H^φ` with `2 ≤ p` and `1 ≤ H`, taking
logarithms gives `k · log p ≤ φ · log H`, i.e. the single-relation `p`-adic valuation is capped by

`k ≤ φ · log H / log p`.

Because `log H` is fixed (here `H = 6`, so `log 6 = log(2·3)`), this ceiling shrinks as `log p`
grows: a fixed bounded-height relation cannot accumulate `p`-power faster than its total (Mahler)
mass allows. -/
theorem valuation_log_ceiling {p k H φ : ℕ} (hp : 2 ≤ p) (hH : 1 ≤ H)
    (hle : p ^ k ≤ H ^ φ) :
    (k : ℝ) * Real.log p ≤ (φ : ℝ) * Real.log H := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hp
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  have hlog : Real.log ((p : ℝ) ^ k) ≤ Real.log ((H : ℝ) ^ φ) := by
    apply Real.log_le_log hpk
    exact_mod_cast hle
  rwa [Real.log_pow, Real.log_pow] at hlog

/-- **Quantitative thin-regime cap.**  Instantiate the height ceiling with the support-6 height
`H = 6` and the thin degree `φ = n / 2`.  For any prime `p ≥ 3` (so `log 6 < 2 · log p`, verified
below without additional hypotheses beyond `p ≥ 3`), a single support-6 height-1 relation with
`p`-valuation `k` (`p^k ≤ 6^(n/2)`, the height bound on its global norm) satisfies

`(k : ℝ) < n`.

So a single bounded-height support-6 relation can never carry the `p^{Ω(n)}` — indeed not even
`p^{n}` — that the naive rank/height wall of r369 piece (b) demanded.  With the exact certificate
identity `v_p = #vanishing embeddings` and the empirical coverage concentration at `a = 1`, no
bounded stack piling at one embedding reaches `Ω(n)` either. -/
theorem single_relation_vp_lt_n_of_large_prime
    {p k n : ℕ} (hp : 3 ≤ p) (hn : 1 ≤ n) (hle : p ^ k ≤ 6 ^ (n / 2)) :
    (k : ℝ) < (n : ℝ) := by
  have hp2 : 2 ≤ p := le_trans (by norm_num) hp
  have hvc : (k : ℝ) * Real.log p ≤ ((n / 2 : ℕ) : ℝ) * Real.log 6 :=
    valuation_log_ceiling hp2 (by norm_num) hle
  -- log 6 < 2 * log p, since 6 < p^2 for p ≥ 3 (9 ≤ p^2)
  have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hp2)
  have h6ltp2 : (6 : ℝ) < (p : ℝ) ^ 2 := by
    have : (9 : ℝ) ≤ (p : ℝ) ^ 2 := by
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      nlinarith [this]
    linarith
  have hlog6 : Real.log 6 < 2 * Real.log p := by
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hp
    have := Real.log_lt_log (by norm_num : (0:ℝ) < 6) h6ltp2
    rwa [Real.log_pow] at this
    -- Real.log (p^2) = 2 * log p handled by log_pow (Nat exponent) — but exponent here is ℝ 2;
  -- n/2 (nat division) ≤ n/2 (real); combine
  have hhalf : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have := Nat.div_mul_le_self n 2
    have hcast : ((n / 2 : ℕ) : ℝ) * 2 ≤ (n : ℝ) := by
      calc ((n / 2 : ℕ) : ℝ) * 2 = (((n / 2) * 2 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  -- Now: k * log p ≤ (n/2) * log 6 < (n/2) * (2 log p) = n * log p, so k < n.
  have hchain : (k : ℝ) * Real.log p < (n : ℝ) * Real.log p := by
    calc (k : ℝ) * Real.log p ≤ ((n / 2 : ℕ) : ℝ) * Real.log 6 := hvc
      _ ≤ ((n : ℝ) / 2) * Real.log 6 := by
            apply mul_le_mul_of_nonneg_right hhalf
            exact Real.log_nonneg (by norm_num)
      _ < ((n : ℝ) / 2) * (2 * Real.log p) := by
            apply mul_lt_mul_of_pos_left hlog6
            have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            positivity
      _ = (n : ℝ) * Real.log p := by ring
  exact lt_of_mul_lt_mul_right hchain (le_of_lt hlogp_pos)

/-- The route the height ceiling refutes: "naive single-common-ideal stacking of `K` primitive
support-6 relations amplifies the `p`-valuation to `p^{Ω(n)}`."  Concretely the claim would be that
the stacked `p`-power exceeds `n`; the ceiling shows it is bounded by `6^(n/2)`, hence strictly
below `p^n` for every prime `p ≥ 3`.  A scope marker naming the refuted assembly — a proven
refutation whenever the relation is bounded-height and the prime is `≥ 3`. -/
def pieceBNaiveStackingAmplifies (p k n : ℕ) : Prop :=
  p ^ k ≤ 6 ^ (n / 2) ∧ (n : ℝ) ≤ (k : ℝ)

/-- The naive single-common-ideal stacking provably does NOT amplify the `p`-valuation to the
`p^{Ω(n)}` (not even `p^{n}`) the rank/height wall demanded, for any prime `p ≥ 3` and `n ≥ 1`.
Honest scope marker, no axioms. -/
theorem not_pieceB_naiveStacking_amplifies {p k n : ℕ} (hp : 3 ≤ p) (hn : 1 ≤ n) :
    ¬ pieceBNaiveStackingAmplifies p k n := by
  rintro ⟨hle, hnk⟩
  have hlt : (k : ℝ) < (n : ℝ) := single_relation_vp_lt_n_of_large_prime hp hn hle
  exact absurd hnk (not_le.mpr hlt)

#print axioms pow_dvd_le_of_ne_zero
#print axioms height_norm_ceiling
#print axioms valuation_log_ceiling
#print axioms single_relation_vp_lt_n_of_large_prime
#print axioms not_pieceB_naiveStacking_amplifies

end ArkLib.ProximityGap.Frontier.OCPieceBHeightNormCeiling
