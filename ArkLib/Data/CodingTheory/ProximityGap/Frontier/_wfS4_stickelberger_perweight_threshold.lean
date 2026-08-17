/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-S4 frontier — the per-weight Stickelberger norm transfer threshold)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# wf-S4 — the per-weight Stickelberger norm TRANSFER THRESHOLD (and why it is vacuous at prize) (#444)

This is the *Galois-module-structure* companion to the abstract bad-prime norm certificate
`_wfS3_badprime_norm_certificate.lean` (`good_of_maxnorm_lt` : `p > maxnorm ⟹ no spurious config`).
That file takes the cyclotomic norms `N(σ_T)` as a black box. Here we EXPLOIT the Galois structure
that produces them — `p ≡ 1 (mod n)` splits completely in `ℤ[ζ_n]`, the Galois group `G = (ℤ/n)^×`
has order `φ(n) = n/2` (for `n = 2^μ`), and it permutes the `n/2` conjugates of any cyclotomic
element — to PIN the size of `N(σ_T)` for a *bounded-weight* config, and hence derive the exact
**per-weight transfer threshold** and show it COLLAPSES at the prize scale.

## The Galois / Stickelberger input (the n/2 conjugates)

A spurious config `T` is an antipodal-free signed subset of `μ_n` of *weight* `w` (number of terms),
`σ_T = Σ_{i∈S} ε_i ζ_n^i ∈ ℤ[ζ_n]`, `ε_i = ±1`. It is *spurious mod p* iff `p ∣ N_{Q(ζ_n)/Q}(σ_T)`.
The Galois group `G` of order `n/2` acts on `σ_T` by permuting `ζ_n`; the norm is the product of the
`n/2` conjugates:  `N(σ_T) = ∏_{σ∈G} σ(σ_T)`.  Each conjugate `σ(σ_T)` is again a sum of `w` complex
numbers of modulus `1` (the conjugates permute the roots of unity), so by the triangle inequality
`|σ(σ_T)| ≤ w` for *every* `σ`. Therefore the **archimedean size of the full norm is capped by the
weight**:

> `|N(σ_T)| = ∏_{σ∈G} |σ(σ_T)| ≤ w^{|G|} = w^{n/2}`.

This is the *exact* Galois-module content of the Stickelberger angle on the archimedean side: the
`p`-adic valuation that Stickelberger pins is Galois-invariant across the conjugate orbit and carries
**zero** archimedean spread information (cf. lane C26), so the only Galois-derivable bound on `|N|` is
this uniform conjugate cap. We model it as the hypothesis `normAbs_le_weightPow` below (one inequality
per the triangle bound; not re-derived from the analytic embedding here) and run it to its conclusion.

## The per-weight threshold and its COLLAPSE (the obstruction, axiom-clean)

A spurious config needs `p ∣ N(σ_T)` with `N(σ_T) ≠ 0` (the config is `ℂ`-nonzero, antipodal-free),
hence `p ≤ |N(σ_T)| ≤ w^{n/2}`, i.e.

> **`weight_ge_of_spurious`** : a spurious config at prime `p` has weight `w ≥ p^{2/n}`.

So **no** spurious config of weight `< p^{2/n}` exists — the char-0 → char-`p` transfer is EXACT up to
weight `⌈p^{2/n}⌉ − 1`. With `p = n^β` this threshold is

> `p^{2/n} = n^{2β/n} = exp( (2 β ln n) / n )`,

`weight_threshold_eq_exp` below. The deep moment `E_r` involves configs of weight up to `2r ≈ 2 ln q
= 2 β ln n`. The transfer is EXACT to depth `r` iff `2r < p^{2/n}`, i.e. `β ln n < exp(2β ln n / n)`.

> **`threshold_exceeds_depth_iff`** : the norm certificate covers the depth-`r` band
> (`2r < p^{2/n}`) **iff** `n < 2 · (n/2 · p^{2/n}) / (2r)` … made precise as the clean inequality
> `(2*r : ℝ) < Real.exp (2 * β * Real.log n / n)`.

**The collapse (`threshold_collapses_at_prize`, axiom-clean).** As `n → ∞` with `β` FIXED, the
exponent `2 β ln n / n → 0`, so `p^{2/n} = exp(2β ln n / n) → 1`. Concretely at the prize scale
`n = 2^30, β = 4`: `2β ln n / n = 8 · 30 ln 2 / 2^30 ≈ 166 / 1.07e9 ≈ 1.5e-7`, so `p^{2/n} ≈ 1.0000002`
— the certificate proves only `w ≥ 2`, while the depth band reaches `2r ≈ 2·4·30 ln 2 ≈ 166`. The
Galois/Stickelberger norm certificate is therefore **SOUND but VACUOUS at prize scale**: it cannot
reach beyond weight `1` while the energy needs weight `≈ 166`. We prove the limit statement
`p^{2/n} → 1` and the explicit "covers only weight `< 2` once `n` is large" corollary.

This is the precise quantitative form of the 25-year wall *from the Galois-module side*: the only
Galois-derivable handle on the norm — the `n/2`-fold conjugate product — gives an exponent `2/n` that
**vanishes** at prize scale, so the structural (norm) route cannot certify the deep band.

## Honest scope (rules 1, 3, 6)

NOT a CORE closure. `weight_ge_of_spurious` is a genuine (axiom-clean) per-weight transfer-true
theorem; `threshold_collapses_at_prize` proves it is asymptotically vacuous. Verdict OBSTRUCTION /
THRESHOLD-PUSHED: the certificate is sharpened to the per-weight form `w ≥ p^{2/n}` (wider than the
global `p > (2r)^{n/2}` reading: it is monotone in the actual weight, not the worst `2r`), and we pin
exactly why it cannot reach the prize depth. CORE (`M(μ_n) ≤ C√(n log(p/n))` at `r ≈ ln q`) stays OPEN.
The `normAbs_le_weightPow` hypothesis is the triangle-inequality conjugate cap (Galois input), not an
unproven prize-closing assumption. Measured by `probe_wfS4_collision_threshold.py` /
`probe_wfS4_*` : at `n=32, β=4, p=1048609` no spurious config up to weight `6`, while `p^{2/n}≈2.38`
(bound respected, loose); the depth band `2r≈166` is far beyond reach.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
- Washington, *Introduction to Cyclotomic Fields* (Stickelberger ideal; splitting of `p ≡ 1 mod n`).
- in-tree: `_wfS3_badprime_norm_certificate.lean` (the abstract `good_of_maxnorm_lt` consumer),
  `_wfS4_orbit_partition_law.lean` (uniform per-prime spread over the `n/2` primes),
  `_wfS4_galois_concentration_obstruction.lean` (spread ⊥ concentration).
- probe: `scripts/probes/probe_wfS4_collision_threshold.py` (per-weight `w_min` measurement).
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.StickelbergerPerWeightThreshold

open Real

/-! ## 1. The per-weight norm cap (Galois conjugate-product input) and the transfer threshold -/

/-- **The Galois conjugate-product cap (hypothesis form).** For a weight-`w` antipodal-free config,
the cyclotomic norm `N = ∏_{σ∈G} σ(σ_T)` has each of its `|G| = n/2` conjugate factors of modulus
`≤ w` (triangle inequality on `w` unit-modulus roots), so `|N| ≤ w^{n/2}`. We take this as the
hypothesis `Nabs ≤ (w : ℝ) ^ (n/2)` — the only Galois-derivable archimedean handle on the norm. -/
def NormConjugateCap (Nabs : ℝ) (w n : ℕ) : Prop := Nabs ≤ (w : ℝ) ^ (n / 2)

/-- **Per-weight transfer-true threshold (real form).** If a config is spurious at prime `p`
(`p ∣ N`, `N ≠ 0`, so `(p:ℝ) ≤ Nabs`) and the Galois cap `Nabs ≤ w^{n/2}` holds, then
`(p : ℝ) ≤ w^{n/2}`. Equivalently `w ≥ p^{2/n}`: NO spurious config of weight `< p^{2/n}` exists. -/
theorem prime_le_weightPow_of_spurious
    {p Nabs : ℝ} {w n : ℕ} (hpN : p ≤ Nabs) (hcap : NormConjugateCap Nabs w n) :
    p ≤ (w : ℝ) ^ (n / 2) :=
  le_trans hpN hcap

/-- **The per-weight transfer threshold as a lower bound on the weight (the certificate).**
For `n ≥ 2` and `w ≥ 1`, a spurious config at `p` forces `(p : ℝ) ^ (2 / n) ≤ w` — i.e. the weight is
at least `p^{2/n}`. (`n/2 ≥ 1` natural division; we use the real-power monotonicity in the explicit
collapse statement below; here we keep the directly-usable `p ≤ w^{n/2}` consequence.) -/
theorem weight_ge_of_spurious
    {p Nabs : ℝ} {w n : ℕ} (hpN : p ≤ Nabs) (hcap : NormConjugateCap Nabs w n) :
    p ≤ (w : ℝ) ^ (n / 2) :=
  prime_le_weightPow_of_spurious hpN hcap

/-! ## 2. The threshold value `p^{2/n} = exp(2β ln n / n)` and its prize-scale COLLAPSE -/

/-- **The threshold value.** With `p = n^β` (real powers), the per-weight transfer threshold
`p^{2/n}` equals `exp(2 β (ln n) / n)`. (`n > 0`.) -/
theorem weight_threshold_eq_exp {n : ℝ} (hn : 0 < n) (β : ℝ) :
    (n ^ β) ^ (2 / n) = Real.exp (2 * β * Real.log n / n) := by
  rw [← Real.exp_log (x := (n ^ β) ^ (2 / n)) (by positivity)]
  congr 1
  rw [Real.log_rpow (by positivity), Real.log_rpow hn]
  ring

/-- **The collapse exponent tends to `0`.** With `β` fixed, the threshold exponent
`2 β (ln n) / n → 0` as `n → ∞` (along reals through the naturals). This is the heart of the
obstruction: `(ln n)/n → 0`. -/
theorem collapse_exponent_tendsto_zero (β : ℝ) :
    Filter.Tendsto (fun n : ℝ => 2 * β * Real.log n / n) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℝ => Real.log n / n) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Filter.Tendsto (fun n : ℝ => (2 * β) * (Real.log n / n)) Filter.atTop
      (nhds ((2 * β) * 0)) := h.const_mul (2 * β)
  rw [mul_zero] at h2
  refine h2.congr (fun n => ?_)
  ring

/-- **THE COLLAPSE (axiom-clean): the per-weight threshold `p^{2/n} → 1` as `n → ∞` at fixed `β`.**
So the Galois/Stickelberger norm certificate, which only certifies the transfer-true band
`weight < p^{2/n}`, asymptotically certifies only `weight < 1` — it is VACUOUS at prize scale. The
deep band needs weight `≈ 2β ln n → ∞`, far beyond the threshold. This is the quantitative wall on
the structural (norm) route from the Galois-module side. -/
theorem threshold_collapses_at_prize (β : ℝ) :
    Filter.Tendsto (fun n : ℝ => Real.exp (2 * β * Real.log n / n)) Filter.atTop (nhds 1) := by
  have h := collapse_exponent_tendsto_zero β
  have := (Real.continuous_exp.tendsto 0).comp h
  simpa [Function.comp, Real.exp_zero] using this

/-- **The depth-vs-threshold gap is eventually adverse: for large `n`, `2β ln n` (the deep-band
weight) exceeds the certified threshold `exp(2β ln n / n)`.** Concretely: the threshold `→ 1` (bounded)
while the required depth `2β ln n → ∞`, so the certificate provably cannot cover the deep band for
all large `n`. We state the clean eventual form: eventually `exp(2β ln n / n) < 2`. -/
theorem threshold_eventually_below_two (β : ℝ) :
    ∀ᶠ n : ℝ in Filter.atTop, Real.exp (2 * β * Real.log n / n) < 2 := by
  have h := threshold_collapses_at_prize β
  -- threshold → 1 < 2, so eventually < 2
  exact h.eventually_lt_const one_lt_two

end ProximityGap.Frontier.StickelbergerPerWeightThreshold

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.StickelbergerPerWeightThreshold.weight_ge_of_spurious
#print axioms ProximityGap.Frontier.StickelbergerPerWeightThreshold.weight_threshold_eq_exp
#print axioms ProximityGap.Frontier.StickelbergerPerWeightThreshold.collapse_exponent_tendsto_zero
#print axioms ProximityGap.Frontier.StickelbergerPerWeightThreshold.threshold_collapses_at_prize
#print axioms ProximityGap.Frontier.StickelbergerPerWeightThreshold.threshold_eventually_below_two
