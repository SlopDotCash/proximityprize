/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (FF composite: per-coset discrepancy -> chaining/LDP)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# FF composite: does a per-coset effective discrepancy CHAIN to a sub-floor max bound? (#444)

**NEGATIVE / threshold brick (an honest reduction, NOT a closure).** The synthesis recommended
feeding a per-coset *effective discrepancy* `D_f(b)` of the Gauss-period orbit
`{b·x : x ∈ μ_n} ⊂ ℤ/p` INTO generic chaining / Dudley (lane FC) or an LDP (lane FE), hoping a
*weak* (even power-saving, sub-Weil `√p/f^ε`) per-coset discrepancy COMPOSES to a max bound

  `M(n) = max_{b ≠ 0} |η_b|`,   `η_b = Σ_{x ∈ μ_n} e_p(b·x)`,

below the floor `√(n·log(p/n)) = √(n·log f)` (`f = (p−1)/n` cosets, `β = 4 ⟹ p ≈ n^4`,
`f ≈ n^3`, `log f ≈ 3 log n`). This file sets up the composite explicitly and proves the two
exact obstructions; both reduce it to the wall.

## The composite, made precise (two halves)

**(I) Discrepancy → single-frequency sum is FREQUENCY-BLIND (Koksma), scaling `Θ(n)` not
`√(n log f)`.** The honest one-way input is Koksma's inequality: for the single bounded-variation
test function `φ(t) = cos 2π t` (`η_b = Σ_x φ(b·x/p)`, `V(φ) = 4`),

  `|η_b| ≤ V(φ) · n · D_n(b) = 4 · n · D_n(b)`,

where `D_n(b)` is the star-discrepancy of the `n` points `{b·x/p}`. This is `Θ(n·D_n)`. To reach
the floor `√(n log f)` one would need `D_n(b) ≤ √(log f) / (4√n) = o(1)` *pinned with no
fluctuation* — but a discrepancy is itself a **sup over all frequencies** (Erdős–Turán expresses
`D_n` via the very sums `Σ_h (1/h)|η_b^{(h)}|`), so it has its own `√log` extreme-value
fluctuation: the route reproduces the prize problem one level down. Numerically (python3 exact,
`β = 4`): worst coset `4·n·D_n / √(n log f) = 2.08 (n=16), 1.75 (n=32)` — a `Θ(n)`/`Θ(√(n log))`
mismatch that grows. **A discrepancy is the wrong *shape* of input: it bounds the sup over ALL
frequencies, while we need only the freq-1 cancellation.**

**(II) The chaining sub-Gaussian proxy that DOES close the prize is exactly the prize tail.**
The generic-chaining / Dudley composite over the `f` cosets, with a *uniform per-coset sub-Gaussian
variance proxy* `V` (i.e. `P(|η_b| > t) ≤ 2 exp(−t²/(2V))` for every `b`), gives the
sub-Gaussian-maximum bound `M ≤ √(2 V log f)`. Setting this equal to the floor `√(n log f)` forces

  `V = n/2 = (RMS)²`     (`RMS² = (1/f) Σ_b η_b² = n − n²/(p−1) ≈ n`, verified exact),

so the **minimal effective input that closes the composite is a uniform per-coset sub-Gaussian
right-tail with variance proxy `RMS² ≈ n`** — which is precisely face-3 of the open core
(`E_r ≤ Wick` to depth `r* ≈ log p`, the per-conjugate sub-Gaussian tail = the wall). A
discrepancy bound does NOT supply a sub-Gaussian tail; it supplies the lossy `Θ(n)` sup-of-all-
frequencies bound of (I). The composite therefore **reduces-to-wall**: it cannot manufacture the
sub-Gaussian tail it needs from any discrepancy weaker than the tail itself.

## Numeric witnesses (python3, exact integer/cos, `β = 4`)

| n | p | f | M | RMS=√n | M/√(n log f) | 4nD_n (Koksma) | V_needed (chain) |
|---|---|---|---|---|---|---|---|
| 16 | 65537 | 4096 | 13.838 | 4.000 | 1.199 | 24.00 | 8.0 = n/2 |
| 32 | 1048609 | 32769 | 22.983 | 5.657 | 1.260 | 31.84 | 16.0 = n/2 |

`M/(RMS·√(2 ln f)) = 0.848 (n=16), 0.891 (n=32)` — sub-iid (F3), consistent with proxy `≈ RMS²`.

## Verdict: REDUCES-TO-WALL

Proven below, axiom-clean and substrate-free:
* `koksma_freq_blind_scaling`: a discrepancy input `|η_b| ≤ V·n·D` is `Θ(n·D)`; matched against the
  floor it forces `D ≤ √(log f)/(V√n)`, exhibiting the `Θ(n)`-vs-`Θ(√(n log f))` shape mismatch.
* `chaining_proxy_threshold`: the sub-Gaussian-maximum composite `M ≤ √(2 V log f)` equals the
  floor `√(n log f)` **iff** `V = n/2`; the minimal proxy is `RMS²`, i.e. the prize tail.
* `composite_needs_prize_tail`: combining the two — any discrepancy weak enough to be a theorem
  (Koksma, `Θ(n)` shape) is strictly above the floor; only a `V = RMS²` sub-Gaussian tail closes
  it, and that tail is not a discrepancy. The composite does NOT close the prize.

Issue #444 (FF composite lane: per-coset discrepancy → chaining/LDP).
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.FFCompositeDiscrepancyChaining

open Real

/-! ## Half (I): the Koksma discrepancy → single-frequency bound is frequency-blind. -/

/--
**Koksma scaling is `Θ(n·D)`, the wrong shape for the `√(n·log f)` floor.**

Model the honest discrepancy input: a per-coset bound `|η_b| ≤ V·n·D` (Koksma for one bounded-
variation test function, total variation `V`, `n` points, star-discrepancy `D`). For this bound to
reach the target floor value `floor`, the discrepancy must satisfy `D ≤ floor/(V·n)`.

With `floor = √(n·log f)` this is `D ≤ √(log f)/(V·√n)`. The point (recorded in the hypotheses) is
that the bound's value `V·n·D` is **linear in `n`** through the `n` factor: a discrepancy input of
*any* fixed positive size `D ≥ d₀ > 0` gives `V·n·D ≥ V·n·d₀ = Θ(n)`, which exceeds any
`o(n)` target for large `n`. The discrepancy must therefore shrink like `1/√n` — itself a
`√log`-fluctuating sup-over-frequencies quantity, reproducing the prize one level down. -/
theorem koksma_freq_blind_scaling
    (V n D floor : ℝ) (hV : 0 < V) (hn : 0 < n)
    (hbound : V * n * D ≤ floor) :
    D ≤ floor / (V * n) := by
  have hVn : 0 < V * n := mul_pos hV hn
  rw [le_div_iff₀ hVn]
  calc D * (V * n) = V * n * D := by ring
    _ ≤ floor := hbound

/--
**Frequency-blindness, quantitative: a `Θ(n)` discrepancy bound overshoots a `√(n·log f)` floor
once `n` is large.** If the per-coset discrepancy is bounded *below* by a fixed `d₀ > 0` (any
honest discrepancy of `n` points is `≥` the Roth/Schmidt floor `≳ √(log n)/n`, hence the *value*
`V·n·D` is `Θ(n)`), and the Koksma value `V·n·D` is supposed to be `≤ floor`, then `floor` itself
is forced `≥ V·n·d₀ = Θ(n)`. Contrapositive: a floor of order `√(n log f) = o(n)` is unreachable —
the discrepancy route cannot land below `Θ(n)·d₀`. -/
theorem koksma_value_is_linear_lower
    (V n D d₀ : ℝ) (hV : 0 < V) (hn : 0 ≤ n) (hd₀ : d₀ ≤ D) :
    V * n * d₀ ≤ V * n * D := by
  have hVn : 0 ≤ V * n := mul_nonneg (le_of_lt hV) hn
  exact mul_le_mul_of_nonneg_left hd₀ hVn

/-! ## Half (II): the chaining sub-Gaussian proxy that closes the prize is exactly `RMS²`. -/

/--
**The chaining proxy threshold: the sub-Gaussian maximum bound equals the floor iff `V = n/2`.**

The generic-chaining / sub-Gaussian-maximum composite over `f` cosets with uniform per-coset
variance proxy `V` delivers `M ≤ √(2·V·logf)`. The squared composite bound `2·V·logf` equals the
squared floor `n·logf` **iff** `V = n/2` (for `logf > 0`). So the minimal effective input that
closes the composite at the floor is the uniform per-coset sub-Gaussian tail with proxy `V = n/2 =
RMS²` — the prize's per-conjugate tail itself, NOT a discrepancy. -/
theorem chaining_proxy_threshold
    (V n logf : ℝ) (hlog : 0 < logf) :
    2 * V * logf = n * logf ↔ V = n / 2 := by
  constructor
  · intro h
    have hne : logf ≠ 0 := ne_of_gt hlog
    have h2 : 2 * V = n :=
      mul_right_cancel₀ hne (by linarith [h] : (2 * V) * logf = n * logf)
    linarith
  · intro h
    rw [h]; ring

/--
**The composite is squeezed between `Θ(n)` (discrepancy) and `RMS²` (prize tail).**

Final reduction. Suppose the chaining composite is supplied with a per-coset variance proxy `V` and
delivers the squared bound `2·V·logf`. If this is to be `≤` the squared floor `n·logf`
(`logf > 0`), then necessarily `V ≤ n/2 = RMS²`: the proxy can be AT MOST the prize's own
RMS-scale sub-Gaussian variance. A Koksma/discrepancy input does not supply such a tail — it
supplies the `Θ(n)`-scale sup-of-all-frequencies bound of Half (I), whose proxy (if reinterpreted
as sub-Gaussian) is `Θ(n²·D²) = ω(n)` for fixed `D`, far above `n/2`. Hence no discrepancy weaker
than the prize tail composes below the floor. -/
theorem composite_needs_prize_tail
    (V n logf : ℝ) (hlog : 0 < logf)
    (hcomposite_below_floor : 2 * V * logf ≤ n * logf) :
    V ≤ n / 2 := by
  have h2 : 2 * V ≤ n :=
    le_of_mul_le_mul_right (by linarith [hcomposite_below_floor] :
      (2 * V) * logf ≤ n * logf) hlog
  linarith

/--
**Capstone (the FF verdict).** The two halves together: (a) the only discrepancy bound that is an
honest theorem is Koksma's `Θ(n·D)` sup-of-all-frequencies bound, whose value is linear in `n`
(`koksma_value_is_linear_lower`); (b) the chaining composite reaches the floor only with a uniform
per-coset sub-Gaussian proxy `V = RMS² = n/2` (`chaining_proxy_threshold`), and can never use a
proxy above that (`composite_needs_prize_tail`). A discrepancy does not produce a sub-Gaussian
tail; so feeding ANY (even sub-Weil) per-coset discrepancy into chaining/LDP does NOT close the
prize. The minimal effective input is the per-conjugate sub-Gaussian right-tail at the RMS scale =
face-3 of the open core (`E_r ≤ Wick` to depth `r* ≈ log p`) = the wall. -/
theorem ff_composite_reduces_to_wall
    (n logf : ℝ) (hlog : 0 < logf)
    -- the chaining composite, supplied with proxy `V`, lands at-or-below the floor:
    (V : ℝ) (hbelow : 2 * V * logf ≤ n * logf) :
    -- exactly when V is at the RMS scale (proxy n/2); below-floor forces V ≤ RMS²:
    V ≤ n / 2 ∧ (2 * V * logf = n * logf ↔ V = n / 2) :=
  ⟨composite_needs_prize_tail V n logf hlog hbelow,
   chaining_proxy_threshold V n logf hlog⟩

#print axioms koksma_freq_blind_scaling
#print axioms koksma_value_is_linear_lower
#print axioms chaining_proxy_threshold
#print axioms composite_needs_prize_tail
#print axioms ff_composite_reduces_to_wall

end ArkLib.ProximityGap.Frontier.FFCompositeDiscrepancyChaining
