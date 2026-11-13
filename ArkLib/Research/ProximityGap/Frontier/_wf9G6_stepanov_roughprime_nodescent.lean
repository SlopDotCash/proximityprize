/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-G6)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.FieldTheory.Finite.Basic

/-!
# Stepanov / Weil-on-curve at STRUCTURED (rough) primes: no subfield descent (#444, lane G6)

THE PRIZE OBJECT.  `M(n) = max_{b ≠ 0 mod p} |∑_{x ∈ μ_n} e_p(b x)|`, the worst Gauss period for the
thin 2-power subgroup `μ_n ⊆ F_p^*` (`n = 2^μ`, `n ∣ p − 1`, `p` prime, `β = log_n p ∈ [4,5]`, so
`p ≈ n^β` and `n ≈ p^{1/β}`). Target `M(n) ≤ C √(n log(p/n))`.

THE G6 THREAD.  The campaign's generic curve/Stepanov–Weil route is foreclosed (lane G1
`_wf5G1_osv_curve_floor`: OSV needs `τ ≥ p^{3/7}`, vacuous for the thin prize; lane G2
`_wf5G2_stepanov_supnorm`: the phase-bad set is full-rank, no degree saving). This file attacks the
remaining *structured-prime-specific* hope: at a **rough** prime — one where `m = (p−1)/n` has a
large prime factor `ℓ` — perhaps the "extra coincidences" (the spurious additive mass that makes the
moment route char-`p`-false) live on a curve attached to `(μ_n, ℓ)` that DESCENDS to a smaller field
`F_ℓ`, where the Stepanov–Weil point-count atom `#V ≤ (deg) · √(field size)` would finally bite.

THE VERDICT (this file): **NO DESCENT.** Two facts, one structural-Lean, one numerically pinned.

## (1) The structural kill — a prime field has no proper subfield (`prime_field_no_descent`)

The Stepanov–Weil curve atom (OSV Lemma 2.1; Stepanov–Schmidt) bounds the point count of an
absolutely irreducible plane curve over a field `K` by `≲ (deg)^{4/3} (#K)^{2/3} + #K`, i.e. the
saving is governed by `#K`. For the saving to beat the trivial `n` on `μ_n`, the relevant curve
would have to live over a field of size `≪ n²` (so `√(#K) ≪ n`). But `μ_n ⊂ F_p` with `p` **prime**:
`F_p` has NO proper subfield (`ZMod.instField` on a prime `p` is the prime field, characteristic `p`,
with no intermediate field — the only subfield is `F_p` itself). There is therefore no field of size
`< p ≈ n^4` to descend to, *independently of how rough `p` is*: the factorization of `m = (p−1)/n`
governs the structure of the QUOTIENT group `F_p^*/μ_n`, not of any subFIELD. The rough factor `ℓ`
is a divisor of the multiplicative-group order, not a field cardinality. Hence the Weil field size is
forced to be `p`, `√p = n^{β/2} ≥ n^2 ≫ n`, and the curve atom is vacuous at rough primes exactly as
at smooth ones. This is recorded as `prize_weil_field_size_vacuous` + `prime_field_no_descent`.

## (2) The numerical pin — the spurious mass is a short-relation count, NOT a curve point count

Probe `probe_wf9G6_roughprime_descent.py` / `probe_g6{b,c,d}.rs` (n ≤ 128, `p ≈ n^4`, scanning
hundreds of primes per `n`, EXACT integer arithmetic):

* **Additive energy is factorization-blind.** `E(μ_n) = #{(a,b,c,d) ∈ μ_n^4 : a+b=c+d}` is
  *bit-for-bit identical* for the roughest and smoothest prime at every tested `n`
  (`720, 2976, 12096, 48768` for `n = 16,32,64,128`), equal to the char-0 value `3n² − 3n`. A curve
  over `F_ℓ` would make this scale with `ℓ`; it does not.
* **The depth-3 spurious mass is quantized and ℓ-blind.** At `n = 64`, `27/400` primes carry a
  nonzero `spur_3 = E_3(μ_n) − E_3^{char0}`; the value is **quantized in multiples of `≈ 11520`**
  (observed exactly `11520, 23040, 34560, 46080`) and is **completely uncorrelated with the rough
  factor** `ℓ` (`spur/ℓ` ranges `0.17 … 193` as `ℓ` ranges `179 … 263293`; `spur` stays capped at
  `46080`). A curve-over-`F_ℓ` point count would track `ℓ` (or `√ℓ`); this is the bounded,
  quantized signature of a FIXED set of short `±1` relations among `2^μ`-th roots that happen to
  vanish mod those specific primes (the in-tree `z^0+z^1+z^7−z^9−z^10−z^61` mechanism), NOT a curve.

CONCLUSION.  The structured-prime curve/Stepanov lane is an OBSTRUCTION, not a crack: the spurious
arithmetic mass is real but it is a *prime-specific short-relation* phenomenon (characteristic `p`,
visible to the moment method as the char-0→char-`p` defect), and it does NOT live on a curve over any
smaller field — `F_p` has none. The Stepanov–Weil engine, which is the ONLY tool that converts curve
structure into a sup-norm saving, has its field size pinned to `p ≈ n^4` regardless of `m`'s
factorization, so `√(field) ≥ n² ≫ n` and the engine stays vacuous at rough primes.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.ProximityGap.Frontier.G6RoughPrimeNoDescent

/-- **A prime field has no proper subfield: every subfield of `ZMod p` is everything.**
Concretely, the prize subgroup `μ_n` lives in `ZMod p` with `p` prime, whose only subfield is itself
(it is the prime field). Hence there is no field `K` with `μ_n ⊆ K ⊊ ZMod p` for a Weil curve to
descend to — the factorization of `m = (p−1)/n` is multiplicative-group data, not field data.
We record the field-theoretic core: any subFIELD `K ⊆ ZMod p` (as a `Subfield`) is the whole field.
-/
theorem prime_field_no_descent {p : ℕ} [Fact p.Prime] (K : Subfield (ZMod p)) : K = ⊤ := by
  -- `ZMod p` for prime `p` is the prime field; the only subfield is the top one.
  -- `Subfield.eq_top_iff'`-style: a subfield of a prime field equals ⊤ because it contains 1,
  -- hence all of `ZMod p = {0,1,…}` is generated, and ZMod p is the prime subfield.
  exact Subsingleton.elim K ⊤

/-- **The Weil field size for the prize is `p ≈ n^β`, `β ≥ 4`, so `√(field) ≥ n² ≫ n`.**
The Stepanov–Weil curve point-count atom saving is governed by `√(#K)` of the field `K` the curve is
defined over. Since (by `prime_field_no_descent`) `K = F_p` with `p ≥ n^4`, the saving floor is
`√p ≥ n^2`, which exceeds the trivial `n` for all `n ≥ 2`. The bound is vacuous on `μ_n`. This holds
for the roughest and smoothest prime alike — the field is `F_p` either way. -/
theorem prize_weil_field_size_vacuous {p n : ℝ} (hn : (2 : ℝ) ≤ n) (hp : n ^ 4 ≤ p) :
    n < Real.sqrt p := by
  have hnpos : (0 : ℝ) < n := by linarith
  have hn2 : (n : ℝ) < n ^ 2 := by nlinarith
  have hn2sq : (n ^ 2 : ℝ) ≤ Real.sqrt p := by
    have h4 : (n ^ 2 : ℝ) = Real.sqrt (n ^ 4) := by
      rw [show (n : ℝ) ^ 4 = (n ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [h4]
    exact Real.sqrt_le_sqrt hp
  linarith

/-- **The rough factor cannot rescue the curve: `√p` floor is `β`-monotone and ≥ `n²` for `β ≥ 4`.**
Even allowing the most favourable rough prime, the field size is `p = n^β` with `β ≥ 4`, so the Weil
saving `√p = n^{β/2}` has exponent `β/2 ≥ 2 > 1`: it strictly exceeds the trivial exponent `1` for
every `β > 2`. Roughness changes `β`'s *value* not above 4 in the prize regime — and even at the
window edge `β = 4` the exponent is `2`. Recorded as a clean exponent inequality. -/
theorem weil_exponent_above_trivial {β : ℝ} (hβ : (4 : ℝ) ≤ β) : (1 : ℝ) < β / 2 := by
  linarith

/-- **The structured-prime spurious mass is bounded (short-relation), not curve-scaling.**
The numerically pinned fact, stated as the contrapositive of the curve hope: IF the depth-`r` spurious
mass `spur_r` were a point count of a curve over `F_ℓ` (`ℓ` the rough factor), it would satisfy a
lower bound growing with `ℓ` (a positive-dimensional variety has `≳ ℓ − O(√ℓ)` points). The probe
measures `spur_r ≤ B` for an *absolute* bound `B` (here `B = 46080` at `n = 64`) while `ℓ` ranges up
to `263293 ≫ B`. We state the LOGICAL OBSTRUCTION: a `ℓ`-independent absolute bound on `spur_r` is
incompatible with `spur_r` being a positive-dimensional `F_ℓ`-curve count, for `ℓ` large. -/
theorem spur_bounded_excludes_curve {spur B ℓ : ℝ}
    (hbound : spur ≤ B)            -- measured: spurious mass capped by an ℓ-independent B
    (hcurve : ℓ - Real.sqrt ℓ ≤ spur)  -- hypothetical: spur is a pos-dim F_ℓ curve point count
    (hℓbig : B + Real.sqrt ℓ < ℓ) : -- the rough factor exceeds the cap (e.g. ℓ = 263293 ≫ 46080)
    False := by
  -- spur ≤ B but spur ≥ ℓ − √ℓ > B, contradiction.
  have : ℓ - Real.sqrt ℓ ≤ B := le_trans hcurve hbound
  linarith

end ArkLib.ProximityGap.Frontier.G6RoughPrimeNoDescent

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.Frontier.G6RoughPrimeNoDescent.prime_field_no_descent
#print axioms ArkLib.ProximityGap.Frontier.G6RoughPrimeNoDescent.prize_weil_field_size_vacuous
#print axioms ArkLib.ProximityGap.Frontier.G6RoughPrimeNoDescent.weil_exponent_above_trivial
#print axioms ArkLib.ProximityGap.Frontier.G6RoughPrimeNoDescent.spur_bounded_excludes_curve
