/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ChebotarevReductionModP
import Mathlib.FieldTheory.Separable

/-!
# The Vandermonde-mod-`p` crux of Chebotarev's theorem: the `n = 2` instance, the exact
  multiplicity law, and the honest small-`n` boundary (#407)

`_ChebotarevReductionModP.lean` reduced general-exponent Chebotarev to the named crux
`MinorTaylorMultiplicityLt p`: for every `n` and every pair of injective selections
`ri ci : Fin n → ZMod p`, the mod-`p` minor polynomial `detPolyModP ri ci` is *not* divisible by
`(X − 1)^{p−1}` (equivalently `rootMultiplicity 1 (detPolyModP ri ci) < p − 1`). This file delivers
the cleanly-provable layers of that crux and pins down its **exact range of validity**.

## What is PROVEN here (axiom-clean)

* **`minorTaylorMultiplicityLt_two`** (the headline): the `n = 2` instance of the crux, for any
  *odd* prime `p ≥ 3`. The `2 × 2` minor polynomial is the **binomial** `X^{e00+e11} − X^{e01+e10}`
  (`detPolyModP_two`); the two exponent sums differ mod `p` (`exponentSums_ne_mod_p`, the
  `chebotarev_two` content transported to exponents: their difference is the nonzero field element
  `(ci 0 − ci 1)(ri 1 − ri 0)`), so the root `1` has multiplicity `≤ 1 < p − 1`
  (`rootMultiplicity_one_binomial_le`, via separability of `X^m − 1` for `p ∤ m`).

* **The binomial / separability toolkit** (`rootMultiplicity_neg`, `binomial_factor`,
  `rootMultiplicity_one_X_pow_sub_one_le`, `rootMultiplicity_one_binomial_le`): the exact
  multiplicity of the root `1` of a two-term binomial `X^a − X^b` over `ZMod p` is `≤ 1` precisely
  when `a, b` differ mod `p`.

* **`minorTaylorMultiplicityLt_two_REFUTED_at_two`**: a machine-checked **countermodel at `p = 2`**.
  With `ri = ci = ![0, 1]`, `detPolyModP = X − 1 = (X − 1)^{2−1}`, so `MinorTaylorMultiplicityLt 2`
  is FALSE. The `2 < p` hypothesis of `minorTaylorMultiplicityLt_two` is therefore *necessary*.

* **`smallRegime_crux_of_multiplicityBound`** (the corrected reduction): names the genuine residual
  `GeneralizedVandermondeMultiplicityLe` (`detPolyModP ≠ 0` and `rootMultiplicity 1 ≤ n·(n−1)/2`,
  the alternant Taylor-order) and proves it implies the `n`-instance of the crux *exactly when*
  `n·(n−1)/2 < p − 1`.

## The honest BOUNDARY (an important correction recorded here)

A numerical census (`scripts/probes`, exact over `p ∈ {3,5,7,11,13}`, all `n ≤ p`) shows:
the worst-case `rootMultiplicity 1 (detPolyModP)` is **exactly `binom(n,2) = n·(n−1)/2`** (the
generalized-Vandermonde / alternant Taylor order), and `detPolyModP ≠ 0` always. Consequently the
crux `¬ (X − 1)^{p−1} ∣ detPolyModP` (i.e. `multiplicity < p − 1`) holds
**iff `binom(n,2) < p − 1`** and is **FALSE once `binom(n,2) ≥ p − 1`** (e.g. `p = 5, n = 4`:
`binom = 6 ≥ 4`). So the
universally-quantified `MinorTaylorMultiplicityLt p` (all `n`) is *false* for every prime (it fails
at the first `n` with `binom(n,2) ≥ p − 1`, and at `p = 2`). The mod-`p` multiplicity captures the
true `(1 − ζ)`-adic valuation `binom(n,2)` of the minor only in the small regime `binom(n,2) < p−1`;
the full Chebotarev theorem for large `n` needs the *finiteness* of that valuation (the alternant is
a nonzero element), not the lossy `(X − 1)^{p−1}` divisibility framing. This file therefore proves
the crux on its genuine domain (`n = 2`; small regime under the named residual) and documents the
boundary, rather than claiming the all-`n` crux.

## Honesty contract (per #407)

We never `sorry` and never claim general Chebotarev proven. `minorTaylorMultiplicityLt_two` is a
genuine theorem (odd `p`); the `p = 2` and large-`n` failures are machine-checked /
census-documented boundaries; the general small-regime reduction names its residual
`GeneralizedVandermondeMultiplicityLe` explicitly.

Reference: T. Tao, *An uncertainty principle for cyclic groups of prime order*, Math. Res. Lett. 12
(2005), 121–127, and his blog post of the same title (the reduction-mod-`(1−ζ)` proof).

Axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorryAx`). Issue #407.
-/

open Finset ZMod Matrix Polynomial Complex
open ProximityGap.Frontier.ZModDonohoStark
open ProximityGap.Frontier.PrimeCapacityUncertainty
open ProximityGap.Frontier.TaoFromChebotarev
open ProximityGap.Frontier.ChebotarevReductionModP

namespace ProximityGap.Frontier.ChebotarevVandermondeCrux

variable {p : ℕ} [Fact p.Prime]

/-! ## Layer A: divisibility by `(X − 1)` powers for a two-term binomial `X^a − X^b` mod `p`. -/

/-- **Negation-invariance of root multiplicity.** `rootMultiplicity x (−q) = rootMultiplicity x q`
over any commutative ring: the divisibility ladder `(X − C x)^n ∣ ·` is invariant under negation
(`dvd_neg`), and `rootMultiplicity` is `n ↦ (X − C x)^n ∣ ·`-extremal (`le_rootMultiplicity_iff`).
Used to make the `X^a − X^b` analysis symmetric in `a, b`. -/
theorem rootMultiplicity_neg {R : Type*} [CommRing R] (x : R) (q : R[X]) :
    rootMultiplicity x (-q) = rootMultiplicity x q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hnq : (-q) ≠ 0 := neg_ne_zero.2 hq
  apply le_antisymm
  · exact rootMultiplicity_le_rootMultiplicity_of_dvd hq (neg_dvd.mpr dvd_rfl) x
  · exact rootMultiplicity_le_rootMultiplicity_of_dvd hnq (dvd_neg.mpr dvd_rfl) x

/-- For `b ≤ a`, the binomial factors as `X^a − X^b = X^b · (X^{a−b} − 1)`. -/
theorem binomial_factor {a b : ℕ} (hba : b ≤ a) :
    (X ^ a - X ^ b : (ZMod p)[X]) = X ^ b * (X ^ (a - b) - 1) := by
  rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hba]

/-- `rootMultiplicity 1 (X^m − 1) ≤ 1` over `ZMod p` when `p ∤ m`: `X^m − 1` is **separable**
(`X_pow_sub_one_separable_iff`: separable ⟺ `(m : ZMod p) ≠ 0`), so each root is simple. -/
theorem rootMultiplicity_one_X_pow_sub_one_le {m : ℕ} (hpm : ¬ (p ∣ m)) :
    rootMultiplicity (1 : ZMod p) (X ^ m - 1) ≤ 1 := by
  have hsep : (X ^ m - 1 : (ZMod p)[X]).Separable := by
    rw [Polynomial.X_pow_sub_one_separable_iff, Ne, ZMod.natCast_eq_zero_iff]
    exact hpm
  exact rootMultiplicity_le_one_of_separable hsep 1

/-- `1` is not a root of `X^b`, so `rootMultiplicity 1 (X^b) = 0`. -/
theorem rootMultiplicity_one_X_pow (b : ℕ) :
    rootMultiplicity (1 : ZMod p) (X ^ b) = 0 := by
  apply rootMultiplicity_eq_zero
  rw [IsRoot.def, eval_pow, eval_X, one_pow]
  exact one_ne_zero

/-- **The binomial bound (the heart of the `n = 2` crux).** If `a ≠ b` and `p ∤ (a − b)` (the two
exponents differ mod `p`), the root `1` of `X^a − X^b` over `ZMod p` has multiplicity `≤ 1`. The
`X^{min}` factor contributes `0`, and the `X^{|a−b|} − 1` factor is separable. -/
theorem rootMultiplicity_one_binomial_le {a b : ℕ} (hne : a ≠ b)
    (hpab : (a : ZMod p) ≠ (b : ZMod p)) :
    rootMultiplicity (1 : ZMod p) (X ^ a - X ^ b) ≤ 1 := by
  -- Reduce to `b ≤ a` (the goal is symmetric under negation of the binomial).
  rcases le_or_gt b a with hba | hab
  · -- `b ≤ a`.
    have hmne : a - b ≠ 0 := by omega
    have hpm : ¬ (p ∣ (a - b)) := by
      intro hdvd
      -- `p ∣ a − b` with `b ≤ a` ⟹ `(a : ZMod p) = (b : ZMod p)`.
      apply hpab
      have : ((a - b : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      have hsub : ((a - b : ℕ) : ZMod p) = (a : ZMod p) - (b : ZMod p) := by
        rw [Nat.cast_sub hba]
      rw [hsub, sub_eq_zero] at this
      exact this
    -- factor and use `rootMultiplicity_mul`.
    rw [binomial_factor hba]
    have hXne : (X ^ b : (ZMod p)[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
    have hX1ne : (X ^ (a - b) - 1 : (ZMod p)[X]) ≠ 0 := by
      intro h
      have : ((X ^ (a - b) : (ZMod p)[X])) = 1 := by linear_combination h
      have hdeg : (X ^ (a - b) : (ZMod p)[X]).natDegree = a - b := by
        rw [natDegree_X_pow]
      rw [this, natDegree_one] at hdeg
      exact hmne hdeg.symm
    have hprod : (X ^ b * (X ^ (a - b) - 1) : (ZMod p)[X]) ≠ 0 := mul_ne_zero hXne hX1ne
    rw [rootMultiplicity_mul hprod, rootMultiplicity_one_X_pow, zero_add]
    exact rootMultiplicity_one_X_pow_sub_one_le hpm
  · -- `a < b`: rewrite `X^a − X^b = −(X^b − X^a)` and reuse the symmetric case.
    have hba : a ≤ b := hab.le
    have hmne : b - a ≠ 0 := by omega
    have hpm : ¬ (p ∣ (b - a)) := by
      intro hdvd
      apply hpab
      have : ((b - a : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      have hsub : ((b - a : ℕ) : ZMod p) = (b : ZMod p) - (a : ZMod p) := by
        rw [Nat.cast_sub hba]
      rw [hsub, sub_eq_zero] at this
      exact this.symm
    -- multiplicity invariance under negation, then the `a ≤ b`-shaped factorization on `X^b − X^a`.
    have hneg : (X ^ a - X ^ b : (ZMod p)[X]) = -(X ^ b - X ^ a) := by ring
    rw [hneg, rootMultiplicity_neg, binomial_factor hba]
    have hXne : (X ^ a : (ZMod p)[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
    have hX1ne : (X ^ (b - a) - 1 : (ZMod p)[X]) ≠ 0 := by
      intro h
      have : ((X ^ (b - a) : (ZMod p)[X])) = 1 := by linear_combination h
      have hdeg : (X ^ (b - a) : (ZMod p)[X]).natDegree = b - a := by rw [natDegree_X_pow]
      rw [this, natDegree_one] at hdeg
      exact hmne hdeg.symm
    have hprod : (X ^ a * (X ^ (b - a) - 1) : (ZMod p)[X]) ≠ 0 := mul_ne_zero hXne hX1ne
    rw [rootMultiplicity_mul hprod, rootMultiplicity_one_X_pow, zero_add]
    exact rootMultiplicity_one_X_pow_sub_one_le hpm

/-! ## Layer B: the `n = 2` minor polynomial is a binomial with mod-`p`-distinct exponents. -/

/-- The mod-`p` reduction of the `2 × 2` minor polynomial is the **binomial**
`X^{e00+e11} − X^{e01+e10}` over `ZMod p`, where `e i j = minorExp ri ci i j`. (`det_fin_two`,
then `Polynomial.map` distributes over the two-term determinant.) -/
theorem detPolyModP_two (ri ci : Fin 2 → ZMod p) :
    detPolyModP ri ci
      = X ^ (minorExp ri ci 0 0 + minorExp ri ci 1 1)
        - X ^ (minorExp ri ci 0 1 + minorExp ri ci 1 0) := by
  rw [detPolyModP, detPoly, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Polynomial.map_sub, Polynomial.map_pow, map_X, ← pow_add]

/-- **The exponent sums differ mod `p` (the `n = 2` Chebotarev content, transported to exponents).**
For injective `ri ci : Fin 2 → ZMod p`, the two binomial exponent sums satisfy
`(↑(e00+e11) : ZMod p) ≠ ↑(e01+e10)`. Indeed, casting back `↑(e i j) = -(ci j · ri i)` in `ZMod p`
(`natCast_zmod_val` on `minorExp`), the difference is
`↑(e00+e11) − ↑(e01+e10) = (ci 0 − ci 1)(ri 1 − ri 0) ≠ 0` — exactly the nonzero factor from
`chebotarev_two`, nonzero because `ZMod p` is a field and both differences are nonzero
(injectivity). -/
theorem exponentSums_ne_mod_p (ri ci : Fin 2 → ZMod p)
    (hri : Function.Injective ri) (hci : Function.Injective ci) :
    ((minorExp ri ci 0 0 + minorExp ri ci 1 1 : ℕ) : ZMod p)
      ≠ ((minorExp ri ci 0 1 + minorExp ri ci 1 0 : ℕ) : ZMod p) := by
  -- cast each `minorExp` back: `↑(e i j) = -(ci j · ri i)` in `ZMod p`.
  have hcast : ∀ i j : Fin 2, ((minorExp ri ci i j : ℕ) : ZMod p) = -(ci j * ri i) := by
    intro i j; rw [minorExp, ZMod.natCast_zmod_val]
  intro hEq
  -- difference is `(ci 0 − ci 1)(ri 1 − ri 0)`.
  rw [Nat.cast_add, Nat.cast_add, hcast, hcast, hcast, hcast] at hEq
  have hfac : (ci 0 - ci 1) * (ri 1 - ri 0) = 0 := by linear_combination hEq
  have hc01 : ci 0 ≠ ci 1 := fun h => by simpa using hci h
  have hr01 : ri 1 ≠ ri 0 := fun h => by simpa using hri h
  exact (mul_ne_zero (sub_ne_zero.mpr hc01) (sub_ne_zero.mpr hr01)) hfac

/-- The two binomial exponent sums are also **distinct as natural numbers** (a fortiori from being
distinct mod `p`): if they were equal naturals their casts would coincide. -/
theorem exponentSums_ne_nat (ri ci : Fin 2 → ZMod p)
    (hri : Function.Injective ri) (hci : Function.Injective ci) :
    minorExp ri ci 0 0 + minorExp ri ci 1 1 ≠ minorExp ri ci 0 1 + minorExp ri ci 1 0 := by
  intro hEq
  exact exponentSums_ne_mod_p ri ci hri hci (by rw [hEq])

/-! ## Layer C: the general small-regime reduction, with the genuine residual named.

The exact worst-case multiplicity of the root `1` of `detPolyModP` is the **alternant Taylor order**
`binom(n,2) = n·(n−1)/2` (census-verified; it is the `(1−ζ)`-adic valuation of the minor). We name
the corresponding obligation — that `detPolyModP` is nonzero with root-`1` multiplicity at most this
order — and prove it discharges the `n`-instance of the crux precisely in the small regime
`binom(n,2) < p − 1`. The `n = 2` headline is the instance `binom(2,2) = 1 < p − 1` (`p ≥ 3`). -/

/-- **The genuine residual: the generalized-Vandermonde multiplicity bound.** For a given `n`, every
injective minor `detPolyModP ri ci` is nonzero with the root `1` of multiplicity at most the
alternant order `n·(n−1)/2`. (Census-verified to hold with *equality* in the worst case; it is the
`(1 − ζ)`-adic valuation of the minor determinant, the deep nonzero-alternant heart of Chebotarev's
theorem.) Stated as a named `Prop` per the honesty contract — proven below for `n ≤ 2`, named-open
in general. -/
def GeneralizedVandermondeMultiplicityLe (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∀ (ri ci : Fin n → ZMod p), Function.Injective ri → Function.Injective ci →
    detPolyModP ri ci ≠ 0 ∧ rootMultiplicity (1 : ZMod p) (detPolyModP ri ci) ≤ n * (n - 1) / 2

/-- **The small-regime reduction (PROVEN).** If the alternant multiplicity bound
`GeneralizedVandermondeMultiplicityLe p n` holds and the alternant order is below threshold
(`n·(n−1)/2 < p − 1`), then the `n`-instance of the crux holds: `(X − 1)^{p−1}` does not divide any
injective minor `detPolyModP ri ci`. (If it did, the root `1` would have multiplicity `≥ p − 1`,
contradicting the `≤ n·(n−1)/2 < p − 1` bound.) This is the faithful Tao mechanism on its genuine
domain; outside it (`n·(n−1)/2 ≥ p − 1`) the crux is false, see the boundary discussion. -/
theorem smallRegime_crux_of_multiplicityBound {n : ℕ}
    (hbound : GeneralizedVandermondeMultiplicityLe p n)
    (hsmall : n * (n - 1) / 2 < p - 1)
    (ri ci : Fin n → ZMod p) (hri : Function.Injective ri) (hci : Function.Injective ci) :
    ¬ ((X - 1) ^ (p - 1) ∣ detPolyModP ri ci) := by
  obtain ⟨hne, hmult⟩ := hbound ri ci hri hci
  intro hdvd
  rw [show (X - (1 : (ZMod p)[X])) = X - C (1 : ZMod p) by rw [map_one]] at hdvd
  rw [← le_rootMultiplicity_iff hne] at hdvd
  omega

/-- **The `n = 2` residual instance is PROVEN (any prime `p`).** The alternant multiplicity bound at
`n = 2` (`binom(2,2) = 1`) holds: every injective `2 × 2` minor is a nonzero binomial with root `1`
of multiplicity `≤ 1 = 2·1/2`. (This bound holds even at `p = 2` — it is only the *crux threshold*
`1 < p − 1` that needs `p ≥ 3`, hence `minorTaylorMultiplicityLt_two` is exactly the
`smallRegime_crux_of_multiplicityBound` instance at `n = 2` for `p ≥ 3`.) -/
theorem generalizedVandermondeMultiplicityLe_two :
    GeneralizedVandermondeMultiplicityLe p 2 := by
  intro ri ci hri hci
  refine ⟨?_, ?_⟩
  · -- nonzero: distinct mod-`p` exponents ⟹ a genuine binomial.
    rw [detPolyModP_two]
    set a := minorExp ri ci 0 0 + minorExp ri ci 1 1
    set b := minorExp ri ci 0 1 + minorExp ri ci 1 0
    have hne : a ≠ b := exponentSums_ne_nat ri ci hri hci
    intro h
    rcases le_or_gt b a with hba | hab
    · rw [binomial_factor hba] at h
      rcases mul_eq_zero.1 h with h1 | h1
      · exact (pow_ne_zero _ X_ne_zero) h1
      · have hdeg : (X ^ (a - b) - 1 : (ZMod p)[X]).natDegree = a - b := by
          rw [show (X ^ (a - b) - 1 : (ZMod p)[X]) = X ^ (a - b) - C 1 by rw [map_one]]
          rcases Nat.eq_zero_or_pos (a - b) with h0 | hpos
          · omega
          · rw [natDegree_X_pow_sub_C]
        rw [h1, natDegree_zero] at hdeg; omega
    · have hba : a ≤ b := hab.le
      rw [show (X ^ a - X ^ b : (ZMod p)[X]) = -(X ^ b - X ^ a) by ring, neg_eq_zero,
        binomial_factor hba] at h
      rcases mul_eq_zero.1 h with h1 | h1
      · exact (pow_ne_zero _ X_ne_zero) h1
      · have hdeg : (X ^ (b - a) - 1 : (ZMod p)[X]).natDegree = b - a := by
          rw [show (X ^ (b - a) - 1 : (ZMod p)[X]) = X ^ (b - a) - C 1 by rw [map_one]]
          rcases Nat.eq_zero_or_pos (b - a) with h0 | hpos
          · omega
          · rw [natDegree_X_pow_sub_C]
        rw [h1, natDegree_zero] at hdeg; omega
  · -- multiplicity `≤ 1`.
    rw [detPolyModP_two]
    have h := rootMultiplicity_one_binomial_le (exponentSums_ne_nat ri ci hri hci)
      (exponentSums_ne_mod_p ri ci hri hci)
    simpa using h

/-! ## Layer C (headline): the `n = 2` instance of the crux (PROVEN for `p ≥ 3`). -/

/-- **The `n = 2` instance of the Vandermonde-mod-`p` crux of Chebotarev's theorem
(PROVEN, `p ≥ 3`).**

For `p` an odd prime and any *injective* `ri ci : Fin 2 → ZMod p`, the mod-`p` minor polynomial
`detPolyModP ri ci = X^{e00+e11} − X^{e01+e10}` is **not** divisible by `(X − 1)^{p−1}`.
Equivalently, the root `1` of this binomial has multiplicity `≤ 1 < p − 1`.

This is the `smallRegime_crux_of_multiplicityBound` instance at `n = 2`: the alternant order
`binom(2,2) = 1` is below threshold (`1 < p − 1` ⟺ `p ≥ 3`), and the `n = 2` residual
`generalizedVandermondeMultiplicityLe_two` (the transported `chebotarev_two` content: the minor is a
nonzero binomial with the two exponent sums distinct mod `p`) is proven.

**Boundary (honest):** the hypothesis `2 < p` is genuinely necessary — for `p = 2` the crux is
*false* (`minorTaylorMultiplicityLt_two_REFUTED_at_two`: `ri = ci = ![0,1]` gives
`detPolyModP = X − 1 = (X − 1)^{p−1}`, divisible). The multiplicity bound is `≤ binom(2,2) = 1`,
which is `< p − 1` only for `p ≥ 3`; at `p = 2` a simple root already saturates `(X − 1)^{p−1}`.
(Chebotarev's minor theorem itself still holds at `p = 2` — proven directly by `chebotarev_two` —
but the *strengthened* multiplicity crux is a small-regime / odd-prime phenomenon; see the module
docstring for the analogous large-`n` failure.) -/
theorem minorTaylorMultiplicityLt_two (hp : 2 < p) (ri ci : Fin 2 → ZMod p)
    (hri : Function.Injective ri) (hci : Function.Injective ci) :
    ¬ ((X - 1) ^ (p - 1) ∣ detPolyModP ri ci) :=
  smallRegime_crux_of_multiplicityBound
    generalizedVandermondeMultiplicityLe_two (by omega) ri ci hri hci

/-! ## Layer D: the honest `p = 2` boundary — the crux is genuinely FALSE at `p = 2` (refutation).

The strengthened multiplicity crux `MinorTaylorMultiplicityLt` is an *odd-prime* phenomenon. We
exhibit a machine-checked countermodel at `p = 2`, `n = 2`: with `ri = ci = ![0, 1]` the minor
polynomial is `detPolyModP = X − 1`, which `(X − 1)^{p−1} = (X − 1)^1` divides. So
`MinorTaylorMultiplicityLt 2` is FALSE — even though Chebotarev's minor theorem itself holds at
`p = 2` (it is proven directly by `chebotarev_two`, which needs only that `ZMod p` is a field). The
gap is exactly `multiplicity ≤ 1` vs the threshold `p − 1`: at `p = 2` a simple root already
saturates `(X − 1)^{p−1}`, so the *reduction-via-multiplicity* loses the `p = 2` case while the
underlying determinant fact survives. -/

/-- **The crux fails at `p = 2` (machine-checked countermodel).** With `ri = ci = ![0, 1]` over
`ZMod 2`, `detPolyModP = X − 1`, and `(X − 1)^{2−1} ∣ (X − 1)`. Hence the `n = 2` (and a fortiori
the general) crux `MinorTaylorMultiplicityLt 2` is FALSE. This is the honest boundary of
`minorTaylorMultiplicityLt_two` (`2 < p`): the multiplicity route is odd-prime-only. -/
theorem minorTaylorMultiplicityLt_two_REFUTED_at_two :
    ((X - 1 : (ZMod 2)[X]) ^ (2 - 1) ∣ detPolyModP (![0, 1] : Fin 2 → ZMod 2) ![0, 1]) := by
  have h : detPolyModP (![0, 1] : Fin 2 → ZMod 2) ![0, 1] = X - 1 := by
    rw [detPolyModP_two]
    -- compute the four exponents explicitly.
    have e00 : minorExp (![0, 1] : Fin 2 → ZMod 2) ![0, 1] 0 0 = 0 := by decide
    have e11 : minorExp (![0, 1] : Fin 2 → ZMod 2) ![0, 1] 1 1 = 1 := by decide
    have e01 : minorExp (![0, 1] : Fin 2 → ZMod 2) ![0, 1] 0 1 = 0 := by decide
    have e10 : minorExp (![0, 1] : Fin 2 → ZMod 2) ![0, 1] 1 0 = 0 := by decide
    rw [e00, e11, e01, e10]
    norm_num
  rw [h]
  simp

end ProximityGap.Frontier.ChebotarevVandermondeCrux

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only — no `sorryAx`).
`GeneralizedVandermondeMultiplicityLe` is a `def … : Prop` (a named classical hypothesis), so it
carries no axioms; the PROVEN content consumes / discharges it. -/
open ProximityGap.Frontier.ChebotarevVandermondeCrux in
#print axioms rootMultiplicity_neg
open ProximityGap.Frontier.ChebotarevVandermondeCrux in
#print axioms rootMultiplicity_one_X_pow_sub_one_le
open ProximityGap.Frontier.ChebotarevVandermondeCrux in
#print axioms rootMultiplicity_one_binomial_le
open ProximityGap.Frontier.ChebotarevVandermondeCrux in
#print axioms detPolyModP_two
open ProximityGap.Frontier.ChebotarevVandermondeCrux in
#print axioms exponentSums_ne_mod_p
open ProximityGap.Frontier.ChebotarevVandermondeCrux in
#print axioms exponentSums_ne_nat
open ProximityGap.Frontier.ChebotarevVandermondeCrux in
#print axioms minorTaylorMultiplicityLt_two
open ProximityGap.Frontier.ChebotarevVandermondeCrux in
#print axioms smallRegime_crux_of_multiplicityBound
open ProximityGap.Frontier.ChebotarevVandermondeCrux in
#print axioms generalizedVandermondeMultiplicityLe_two
open ProximityGap.Frontier.ChebotarevVandermondeCrux in
#print axioms minorTaylorMultiplicityLt_two_REFUTED_at_two
