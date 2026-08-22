/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Newton polygon / tropical of the PERIOD POLYNOMIAL — the `√p` wall localizes to ONE coefficient
# `e₂`, and the only spread-aware escape is the power-sum (Graeffe) bound = the Paley moment wall
# (#334 / #444)

ATTACK `newton-polygon-period-poly`. The `m = (p−1)/n` Gauss periods `η_b` are the roots of the
**period polynomial** `Ψ(X) = ∏_{cosets}(X − η_b) ∈ ℤ[X]` (degree `m`, integer coefficients =
elementary symmetric functions of the periods). `B = max_b |η_b|` is its largest root. The angle:
bound `B` via the Newton polygon (p-adic root sizes from the coefficients' `p`-valuations) plus the
archimedean coefficient sizes (Cauchy / Lagrange / Fujiwara root bounds). This file gives the exact,
honest resolution of that angle, with three precise findings — all numerically verified
(`/private/tmp/.../scratchpad/np_*.py`, exact integer arithmetic via power sums + Newton's
identities; periods cross-checked by FFT of `1_{μ_n}`).

## The three findings

**(NP-1) The `p`-adic Newton polygon of `Ψ` at `p` is FLAT — the Stickelberger half is vacuous.**
Every coefficient `e_k` of `Ψ` is a `p`-adic UNIT (`v_p(e_k) = 0`), because the `e_k` are integer
symmetric functions of the periods and the periods are algebraic units; the ramification of `p`
lives in the discriminant `= ±p^{m−1}`, not in any individual coefficient. So the Newton polygon at
`p` is the flat segment from `(0,0)` to `(m,0)`: every root is a `p`-adic unit. This is a genuine
NO-GO for the "p-adic valuation bounds the root size" idea: the archimedean magnitude `|η_b|` and
the `p`-adic size are locally independent (linked only by the global product formula). Verified
exactly (`np_powersum_exact.py`: `v_p(e_k) = 0` for all `k`, all tested `(n,p)`).

**(NP-2) The archimedean Cauchy / Fujiwara root bound is PINNED at `√(2p)` by the SINGLE
coefficient `e₂`.** Two exact integer identities hold for every even `n` with `p ≡ 1 (mod n)`
prime (`−1 ∈ μ_n`, so the periods are real):
* `T₁ := Σ_b η_b = −1` (sum of the `m` distinct periods),
* `T₂ := Σ_b η_b² = p − n` (because `N₂ := #{(y₁,y₂)∈μ_n² : y₁+y₂ ≡ 0} = n`, the involution
  `y ↦ −y`, and `Σ_{b≠0} η_b² = p·N₂ − n²`, divided by the coset size `n`),

whence the second elementary symmetric function is, EXACTLY,
`e₂ = (T₁² − T₂)/2 = (1 − (p − n))/2 = (n + 1 − p)/2`, so `|e₂| = (p − n − 1)/2 ≈ p/2`.
Every Cauchy-family root bound is an increasing function of the coefficient-modulus profile
`max_k |e_k|^{1/k}`, and (numerically, exactly) that profile's maximum is achieved at `k = 2`
(`np_coeff_profile.py`: `argmax_k |e_k|^{1/k} = 2` in every case). The Fujiwara bound
`B ≤ 2·max_k |e_k|^{1/k}` therefore has a hard FLOOR of `2·|e₂|^{1/2} = √(2(p − n − 1)) ≈ √(2p)`:
**no Cauchy/Lagrange/Fujiwara/Kojima bound can certify `B < √(2(p−n−1))`.** This re-derives the
`√q` completion wall and localizes it to one symmetric function, forced by `−1 ∈ μ_n` alone.

**(NP-3) The ONLY spread-aware escape is Graeffe root-squaring = the power-sum (moment) bound =
the Paley wall.** Graeffe iteration produces `Ψ_j` with roots `η_b^{2^j}`; its first symmetric
function is the power sum `e₁(Ψ_j) = T_{2^j} = Σ_b η_b^{2^j}`, so the Cauchy bound on `Ψ_j` reads
`B^{2^j} ≤ T_{2^j}` (up to lower-order terms), i.e. `B ≤ T_{2^j}^{1/2^j}`. Numerically this DOES
drop below `√(2n ln p)` once `2^j ≳ ln p` (`np_graeffe.py`, `n=16,p=1153`: `j=1` gives `33.7 > 15`,
the wall; `j≥2` gives `14.8, 10.9, …, 9.98 < 15`, converging to `B`). But the content of step `j`
is exactly whether `T_{2^j} = (p·N_{2^j} − n^{2^j})/n` is small, i.e. whether the additive-energy
count `N_{2^j} ≤ Wick` at depth `r = 2^{j−1} ≈ ln p` — **the Paley moment wall**. Graeffe converts
the `√p`-Cauchy bound into the `√(2n ln p)`-moment bound, moving all the difficulty into the
power sums.

## Verdict

REDUCES TO PALEY, but with a sharp new EXACT localization. The Newton-polygon-period-poly angle
splits cleanly: (i) the `p`-adic Newton polygon is FLAT (no root-size content — genuine no-go),
(ii) the archimedean Cauchy/Fujiwara bound is pinned at `√(2p)` by the single exact coefficient
`e₂ = (n+1−p)/2`, (iii) the only coefficient-based bound that uses the period SPREAD and reaches
the target is Graeffe = the power-sum / moment bound, whose content `N_{2^j} ≤ Wick` IS the Paley
wall. Everything here is a magnitude functional of `Ψ`'s coefficients / power sums — consistent
with the phase-blind floor: the `√`-cancellation needed for the prize lives in the archimedean
SPREAD of the roots around their `L²` mean, which no coefficient `p`-valuation or single symmetric
function pins.

This file formalizes, axiom-clean: (NP-2a) the exact `e₂` identity `e₂ = (n+1−p)/2`, (NP-2b) its
modulus `|e₂| = (p−n−1)/2`, (NP-2c) the Fujiwara floor `√(2(p−n−1)) ≤ Fujiwara bound` and the
quantitative wall `√(2(p−n−1)) ≥ √p` (so the bound is at least `√p`, far above the target
`√(2n ln p)`), and (NP-3) the geometric Graeffe/power-sum identity `B^{2^j} ≤ Σ_b |η_b|^{2^j}` that
relocates the bound onto the power sums.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.NewtonPolygonPeriodPolyE2Wall

open scoped BigOperators

/-! ## (NP-2a) The exact `e₂` identity of the period polynomial.

`e₂` is the second elementary symmetric function of the `m` periods. Newton's identity for `k = 2`
is `2·e₂ = T₁² − T₂` (with `T₁ = e₁` the first power sum and `T₂` the second). Feeding the two
exact period facts `T₁ = −1` and `T₂ = p − n` (both consequences of `−1 ∈ μ_n`) gives the closed
form `e₂ = (n + 1 − p)/2`. We package this abstractly: from the Newton relation and the two power
sums, the algebra is forced. -/

/-- **(NP-2a) Newton's `k=2` identity gives `e₂` from the power sums.** With `T₁ = −1` and
`T₂ = p − n` (the exact first two period power sums for even `n`, `p ≡ 1 mod n`), the second
elementary symmetric function `e₂ = (T₁² − T₂)/2` equals `(n + 1 − p)/2`. Stated over `ℝ` so the
division is literal. -/
theorem e2_closed_form (n p : ℝ) (T1 T2 e2 : ℝ)
    (hT1 : T1 = -1) (hT2 : T2 = p - n) (hNewton : 2 * e2 = T1 ^ 2 - T2) :
    e2 = (n + 1 - p) / 2 := by
  subst hT1 hT2
  linarith [hNewton]

/-- **(NP-2b) The modulus of `e₂`.** For a prime `p > n + 1` (always true at the prize scale,
`p ≈ 2¹⁵⁸ ≫ n ≈ 2³⁰`), `e₂ = (n+1−p)/2 < 0`, so `|e₂| = (p − n − 1)/2 ≈ p/2`. -/
theorem abs_e2 (n p e2 : ℝ) (he2 : e2 = (n + 1 - p) / 2) (hpn : n + 1 < p) :
    |e2| = (p - n - 1) / 2 := by
  rw [he2, abs_of_nonpos (by linarith)]
  ring

/-! ## (NP-2c) The Fujiwara floor: the coefficient bound is pinned at `√(2p)`.

Fujiwara's root bound for a monic degree-`m` polynomial `Xᵐ + a₁Xᵐ⁻¹ + ⋯ + aₘ` is
`B ≤ 2·max_k |aₖ|^{1/k}`. Since `a₂ = e₂`, the `k = 2` term forces
`2·max_k|aₖ|^{1/k} ≥ 2·|e₂|^{1/2}`. With `|e₂| = (p − n − 1)/2`, the floor on what Fujiwara can
deliver is `2·√((p−n−1)/2) = √(2(p−n−1))`. We formalize the floor and that it is `≥ √p` (so the
coefficient bound is never better than `√p`, while the prize target is `√(2n ln p) ≪ √p`). -/

/-- **Fujiwara floor (abstract core).** If `Bd` is any upper bound of Fujiwara shape
`Bd ≥ 2 · |e₂|^{1/2}` (the `k=2` Fujiwara term is always one of the maxed terms), then with
`|e₂| = (p−n−1)/2` we get `Bd ≥ √(2(p−n−1))`. So the Cauchy/Fujiwara root bound on `Ψ` cannot beat
`√(2(p−n−1)) ≈ √(2p)`. -/
theorem fujiwara_floor (p n Bd absE2 : ℝ)
    (hAbs : absE2 = (p - n - 1) / 2)
    (hFuj : 2 * Real.sqrt absE2 ≤ Bd) :
    Real.sqrt (2 * (p - n - 1)) ≤ Bd := by
  refine le_trans ?_ hFuj
  rw [hAbs]
  -- 2·√((p−n−1)/2) = √(4 · (p−n−1)/2) = √(2(p−n−1))
  rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)],
      ← Real.sqrt_mul (by norm_num)]
  apply le_of_eq
  congr 1
  ring

/-- **The wall, quantitatively: the coefficient bound is at least `√p`.** Since
`2(p − n − 1) ≥ p` whenever `p ≥ 2n + 2` (true at every relevant scale), the Fujiwara floor
`√(2(p−n−1))` is `≥ √p`. Hence ANY Cauchy/Lagrange/Fujiwara root bound certifies only `B ≤ √p`-scale
— never the prize target `√(2n ln p)`, which is asymptotically `√p`-times smaller (for fixed `n`,
`√(2n ln p)/√p → 0`). This is the `√q` completion wall, localized to the single coefficient `e₂`. -/
theorem coeff_bound_at_least_sqrt_p (p n Bd : ℝ)
    (hp : 0 ≤ p) (hscale : 2 * n + 2 ≤ p)
    (hFloor : Real.sqrt (2 * (p - n - 1)) ≤ Bd) :
    Real.sqrt p ≤ Bd := by
  refine le_trans ?_ hFloor
  apply Real.sqrt_le_sqrt
  linarith

/-! ## (NP-3) Graeffe root-squaring = power-sum (moment) bound: the spread-aware escape.

The only way coefficient data can drop below `√p` is to use the SPREAD of the roots, captured by
higher power sums. Graeffe iteration `Ψ ↦ Ψ_j` (roots `η_b^{2^j}`) has first symmetric function
`e₁(Ψ_j) = T_{2^j} = Σ_b η_b^{2^j}`, and the trivial root bound `B^{2^j} ≤ Σ_b |η_b|^{2^j}` holds
because the maximum term is one of the summands (all summands nonneg). This is the moment method;
its content (`Σ_b |η_b|^{2^j}` small at `2^j ≈ ln p`) is the Paley wall. -/

/-- **(NP-3) The power-sum / Graeffe root bound.** For any finite family of reals `η : ι → ℝ` and
any exponent `s`, the maximum even power `max_b η_b^{2s}` is at most the power sum
`Σ_b η_b^{2s}` (each term nonneg, the max is one of them). With `2s = 2^j` this is the Graeffe
step-`j` bound `B^{2^j} ≤ Σ_b |η_b|^{2^j}`: the coefficient bound on `Ψ_j` reduces to the power
sum, relocating all difficulty onto the additive-energy moments (the Paley wall). -/
theorem powersum_root_bound {ι : Type*} (s : Finset ι) (η : ι → ℝ) (k : ℕ)
    (b : ι) (hb : b ∈ s) :
    (η b) ^ (2 * k) ≤ ∑ i ∈ s, (η i) ^ (2 * k) := by
  have hnn : ∀ i ∈ s, 0 ≤ (η i) ^ (2 * k) := by
    intro i _
    rw [pow_mul]
    positivity
  exact Finset.single_le_sum hnn hb

/-- **The Graeffe escape is genuine but its content is the moment.** Packaged: if the depth-`2^j`
power sum is bounded by the Wick target `Σ_b η_b^{2^j} ≤ W`, then `B^{2^j} ≤ W`, i.e.
`B ≤ W^{1/2^j}`. This is the EXACT shape of the prize bound — the input `Σ_b η_b^{2^j} ≤ Wick` at
`2^j ≈ ln p` is precisely the open Paley moment statement (`E_r ≤ Wick`). The coefficient angle
delivers the bound IFF this moment input is supplied; that is the reduction. -/
theorem graeffe_reduces_to_moment {ι : Type*} (s : Finset ι) (η : ι → ℝ) (k : ℕ) (W : ℝ)
    (b : ι) (hb : b ∈ s) (hMoment : ∑ i ∈ s, (η i) ^ (2 * k) ≤ W) :
    (η b) ^ (2 * k) ≤ W :=
  le_trans (powersum_root_bound s η k b hb) hMoment

end ArkLib.ProximityGap.Frontier.NewtonPolygonPeriodPolyE2Wall

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ArkLib.ProximityGap.Frontier.NewtonPolygonPeriodPolyE2Wall.e2_closed_form
#print axioms ArkLib.ProximityGap.Frontier.NewtonPolygonPeriodPolyE2Wall.abs_e2
#print axioms ArkLib.ProximityGap.Frontier.NewtonPolygonPeriodPolyE2Wall.fujiwara_floor
#print axioms ArkLib.ProximityGap.Frontier.NewtonPolygonPeriodPolyE2Wall.coeff_bound_at_least_sqrt_p
#print axioms ArkLib.ProximityGap.Frontier.NewtonPolygonPeriodPolyE2Wall.powersum_root_bound
#print axioms ArkLib.ProximityGap.Frontier.NewtonPolygonPeriodPolyE2Wall.graeffe_reduces_to_moment
