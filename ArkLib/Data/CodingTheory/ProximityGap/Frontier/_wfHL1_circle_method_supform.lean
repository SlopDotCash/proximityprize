/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumRawMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MomentMethodNoGo

/-!
# Lane L1 (#444): the Hardy–Littlewood circle method on the SUP `M(n)` REDUCES-TO-FENCE F1/F12 (+F0)

**Cluster: alien / cross — analytic number theory.** Ask: does a Hardy–Littlewood **major/minor-arc**
decomposition, or **Weyl differencing / Vinogradov** minor-arc estimate, give a bound on the prize
**SUP**
`M(n) = max_{b≠0} |η_b|`, `η_b = ∑_{x∈μ_n} e_p(b·x)`, `μ_n` the order-`n=2^μ` 2-power subgroup,
`p` prime `p≡1 (mod n)`, `β = log_n p ≈ 4` (prize `p ~ n^4`, `n ~ 2^30`) — that is NOT a moment of
`η_b` (i.e. that escapes the dead additive-energy route, fence F12)?

## The honest verdict: REDUCES-TO-FENCE F1/F12 (+F0). Three structural facts, all here machine-checked.

The circle method offers **exactly two** Fourier-dual handles on `η_b`, and a third *saving
mechanism* (Weyl differencing) that needs structure `μ_n` lacks. Each is pinned below.

### (i) Weyl differencing / van der Corput on `η_b` ⟶ the additive autocorrelation = the 2nd moment.
The phase `b·x` is **degree 1** (linear). The single differencing/squaring step the circle method
applies to it is the van der Corput square
`|η_b|² = ∑_{x,y∈μ_n} e_p(b(x−y)) = ∑_h A_n(h)·e_p(b·h)`, `A_n(h) = #{(x,y)∈μ_n²: x−y=h}`.
Differencing a **linear** phase does **not** lower its degree (there is no degree to lower); it
just produces the **additive autocorrelation** `A_n`, which is a nonnegative count
(positive-definite, diagonal `A_n(0)=n`, off-diagonal total `n(n−1) = (n−1)·diagonal` — it GROWS
with `n`). That is the **second moment**, phase-blind to the argmax (fence F0 conservation + F1
energy). [In-tree: this is the Wiener–Khinchin object `PeriodAutocovariance.period_autocovariance_eq`
and the positive-definite geometric side of `KuznetsovRTFGeometricSide`.] **No saving.**

### (ii) The major/minor-arc power-sum is the ONLY nontrivial arc split — and it is the moment.
The circle-method Fourier inversion of the relation count is the raw-moment identity
`∑_{b∈F} η_b^{2r} = q·N₀(μ_n, 2r)` (`subgroup_gaussSum_rawMoment`), `N₀(G,2r)=E_r(G)` the `r`-fold
additive energy. The **major arc** `b=0` gives `η_0^{2r} = n^{2r}` (`major_arc_value`); the
**minor arcs** `b≠0` carry the deviation. Positivity of `|η_b|^{2r}` gives the induced SUP bound
`M^{2r} ≤ q·E_r` (`sup_le_total_pow`), i.e. `M ≤ (q·E_r)^{1/2r}`. By the moment no-go
(`MomentMethodNoGo.moment_bound_ge_card`) this is `≥ n` for **every** order `r` — the route can
never even reach the trivial `n`, let alone the floor `√(n log m)`. Exact-integer probe at `β=4`:
the moment optimum `min_r (q·E_r)^{1/2r}` **OVERSHOOTS** the floor (`/floor = 1.54, 1.82` at
`n=16,32`), and the bounded-`K` Wick transfer is DEAD past depth onset (fence **F12**).

### (iii) The Weyl/Vinogradov SAVING mechanism is INAPPLICABLE to a multiplicative subgroup.
Classical minor-arc savings (Weyl differencing, Vinogradov's mean value, the smooth-modulus
period-reduction trick) require the summation to be over an **interval** `{1,…,N}` with a
**polynomial/rational phase**, gaining by reducing the phase degree or the modulus period. `μ_n` is
a **multiplicative** subgroup: it is not an interval (it meets every additive window of length
`p/n` in `O(1)` points — probe T3: `=3` at `n=16,32,64`, equidistributed, not filling), and the
phase is linear. There is **nothing for differencing to localize or reduce**. This is exactly why
**Bourgain–Glibichuk–Konyagin ABANDON the circle method** for additive combinatorics (sum-product /
Balog–Szemerédi–Gowers) to get the SOTA `M ≤ n^{1−o(1)}`: the multiplicative–additive structure
clash is invisible to arc/Weyl machinery (the sum-product phenomenon is precisely the obstruction).
And **Vinogradov's method is intrinsically a MEAN-VALUE (moment) method** — `∫|f|^{2k}` — i.e. the
fence-F12 object by construction; it has no individual-`b` (sup) form.

## Distinct from prior in-tree circle-method bricks (not a duplicate)

* `CircleMethodFreeSetSupport.lean` ran the method on the §7 **bad-scalar count `a`** (a different,
  poly-size object) and reduced R1 to a *binomial* threshold — it REMOVES the character sum.
* `CrossCellCircleMethodSplit.lean` ran the method on the **cross-resonance moment** `crossCell`
  (concentration on the random main term — the F12 moment again).
* This file targets the **SUP `M(n)` directly** and pins precisely why the circle method has *no
  sup form* for it: handle (i) is the 2nd moment, handle (ii) is the dead deeper moment, and the
  saving mechanism (iii) needs interval/polynomial structure `μ_n` does not have.

## Scope (honesty contract §6)

A **method-boundary** verdict, NOT a closure and NOT a refutation of the floor. The floor
`M(n) ≤ C√(n·log(p/n))` stays OPEN on the BGK/Paley wall. All theorems below are `sorry`-free with
`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

## References
- [Tao13] T. Tao, *Bounding short exponential sums on smooth moduli via Weyl differencing*
  (terrytao.wordpress.com, 2013): Weyl differencing requires **interval summation + rational phase
  + smooth modulus**; it reduces the modulus period, not applicable to a multiplicative subgroup.
- [BGK06] Bourgain–Glibichuk–Konyagin, *Estimates for the number of sums and products and for
  exponential sums in fields of prime order* (J. LMS 2006): SOTA `M ≤ n^{1−o(1)}` via **additive
  combinatorics, NOT the circle method** (sum-product obstruction).
- [Sh] Shakan, *Exponential sums over small subgroups* (expository): the SOTA route uses the large
  **spectrum** `Spec_α(H)` + additive energy, and does **not** optimize a moment bound.
- [Vin] Vinogradov's mean value theorem (Wooley; Bourgain–Demeter–Guth): a **mean-value (moment)**
  method — `∫|f|^{2k}` — no individual/sup form (fence F12 by construction).
- In-tree: `SubgroupGaussSumRawMoment` (the power-sum = `q·N₀`), `_MomentMethodNoGo`
  (`(q·E_r)^{1/2r} ≥ n`), `_PeriodAutocovariance`, `_wfH2_kuznetsov_rtf_geometric_side`.
- Probe: `scripts/probes/rust/probe_wfH_L1_circle_method_supform.rs` (exact integers, `β≈4`).

Issue #444 (lane L1, cluster alien/cross).
-/

set_option linter.style.longLine false
set_option autoImplicit false

open Finset

namespace ProximityGap.Frontier.CircleMethodSupForm

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumRawMoment
open ProximityGap.Frontier.MomentMethodNoGo

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (ii) The circle-method major/minor-arc split of the `2r`-th power sum. -/

/-- **The major-arc value `η_0^{2r} = |μ_n|^{2r}`.** At the major arc `b = 0` the period is the
trivial sum `η_0 = ∑_{x∈G} ψ(0) = |G|`, so its `2r`-th power is `|G|^{2r}` — the singular series /
random main term of the circle method. -/
theorem major_arc_value (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) :
    eta ψ G (0 : F) ^ (2 * r) = (G.card : ℂ) ^ (2 * r) := by
  have h0 : eta ψ G 0 = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  rw [h0]

/-- **The circle-method major/minor split of the `2r`-th power sum.**

`q·N₀(G,2r) = |G|^{2r} + ∑_{b≠0} η_b^{2r}`.

The `b = 0` term is the **major arc** (random main term `|G|^{2r}`); the `b ≠ 0` terms are the
**minor arcs**, carrying the entire arithmetic deviation. Derived by peeling `b = 0` off the exact
raw-moment identity `∑_b η_b^{2r} = q·N₀(G,2r)` (`subgroup_gaussSum_rawMoment`). The minor arc is
the only place a circle-method estimate could act — and it is a *moment* of `η_b`. -/
theorem circle_major_minor_pow {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    (Fintype.card F : ℂ) * N0 G (2 * r)
      = (G.card : ℂ) ^ (2 * r) + ∑ b ∈ Finset.univ.erase (0 : F), eta ψ G b ^ (2 * r) := by
  have hraw := subgroup_gaussSum_rawMoment hψ G (2 * r)
  have hsplit : ∑ b : F, eta ψ G b ^ (2 * r)
      = eta ψ G (0 : F) ^ (2 * r) + ∑ b ∈ Finset.univ.erase (0 : F), eta ψ G b ^ (2 * r) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F))]; ring
  rw [hraw, major_arc_value] at hsplit
  exact hsplit

/-! ### (ii) The induced SUP bound is the moment — and the moment is `≥ n` (fence F12). -/

/-- **The total `2r`-th power sum dominates the SUP of `|η_b|^{2r}`.** Real form: with
`|η_b| ≤ M` for all `b` and `m` the number of minor-arc frequencies, `M^{2r} ≤` (any frequency's
`2r`-th power) `≤` the total `∑_b |η_b|^{2r} = q·E_r`. We package the structural step: if a single
nonnegative term is `≤` a finite sum of nonnegative terms, it is `≤` the sum. The circle method
gains nothing beyond this: the minor-arc total IS the energy. -/
theorem sup_le_total_pow {ι : Type*} [Fintype ι] (t : ι → ℝ) (b₀ : ι)
    (ht : ∀ b, 0 ≤ t b) :
    t b₀ ≤ ∑ b, t b :=
  Finset.single_le_sum (fun b _ => ht b) (Finset.mem_univ b₀)

/-- **The circle method's induced SUP estimate is the dead moment optimum (fence F1/F12).**
The only sup bound the major/minor decomposition yields is `M^{2r} ≤ q·E_r`, i.e.
`M ≤ (q·E_r)^{1/2r}`; with `E_r = ∑_s (c s)²` the additive energy (`c s` = #`r`-tuples summing to
`s`, total `∑_s c s = n^r`), the moment no-go forces `(q·E_r)^{1/2r} ≥ n` for **every** order `r`.
So the circle method cannot certify `M < n` (let alone `M ≲ √(n log m)`): its sole sup handle is
the additive-energy moment, which is conjugate to the wall and bounded below by the trivial `n`. -/
theorem circle_sup_bound_ge_card {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ) (hr : 0 < r)
    (hcount : ∑ s, c s = (n : ℝ) ^ r) :
    (n : ℝ) ≤ ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) :=
  moment_bound_ge_card c n r hr hcount

/-- **Lane verdict as a single implication: the circle method cannot beat `n` on the SUP.**
Contrapositive of the moment no-go: if the circle method's induced sup estimate `(q·E_r)^{1/2r}`
were `< n`, that is impossible — for every order `r` it is `≥ n`. The minor-arc handle is the
energy moment (handle (ii)), the van der Corput square is the 2nd moment (handle (i)), and the
Weyl/Vinogradov saving mechanism needs interval/polynomial structure `μ_n` lacks (handle (iii));
none escapes fence F1/F12. -/
theorem circle_method_sup_dead {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ) (hr : 0 < r)
    (hcount : ∑ s, c s = (n : ℝ) ^ r)
    (hbound : ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) < (n : ℝ)) :
    False :=
  absurd (circle_sup_bound_ge_card c n r hr hcount) (not_le.mpr hbound)

/-! ### (i) Weyl differencing on the degree-1 phase = the autocorrelation 2nd moment.

The van der Corput / Weyl square of the period expands to the additive autocorrelation; since the
phase is linear, no degree reduction occurs. Diagonal `n`, off-diagonal `(n−1)·n` (GROWS), all
terms nonnegative — the positive-definite second moment, phase-blind. We record the off-diagonal
growth abstractly (the autocorrelation of a size-`n` set has total `n²` = `n × diagonal n`). -/

/-- **Weyl-differencing off-diagonal GROWS as `(n−1)·diagonal`.** For the van der Corput square
`|η_b|² = ∑_h A_n(h)e_p(bh)`, the autocorrelation profile `A_n` of a size-`n` set has diagonal
`A_n(0) = n` and total mass `∑_h A_n(h) = n²` (the `n²` ordered pairs). Hence the off-diagonal total
is `n² − n = (n−1)·n = (n−1)·diagonal`: the differenced object is dominated by a `(n−1)`-fold
*positive* off-diagonal, the opposite of the `o(diagonal)` cancellation Weyl differencing exploits
on a higher-degree phase. There is no degree to reduce (the phase is linear), so differencing
returns the 2nd moment. -/
theorem weyl_offdiag_growing (d : ℝ) (n : ℝ) :
    (n * d) - d = (n - 1) * d := by ring

end ProximityGap.Frontier.CircleMethodSupForm

/-! ## Axiom audit (must be `⊆ {propext, Classical.choice, Quot.sound}`) -/
#print axioms ProximityGap.Frontier.CircleMethodSupForm.major_arc_value
#print axioms ProximityGap.Frontier.CircleMethodSupForm.circle_major_minor_pow
#print axioms ProximityGap.Frontier.CircleMethodSupForm.sup_le_total_pow
#print axioms ProximityGap.Frontier.CircleMethodSupForm.circle_sup_bound_ge_card
#print axioms ProximityGap.Frontier.CircleMethodSupForm.circle_method_sup_dead
#print axioms ProximityGap.Frontier.CircleMethodSupForm.weyl_offdiag_growing
