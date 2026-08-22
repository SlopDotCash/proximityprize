/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumRawMoment

/-!
# The circle-method (major/minor arc) split of the relation count `N₀` and of `crossCell` (#407, wf-NE)

**Lane wf-NE.** A genuinely new application of the Hardy–Littlewood circle method, distinct from
`CircleMethodFreeSetSupport.lean` (which ran the method on the §7 bad-scalar count `a`). Here the
method is applied to the **additive-relation count** `N₀(G,r)` and, via the dyadic split
`G = H ⊔ ζ·H` of `CumulantDyadicDescent`, to the **off-diagonal cross-resonance count**
`crossCell := N₀(G,r) − 2·N₀(H,r)` (`CumulantDyadicDescent.cumulant_descent_ge`).

## The exact major/minor arc identity (the airtight combinatorial backbone)

The substrate `subgroup_gaussSum_rawMoment` is the circle-method Fourier inversion of the relation
count over the *full* frequency set: `∑_{b∈F} η_b^r = q·N₀(G,r)`, with `η_b = ∑_{x∈G} ψ(bx)` the
period (the additive character sum of `G` at frequency `b`). Splitting the `b`-sum into the
**major arc** `b = 0` (where `η_0 = |G|`) and the **minor arcs** `b ≠ 0`:

> `q·N₀(G,r) = |G|^r + ∑_{b≠0} η_b^r`.            (`q_N0_major_minor`)

So the relation count is **exactly** the random main term `|G|^r/q` plus the minor-arc contribution
`(1/q)∑_{b≠0}η_b^r`. For the cross object, taking `G = H ⊔ ζH` (so `|G| = 2|H|`) and subtracting
twice the `H`-count:

> `q·crossCell(G,H,r) = (2^r − 2)·|H|^r + minorCross`,                (`q_crossCell_major_minor`)
> `minorCross := (∑_{b≠0} η_b(G)^r) − 2·(∑_{b≠0} η_b(H)^r)`.

The **major arc of `crossCell` is exactly `(2^r − 2)|H|^r`** — the random/BCHKS-1.12 main term
(`(n/2)^r(2^r−2)/q` after dividing by `q`, matching the probe `major(t=0)` column). The whole
arithmetic content of `crossCell` is the minor arc.

## What the numerics say (the honest verdict of the lens)

`scripts/probes/probe_wf2NE_crosscell_circlemethod.py` and `..._deepdepth.py` compute the split
exactly (DFT power-sum, integer-cross-checked to ~1e-9, `n=8,16,32`, primes `β = 2…5`):

* **Small `r` (fixed):** `crossCell` is **`p`-independent** (a fixed char-0 integer: `96` at `n=8`,
  `1536` at `n=32`, `r=4`), while the major arc `(2^r−2)|H|^r/q → 0` as `q` grows. Hence the minor
  arc *is* essentially all of `crossCell` and `|minor|/major` BLOWS UP with `q`. There is **no**
  concentration on the random main term at shallow depth — the opposite (this is the char-0
  over-determined-incidence rigidity already pinned in §5/R4).
* **Deep depth `r* ≈ β·log₂ n ≈ ln q / ln 2` (the genuinely-open band):** the major arc CATCHES UP
  and `crossCell ≈ major` (cc/major `→ 1`). At the cleanest prize-shaped point `n=32`, `|H|=16`,
  `β ∈ {1.83, 2.40, 3.00}`, the deep-depth `|minor|/major = 0.011, 0.032, 0.0055` — the minor arc
  is **subdominant** and `crossCell` **concentrates on its random major-arc value**.

**Verdict (honest): WALLED — concentration, not cancellation.** The circle method shows `crossCell`
equals its random main term `(2^r−2)|H|^r` at the deep depth, neither anomalously large (no excess)
nor sub-trivially small (no savings). This is **exactly** the "= random BCHKS-1.12 expectation"
already recorded by lane wf-LF and the A02 autocorrelation thread, now derived through the
arc-decomposition and localized to the minor arc. It is **not** a sub-trivial improvement over the
random value: the floor follows iff the *random* value satisfies the deep-moment target (which it
does by construction, `= (2r−1)‼·n^r`), so the circle method **transfers** the question to the
uniform-in-`q` control of the minor arc `∑_{b≠0}η_b^r` at the prize `n = 2^32` — i.e. back to the
deep-moment / Gauss-period W4 wall, with **no new lever**. The two precision caveats are honest:
(i) at `r ≳ 16`, `q ≳ 6·10^4`, the float64 power-sum loses the low-order minor digits, so the exact
`~1%` minor value is at the resolution limit; (ii) the n=32 data is `n=32`, not the prize `n=2^32` —
the *uniformity* of the subdominance in `n` is the unproven step.

## What this file PROVES (axiom target `[propext, Classical.choice, Quot.sound]`)

The **exact arc-decomposition identities** — the airtight, character-sum-free combinatorial
backbone of the lens (the analytic content, the minor-arc estimate, remains the named open wall):

* `q_N0_major_minor` — `q·N₀(G,r) = |G|^r + ∑_{b≠0} η_b^r` (major/minor split of the relation count).
* `eta_zero_pow` — `η_0^r = |G|^r` (the major-arc value).
* `q_crossCell_major_minor` — the cross-object split with major arc `(2^r−2)|H|^r`.
* `crossCell_minor_eq` — the minor arc of `crossCell` as the named open object `minorCross`.

## References
- [BCHKS25] ECCC TR25-169 / ePrint 2025/2055, Conjecture 1.12 (the cross-resonance / random count).
- [ABF26] Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement*, 2026 (#407).
- `CumulantDyadicDescent.lean` (the dyadic split `N₀(G,r) = 2N₀(H,r) + crossCell`).
- `CircleMethodFreeSetSupport.lean` (the prior, distinct circle-method application — on `a`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumRawMoment

namespace ArkLib.ProximityGap.Frontier.CrossCellCircleMethod

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The major-arc value: `η_0^r = |G|^r`.** At frequency `b = 0` the period is the trivial
character sum `η_0 = ∑_{x∈G} ψ(0) = |G|`, so its `r`-th power is `|G|^r` — the singular series /
random main term of the circle method. -/
theorem eta_zero_pow (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) :
    eta ψ G (0 : F) ^ r = (G.card : ℂ) ^ r := by
  have h0 : eta ψ G 0 = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  rw [h0]

/-- **The circle-method major/minor split of the relation count.**

`q·N₀(G,r) = |G|^r + ∑_{b≠0} η_b^r`.

The `b = 0` term is the **major arc** (the random main term `|G|^r`); the `b ≠ 0` terms are the
**minor arcs**, carrying the entire arithmetic deviation of `N₀` from the random value. Derived by
peeling the `b = 0` term off the exact raw-moment identity `∑_b η_b^r = q·N₀(G,r)`
(`subgroup_gaussSum_rawMoment`). -/
theorem q_N0_major_minor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    (Fintype.card F : ℂ) * N0 G r
      = (G.card : ℂ) ^ r + ∑ b ∈ Finset.univ.erase (0 : F), eta ψ G b ^ r := by
  have hraw := subgroup_gaussSum_rawMoment hψ G r
  -- peel b = 0 from the full b-sum
  have hsplit : ∑ b : F, eta ψ G b ^ r
      = eta ψ G (0 : F) ^ r + ∑ b ∈ Finset.univ.erase (0 : F), eta ψ G b ^ r := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F))]
    ring
  rw [hraw, eta_zero_pow] at hsplit
  exact hsplit

/-- **The minor arc of a frequency family** (the named open analytic object). -/
noncomputable def minorArc (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) : ℂ :=
  ∑ b ∈ Finset.univ.erase (0 : F), eta ψ G b ^ r

/-- **`q·N₀` as major-arc + minor-arc, in `minorArc` notation.** -/
theorem q_N0_eq_major_add_minorArc {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    (Fintype.card F : ℂ) * N0 G r = (G.card : ℂ) ^ r + minorArc ψ G r :=
  q_N0_major_minor hψ G r

/-- **The circle-method major/minor split of `crossCell` (the cross-resonance count).**

For the dyadic split `G = H ⊔ ζH` (so `|G| = 2|H|`), the cross object
`crossCell = N₀(G,r) − 2·N₀(H,r)` has, after multiplying by `q`,

> `q·N₀(G,r) − 2·q·N₀(H,r) = (2^r − 2)·|H|^r + (minorArc(G,r) − 2·minorArc(H,r))`.

The **major arc of `crossCell` is exactly `(2^r − 2)·|H|^r`** — the random/BCHKS-1.12 main term
(this is `((n/2)^r·(2^r−2))` , dividing by `q` gives the probe's `major(t=0)` column). The full
arithmetic content of `crossCell` is the minor difference `minorArc(G,r) − 2·minorArc(H,r)` (the
named open object: the deep-moment / Gauss-period W4 wall). The hypothesis `hGcard : |G| = 2|H|`
encodes the disjoint dyadic coset union `μ_n = μ_{n/2} ⊔ ζ·μ_{n/2}`. -/
theorem q_crossCell_major_minor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G H : Finset F) (r : ℕ) (hGcard : G.card = 2 * H.card) :
    (Fintype.card F : ℂ) * N0 G r - 2 * ((Fintype.card F : ℂ) * N0 H r)
      = (2 ^ r - 2) * (H.card : ℂ) ^ r
        + (minorArc ψ G r - 2 * minorArc ψ H r) := by
  rw [q_N0_eq_major_add_minorArc hψ G r, q_N0_eq_major_add_minorArc hψ H r]
  have hGexp : (G.card : ℂ) ^ r = (2 : ℂ) ^ r * (H.card : ℂ) ^ r := by
    rw [hGcard]; push_cast; rw [mul_pow]
  rw [hGexp]
  ring

/-- **The minor arc of `crossCell`, isolated** (the named open object `minorCross`). All the
arithmetic deviation of the cross-resonance count from its random main term `(2^r−2)|H|^r` lives in
`minorArc(G,r) − 2·minorArc(H,r)`; the lens reduces the floor to a uniform-in-`q` (and in-`n`) bound
on this minor difference — which is the deep-moment / Gauss-period wall, with no new lever. -/
theorem crossCell_minor_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G H : Finset F) (r : ℕ) (hGcard : G.card = 2 * H.card) :
    ((Fintype.card F : ℂ) * N0 G r - 2 * ((Fintype.card F : ℂ) * N0 H r))
        - (2 ^ r - 2) * (H.card : ℂ) ^ r
      = minorArc ψ G r - 2 * minorArc ψ H r := by
  rw [q_crossCell_major_minor hψ G H r hGcard]; ring

end ArkLib.ProximityGap.Frontier.CrossCellCircleMethod

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.Frontier.CrossCellCircleMethod.eta_zero_pow
#print axioms ArkLib.ProximityGap.Frontier.CrossCellCircleMethod.q_N0_major_minor
#print axioms ArkLib.ProximityGap.Frontier.CrossCellCircleMethod.q_N0_eq_major_add_minorArc
#print axioms ArkLib.ProximityGap.Frontier.CrossCellCircleMethod.q_crossCell_major_minor
#print axioms ArkLib.ProximityGap.Frontier.CrossCellCircleMethod.crossCell_minor_eq
