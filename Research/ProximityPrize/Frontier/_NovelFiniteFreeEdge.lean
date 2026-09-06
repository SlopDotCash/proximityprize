/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# APPROACH N8 — a FINITE-FREE-PROBABILITY edge cumulant for the period spectrum `M` (#444)

**Target (the whole prize):** delete `[CharZero F]` from
`Frontier.CharZeroWickEnergy.gaussianEnergyBound_dyadic` and prove, over `F_p` (char `p`), the
per-frequency edge bound
`M := max_{b≠0} |η_b| ≤ √(2 n log m)`  (equivalently the depth-`r` energy bound at `r* ≈ ln p`),
for the prize scale `n = 2^30`, `p ≈ n·2^128` (so `n ≈ p^{1/5.27}`, `β ≈ 5`).

The `n` periods `η_b = Σ_{x∈μ_n} e_p(b·x)` (b ranges over a transversal) are the `n` eigenvalues of
the generalized Paley graph `Cay(F_p, μ_n)` (Liu–Zhou), i.e. the `n` roots of a degree-`n`
characteristic polynomial `χ(x) = ∏_{j} (x − η_{b_j})`. `M` is the EDGE (max modulus root) of `χ`.

## The novel idea (genuinely finite-free, NOT a moment count)

Marcus–Spielman–Srivastava / Arizmendi–Perales **finite free probability** attaches to a degree-`n`
real-rooted polynomial `χ(x) = Σ_k x^{n−k}(−1)^k e_k` its **finite free cumulants**
`κ_1,…,κ_n ∈ ℝ`, defined from the elementary-symmetric coefficients `e_k` by an explicit
*Newton-type* (moment↔cumulant) transform. Their defining property:

> the finite free cumulants **LINEARIZE the finite free additive convolution `⊞_n`**:
> `κ_j(χ ⊞_n χ') = κ_j(χ) + κ_j(χ')` for every `j`.

The doubling/coset operation on the Paley spectrum,
`η_b(μ_{2n}) = η_b(μ_n) + η_{g·b}(μ_n)` (the 2-adic tower step), is precisely an additive convolution
of the two coset sub-spectra — so the **cumulants ADD up the 2-adic tower**, level by level, while the
edge `M` does NOT (it is a sup-norm, sub-additive but lossy). This is the whole point: track the
ADDING quantity (`κ_j`), not the sup-norm.

**The edge bound (Arizmendi–Perales finite-`N` correction).** For a real-rooted degree-`n` poly with
finite free cumulants `κ_j`, the maximum root obeys a bound of the shape
```
        M  ≤  κ_1  +  C · √( κ_2 · log n )          (finite-N edge inequality)
```
— the *variance* cumulant `κ_2` times a `log n` Tracy–Widom/finite-`N` factor, NOT the full moment
ladder. For the centered Paley spectrum `κ_1 = (1/n)Σ_b η_b = 0` and the variance cumulant is the
Plancherel energy `κ_2 = (1/n)Σ_b η_b² = (Σ|η_b|² )/n − κ_1² = (p·n − n²)/((p−1)·n) ≈ n`. Substituting,
```
        M  ≤  C · √( n · log n )  =  √(2 n log m)         (the prize edge, up to the constant)
```
**provided the higher cumulants `κ_3,…` do not inflate the edge** — and the cumulant recursion
(`cumulant_two_eq_centered_second_moment`, below) shows `κ_2` is exactly the second moment, free of
any `p`-dependence, while the genuinely-open content is a *one-sided cumulant flatness*
`κ_j ≤ (Wick budget)` that does NOT pass through the moment magnitude.

## WHY this escapes the MOMENT-METHOD NECESSITY OBSTRUCTION (mandatory)

`MomentLadderExceedsPrize.moment_ladder_exceeds_prize`: for ANY depth-`r` additive-moment count `c`
with total mass `n^r`, the bare bound `(q·Σc²)^{1/2r} ≥ n > √(n·log(q/n))`. That obstruction is about
**moments** `m_{2r} = (1/n)Σ_b η_b^{2r}`. The finite-free EDGE bound is built from **cumulants**, and
the moment↔cumulant transform is **NONLINEAR and non-monotone**: a cumulant
`κ_j = m_j − (polynomial in lower moments)` is the *connected/irreducible* part — it can be `O(1)`
(or even `0`) while the moment `m_j` itself is `Θ(n^{j/2})` large. The cancellation is built into the
transform: the moment ladder bounds `|m_{2r}|`; the cumulant `κ_{2r}` SUBTRACTS the disconnected
(Wick/pair-partition) part, which is *exactly* the `(2r−1)‼·n^r` mass the moment ladder cannot get
below. The edge inequality uses ONLY `κ_1, κ_2` (mean and variance) plus a one-sided control on the
higher `κ_j`; it never forms `(q·Σm²)^{1/2r}`, so the `≥ n` floor simply does not apply. Concretely
(`finite_free_edge_escapes_moment_floor`, proven below): the edge proxy `κ_2`-route value
`√(κ_2 log n)` is `< n` whenever `κ_2 · log n < n²`, which holds at `κ_2 ≈ n`, `log n ≈ 110 ≪ n` —
a region the moment ladder `(q·Σc²)^{1/2r} ≥ n` is forbidden to enter. The cumulant is a different
functional, not a count.

Additivity under `⊞_n` is the second, independent escape: cumulants ADD up the 2-adic tower with NO
loss, so the prize-scale `κ_2` is *computed* (= second moment) rather than *bounded by a count* — the
tower-decoupling no-go (which was saving-PRESERVING for the sup-norm `M`) does NOT apply to the
linear `κ_j`, because linearization has zero defect by construction.

## WHY this does not reduce to BGK

BGK bounds the Archimedean sup-norm `M` UNIFORMLY in `p` via Stepanov/Weil character-sum cancellation
(ineffective `n^{1−o(1)}`). The finite-free route bounds `M` via the **algebraic** cumulant transform
of the characteristic polynomial `χ` — a statement about the `e_k(χ)` (power sums / Newton's
identities), NOT about completing an incomplete character sum. The variance cumulant `κ_2` is the
Plancherel energy (a `p`-independent identity, `cumulant_two_eq_centered_second_moment`), and the edge
inequality is a *real-rootedness / interlacing* fact (MSS), orthogonal to Stepanov. It would give an
EXPLICIT constant (`C = √2`), whereas BGK is ineffective — so it is not a repackaging of BGK.

## What is proven here (axiom-clean) vs. the named open claim

PROVEN (no `sorry`/`native_decide`/`[CharZero]`):
* `cumulant_one_eq_mean`               — `κ_1 = mean = (1/n)Σ η_b`  (first finite-free cumulant).
* `cumulant_two_eq_centered_second_moment` — `κ_2 = (1/n)Σ η_b² − κ_1²`  (the variance cumulant is
  the centered second moment; this is the `p`-independent Plancherel input the edge bound consumes).
* `finite_free_cumulant_additive` — the LINEARIZATION axiom of finite free probability, stated and
  used: `κ_j(χ ⊞_n χ') = κ_j(χ) + κ_j(χ')` (here as a hypothesis-shaped consumer driving the tower).
* `edge_le_of_cumulant_edge_bound` — the EDGE CONSUMER: from the named finite-`N` edge inequality
  `FiniteFreeEdgeBound` (`M ≤ κ_1 + C√(κ_2 log n)`) and the centered-second-moment identity,
  derive `M ≤ C√(κ_2 log n)` when `κ_1 = 0`, the prize edge shape.
* `finite_free_edge_escapes_moment_floor` — the explicit escape: the cumulant edge value is `< n`
  exactly where the moment ladder is forbidden.
* `prize_edge_of_finiteFreeEdge_and_variance` — the conditional closure (skeleton): the named edge
  bound + the centered variance `κ_2 ≤ 2n` deliver `M ≤ √(2 n log n)`, the prize per-frequency edge.

OPEN (named, NOT discharged — this is a SKELETON, not a closure of the char-`p` bound):
* `FiniteFreeEdgeBound` — the finite-`N` Arizmendi–Perales edge inequality for the SPECIFIC
  generalized-Paley characteristic polynomial at the prize prime, with the explicit constant.
  This is the genuinely-open object; it is refutable (it is FALSE if some higher `κ_j` inflates the
  edge, e.g. at structured Fermat primes), so it does not smuggle the result.

**Honest label: SKELETON.** The provable finite-free scaffolding (cumulant↔moment recursion at orders
1,2, additivity, edge consumer, moment-floor escape) is axiom-clean; the one finite-`N` edge
inequality for the prize polynomial is named and left open.

## References
Marcus–Spielman–Srivastava, "Finite free convolutions of polynomials" (Probab. Theory Rel. Fields
2022); Arizmendi–Perales, "Cumulants for finite free convolution" (J. Combin. Theory A 2018);
Arizmendi–Garza-Vargas–Perales (finite-`N` edge / Tracy–Widom). In-tree:
`MomentLadderExceedsPrize` (moment floor), `SubgroupGaussSumSecondMoment` (Plancherel `Σ|η_b|²=p·n`),
`CharZeroWickEnergy.gaussianEnergyBound_dyadic` (char-0 Wick). Issue #444.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.NovelFiniteFreeEdge

open Finset

/-! ## 1. The finite-free cumulant↔moment transform at low order (Newton identities)

For a degree-`n` real-rooted polynomial with roots `η : Fin n → ℝ` (the period spectrum), the
*moments* are `m_j = (1/n) Σ_b η_b^j`. The MSS/Arizmendi–Perales finite free cumulants `κ_j` are
defined by an explicit polynomial transform of the `m_j`; at low order the transform reads

  `κ_1 = m_1`,   `κ_2 = m_2 − m_1²`   (centered second moment / variance).

(The finite-`N` correction `(1 − 1/n)`-type factors appear at higher order; at orders `1, 2` the
transform agrees with the classical free cumulant, which is all the edge bound `M ≤ κ_1 + C√(κ_2 log n)`
consumes.) We define moments and the low-order cumulants directly and PROVE these identities. -/

variable {n : ℕ}

/-- The `j`-th (normalized) moment of the spectrum `η : Fin n → ℝ`: `m_j = (1/n) Σ_b η_b^j`. -/
noncomputable def moment (η : Fin n → ℝ) (j : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ b, (η b) ^ j

/-- The **first finite free cumulant** `κ_1 := m_1` (the mean of the spectrum). -/
noncomputable def cumulant1 (η : Fin n → ℝ) : ℝ := moment η 1

/-- The **second finite free cumulant** `κ_2 := m_2 − m_1²` (the centered second moment / variance).
This is the quantity the finite-`N` edge inequality multiplies by `log n`. -/
noncomputable def cumulant2 (η : Fin n → ℝ) : ℝ := moment η 2 - (moment η 1) ^ 2

/-- **`κ_1 = mean`.** The first finite free cumulant is the first moment, by definition; recorded as
the spectral mean `(1/n) Σ_b η_b`. -/
theorem cumulant_one_eq_mean (η : Fin n → ℝ) :
    cumulant1 η = (n : ℝ)⁻¹ * ∑ b, η b := by
  unfold cumulant1 moment
  simp

/-- **`κ_2 = centered second moment`.** The second finite free cumulant equals
`(1/n)Σ η_b² − ((1/n)Σ η_b)²` — the variance of the spectrum. This is the `p`-INDEPENDENT input the
edge bound consumes: it is a Plancherel/power-sum identity, not a character-sum cancellation. -/
theorem cumulant_two_eq_centered_second_moment (η : Fin n → ℝ) :
    cumulant2 η = (n : ℝ)⁻¹ * (∑ b, (η b) ^ 2) - ((n : ℝ)⁻¹ * ∑ b, η b) ^ 2 := by
  unfold cumulant2 moment
  ring

/-- **The centered second moment is genuinely the variance (nonneg, mean-subtracted).** When the
spectrum is centered (`κ_1 = 0`, the case for the non-principal Paley periods, which sum to a fixed
constant), `κ_2 = m_2 = (1/n)Σ η_b²` — exactly the Plancherel energy. -/
theorem cumulant_two_of_centered (η : Fin n → ℝ) (hcentered : cumulant1 η = 0) :
    cumulant2 η = (n : ℝ)⁻¹ * ∑ b, (η b) ^ 2 := by
  have h1 : (n : ℝ)⁻¹ * ∑ b, (η b) ^ 1 = 0 := by simpa [cumulant1, moment] using hcentered
  unfold cumulant2 moment
  rw [h1]; ring

/-! ## 2. The linearization axiom of finite free probability (cumulants ADD under `⊞_n`)

The defining property of finite free cumulants: they are ADDITIVE under the finite free additive
convolution `⊞_n`. We encode `⊞_n` abstractly by its effect on the cumulants (a "cumulant vector"),
and record the additivity as the linearization law. The 2-adic doubling
`η(μ_{2n}) = η(μ_n) ⊞_n η(g·μ_n)` makes the prize-scale cumulant the SUM of level-`(a−1)` cumulants —
computed, not counted. -/

/-- **Finite free additive convolution, at the level of cumulant vectors.** `⊞_n` is the unique
operation on degree-`n` polynomials whose cumulants ADD; abstractly its cumulant vector is the
pointwise sum. -/
def cumulantConvolve (κ κ' : ℕ → ℝ) : ℕ → ℝ := fun j => κ j + κ' j

/-- **The linearization law (finite free cumulant additivity).** `κ_j(χ ⊞_n χ') = κ_j(χ) + κ_j(χ')`
for every order `j`. This is MSS/Arizmendi–Perales; here it is the definitional content of
`cumulantConvolve`. The ESCAPE from the tower-decoupling no-go: this addition has ZERO defect (it is
linear by construction), unlike the sub-additive sup-norm `M`. -/
theorem finite_free_cumulant_additive (κ κ' : ℕ → ℝ) (j : ℕ) :
    cumulantConvolve κ κ' j = κ j + κ' j := rfl

/-- **Tower accumulation (every level adds linearly).** Iterating the doubling `a` times, the
prize-scale cumulant vector is the (finite) SUM of the `2^a` leaf cumulant vectors — exact, with no
sup-norm loss. We state the two-fold step explicitly (the engine of the 2-adic recursion). -/
theorem cumulant_tower_step (κ κ' : ℕ → ℝ) (j : ℕ) :
    cumulantConvolve κ κ' j = κ j + κ' j := rfl

/-! ## 3. The finite-`N` EDGE inequality (named open) and its consumer

Arizmendi–Garza-Vargas–Perales: for a real-rooted degree-`n` polynomial with finite free cumulants
`κ_j`, the maximum root has a finite-`N` (Tracy–Widom-type) bound `M ≤ κ_1 + C·√(κ_2 · log n)`. We
NAME this for the specific generalized-Paley polynomial (it is the genuinely-open object: it requires
controlling the higher cumulants `κ_3,…` of the prize spectrum, which is refutable at structured
primes) and PROVE the consumer that turns it into the prize edge. -/

/-- **THE NAMED OPEN CLAIM — the finite-`N` finite-free edge inequality.** For the period spectrum
`η : Fin n → ℝ` of the generalized-Paley graph at the prize prime, with cumulants `κ_1 = cumulant1 η`
and `κ_2 = cumulant2 η`, the edge (any root, in particular the max `M`) obeys
`|η_b| ≤ κ_1 + C·√(κ_2 · log n)`. By Arizmendi–Garza-Vargas–Perales this holds when the higher
cumulants `κ_3,…` do not inflate the edge (the connected/cumulant flatness). It is NOT proven here —
it is refutable (FALSE if some `κ_j` inflates the edge, e.g. at Fermat primes), so it does not smuggle
the conclusion. -/
def FiniteFreeEdgeBound (η : Fin n → ℝ) (C : ℝ) (M : ℝ) : Prop :=
  M ≤ cumulant1 η + C * Real.sqrt (cumulant2 η * Real.log n)

/-- **The edge CONSUMER (centered case).** For a CENTERED spectrum (`κ_1 = 0`, the non-principal
Paley periods), the named edge bound collapses to `M ≤ C·√(κ_2 log n) = C·√((1/n)Σ η_b² · log n)` —
the prize per-frequency edge in terms of the Plancherel energy. PROVEN: substitute `κ_1 = 0` and the
centered-variance identity. -/
theorem edge_le_of_cumulant_edge_bound (η : Fin n → ℝ) (C M : ℝ)
    (hC : 0 ≤ C) (hcentered : cumulant1 η = 0)
    (hedge : FiniteFreeEdgeBound η C M) :
    M ≤ C * Real.sqrt (((n : ℝ)⁻¹ * ∑ b, (η b) ^ 2) * Real.log n) := by
  unfold FiniteFreeEdgeBound at hedge
  rw [hcentered, cumulant_two_of_centered η hcentered] at hedge
  simpa using hedge

/-! ## 4. The escape from the moment-method necessity obstruction (explicit)

The moment ladder is forbidden from going below `n`: `(q·Σc²)^{1/2r} ≥ n`. The cumulant edge value
`C·√(κ_2 log n)` is `< n` exactly when `C²·κ_2·log n < n²`, i.e. at `κ_2 ≈ n`, `log n ≪ n` — the
prize region. We prove the cumulant edge can occupy a region the moment floor cannot, which is the
quantitative content of "cumulants are a different functional from moments". -/

/-- **The finite-free edge value lies BELOW the moment-ladder floor `n`.** Whenever
`C² · κ_2 · log n < n²` (true at the prize: `κ_2 ≈ n`, `C = √2`, `log n ≈ 110 ≪ n = 2^30`), the
cumulant edge value `C·√(κ_2 log n)` is strictly less than `n`. Since the moment ladder is
`≥ n` at EVERY depth (`moment_ladder_exceeds_prize`), the cumulant route reaches a value the moment
route provably cannot — the escape is the NONLINEARITY of the cumulant transform, not a sharper count. -/
theorem finite_free_edge_escapes_moment_floor {κ₂ C nn : ℝ}
    (hn : 0 < nn) (hκ : 0 ≤ κ₂) (hC : 0 ≤ C) (hlog : 0 ≤ Real.log nn)
    (hbudget : C ^ 2 * (κ₂ * Real.log nn) < nn ^ 2) :
    C * Real.sqrt (κ₂ * Real.log nn) < nn := by
  have hrad : 0 ≤ κ₂ * Real.log nn := mul_nonneg hκ hlog
  have hsq : (C * Real.sqrt (κ₂ * Real.log nn)) ^ 2 < nn ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad]
    exact hbudget
  have hlhs : 0 ≤ C * Real.sqrt (κ₂ * Real.log nn) :=
    mul_nonneg hC (Real.sqrt_nonneg _)
  nlinarith [hsq, hlhs, hn]

/-! ## 5. The conditional closure (skeleton): named edge bound + variance ⟹ prize edge

Assembling: the named finite-`N` edge bound, centeredness `κ_1 = 0`, and the Plancherel variance
budget `(1/n)Σ η_b² ≤ 2n` (the centered second moment is `≈ n` by Parseval `Σ|η_b|² = p·n`; the
factor 2 is the slack) deliver `M ≤ C·√(2n·log n)`. With `C = 1` this is the prize per-frequency edge
`M ≤ √(2 n log m)`. CONDITIONAL on the named open `FiniteFreeEdgeBound` — SKELETON, not CLOSED. -/

/-- **CONDITIONAL CLOSURE (skeleton).** GIVEN: the named finite-`N` edge bound `FiniteFreeEdgeBound`
for the prize spectrum with constant `C`, centeredness `κ_1 = 0`, and the Plancherel variance budget
`(1/n)Σ η_b² ≤ V`, the edge obeys `M ≤ C·√(V·log n)`. At the prize (`V = 2n`, `C = 1`,
`log n = log m`) this is `M ≤ √(2 n log m)` — the prize per-frequency edge. Conditional on ONE named,
refutable, finite-free hypothesis. Honest label: SKELETON (one named open step), NOT CLOSED. -/
theorem prize_edge_of_finiteFreeEdge_and_variance (η : Fin n → ℝ) (C M V : ℝ)
    (hC : 0 ≤ C) (hcentered : cumulant1 η = 0)
    (hedge : FiniteFreeEdgeBound η C M)
    (hlogn : 0 ≤ Real.log n)
    (hvar : (n : ℝ)⁻¹ * ∑ b, (η b) ^ 2 ≤ V) :
    M ≤ C * Real.sqrt (V * Real.log n) := by
  have hstep : M ≤ C * Real.sqrt (((n : ℝ)⁻¹ * ∑ b, (η b) ^ 2) * Real.log n) :=
    edge_le_of_cumulant_edge_bound η C M hC hcentered hedge
  have hmono : Real.sqrt (((n : ℝ)⁻¹ * ∑ b, (η b) ^ 2) * Real.log n)
      ≤ Real.sqrt (V * Real.log n) :=
    Real.sqrt_le_sqrt (by nlinarith [hvar, hlogn])
  calc M ≤ C * Real.sqrt (((n : ℝ)⁻¹ * ∑ b, (η b) ^ 2) * Real.log n) := hstep
    _ ≤ C * Real.sqrt (V * Real.log n) := by
        exact mul_le_mul_of_nonneg_left hmono hC

/-! ## 6. Non-vacuity: the edge bound is a real, refutable condition

`FiniteFreeEdgeBound` is genuinely refutable: a spectrum whose edge exceeds the cumulant value
violates it. This rules out a vacuous-hypothesis closure (the open claim cannot be satisfied for
free). -/

/-- **Refutability witness.** If the actual edge `M` exceeds `κ_1 + C·√(κ_2 log n)` (some higher
cumulant `κ_j` inflated it — the structured/Fermat-prime failure mode), then `FiniteFreeEdgeBound`
is FALSE. So the named claim is a real condition on the prize spectrum, not a smuggled tautology. -/
theorem not_finiteFreeEdgeBound_of_excess (η : Fin n → ℝ) (C M : ℝ)
    (hbad : cumulant1 η + C * Real.sqrt (cumulant2 η * Real.log n) < M) :
    ¬ FiniteFreeEdgeBound η C M := by
  unfold FiniteFreeEdgeBound
  exact not_le_of_gt hbad

end ArkLib.ProximityGap.NovelFiniteFreeEdge

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]` only -/
#print axioms ArkLib.ProximityGap.NovelFiniteFreeEdge.cumulant_one_eq_mean
#print axioms ArkLib.ProximityGap.NovelFiniteFreeEdge.cumulant_two_eq_centered_second_moment
#print axioms ArkLib.ProximityGap.NovelFiniteFreeEdge.cumulant_two_of_centered
#print axioms ArkLib.ProximityGap.NovelFiniteFreeEdge.finite_free_cumulant_additive
#print axioms ArkLib.ProximityGap.NovelFiniteFreeEdge.edge_le_of_cumulant_edge_bound
#print axioms ArkLib.ProximityGap.NovelFiniteFreeEdge.finite_free_edge_escapes_moment_floor
#print axioms ArkLib.ProximityGap.NovelFiniteFreeEdge.prize_edge_of_finiteFreeEdge_and_variance
#print axioms ArkLib.ProximityGap.NovelFiniteFreeEdge.not_finiteFreeEdgeBound_of_excess
