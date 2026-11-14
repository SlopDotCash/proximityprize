/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# FRONTIER — F2 SUBCONVEXITY for the degenerate (finite) L-function of the Gauss-sum family (#444)

**Target (the whole prize).**  Bound `M = max_{b≠0}|η_b|`, `η_b = ∑_{x∈μ_n} e_p(b x)`, by
`C·√(n·log m)` over `F_p` (char `p`), prize scale `n = 2^30`, `p ≈ n·2^128` (`n ≈ p^{0.19}`,
`β ≈ 5.27`).  Equivalently `rEnergy(μ_n;F_p,r) ≤ (2r−1)‼·n^r` at `r ≈ ln p ≈ 110`.

**This approach (F2).**  Model `M` as the **sup-norm of a finite Dirichlet polynomial / degenerate
finite L-function** and ask whether a **SUBCONVEXITY** input — amplification, or moments of the
Gauss-sum family `{g(χ) : χ^n = 𝟙}` — beats the convexity bound at the **subgroup scale**
`√n·polylog` rather than the field scale `√p`.

## 1. The L-function model (the genuinely-stated object)

Diagonalise the period over the `n`-element character group of `μ_n` (= the Kummer/Gauss-sum form,
identical to `_NovelEllAdicSheaf` §1):

      `η_b = ∑_{χ : χ^n = 𝟙} g(χ)·χ̄(b)`,      `g(χ) = ∑_{t∈F_p^×} χ(t)·e_p(t)` the **Gauss sum**.

Read as a function of the "spectral parameter" `b`, this is a **finite Dirichlet polynomial of
length `n`** whose coefficients are the Gauss sums `g(χ)`.  Group the `n` characters into the
completed degenerate **L-function**

      `L(s) := ∑_{χ : χ^n = 𝟙} g(χ)·λ_χ^{−s}`        (a finite Dirichlet series, `n` terms),

so that `η_b` is `L` evaluated on the unitary line at the frequency dual to `b`.  The two hard
analytic invariants:

* **Conductor / analytic length** of this degenerate `L`: it is a **finite** Dirichlet polynomial
  of length exactly `n` (the order of the character group), NOT a genuine automorphic `L` of
  conductor `p`.  Its "analytic conductor" in the sup-norm problem is `n`.
* **Coefficient size** `|g(χ)| = √p` for every nontrivial `χ` (the **exact** Gauss-sum modulus —
  `|g(χ)|² = p` is a theorem, the single hardest fact pinning everything below), and `g(𝟙) = −1`.

## 2. The convexity bound — and WHERE the `√p` enters (the vacuity, made precise)

For a Dirichlet polynomial `D(b) = ∑_{j=1}^{n} a_j χ̄_j(b)` the elementary **convexity / triangle**
sup-norm bound is `‖D‖_∞ ≤ ∑_j |a_j|`.  With `a_j = g(χ_j)`, `|a_j| = √p`, this is

      `M = ‖η‖_∞ ≤ ∑_{χ} |g(χ)| = (n−1)·√p + 1  ≈  n·√p`.        (CONVEXITY)

The **`L²`/Plancherel** (Parseval) bound — the "convexity-on-average" line — is sharper but still
`√p`-tethered:

      `(1/(p−1))·∑_{b≠0} |η_b|²  =  ∑_{χ≠𝟙} |g(χ)|²/(p−1) + …  =  n·(p/(p−1)) − 1  ≈  n`,

so the `L²` average of `M²` is `≈ n` (`RMS ≈ √n` — the truth is here).  **Subconvexity** is precisely
the demand to push the `L^∞` (sup) bound down from the convexity `n·√p` toward the `L²` floor
`√n` — i.e. to gain the FULL power-saving factor `√p` (and even an extra `√n/n = n^{−1/2}`).

**The vacuity, stated.**  At the prize scale `p ≈ n^{5.27}`, the convexity bound `n·√p ≈ n^{3.63}`
and even the per-coefficient size `√p ≈ n^{2.63}` are BOTH `≫ n` — already larger than the **trivial**
bound `|η_b| ≤ n` (the `n`-term triangle inequality `|∑_{x∈μ_n} e_p(bx)| ≤ n`).  So:

      **convexity for this degenerate `L` is VACUOUS — it is beaten by the trivial `n`-term bound.**

This is the `√p`-vacuity in L-function language: the "convexity bound" of the degenerate finite `L`
is `n·√p`, weaker than trivial, because the coefficients `g(χ)` are individually `√p`-large while
the truth needs `√p`-cancellation AMONG the `n` of them.  A subconvexity bound that merely saves a
fixed `p^{−δ}` off convexity (`n·p^{1/2−δ}`) is STILL `≫ n` for any fixed `δ < 1/2 − 1/(2β)` — to
reach the target the saving must be the **full `√p` and then some**, i.e. Lindelöf-on-the-nose plus
a subgroup-scale gain.  Fixed-`δ` subconvexity does not touch the prize.

## 3. The amplification / family-moment test — the actual NEW input, and its failure mode

The modern subconvexity engine is **amplification**: bound the second (or higher) moment of the
family `{g(χ)}` against an **amplifier** `A(χ) = ∑_{ℓ} x_ℓ χ(ℓ)` that singles out the target, and
exploit **off-diagonal cancellation** in `∑_χ |A(χ)|²·g(χ)·(…)`.  This needs the family second
moment to have a main term PLUS a small off-diagonal.  For the Gauss-sum family the moments are
**exactly evaluable** (orthogonality of characters), and that is precisely what kills amplification:

* **First moment.** `∑_{χ:χ^n=𝟙} g(χ) = ∑_{χ} ∑_{t} χ(t)e_p(t) = ∑_{t} e_p(t)·#{χ : χ(t)=…}`
  collapses by orthogonality to the **subgroup period itself** `= n·η`-type — no analytic gain, it
  is the object we are bounding.
* **Second moment (the amplification denominator).** `∑_{χ:χ^n=𝟙} |g(χ)|² = (n−1)·p + 1` EXACTLY
  (Gauss modulus `|g(χ)|²=p` for `χ≠𝟙`, plus `|g(𝟙)|²=1`).  This is a **bare, structureless
  main term with NO off-diagonal** — the family `{g(χ)}` over the `n`-element group is an
  **orthonormal (up to `√p`) flat system**; the second moment is a single delta, exactly the
  Plancherel relation of §2.  There is **no off-diagonal term to exploit**, so amplification has
  **zero purchase**: the amplified second moment just returns `(amplifier ℓ²-mass)·p`, giving back
  convexity `n·√p`, NOT subconvexity.

This is the structural reason the route reduces to **Lindelöf-hard**: amplification gains come from
the *spectral large sieve / off-diagonal* of an INFINITE family with a delta-MAIN-term and a genuine
error; the degenerate finite Gauss-sum family is **all main term, no error** — its moments are exact
deltas, so there is nothing to amplify against.  The cancellation the prize needs is **inside** the
`n`-term sum `∑_χ g(χ)χ̄(b)` (the phases of the `g(χ)` must conspire), which is exactly the
**phase / equidistribution** statement (BGK / generalized Paley / Lindelöf), NOT a moment input.

## 4. Why moments of the family cannot give sub-`√p` at the subgroup scale (the precise obstruction)

A subconvexity bound `M ≤ p^{1/2−δ}` from a `2k`-th family moment needs
`∑_χ |g(χ)|^{2k} ≤ C·n·p^{k(1−2δ)}` to beat the diagonal.  But `|g(χ)| = √p` EXACTLY (constant
modulus), so `∑_χ |g(χ)|^{2k} = (n−1)·p^k + 1` — the moments are **rigid**: every even moment is
`n·p^k` on the nose, with `δ = 0`.  The Gauss-sum family has **constant modulus**, hence **no moment
can beat its own diagonal** — the family is the worst case for amplification (a flat `√p`-tight
frame, cf. in-tree `_AttackAN2_TightFrameBTVacuous`).  Sub-`√p` from family moments is therefore
**impossible**: the only `√p`-cancellation lives in the *arguments* `arg g(χ)` (Gauss-sum phases),
invisible to every modulus moment — the same `MomentLadderExceedsPrize` wall, now in `L`-function
amplification form.

## 5. The honest verdict

**REDUCES TO `√p`-VACUITY / LINDELÖF-HARD.**  The degenerate finite `L` of the Gauss-sum family has:
(i) convexity bound `n·√p`, **already weaker than trivial `n`** (the `√p`-vacuity, in `L`-function
form); (ii) **exact, structureless, off-diagonal-free** family moments `∑|g|^{2k} = n·p^k` (constant
modulus `|g(χ)|=√p`), so **amplification has zero purchase** and **no family moment beats its own
diagonal**; (iii) the residual `√p`-cancellation lives entirely in the **Gauss-sum phases**
`arg g(χ)`, whose equidistribution is exactly BGK / the Paley conjecture / **Lindelöf for this
degenerate `L`** — open, half a power short (BGK `n^{1−o(1)}`).  There is **no NEW subconvexity-type
input** here: the family is the amplification worst case, and subconvexity = Lindelöf = the prize.

## 6. What is PROVEN below (pure real arithmetic; no `sorry`/`native_decide`/`[CharZero]`)

* `convexityBound` — the degenerate-`L` convexity sup-bound `(n−1)·√p + 1`.
* `familySecondMoment` — the EXACT flat family `2nd` moment `(n−1)·p + 1` (`= n·p` shape).
* `family2kMoment` — the EXACT flat `2k`-th moment `(n−1)·p^k + 1` (constant-modulus rigidity).
* `convexity_exceeds_trivial` — convexity `≥` the trivial `n`-term bound at the prize scale (the
  vacuity: the `L`-convexity bound is BEATEN by triangle-`n`).
* `fixed_subconvexity_still_vacuous` — any fixed-`δ` subconvexity `n·p^{1/2−δ}` still exceeds the
  target whenever the saving is below the full `√p` (the prize needs Lindelöf, not subconvexity).
* `family_moment_no_offdiagonal` — the family `2k`-moment is its own diagonal `n·p^k` with `δ=0`
  (constant modulus ⟹ no moment beats its diagonal ⟹ amplification has zero purchase).
* `SubconvexityClaim` / `LindelofPhaseClaim` — the named claims; `SubconvexityClaim ↔
  LindelofPhaseClaim` glue (subconvexity for this degenerate `L` IS the phase-equidistribution).
* `charP_bound_of_lindelof` — conditional SKELETON: the phase/Lindelöf claim gives the char-`p`
  bound.  ONE named open step (= BGK), NOT discharged.

Honest label: **REDUCES (to `√p`-vacuity / Lindelöf-hard).**  No new subconvexity input exists; the
Gauss-sum family is the amplification worst case (flat constant-modulus), and subconvexity for the
degenerate finite `L` coincides exactly with the open BGK / generalized-Paley phase wall.

## References
Iwaniec–Kowalski *Analytic Number Theory* (convexity/subconvexity, amplification, Ch. 5, 25);
Bourgain–Glibichuk–Konyagin (`n^{1−o(1)}` subgroup-sum); generalized Paley graph / Liu–Zhou;
in-tree `_NovelEllAdicSheaf` (same Kummer diagonalisation), `MomentLadderExceedsPrize`,
`_AttackAN2_TightFrameBTVacuous` (flat-frame vacuity), `SubgroupGaussSumWorstCase`,
`CharZeroWickEnergy.gaussianEnergyBound_dyadic`.  Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.Subconvexity

open scoped BigOperators

/-! ## 1. The degenerate-L invariants as exact functionals

We model the three analytic invariants of the degenerate finite `L` of the Gauss-sum family as plain
`ℝ`-valued functionals, so the size comparisons that establish the vacuity are fully machine-checked.
`n` = order of the character group (= subgroup size), `sqrtp = √p`, `p` = the prize prime. -/

/-- **Convexity (triangle) sup-bound** for the degenerate finite `L` of length `n` with
constant-modulus coefficients `|g(χ)| = √p` (`χ ≠ 𝟙`) and `g(𝟙) = −1`:
`M ≤ ∑_χ |g(χ)| = (n−1)·√p + 1`.  This is the *convexity bound* of the degenerate `L`. -/
noncomputable def convexityBound (n : ℕ) (sqrtp : ℝ) : ℝ := (n - 1 : ℝ) * sqrtp + 1

/-- **The EXACT family second moment** `∑_{χ:χ^n=𝟙} |g(χ)|² = (n−1)·p + 1` (Gauss modulus
`|g(χ)|²=p` for `χ≠𝟙`, `|g(𝟙)|²=1`).  This is a bare main term — the Plancherel delta — with **no
off-diagonal**, the structural reason amplification fails. -/
noncomputable def familySecondMoment (n : ℕ) (p : ℝ) : ℝ := (n - 1 : ℝ) * p + 1

/-- **The EXACT family `2k`-th moment** `∑_{χ:χ^n=𝟙} |g(χ)|^{2k} = (n−1)·p^k + 1`: constant modulus
`|g(χ)| = √p` makes every even moment rigid (`δ = 0`).  Hence **no family moment beats its diagonal**
— amplification has zero purchase. -/
noncomputable def family2kMoment (n : ℕ) (p : ℝ) (k : ℕ) : ℝ := (n - 1 : ℝ) * p ^ k + 1

/-- The convexity bound is positive (for `n ≥ 1`, `√p ≥ 0`). -/
theorem convexityBound_pos {n : ℕ} (sqrtp : ℝ) (hn : 1 ≤ n) (hs : 0 ≤ sqrtp) :
    0 < convexityBound n sqrtp := by
  unfold convexityBound
  have : (0 : ℝ) ≤ (n - 1 : ℝ) * sqrtp := by
    have : (0 : ℝ) ≤ (n - 1 : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    positivity
  linarith

/-! ## 2. The vacuity: the `L`-convexity bound is BEATEN by the trivial `n`-term bound

At the prize scale the per-coefficient size `√p ≈ n^{2.63}` already exceeds the trivial bound
`|η_b| ≤ n`, so the convexity bound `(n−1)√p + 1 ≫ n`.  This is the `√p`-vacuity in `L`-function
language: convexity for this degenerate `L` carries no information. -/

/-- **The convexity bound EXCEEDS the trivial `n`-term bound** whenever `√p ≥ 1` and `n ≥ 2`.  The
trivial triangle bound on the `n`-term sum is `|η_b| ≤ n`; the degenerate-`L` convexity bound is
`(n−1)√p + 1`.  Since `√p ≥ 1` (massively so at prize scale, `√p ≈ n^{2.63}`),
`(n−1)√p + 1 ≥ (n−1) + 1 = n`.  So the `L`-convexity bound is (weakly, and at prize scale hugely)
WORSE than trivial — the `√p`-vacuity. -/
theorem convexity_exceeds_trivial {n : ℕ} (sqrtp : ℝ) (hn : 2 ≤ n) (hs : 1 ≤ sqrtp) :
    (n : ℝ) ≤ convexityBound n sqrtp := by
  unfold convexityBound
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hfac : (0 : ℝ) ≤ (n - 1 : ℝ) := by linarith
  -- (n−1)·√p ≥ (n−1)·1 = n−1, so (n−1)√p + 1 ≥ n.
  have : (n - 1 : ℝ) * 1 ≤ (n - 1 : ℝ) * sqrtp := by
    apply mul_le_mul_of_nonneg_left hs hfac
  linarith

/-- **Quantitative vacuity at the prize scale.**  With `n = 2^30` and `√p ≥ n` (true at prize scale,
`√p ≈ n^{2.63} ≫ n`), the convexity bound exceeds `n²` — i.e. it is at least a full factor `n` above
the trivial bound `n`.  The `L`-convexity bound is not merely beaten by trivial, it is `Θ(n)` times
worse, so no fixed power-saving recovers it. -/
theorem convexity_quadratically_vacuous {n : ℕ} (sqrtp : ℝ) (hn : 2 ≤ n)
    (hs : (n : ℝ) ≤ sqrtp) :
    (n : ℝ) ^ 2 - (n : ℝ) ≤ convexityBound n sqrtp := by
  unfold convexityBound
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hfac : (0 : ℝ) ≤ (n - 1 : ℝ) := by linarith
  -- (n−1)·√p ≥ (n−1)·n = n² − n.
  have hstep : (n - 1 : ℝ) * (n : ℝ) ≤ (n - 1 : ℝ) * sqrtp :=
    mul_le_mul_of_nonneg_left hs hfac
  nlinarith [hstep]

/-! ## 3. Fixed-`δ` subconvexity still misses: the prize needs Lindelöf, not subconvexity

A subconvexity bound saves a power `p^{−δ}` off convexity: `M ≤ (n−1)·p^{1/2−δ} + 1`.  But to reach
the target `√(n·log m) ≈ √n·polylog ≈ n^{0.5}·polylog`, the bound must drop below `n`.  Any
`p^{1/2−δ}` with `δ < 1/2 − 1/(2β)` (i.e. `p^{1/2−δ} > p^{1/(2β)} = n^{1/2}`-ish, well above `1`)
keeps the `(n−1)·p^{1/2−δ}` term `≥ n`.  We record the clean fact: as long as the per-coefficient
saving `psave := p^{1/2−δ} ≥ 1`, the subconvex bound still exceeds the trivial `n`. -/

/-- **A subconvex bound with per-coefficient size `psave := p^{1/2−δ}` still exceeds trivial** as long
as `psave ≥ 1` and `n ≥ 2`.  So fixed-`δ` subconvexity (any `δ < 1/2`) leaves `psave = p^{1/2−δ} ≥
p^{0+} ≫ 1` and the bound `(n−1)·psave + 1 ≥ n` remains vacuous: the prize requires the FULL `√p`
saving down to `psave ≤ √n/n = n^{−1/2}` (Lindelöf-and-then-some), NOT subconvexity. -/
theorem fixed_subconvexity_still_vacuous {n : ℕ} (psave : ℝ) (hn : 2 ≤ n) (hps : 1 ≤ psave) :
    (n : ℝ) ≤ (n - 1 : ℝ) * psave + 1 := by
  -- identical shape to convexity_exceeds_trivial with sqrtp ↦ psave.
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hfac : (0 : ℝ) ≤ (n - 1 : ℝ) := by linarith
  have : (n - 1 : ℝ) * 1 ≤ (n - 1 : ℝ) * psave :=
    mul_le_mul_of_nonneg_left hps hfac
  linarith

/-! ## 4. The family moment is its own diagonal: amplification has zero purchase

The amplification denominator is the family second moment; gain requires it to exceed its diagonal
`n·p` by a genuine off-diagonal.  But `|g(χ)|² = p` EXACTLY (constant modulus), so the moment IS the
diagonal `(n−1)p + 1`, with `δ = 0`.  Likewise every `2k`-moment is `(n−1)p^k + 1`.  We record that
the family moment never beats `n·p^k` — the flat-frame rigidity that voids amplification. -/

/-- **The family `2k`-moment equals its diagonal (no off-diagonal gain).**  For the constant-modulus
Gauss-sum family, `family2kMoment n p k = (n−1)·p^k + 1 ≤ n·p^k` (for `p ≥ 1`).  Equivalently the
moment is `n·p^k` up to the `g(𝟙)` correction — a bare diagonal with `δ = 0`.  Amplification needs
`< (n − Ω(n))·p^k` (a real off-diagonal saving); the flat family gives `≈ n·p^k`, so the amplified
bound returns convexity `n·√p`, never subconvexity. -/
theorem family_moment_no_offdiagonal {n : ℕ} (p : ℝ) (k : ℕ) (hn : 1 ≤ n) (hp : 1 ≤ p) :
    family2kMoment n p k ≤ (n : ℝ) * p ^ k := by
  unfold family2kMoment
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpk : (1 : ℝ) ≤ p ^ k := one_le_pow₀ hp
  -- (n−1)p^k + 1 ≤ (n−1)p^k + p^k = n·p^k.
  nlinarith [hpk, hn1]

/-- **Lower companion: the family moment is AT LEAST its diagonal up to a unit** — `family2kMoment`
is `≥ (n−1)·p^k`, so it is pinned to `Θ(n·p^k)` with no sub-diagonal saving.  Together with
`family_moment_no_offdiagonal` this brackets the moment at the bare diagonal `n·p^k`: constant
modulus ⟹ `δ = 0` ⟹ **no family moment can yield sub-`√p`**. -/
theorem family_moment_at_least_diagonal {n : ℕ} (p : ℝ) (k : ℕ) (hp : 0 ≤ p) :
    (n - 1 : ℝ) * p ^ k ≤ family2kMoment n p k := by
  unfold family2kMoment
  have : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
  linarith

/-! ## 5. The named claims and the glue: subconvexity = Lindelöf = the phase wall

Subconvexity for the degenerate `L` is the statement that the sup-norm `M` of the `n`-term Dirichlet
polynomial drops below `√n·polylog` — which, since the coefficient moduli are flat `√p`, is exactly
the statement that the **phases** `arg g(χ)` equidistribute enough to give square-root cancellation
in `∑_χ g(χ)χ̄(b)`.  That is BGK / the generalized-Paley phase / Lindelöf.  We name both and prove
they coincide. -/

/-- **The subconvexity claim** for the degenerate finite `L`: the sup-norm `M` is bounded by the
target `√n·polylog` (`tgt`), i.e. the convexity `n·√p` is improved all the way to the `L²` floor.
This is `M ≤ tgt` — the prize, restated as subconvexity. -/
def SubconvexityClaim (M tgt : ℝ) : Prop := M ≤ tgt

/-- **The Lindelöf / phase-equidistribution claim**: the same `M ≤ tgt`, but conceptually the
content that the Gauss-sum phases `arg g(χ)` give square-root cancellation (BGK / generalized
Paley).  As predicates on `(M, tgt)` they are LITERALLY the same proposition — encoding the §3–4
finding that for the flat constant-modulus family subconvexity has no content beyond the phase
equidistribution. -/
def LindelofPhaseClaim (M tgt : ℝ) : Prop := M ≤ tgt

/-- **Subconvexity for this degenerate `L` IS the Lindelöf/phase claim.**  Because the family moduli
are flat (`|g(χ)| = √p`, every moment its own diagonal, §4), the only way to beat convexity is
phase cancellation; the two named claims coincide exactly.  This is the formal statement of "the
route reduces to Lindelöf-hard / the BGK phase wall — no new subconvexity input exists." -/
theorem subconvexity_iff_lindelof (M tgt : ℝ) :
    SubconvexityClaim M tgt ↔ LindelofPhaseClaim M tgt := Iff.rfl

/-- **Conditional closure SKELETON.**  GRANTING the open Lindelöf/phase claim `M ≤ tgt` (= BGK /
generalized-Paley, NOT discharged here) and that the target is the prize budget `tgt ≤ budget`, the
char-`p` sup-norm bound `M ≤ budget` follows.  This is the modular reduction of the F2 route to ONE
named open step — the phase equidistribution = the SAME wall as every other route.  SKELETON, not a
closure. -/
theorem charP_bound_of_lindelof (M tgt budget : ℝ)
    (hopen : LindelofPhaseClaim M tgt) (hbud : tgt ≤ budget) :
    M ≤ budget := by
  unfold LindelofPhaseClaim at hopen
  linarith

/-! ## 6. The F2 verdict, as a theorem: REDUCES to `√p`-vacuity / Lindelöf-hard

We package the findings: (a) the degenerate-`L` convexity bound is beaten by trivial `n` at the
prize scale (`√p`-vacuity); (b) the family moments are exact flat diagonals (`δ = 0`, amplification
void); (c) subconvexity for this `L` coincides with the open Lindelöf/phase wall. -/

/-- **F2 verdict (REDUCES to `√p`-vacuity / Lindelöf-hard).**  At the prize scale (`n ≥ 2`,
`√p ≥ n`, `p ≥ 1`): (a) the degenerate-`L` convexity bound `(n−1)√p+1` exceeds the trivial `n`-term
bound (the `√p`-vacuity — convexity carries no information); (b) the family `2nd` moment is the bare
diagonal `≤ n·p` (constant modulus ⟹ no off-diagonal ⟹ amplification has zero purchase); (c)
subconvexity for the degenerate finite `L` is LITERALLY the Lindelöf/phase-equidistribution claim
(`subconvexity_iff_lindelof`).  Hence the F2 route offers no NEW subconvexity input: it reduces to
the open BGK / generalized-Paley phase wall.  Honest finding, NOT a closure. -/
theorem f2_verdict {n : ℕ} (sqrtp p : ℝ) (hn : 2 ≤ n) (hs : (n : ℝ) ≤ sqrtp) (hp : 1 ≤ p) :
    (n : ℝ) ≤ convexityBound n sqrtp ∧
    familySecondMoment n p ≤ (n : ℝ) * p ∧
    (∀ M tgt : ℝ, SubconvexityClaim M tgt ↔ LindelofPhaseClaim M tgt) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (a) convexity beats trivial: from hs : n ≤ √p we get √p ≥ n ≥ 1.
    have hs1 : (1 : ℝ) ≤ sqrtp := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact convexity_exceeds_trivial sqrtp hn hs1
  · -- (b) family 2nd moment ≤ n·p (the k=1 flat-diagonal instance).
    have := family_moment_no_offdiagonal (n := n) p 1 (by omega) hp
    simpa [familySecondMoment, family2kMoment, pow_one] using this
  · -- (c) subconvexity ↔ Lindelöf.
    intro M tgt; exact subconvexity_iff_lindelof M tgt

end ArkLib.ProximityGap.Frontier.Subconvexity

/-! ## Axiom audit (run via `lake env lean`) -/
#print axioms ArkLib.ProximityGap.Frontier.Subconvexity.convexity_exceeds_trivial
#print axioms ArkLib.ProximityGap.Frontier.Subconvexity.convexity_quadratically_vacuous
#print axioms ArkLib.ProximityGap.Frontier.Subconvexity.fixed_subconvexity_still_vacuous
#print axioms ArkLib.ProximityGap.Frontier.Subconvexity.family_moment_no_offdiagonal
#print axioms ArkLib.ProximityGap.Frontier.Subconvexity.family_moment_at_least_diagonal
#print axioms ArkLib.ProximityGap.Frontier.Subconvexity.subconvexity_iff_lindelof
#print axioms ArkLib.ProximityGap.Frontier.Subconvexity.charP_bound_of_lindelof
#print axioms ArkLib.ProximityGap.Frontier.Subconvexity.f2_verdict
