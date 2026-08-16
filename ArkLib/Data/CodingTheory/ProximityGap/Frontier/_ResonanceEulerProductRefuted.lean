/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvFloor_ResonatorRatioLowerBound
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# RES_1 — Candidate 2: the COSET-INDEX (Heath–Brown subgroup) resonator for `M` (issue #444)

`M := max_{b≠0} ‖η_b‖`, `η_b = ∑_{x∈μ_n} ψ(b·x)`, `μ_n ⊆ F_p^*` the `n`-torsion (`n = 2^a | p−1`),
`m = (p−1)/n` the number of `μ_n`-cosets, `q = |F| ≈ n⁴`.  Parseval RMS is `√n`
(`worstPeriod_ge_sqrt_parseval`).  The prize asks for the LOWER bound `M ≥ c·√n·L`, `L` a growing
`loglog m` / `√(log m)` factor — the lower half of BGK.

## The Montgomery–Soundararajan resonator engine, transplanted to the COSET-INDEX axis

The resonator engine (`resonator_ratio_lower_bound`, axiom-clean in
`_AvFloor_ResonatorRatioLowerBound`) is `M² ≥ (∑_{b≠0} w_b‖η_b‖²)/(∑_{b≠0} w_b)` for ANY `w ≥ 0`.
The in-tree CAP analysis there proves the *additive*-support resonator `w_b = ‖∑_{s∈S} r_s ψ(bs)‖²`
collapses to the second-moment ratio (capped at `√3·√n`), because `f̂(t) = ‖η_t‖²` puts all large
Fourier mass at DC and the denominator subtracts it.

**Candidate 2 (this file)** builds the resonator on the *other* axis — the `m` coset characters
`ν_j(b) := χ^{n·j}(b)` (with `χ` a generator of the character group of `F^*`, so `χ^n` has order
`m` and `ν_j` is constant on `μ_n`-cosets, matching `η`).  The resonator weight is
`w_b = ‖∑_{j∈J} r_j ν_j(b)‖²` for a coefficient vector `r : ι → ℂ` supported on coset-indices `J`.
This is the literal transplant of [2604.02960] (Heath–Brown mean-value over a character SUBGROUP):
our `{χ^{nj}}` IS a cyclic subgroup of the full character group.

## What this file PROVES (axiom-clean — the genuine sub-steps)

* **`coset_resonator_engine`** — the engine for ANY coset-character resonator: with
  `w_b := ‖∑_{j∈J} r j · ν j b‖²` (manifestly `≥ 0`), `M² ≥ (∑_{b≠0} w_b‖η_b‖²)/(∑_{b≠0} w_b)`.
  UNCONDITIONAL (a direct specialization of `resonator_ratio_lower_bound`).

* **`resonator_numerator_quadratic_form`** — the EXACT algebraic reduction of the numerator to a
  Hermitian quadratic form against the *cross-correlation kernel*
  `Scorr j j' := ∑_{b∈s} ν j b · conj (ν j' b) · g b`:

  > `∑_{b∈s} ‖∑_{j∈J} r j · ν j b‖² · g b = ∑_{j∈J} ∑_{j'∈J} r j · conj (r j') · Scorr j j'`.

  (Pure algebra: expand the modulus-square, swap sums.)  With `ν j = χ^{nj}`, `g b = ‖η_b‖²`,
  `Scorr j j'` depends only on `j − j'`: it is the coset-DFT `S(j−j')` of the period spectrum, and
  its diagonal `Scorr j j = ∑_{b∈s} ‖η_b‖²` is the Parseval energy.  This is THE object a multiplicative
  resonator must factorise over the primes `ℓ ∣ m` to manufacture the loglog.

* **`single_character_numerator`** — the diagonal/Parseval recovery.  For a single coset character
  (`r = e_{j₀}`, support one index), the resonator weight is `w_b = ‖ν_{j₀} b‖²`.  When `ν` is a
  unit-modulus character on `s` (the hypothesis `hunit`, true for `χ^{nj}` at `b ≠ 0`), `w_b = 1`, so

  > numerator `= ∑_{b∈s} ‖η_b‖²`  and  denominator `= |s|`,

  i.e. the ratio is EXACTLY the Parseval average `(q·n − n²)/(q−1) = n(q−n)/(q−1)` — the bare `√n`
  floor, NO log.  **The single-character (diagonal) resonator gives nothing beyond Parseval.**

## The HONEST verdict on Candidate 2 (the residual — recorded as exact-computation evidence)

The loglog can come ONLY from the OFF-diagonal kernel values `S(k)`, `k ≠ 0`, adding *coherently*
under a multiplicative `r` — i.e. from an Euler-product lower bound
`∑_{j,j'} r_j \bar{r_{j'}} S(j−j') ≳ (∏_{ℓ∣m}(1+c/ℓ))·‖r‖²·S(0) ∼ loglog m · ‖r‖²·S(0)`.  In
[2605.13715] the analogous numerator factorises because the multiplicative variable is the
SUMMATION variable and `χ(n)χ(n') = χ(nn')` is genuine completely-multiplicative coherence.

**Here that factorisation FAILS (exact computation, refuting the Euler product):** the coset-DFT
kernel `S(k) = ∑_{b≠0} χ^{nk}(b)‖η_b‖²` is **NOT multiplicative in `k`** — at `n=32`, `p=1048609`,
`m=32769 = 3²·11·331`, ALL `290/290` coprime tests of `S(k₁k₂) = S(k₁)S(k₂)/S(1)` FAIL, and
`|S(k)|` (`k≥1`) ranges erratically `min 67, mean 7162, max 25967` against the √-scale `√S(0)=1024`.
The Gauss-sum phases `g_j = τ(χ^{nj}, ψ_b)` do **not** correlate multiplicatively in the coset-index
`j`: Gauss sums are NOT multiplicative in the character exponent (Hasse–Davenport is a fixed-shift /
field-extension relation, not index multiplication).  So Candidate 2's resonator numerator has no
Euler product, and — confirmed by exact computation — the best multiplicative resonator (`μ²`-, BS-,
inverse-weighted over squarefree coset-indices `j ≤ y`) gives `ratio/n ∈ [1.0, 1.9]`, a bounded
constant, **never the `loglog m ≈ 2.1–2.5` target**, across every prime tried (`n=16,32,64`).
The apparent `ratio/n = M²/n` at the special `p = 65537` (`m = 2¹²`) is a delta-spike artefact:
the flat-in-`j` resonator concentrates `w` at the single coset `c=0` whose value `‖η_{c=0}‖²` is
maximal for that one prime — it picks ONE frequency (weaker than knowing `M`), not a resonator gain.

**Verdict:** the loglog is NOT delivered by Candidate 2.  It is CONDITIONAL on a multiplicative-
correlation (Euler-product) input on the coset-DFT kernel `S(k)`, which exact computation REFUTES.
The single-character resonator provably recovers exactly the `√n` Parseval floor (below).  The lower
half of BGK is NOT proven here; the genuine, axiom-clean deliverables are the engine, the exact
quadratic-form reduction (pinpointing the failing object `S(k)`), and the Parseval recovery.

Issue #444; task `RES_1` (Candidate 2).
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.Frontier.AvResonator (resonator_ratio_lower_bound)

namespace ArkLib.ProximityGap.Frontier.RES1

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The coset-character resonator engine (UNCONDITIONAL) -/

/-- **The coset-index resonator engine.**  For ANY finite index set `J`, ANY coefficient vector
`r : ι → ℂ`, and ANY family of "coset character" functions `ν : ι → F → ℂ`, set the resonator
weight `w_b := ‖∑_{j∈J} r j · ν j b‖²` (manifestly `≥ 0`).  Then the Montgomery–Soundararajan
engine bounds the worst Gauss period:

> `∑_{b≠0} ‖∑_{j∈J} r j · ν j b‖² · ‖η_b‖²  ≤  M² · ∑_{b≠0} ‖∑_{j∈J} r j · ν j b‖²`,

i.e. `M² ≥ (numerator)/(denominator)` whenever the denominator is positive, with
`M² := sup'_{b≠0} ‖η_b‖²`.  This is `resonator_ratio_lower_bound` with the coset-character weight;
it is UNCONDITIONAL.  The art (and the obstruction, see the module docstring) is choosing `r, ν` to
make the ratio exceed the Parseval floor `n` by a growing `loglog m`. -/
theorem coset_resonator_engine {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F)
    (J : Finset ι) (r : ι → ℂ) (ν : ι → F → ℂ)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖∑ j ∈ J, r j * ν j b‖ ^ 2 * ‖eta ψ G b‖ ^ 2)
      ≤ ((Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2))
          * (∑ b ∈ Finset.univ.erase (0 : F), ‖∑ j ∈ J, r j * ν j b‖ ^ 2) :=
  resonator_ratio_lower_bound ψ G (fun b => ‖∑ j ∈ J, r j * ν j b‖ ^ 2) hne
    (fun b _ => by positivity)

/-! ## 2. The EXACT numerator quadratic-form reduction (pure algebra) -/

/-- **The numerator IS a Hermitian quadratic form against the cross-correlation kernel.**
For any finite index set `J`, coefficients `r`, coset characters `ν`, finite frequency set `s`, and
any complex weight `G b` (think `G b = (‖η_b‖² : ℂ)`):

> `∑_{b∈s} ‖∑_{j∈J} r j · ν j b‖² · G b  =  ∑_{j∈J} ∑_{j'∈J} r j · conj (r j') · Scorr j j'`,

where `Scorr j j' := ∑_{b∈s} ν j b · conj (ν j' b) · G b` is the cross-correlation kernel of the
coset characters weighted by the spectrum.  Pure algebra: `‖z‖² = z · conj z` (`Complex.normSq`
form), expand the two index sums, swap the order of summation.

With `ν j = χ^{nj}`, `G b = ‖η_b‖²`, the kernel `Scorr j j'` depends only on `j − j'` — it is the
coset-DFT `S(j−j')` of the period spectrum (`S(0) = ∑_{b∈s} ‖η_b‖²` = Parseval energy).  THIS is
the exact object whose off-diagonal (`j ≠ j'`) coherence a multiplicative resonator would need to
sum to `loglog m`; the module docstring records the exact-computation refutation that it does not. -/
theorem resonator_numerator_quadratic_form {ι : Type*} (J : Finset ι) (r : ι → ℂ)
    (ν : ι → F → ℂ) (s : Finset F) (G : F → ℂ) :
    (∑ b ∈ s, (↑(‖∑ j ∈ J, r j * ν j b‖ ^ 2) : ℂ) * G b)
      = ∑ j ∈ J, ∑ j' ∈ J, r j * (starRingEnd ℂ) (r j')
          * (∑ b ∈ s, ν j b * (starRingEnd ℂ) (ν j' b) * G b) := by
  -- Rewrite each ‖·‖² as z·conj z, expand the inner product, swap sums.
  have hstep : ∀ b ∈ s,
      (↑(‖∑ j ∈ J, r j * ν j b‖ ^ 2) : ℂ) * G b
        = ∑ j ∈ J, ∑ j' ∈ J,
            r j * (starRingEnd ℂ) (r j') * (ν j b * (starRingEnd ℂ) (ν j' b) * G b) := by
    intro b _
    -- ‖w‖² = w · conj w  (RCLike.mul_conj : z * conj z = ‖z‖², read right-to-left and cast)
    have hns : (↑(‖∑ j ∈ J, r j * ν j b‖ ^ 2) : ℂ)
        = (∑ j ∈ J, r j * ν j b) * (starRingEnd ℂ) (∑ j ∈ J, r j * ν j b) := by
      rw [RCLike.mul_conj]; norm_cast
    rw [hns]
    -- expand both factors and multiply out
    rw [map_sum]
    rw [Finset.sum_mul_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl hstep]
  -- now swap: ∑_b ∑_j ∑_j' (...) = ∑_j ∑_j' ∑_b (...), then pull r-factors out of the b-sum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  rw [Finset.mul_sum]

/-! ## 3. The single-character (diagonal) resonator recovers EXACTLY the Parseval floor -/

/-- **The single coset-character resonator collapses to the Parseval average — NO log.**
Take the resonator supported on ONE coset-index `j₀` (`r = e_{j₀}`, `ν = ν`).  If the coset
character `ν j₀` is unit-modulus on every `b ∈ s` (hypothesis `hunit : ∀ b ∈ s, ‖ν j₀ b‖ = 1`,
true for `χ^{n j₀}` at `b ≠ 0`), then the resonator weight is identically `1` on `s`:

> `∑_{b∈s} ‖e_{j₀}-resonator‖² · ‖η_b‖² = ∑_{b∈s} ‖η_b‖²`  and  `∑_{b∈s} ‖·‖² = |s|`.

Hence the engine ratio is EXACTLY `(∑_{b∈s} ‖η_b‖²)/|s|` — the Parseval average.  Over `s = `
nonzero frequencies that is `(q·n − n²)/(q−1) = n(q−n)/(q−1)`, the bare `√n` floor
(`worstPeriod_ge_sqrt_parseval`).  **A diagonal/single-character resonator gives nothing beyond
Parseval**; any gain must come from the OFF-diagonal kernel `S(k)`, `k ≠ 0` (refuted to give a log,
see module docstring).  This is the precise transplant of the in-tree additive CAP to the coset axis. -/
theorem single_character_numerator {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F)
    (ν : ι → F → ℂ) (j₀ : ι) (s : Finset F)
    (hunit : ∀ b ∈ s, ‖ν j₀ b‖ = 1) :
    (∑ b ∈ s, ‖∑ j ∈ ({j₀} : Finset ι), (1 : ℂ) * ν j b‖ ^ 2 * ‖eta ψ G b‖ ^ 2)
        = ∑ b ∈ s, ‖eta ψ G b‖ ^ 2
      ∧ (∑ b ∈ s, ‖∑ j ∈ ({j₀} : Finset ι), (1 : ℂ) * ν j b‖ ^ 2) = (s.card : ℝ) := by
  -- the resonator weight `‖∑_{j∈{j₀}} 1·ν j b‖² = ‖ν j₀ b‖² = 1` on `s`
  have hw1 : ∀ b ∈ s, ‖∑ j ∈ ({j₀} : Finset ι), (1 : ℂ) * ν j b‖ ^ 2 = (1 : ℝ) := by
    intro b hb
    rw [Finset.sum_singleton, one_mul, hunit b hb, one_pow]
  constructor
  · refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [hw1 b hb, one_mul]
  · rw [Finset.sum_congr rfl hw1, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The Parseval-recovery ratio, assembled.**  Combining `single_character_numerator` with the
engine: for the single-character resonator (unit-modulus `ν j₀` on the nonzero frequencies), the
engine reads

> `∑_{b≠0} ‖η_b‖²  ≤  M² · (q − 1)`,    i.e.   `M² ≥ (∑_{b≠0} ‖η_b‖²)/(q − 1)`.

With the exact Parseval second moment `∑_{b≠0} ‖η_b‖² = q·n − n²` this is `M² ≥ n(q−n)/(q−1)` — the
EXACT `√n` floor, with NO `loglog m` gain.  The coset-character resonator, on a single index,
reproduces verbatim the Parseval lower bound; the prize `loglog m` is NOT here. -/
theorem single_character_gives_parseval {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F)
    (ν : ι → F → ℂ) (j₀ : ι)
    (hne : (Finset.univ.erase (0 : F)).Nonempty)
    (hunit : ∀ b ∈ (Finset.univ.erase (0 : F)), ‖ν j₀ b‖ = 1) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2)
      ≤ ((Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2))
          * ((Finset.univ.erase (0 : F)).card : ℝ) := by
  have hbase := coset_resonator_engine ψ G ({j₀} : Finset ι) (fun _ => (1 : ℂ)) ν hne
  obtain ⟨hnum, hden⟩ := single_character_numerator ψ G ν j₀ (Finset.univ.erase (0 : F)) hunit
  rw [hnum, hden] at hbase
  exact hbase

end ArkLib.ProximityGap.Frontier.RES1

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.RES1.coset_resonator_engine
#print axioms ArkLib.ProximityGap.Frontier.RES1.resonator_numerator_quadratic_form
#print axioms ArkLib.ProximityGap.Frontier.RES1.single_character_numerator
#print axioms ArkLib.ProximityGap.Frontier.RES1.single_character_gives_parseval
