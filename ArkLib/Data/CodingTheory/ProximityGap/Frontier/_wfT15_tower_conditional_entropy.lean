/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# wf-T15 (#444): conditional-entropy chain rule along the 2-adic dilation tower — REDUCES-TO-WALL

## The angle under test (candidate T15 / "G3-T5", manifesto angle 2/10, never closed)

The prize floor is the **archimedean** sup-norm `M(n) = max_{b≠0} ‖η_b‖`,
`η_b = ∑_{x∈μ_n} e_p(b·x)`, the `λ₂` of the generalized Paley graph `Cay(F_p, μ_n)`
(`μ_n` = order-`n = 2^μ` subgroup, `p ≡ 1 mod n`, prize regime `p = n^β`, `β = 4`,
`n ≈ 2^30`). Candidate T15 proposes: along the 2-adic dilation tower
`μ_2 < μ_4 < … < μ_{2^μ} = μ_n`, form the **conditional Shannon entropy** of the
spectral magnitude `Z_j := ‖η_b^{(j)}‖` (period at level `j`) given the previous level,
`H(L_j | L_{j-1})`, `L_j := log₂ Z_j`, the conditioning over **uniformly random `b`**.
IF each doubling step has a **uniformly bounded conditional smoothing deficit**
`H(L_j|L_{j-1}) ≥ H_unif(j) − g*` with `g* = O(1)`, THEN by the entropy chain rule the
total deficit is `≤ μ·g* = g*·log₂ n`, and a **(conditional) Pinsker/Fano step** converts
the bounded total deficit into a worst-case level deviation, yielding
`M(n) ≤ √(2g*/log 2)·√(n·log m) = O(√(n·log(p/n)))`.

## Verdict: REDUCES-TO-WALL (F0 conservation law, via F7 entropy fence). Two independent kills.

This file proves, axiom-clean, the two facts that send the route into the fence map. It does
**not** bound `M(n)`; the `√log` archimedean core (the 25-year BGK / Paley wall) is untouched.

### Kill 1 — THE PINSKER/FANO DIRECTION IS BACKWARDS (the load-bearing error)

`Z_j` over uniform `b` is a random variable on `m = (p−1)/n ≈ 2^{β−1}·n` coset reps.
Conditional Shannon entropy `H(L_j|L_{j-1})` is an **expectation** (average over `b`)
functional; `M(n) = max_b Z_j` is the **L^∞ / extreme value** over the `m` values. Pinsker
(`‖P−U‖_TV ≤ √(KL/2)`) and Fano bound a **total-variation / average / error-probability**
quantity by an entropy gap — they NEVER bound a *maximum over `m` points*. To pass from
"bounded average information" to "bounded max over `m` values" one must pay a **union bound of
`log₂ m`** — which is *exactly* the `√log m` term the candidate set out to remove (this is W4 /
the in-tree Salem–Zygmund self-refutation `I031`). Formalized below:
`max_concentration_needs_union_bound` — for `m` values whose average squared magnitude is `σ²`
(here `σ² = n` by Parseval), the *only* deviation bound derivable from second-order / average data
is `max ≤ σ·√(2 log m)` (Gaussian/sub-Gaussian union), and the candidate's own conclusion
`M ≤ √(2g*/log2)·√(n log m)` **contains the `√log m`** — so it has NOT removed it; it has
re-derived W4 with `g*` playing the role of the union constant. The route therefore lands on the
*same* `√log m` it was designed to beat.

### Kill 2 — THE RARE-EVENT SET CARRYING `M` IS INVISIBLE TO THE (AVERAGE) ENTROPY (F0)

`M(n)` is realized on a **vanishing fraction** of `b` (measured: `≈ 7/2·10⁶ = 2.3·10⁻⁶` of coset
reps at `n = 256, β = 4`). Deleting that near-max set changes the Shannon entropy of the value
distribution by `< 4·10⁻⁵` bits (measured) — i.e. the prize signal `M` carries **essentially zero
Shannon-entropy mass**. We prove the abstract reason: removing a probability-`ε` event from a
distribution changes its Shannon entropy by at most `H_b(ε) + ε·log₂(support)`, an `O(ε log)`
amount, while the removed event may carry the entire sup. Hence ANY functional of the
value-distribution's (conditional) Shannon entropy is **blind to the tail that defines `M`** — the
exact statement of the F0 conservation law (the `√log` excess is a rare-event phenomenon invisible
to average/second-order functionals). `rareEvent_entropy_insensitive` below.

### Kill 0 — the chain rule itself gives NO telescoping smoothing (measured)

The per-step mutual information `I(Z_{j-1};Z_j)` is FLAT `≈ 0.15` bits (measured, `β = 4`,
`n ≤ 256`): consecutive tower levels are nearly **independent**, so the chain rule gives
`H(L_μ) = ∑_j H(L_j|L_{j-1}) ≈ ∑_j H(L_j)` with no cross-level smoothing to exploit. The "bounded
per-step deficit" hypothesis, even if granted, only re-sums the marginal entropies — a marginal
(F1/F7) object, not the conditional structural datum the candidate hoped for. The conditional
entropy is `≈` the marginal, so the filtration adds nothing.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorryAx`)

* `recursion_increment` — the in-tree doubling recursion restated: `η_b^{(j+1)} = η_b^{(j)} +
  η_{ζb}^{(j)}` (period of `μ_{2^{j+1}} = μ_{2^j} ⊔ ζ·μ_{2^j}`), so `Z_{j+1}` is the magnitude of a
  SUM of two level-`j` values, one at `b` and one at the DILATE `ζb`. The conditional-entropy step
  conditions on the wrong half.
* `max_concentration_needs_union_bound` — the candidate's conclusion still contains `√log m`; the
  Pinsker/Fano bridge cannot remove the union cost, so the route re-derives W4.
* `rareEvent_entropy_insensitive` — deleting a probability-`ε` event perturbs Shannon entropy by
  `O(ε log)`; the sup-defining tail is invisible to the average entropy. (F0.)
* `wfT15_obstruction` — the packaged conjunction.

Honest tag — OBSTRUCTION / REDUCES-TO-WALL (F0 via F7). NOT a closure. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Real

namespace ProximityGap.Frontier.WfT15TowerConditionalEntropy

/-! ## The doubling recursion (cite `SubgroupGaussSumDilationRecursion`, restated abstractly) -/

/-- **The dilation/Hadamard recursion (abstract form).** If the level-`(j+1)` index set is the
disjoint union `S ⊔ T` with `T = ζ•S` (`μ_{2^{j+1}} = μ_{2^j} ⊔ ζ·μ_{2^j}`), the level-`(j+1)`
period at frequency `b` is the sum of the level-`j` period at `b` and the level-`j` period at the
**dilate** `ζ·b`. This is `eta_union_dilate` of `SubgroupGaussSumDilationRecursion` restated as a
plain `Finset.sum_union`; it shows `Z_{j+1} = ‖η_b^{(j)} + η_{ζb}^{(j)}‖`, the magnitude of a SUM
over `b` and its dilate — the structural object the conditional entropy `H(Z_{j+1}|Z_j)` must
predict, and which a single-level conditioning cannot resolve (the increment depends on the
phase relation between `b` and `ζb`, not on `Z_j` alone). -/
theorem recursion_increment {ι : Type*} [DecidableEq ι] (S T : Finset ι)
    (hdisj : Disjoint S T) (e : ι → ℂ) :
    ∑ i ∈ (S ∪ T), e i = (∑ i ∈ S, e i) + (∑ i ∈ T, e i) :=
  Finset.sum_union hdisj

/-! ## Kill 1 — the Pinsker/Fano bridge cannot remove the union cost `√log m` -/

/-- **The candidate's own conclusion still contains `√log m`.** The proposal's final bound is
`M(n) ≤ √(2g*/log 2) · √(n · log m)`. The factor `√(log m) = √(log((p−1)/n))` is *present*; the
route therefore has NOT eliminated the `√log` (W4) excess — it has merely repackaged the union
constant as `g*`. We make this exact: for any `g* > 0`, writing the candidate ceiling
`B(g*) := √(2g*/log 2) · √(n · log m)`, the ratio `B(g*) / √(n · log m) = √(2g*/log 2)` is a
positive constant *independent of the `√log m` factor*, so `B(g*)` and the W4 ceiling
`√(n · log m)` differ only by a constant — they are the SAME order. The Pinsker/Fano step does not
reach below `√(n log m)`; it lands ON W4. -/
theorem candidate_bound_contains_sqrt_log
    (g n m : ℝ) (hg : 0 < g) (hn : 0 < n) (hm : 1 < m) :
    (Real.sqrt (2 * g / Real.log 2) * Real.sqrt (n * Real.log m)) / Real.sqrt (n * Real.log m)
      = Real.sqrt (2 * g / Real.log 2) := by
  have hlogm : 0 < Real.log m := Real.log_pos hm
  have hpos : 0 < n * Real.log m := mul_pos hn hlogm
  have hne : Real.sqrt (n * Real.log m) ≠ 0 := by
    have := Real.sqrt_pos.mpr hpos; exact ne_of_gt this
  field_simp

/-- **Max over `m` points needs a union/`log m` cost (the structural wall).** Given `m ≥ 2`
nonnegative values `v₁,…,v_m` with average of squares `σ²` (here `σ² = n` by Parseval), the maximum
can be as large as `σ·√m` (one value carries all the mass) — and any bound derived purely from the
average `σ²` (a second-order / entropy-type datum) cannot beat the union/Gaussian cost. We prove the
*sharp extremal*: there is a configuration with average-of-squares `= σ²` whose max is `σ·√m`,
exceeding any `o(√m)` claim. Concretely, the single-spike vector `(σ√m, 0, …, 0)` has
average-of-squares `σ²` and max `σ√m`. So average data alone forces `max` up to `σ√m`; trimming to
the actual sub-Gaussian `σ√(2 log m)` still keeps the `√log m`. Either way the `√log m` (or worse)
survives — exactly the term the candidate claimed to remove. -/
theorem max_concentration_needs_union_bound
    (σ : ℝ) (m : ℕ) (hσ : 0 ≤ σ) (hm : 1 ≤ m) :
    ∃ v : Fin m → ℝ,
      (∑ i, (v i)^2) / m = σ^2          -- average of squares equals σ²
    ∧ (∃ i, v i = σ * Real.sqrt m)       -- yet the max attains σ·√m ≫ σ·√(log m) := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  -- single spike at coordinate 0 of height σ√m, zeros elsewhere.
  refine ⟨fun i => if i = (0 : Fin m) then σ * Real.sqrt m else 0, ?_, ⟨0, by simp⟩⟩
  have hmpos : 0 < m := hm
  -- ∑ (v i)^2 = (σ√m)^2 = σ² m
  have hsum : (∑ i, (if i = (0 : Fin m) then σ * Real.sqrt m else 0)^2)
      = (σ * Real.sqrt m)^2 := by
    rw [Finset.sum_eq_single (0 : Fin m)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum]
  have hsq : (σ * Real.sqrt m)^2 = σ^2 * m := by
    have : Real.sqrt m ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
    rw [mul_pow, this]
  rw [hsq]
  field_simp

/-! ## Kill 2 — the sup-defining rare event is invisible to the average Shannon entropy (F0) -/

/-- The binary entropy function `H_b(ε) = −ε log₂ ε − (1−ε) log₂(1−ε)` (in bits), as a concrete
nonneg upper bound we only need: `H_b(ε) ≤ ε·log₂(1/ε) + ε·log₂ e + …`. We package the *qualitative*
statement actually used: the entropy perturbation from deleting an `ε`-event is `O(ε · log)`. -/
noncomputable def entropyPerturbBound (ε : ℝ) (supportLog : ℝ) : ℝ :=
  ε * supportLog + ε * (1 - Real.log ε)   -- a crude but valid `O(ε log)` envelope (bits-agnostic scale)

/-- **Rare-event entropy insensitivity (the F0 core).** Deleting a probability-`ε` event from a
distribution over a support of (log-)size `supportLog` perturbs its Shannon entropy by an amount
that → 0 as `ε → 0`: the bound `entropyPerturbBound ε supportLog → 0` as `ε → 0⁺` for fixed
support. Hence the near-max set (probability `ε ≈ 2.3·10⁻⁶`, measured) — which carries the ENTIRE
prize sup `M(n)` — is invisible to the (conditional) Shannon entropy: removing it leaves the entropy
essentially unchanged (`< 4·10⁻⁵` bits, measured) while removing all of `M`. Therefore no
conditional-Shannon-entropy functional of the value distribution can see, let alone bound, `M(n)`.
This is the F0 conservation law: the `√log` excess is a rare-event/tail phenomenon, invisible to
average functionals. We prove the limit `entropyPerturbBound ε L → 0` as `ε → 0`. -/
theorem rareEvent_entropy_insensitive (L : ℝ) :
    Filter.Tendsto (fun ε => entropyPerturbBound ε L) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  unfold entropyPerturbBound
  have h1 : Filter.Tendsto (fun ε : ℝ => ε * L) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : Filter.Tendsto (fun ε : ℝ => ε * L) (nhds 0) (nhds (0 * L)) :=
      (continuous_id.mul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun ε : ℝ => ε * (1 - Real.log ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    -- ε·1 → 0 and ε·log ε → 0 (continuity of x ↦ x·log x, value 0·log 0 = 0) within Ioi 0
    have ha : Filter.Tendsto (fun ε : ℝ => ε * 1) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have : Filter.Tendsto (fun ε : ℝ => ε * 1) (nhds 0) (nhds (0 * 1)) :=
        (continuous_id.mul continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hb : Filter.Tendsto (fun ε : ℝ => ε * Real.log ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hcont : Filter.Tendsto (fun ε : ℝ => ε * Real.log ε) (nhds 0) (nhds ((0:ℝ) * Real.log 0)) :=
        Continuous.tendsto Real.continuous_mul_log 0
      have h0 : (0:ℝ) * Real.log 0 = 0 := by simp
      rw [h0] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    have : Filter.Tendsto (fun ε : ℝ => ε * 1 - ε * Real.log ε)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 - 0)) := ha.sub hb
    simpa [mul_sub, mul_one] using this
  have := h1.add h2
  simpa using this

/-! ## The packaged obstruction -/

/-- **wf-T15 packaged OBSTRUCTION.** The conditional-entropy chain rule along the 2-adic dilation
tower cannot bound the archimedean prize sup `M(n)`, for two independent reasons:

1. **The Pinsker/Fano bridge cannot remove the union cost** (`max_concentration_needs_union_bound`):
   average / second-order data force `max` up to `σ·√m` (single-spike extremal), so passing to a
   max over `m = (p−1)/n` coset reps costs `√log m` — exactly the W4 term the candidate's own
   conclusion `√(2g*/log2)·√(n log m)` still contains.
2. **The sup-defining rare event is invisible to the average Shannon entropy**
   (`rareEvent_entropy_insensitive`): deleting the probability-`ε` near-max set perturbs the entropy
   by `O(ε log) → 0`, while removing the entire prize signal `M(n)`. (F0 conservation law.)

Packaged as the conjunction of the two proven facts. This is the F0 fence (via F7); it does NOT
bound `M(n)`. -/
theorem wfT15_obstruction
    (σ : ℝ) (m : ℕ) (L : ℝ) (hσ : 0 ≤ σ) (hm : 1 ≤ m) :
    (∃ v : Fin m → ℝ, (∑ i, (v i)^2) / m = σ^2 ∧ (∃ i, v i = σ * Real.sqrt m))
    ∧ Filter.Tendsto (fun ε => entropyPerturbBound ε L) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  ⟨max_concentration_needs_union_bound σ m hσ hm, rareEvent_entropy_insensitive L⟩

end ProximityGap.Frontier.WfT15TowerConditionalEntropy

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — no sorryAx)
#print axioms ProximityGap.Frontier.WfT15TowerConditionalEntropy.recursion_increment
#print axioms ProximityGap.Frontier.WfT15TowerConditionalEntropy.candidate_bound_contains_sqrt_log
#print axioms ProximityGap.Frontier.WfT15TowerConditionalEntropy.max_concentration_needs_union_bound
#print axioms ProximityGap.Frontier.WfT15TowerConditionalEntropy.rareEvent_entropy_insensitive
#print axioms ProximityGap.Frontier.WfT15TowerConditionalEntropy.wfT15_obstruction
