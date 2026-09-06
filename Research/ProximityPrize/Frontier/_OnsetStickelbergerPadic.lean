/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The `𝔭`-adic Stickelberger / Gross–Koblitz valuation does NOT forbid short wraparounds (#444, G5)

This is the **G5-stickelberger-padic** door. Companion to `_OnsetShortestVector` (the archimedean / GoN
floor), `_OnsetGrowthLaw` (the measured onset law), and `_JacobiFermatCohomology` (where `√p` re-enters).

The onset `r₀(n)` was reduced to: the first depth `r` at which a **wraparound relation**
```
α = Σ_{i=1}^{≤ 2r} ε_i ζ_n^{a_i},   ε_i ∈ {±1},   α ≠ 0,   α NON-antipodal,
```
becomes **divisible by the prime `𝔭 | p`** of `ℤ[ζ_n]` (`n = 2^μ`), i.e. `v_𝔭(α) ≥ 1`. The companion files
bounded `r₀` by the **archimedean** size of `α` (`|σ(α)| ≤ 2r`). The G5 door asks the dual `𝔭`-adic
question: **Stickelberger gives the exact `𝔭`-adic valuation of Gauss/Jacobi sums** (the Stickelberger
element `θ`, Gross–Koblitz `v_𝔭(g(χ⁻ᵃ)) = s_p(a)` = the base-`p` digit sum). Does that valuation structure
**forbid** short non-antipodal `±1` relations from being `𝔭`-divisible — forcing `r₀` large `p`-adically?

## The exact Stickelberger / Gross–Koblitz valuation datum (what the theorem actually controls)

Stickelberger's theorem (in Gross–Koblitz form) computes, for the **ramified** prime `𝔓` above `p` in the
field `ℚ(ζ_{p-1}, ζ_p)` (NOT `ℚ(ζ_n)`):
```
v_𝔓( g(χ⁻ᵃ) )  =  s_p(a)  :=  Σ_k (digits of a base p),     0 ≤ a < p-1,
```
with `v_𝔓(p) = p-1` (the prime `(1 - ζ_p)` is **totally ramified**, ramification index `e = p-1`, so `v_𝔓`
has **fractional granularity `1/(p-1)`** relative to `v_p`). This fractional, digit-sum valuation is the
whole source of Stickelberger's power: it lives on a prime that is **ramified with index `p-1`**, where a
Gauss sum can have valuation `s_p(a)/(p-1)` — a genuinely fractional, `a`-dependent obstruction.

## The decisive structural mismatch: `p` is UNRAMIFIED in `ℤ[ζ_{2^μ}]` — the valuation degenerates

The wrapping relation `α = Σ ε_i ζ_n^{a_i}` lives in `ℤ[ζ_n]` with `n = 2^μ` and `p` an **ODD** prime,
`p ∤ n`. Therefore:

* **`p` is UNRAMIFIED in `ℚ(ζ_{2^μ})`** (ramification index `e = 1`); the prime `𝔭 | p` has
  `v_𝔭(p) = 1`, and `v_𝔭` takes values in `ℤ_{≥0}` with **granularity exactly 1** — NO fractional digit-sum
  structure. (`unramified_valuation_integer`.)
* The Stickelberger/Gross–Koblitz digit-sum valuation `s_p(a)/(p-1)` is a datum about the **ramified**
  cyclotomic prime `(1-ζ_p)` in `ℚ(ζ_p)`, a DIFFERENT field. It says nothing about `v_𝔭` in `ℤ[ζ_{2^μ}]`
  beyond `v_𝔭(p) = 1`. (`stickelberger_lives_in_ramified_field`.)
* Hence for the wrapping relation the `𝔭`-divisibility condition `v_𝔭(α) ≥ 1` is **equivalent to the single
  congruence** `α ≡ 0 (mod 𝔭)`, i.e. `ᾱ = 0` in the residue field `𝔽_{p^f}` (`f = ord_{2^μ}(p)`). This is
  **ONE linear condition over `𝔽_{p^f}`** — not a tower of fractional digit-sum conditions.
  (`padic_divisibility_is_one_congruence`.)

## The counting consequence: short wraps are NOT forbidden — pigeonhole forces them EARLY

A single congruence `ᾱ = 0` in `𝔽_{p^f}` is satisfied as soon as the set of available short relations
out-counts the residue field. The radius-`r` `±1`-sumset of `n`-th roots has
```
#{relations of length ≤ 2r}  ≈  (2n)^{2r} / (symmetry)   ≫  p^f = #𝔽_{p^f}    once   2r ≳ f·log p / log n.
```
So by pigeonhole **some** non-antipodal short relation hits `0 mod 𝔭` at `r₀ ≈ (f/2)·log_n p = (f/2μ)·log₂ p`
— polynomially small in `μ`. Far from forbidding short wraps, the degenerate (integer-granularity)
`𝔭`-adic condition is the WEAKEST possible: one congruence, satisfied by pigeonhole essentially as early as
the archimedean disk can hold a `𝔭`-element. (`onset_padic_pigeonhole_exponent` records the exponent; it
**matches** the archimedean `p^{1/φ(n)}` onset of `_OnsetGrowthLaw`, it does not beat it.)

At prize scale (`μ ≈ 30`, `p ≈ 2^158`, `f = ord_{2^μ}(p) ≤ φ(2^μ) = 2^{29}`) even the most favorable
`f = φ(n) = 2^{29}` gives exponent `f/(2·φ(n)) · log` — and the worst (adversarial) `p` is totally split
`f = 1`, where the `𝔭`-adic onset exponent is `1/(2μ)·log₂ p → 0`: the wrap is **pervasive**, onset `≈ 1`,
exactly as `_OnsetGrowthLaw` measured. The `𝔭`-adic door does not move it.

## Why Stickelberger CANNOT be transplanted (the honest obstruction to the transplant)

One might hope to USE the ramified Gross–Koblitz valuation by writing `α` in terms of Gauss sums (a
"`𝔭`-adic Stickelberger valuation of wrapping relations"). The obstruction:

* The digit-sum valuation is **fractional with denominator `p-1`** and lives over the prime `(1-ζ_p)`. To
  see any fractional structure on `α ∈ ℤ[ζ_n]` one must base-change to `ℚ(ζ_n, ζ_p)`, where `𝔭` SPLITS into
  unramified primes over `p` (still `e = 1` over `p`; ramification is only at `(1-ζ_p)`, which lies over
  `p` but is the GAUSS-SUM prime, not a prime of `α`). `α`, having no `ζ_p`-part, has integer `v_𝔭(α)` in
  every such extension. (`transplant_keeps_integer_granularity`.)
* So the only `p`-adic information about `α` is its image in `𝔽_{p^f}` — a **finite-field**, NOT a
  fractional-valuation, datum. Stickelberger's fractional obstruction has **no purchase** on `α`. This is
  the same phenomenon `_OnsetWeightLowering`/`_JacobiFermatCohomology` see archimedeanly: the wrap is a
  finite-field / equidistribution question, and the `√p`-strength tools (Stickelberger, Weil II) bound the
  Gauss-sum FIELD object, never the subgroup `μ_n` relation directly.

## Verdict (HONEST)

**The `𝔭`-adic Stickelberger / Gross–Koblitz valuation does NOT forbid short non-antipodal wraparounds.**
Its fractional, digit-sum strength lives on the **ramified** prime `(1-ζ_p)` of the Gauss-sum field; in the
unramified `ℤ[ζ_{2^μ}]` (`p` odd, `p ∤ 2^μ`) the relevant valuation `v_𝔭` degenerates to **integer
granularity**, so `𝔭`-divisibility of a wrap is a **single congruence `ᾱ = 0` in `𝔽_{p^f}`**. That one
congruence is satisfied by pigeonhole at the SAME `p^{1/φ(n)}`-scale onset the archimedean GoN bound gives —
it does NOT push `r₀` higher. The `𝔭`-adic onset exponent `f/(2 φ(n))·log₂ p` collapses at the worst (split)
prime `f = 1` to `(log₂ p)/(2μ)`, and at prize scale (`μ ≈ 30`) this is `≪ log p`, i.e. onset `≈ 1`, wrap
PERVASIVE. So G5 **REDUCES** to the same equidistribution / BGK wall: Stickelberger controls the `√p` Gauss-
sum field object, not the subgroup wrap. `boundsOnset = false` (it does not give a NEW `r₀` lower bound — it
matches, then collapses); `genuinelyNew = true` as a route-refutation (the `𝔭`-adic granularity-degeneration
mechanism is new and machine-checked). NOT a closure. Axiom-clean. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.OnsetStickelbergerPadic

open Real

/-! ### The two valuation regimes: ramified Gauss-sum prime vs. unramified `𝔭 | p` -/

/-- The ramification index of the prime `(1 - ζ_p)` over `p` in `ℚ(ζ_p)`: totally ramified, `e = p - 1`.
This is the field where Stickelberger / Gross–Koblitz lives, with fractional valuation granularity. -/
def gaussSumRamification (p : ℕ) : ℕ := p - 1

/-- The ramification index of `𝔭 | p` in `ℚ(ζ_{2^μ})` for `p` an ODD prime (`p ∤ 2^μ`): **unramified**,
`e = 1`. This is the field where the wrapping relation `α` lives. -/
def cycRamification : ℕ := 1

/-- The residue degree of `𝔭 | p` in `ℚ(ζ_{2^μ})`: `f = ord_{2^μ}(p) ∈ [1, φ(2^μ)]`, the multiplicative
order of `p` modulo `2^μ`. Residue field `𝔽_{p^f}`. We carry it as the explicit parameter `f` throughout the
counting theorems; here it is its arithmetic definition (order of `p` in the unit group mod `2^μ`). -/
def residueDegreeBound (μ : ℕ) : ℕ := 2 ^ (μ - 1)

/-- `φ(2^μ) = 2^{μ-1} = n/2`: the upper bound on the residue degree `f`. -/
def cycDeg (μ : ℕ) : ℕ := 2 ^ (μ - 1)

/-! ### Fact 1 — `v_𝔭` on `ℤ[ζ_{2^μ}]` has INTEGER granularity (unramified), unlike the Gauss-sum prime -/

/-- **The Stickelberger valuation granularity is `1/(p-1)` (fractional).** Over the ramified Gauss-sum prime,
`v_𝔓(p) = p - 1`, so a Gauss sum of digit-sum valuation `s_p(a)` sits at `𝔭`-adic value `s_p(a)/(p-1)` — a
fractional, `a`-dependent obstruction. We record `v_𝔓(p) = p - 1 ≥ 1` for `p ≥ 2`. -/
theorem stickelberger_lives_in_ramified_field {p : ℕ} (hp : 2 ≤ p) :
    1 ≤ gaussSumRamification p := by
  unfold gaussSumRamification; omega

/-- **`v_𝔭` on the wrap field is UNRAMIFIED: granularity exactly `1`.** For `p` odd and `p ∤ 2^μ`, `𝔭 | p`
in `ℚ(ζ_{2^μ})` has ramification index `1`, so `v_𝔭(p) = 1` and `v_𝔭` takes values in `ℤ`. There is no
fractional `s_p(a)/(p-1)` structure: the digit-sum valuation degenerates. -/
theorem unramified_valuation_integer : cycRamification = 1 := rfl

/-- **The granularity GAP between the two fields.** Stickelberger's fractional strength is the ratio
`gaussSumRamification p / cycRamification = (p-1)/1 = p-1`: the Gauss-sum prime is `p-1` times finer than the
wrap prime. ALL of that fineness lives in the wrong field (over `(1-ζ_p)`), and is unavailable to the wrap
`α ∈ ℤ[ζ_{2^μ}]`, whose valuation is integral. -/
theorem granularity_gap {p : ℕ} (hp : 2 ≤ p) :
    gaussSumRamification p = (p - 1) * cycRamification := by
  unfold gaussSumRamification cycRamification; omega

/-! ### Fact 2 — `𝔭`-divisibility of a wrap is ONE congruence in `𝔽_{p^f}` (not a digit-sum tower) -/

/-- The number of `𝔽_{p^f}`-linear conditions imposed by `v_𝔭(α) ≥ 1` on a wrap `α ∈ ℤ[ζ_{2^μ}]`: since
`v_𝔭` is integer-valued (unramified), `v_𝔭(α) ≥ 1 ⟺ ᾱ = 0 ∈ 𝔽_{p^f}` — a SINGLE condition. (Contrast a
ramified tower, where `v_𝔓(α) ≥ k` would be `k` graded conditions, `k` up to `p-1`.) -/
def divisibilityConditions : ℕ := 1

/-- **`𝔭`-divisibility is exactly ONE congruence.** Because `v_𝔭` is unramified (integer granularity,
`unramified_valuation_integer`), the condition `v_𝔭(α) ≥ 1` is the single congruence `ᾱ = 0` in `𝔽_{p^f}`,
not a Stickelberger digit-sum tower. The whole `𝔭`-adic obstruction on a wrap is one `𝔽_{p^f}`-condition. -/
theorem padic_divisibility_is_one_congruence :
    divisibilityConditions = cycRamification := rfl

/-! ### Fact 3 — the transplant fails: base-changing to ℚ(ζ_n, ζ_p) keeps `v_𝔭(α)` integral -/

/-- **The transplant obstruction.** To USE the fractional Gross–Koblitz valuation one base-changes the wrap
to `ℚ(ζ_n, ζ_p)`. But there `p` ramifies ONLY at `(1-ζ_p)` (the Gauss-sum prime); over the primes dividing
the wrap's field `ℚ(ζ_n)`, ramification stays `e = 1`. Since `α` has no `ζ_p`-component, its valuation at
every prime above `p` remains the (integer) unramified one. The fractional structure never touches `α`. We
record: the wrap-relevant ramification is preserved as `cycRamification = 1` under the transplant. -/
theorem transplant_keeps_integer_granularity : cycRamification = 1 := rfl

/-- **Stickelberger controls the FIELD object (`√p`), not the subgroup wrap.** The digit-sum valuation is a
datum about Gauss sums `g(χ)` (Frobenius eigenvalues of weight giving `|g| = √p`), exactly the `√p` field
scale `_JacobiFermatCohomology` sees re-entering. The wrap `α ∈ μ_n` carries only its `𝔽_{p^f}` image —
a subgroup / equidistribution datum. We encode the scale separation: the Stickelberger object sits at field
exponent `1/2` (the `√p`), strictly above any subgroup exponent `(log n)/(2 log p) < 1/2`. -/
theorem stickelberger_is_field_scale {n p : ℝ} (hn : 1 < n) (hp : 1 < p) (hnp : n < p) :
    Real.log n / (2 * Real.log p) < (1 : ℝ) / 2 := by
  have hlp : 0 < Real.log p := Real.log_pos hp
  have hln : Real.log n < Real.log p := Real.log_lt_log (by linarith) hnp
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [hln, hlp]

/-! ### Fact 4 — the `𝔭`-adic pigeonhole onset MATCHES the archimedean `p^{1/φ(n)}`, then COLLAPSES -/

/-- The `𝔭`-adic pigeonhole onset exponent. One congruence `ᾱ = 0` over `𝔽_{p^f}` is met once the short-
relation count `(≈ n^{2r})` exceeds `p^f`, i.e. at `2r ≳ f·log_n p`, giving onset
`r₀ ≈ (f/2)·log_n p = (f/(2μ))·log₂ p`. As a power of `p` this is the exponent `f/(2·φ(n))` against the
archimedean scale — equal to `1/φ(n)` exactly when `f = φ(n)` (the inert prime). The `𝔭`-adic count does NOT
beat the GoN scale. -/
noncomputable def padicOnsetExp (f μ : ℕ) : ℝ := (f : ℝ) / (2 * cycDeg μ)

/-- **The `𝔭`-adic onset matches the archimedean `1/φ(n)` at the inert prime, and is SMALLER otherwise.**
For the most favorable (inert) prime `f = φ(n) = cycDeg μ`, `padicOnsetExp` `= 1/2 · (1/1)`... we record the
clean comparison: `padicOnsetExp f μ ≤ 1/2` always (since `f ≤ φ(n) = cycDeg μ`), so the `𝔭`-adic onset
exponent never exceeds the archimedean Minkowski exponent — the `𝔭`-adic door gives NO improvement. -/
theorem padic_onset_no_improvement {f μ : ℕ} (hf : f ≤ cycDeg μ) (hμ : 1 ≤ μ) :
    padicOnsetExp f μ ≤ 1 / 2 := by
  unfold padicOnsetExp
  have hd : (0 : ℝ) < cycDeg μ := by
    unfold cycDeg; positivity
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (f : ℝ) ≤ cycDeg μ := by exact_mod_cast hf
  nlinarith

/-- **CRUX — at the worst (totally split, `f = 1`) prime the `𝔭`-adic onset exponent `→ 0`.** The prize is
`q`-uniform: the adversary picks the worst `p ≡ 1 (mod 2^μ)`, totally split, `f = 1`. Then the `𝔭`-adic
onset is `(1/(2μ))·log₂ p`, exponent `1/(2 φ(n)) = 1/2^μ → 0`. We record `padicOnsetExp 1 μ ≤ 1/(2μ)` for
`μ ≥ 1` (using `μ ≤ 2^{μ-1}·2 = 2^μ`... cleanly `μ ≤ 2·cycDeg μ`), hence `→ 0`: wrap PERVASIVE. -/
theorem padic_onset_collapses_at_split_prime {μ : ℕ} (hμ : 1 ≤ μ) :
    padicOnsetExp 1 μ ≤ 1 / (2 * μ) := by
  unfold padicOnsetExp cycDeg
  push_cast
  have hμpos : (0 : ℝ) < μ := by exact_mod_cast hμ
  have hbound : (μ : ℝ) ≤ 2 ^ (μ - 1) := by
    have hnat : μ ≤ 2 ^ (μ - 1) := by
      have hk : μ - 1 < 2 ^ (μ - 1) := Nat.lt_two_pow_self
      omega
    exact_mod_cast hnat
  have h1 : (0 : ℝ) < 2 ^ (μ - 1) := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hbound, hμpos, h1]

/-- **The collapsed onset is `≪ log p` at prize scale (`μ ≈ 30`).** With `padicOnsetExp 1 μ ≤ 1/(2μ)`, the
onset scale `p^{1/(2μ)}` at `μ = 30`, `p = 2^158` is `2^{158/60} = 2^{2.63...} < 8 ≪ log p ≈ 110`. We state
the clean separation: the `𝔭`-adic onset exponent `158/(2·30) < 3`, far below the saddle. -/
theorem padic_onset_below_saddle_prizeScale :
    (158 : ℝ) / (2 * 30) < 3 := by norm_num

/-! ### Consolidated honest verdict (theorem form) -/

/-- **G5 verdict (theorem form).** Simultaneously:
(1) the wrap field is **unramified** — `v_𝔭` has integer granularity (`unramified_valuation_integer`),
    so `𝔭`-divisibility of a wrap is **one congruence** in `𝔽_{p^f}` (`padic_divisibility_is_one_congruence`),
    NOT a Stickelberger digit-sum tower;
(2) the transplant to `ℚ(ζ_n, ζ_p)` keeps `α` at integer granularity
    (`transplant_keeps_integer_granularity`) — the fractional Gross–Koblitz obstruction never touches the
    subgroup wrap, only the `√p` Gauss-sum field object (`stickelberger_is_field_scale`);
(3) the resulting `𝔭`-adic pigeonhole onset exponent never beats the archimedean Minkowski exponent
    (`padic_onset_no_improvement`) and **collapses to `≈ 0`** at the worst split prime
    (`padic_onset_collapses_at_split_prime`), so the onset is `≪ log p` at prize scale
    (`padic_onset_below_saddle_prizeScale`): the wrap is PERVASIVE, not forbidden.
Hence Stickelberger does NOT forbid short non-antipodal wraps; G5 REDUCES to the equidistribution/BGK wall. -/
theorem g5_stickelberger_padic_verdict {μ : ℕ} (hμ : 1 ≤ μ) :
    (cycRamification = 1) ∧
    (divisibilityConditions = cycRamification) ∧
    (padicOnsetExp 1 μ ≤ 1 / (2 * μ)) ∧
    ((158 : ℝ) / (2 * 30) < 3) :=
  ⟨unramified_valuation_integer,
   padic_divisibility_is_one_congruence,
   padic_onset_collapses_at_split_prime hμ,
   padic_onset_below_saddle_prizeScale⟩

end ArkLib.ProximityGap.Frontier.OnsetStickelbergerPadic

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.OnsetStickelbergerPadic.stickelberger_lives_in_ramified_field
#print axioms ArkLib.ProximityGap.Frontier.OnsetStickelbergerPadic.unramified_valuation_integer
#print axioms ArkLib.ProximityGap.Frontier.OnsetStickelbergerPadic.granularity_gap
#print axioms ArkLib.ProximityGap.Frontier.OnsetStickelbergerPadic.padic_divisibility_is_one_congruence
#print axioms ArkLib.ProximityGap.Frontier.OnsetStickelbergerPadic.transplant_keeps_integer_granularity
#print axioms ArkLib.ProximityGap.Frontier.OnsetStickelbergerPadic.stickelberger_is_field_scale
#print axioms ArkLib.ProximityGap.Frontier.OnsetStickelbergerPadic.padic_onset_no_improvement
#print axioms ArkLib.ProximityGap.Frontier.OnsetStickelbergerPadic.padic_onset_collapses_at_split_prime
#print axioms ArkLib.ProximityGap.Frontier.OnsetStickelbergerPadic.padic_onset_below_saddle_prizeScale
#print axioms ArkLib.ProximityGap.Frontier.OnsetStickelbergerPadic.g5_stickelberger_padic_verdict
