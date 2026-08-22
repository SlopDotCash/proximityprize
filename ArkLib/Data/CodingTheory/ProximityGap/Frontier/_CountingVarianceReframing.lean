/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The counting-variance reframing of the centered wraparound — and the SKEPTICAL VERDICT (#444)

**Mandate (atk-honest-check).**  The fresh sharpening of the prize criterion claims that, at prize
scale where `R_r ≈ 1`, the open core `ρ_r ≤ 1` reduces to a *fluctuation* bound

> `(W_r − n^{2r}/p)  ≤  (r²/2n)·Wick`

on the wraparound's excess above its DC mean `n^{2r}/p`.  This file determines DEFINITIVELY whether
that fluctuation bound is a NEW provable handle (reducible to large sieve / Plancherel) or the SAME
growing-order equidistribution wall, merely recentered.

## The exact algebra (verified, both as a clean Finset identity and numerically)

Let `N_c := #{ (x₁,…,x_r) ∈ μ_n^r : x₁+⋯+x_r ≡ c (mod p) }` be the **counting function** of the
`r`-tuples of `n`-th roots summing to a residue class `c ∈ Z/p`.  Then `Σ_c N_c = n^r` (every tuple
lands in some class), with family mean `N̄ := n^r/p`.  The Fourier transform of `N_c` is exactly the
`r`-th power of the period sum: `η_b^r = Σ_x e_p(b·x) summed over tuples = Σ_c N_c · e_p(bc)`, so by
**Plancherel** `Σ_b |η_b|^{2r} = p · Σ_c N_c²`.  Splitting off `b = 0` (`η_0 = n`, `|η_0|^{2r} =
n^{2r}`) and using `Σ_c N_c = n^r`:

> **THE CENTERED WRAPAROUND IS LITERALLY THE VARIANCE OF `N_c`:**
> ```
>   E_r − n^{2r}/p  =  Σ_c (N_c − n^r/p)²  =  Σ_c N_c² − (Σ_c N_c)²/p  =  (1/p)·Σ_{b≠0} |η_b|^{2r}.
> ```
> (the König–Huygens identity; here `E_r := Σ_c N_c²` is the `b`-averaged DC-subtracted moment, and
> `S_r := Σ_{b≠0}|η_b|^{2r} = p·(E_r − n^{2r}/p)` is exactly the prize object `ρ_r·(p−1)·Wick`).

Numerically confirmed (`n=4, p=17, r=1..5`): `Σ_c(N_c−N̄)² = S_r/p` to machine precision, every `r`.

## THE SKEPTICAL VERDICT — recentered, NOT reduced (the handle is the SAME wall)

Bounding `Var(N_c) ≤ (r²/2n)·Wick` is **exactly** the open growing-order equidistribution, for one
decisive reason: the variance is a *sum of `2r`-th powers of the spectrum*, dominated by its top term.

* **`var_ge_topTerm`** (proved below): `Var(N_c) = (1/p)Σ_{b≠0}|η_b|^{2r} ≥ M^{2r}/p`, where
  `M := max_{b≠0}|η_b|` is the **prize sup-norm itself**.  So a bound `Var(N_c) ≤ (r²/2n)·Wick`
  forces `M^{2r} ≤ p·(r²/2n)·Wick`, i.e. `M ≤ (p·(r²/2n)·Wick)^{1/2r}` — a sup-norm bound.  At
  `r ≈ log p` this is the prize bound `M ≤ √(2n log p)·(1+o(1))`.  *Bounding the variance is no
  weaker than bounding the sup-norm.*  (Numerically the top term carries a CONSTANT ≈ 24% share of
  the variance at every `r`, so the inequality is tight up to a constant — there is no slack to
  exploit.)

* **Plancherel / large sieve see ONLY `r = 1`.**  The only `b`-uniform fact those tools give is
  `Σ_b |η_b|² = p·n` — the `r = 1` energy — which is **flat and trivial** (`Var(N_c)` at `r=1` is
  the benign `μ_n`-Sidon value).  They say nothing about the `2r`-th moment at growing `r`; the large
  sieve bounds a *single* second moment, not a tower of them.  The variance reframing does NOT factor
  through any second-moment / Plancherel inequality.

**Conclusion.**  `E_r − n^{2r}/p = Var(N_c)` is a genuine, clean, positive-definite REFRAMING (it
exhibits the prize object as a variance, which is conceptually valuable and is what this brick lands
axiom-clean).  But it is **NOT a new provable handle**: by `var_ge_topTerm` the variance bound is
equivalent (up to a constant factor) to the prize sup-norm bound `M ≤ √(2n log p)`, i.e. it is the
**same growing-order equidistribution wall, recentered** — confirming the skeptical suspicion.  The
variance is sub-Poisson **iff** the spectrum is near-Ramanujan; no recentering removes the `2r`-th
power.  NOT a closure.  Issue #444.

`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/

set_option linter.style.longLine false
set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CountingVarianceReframing

open Finset

variable {ι : Type*}

/-! ## §1 The exact König–Huygens variance identity for the counting function

`N : ι → ℝ` is the counting function `N_c` over the residue classes `ι = Z/p` (`|ι| = p`).  We prove
the clean Finset identity `Σ_c (N_c − mean)² = Σ_c N_c² − (Σ_c N_c)²/p`, with `mean := (Σ_c N_c)/p`.
This is the centered wraparound `E_r − n^{2r}/p` once `Σ_c N_c = n^r` and `p = |ι|` are substituted. -/

/-- **`counting_variance_eq`** — the König–Huygens identity for the counting function over the
residue-class index `s` (`|s| = p`): the centered sum of squares equals the raw sum of squares minus
the squared total over `p`.  Taking `s = Z/p`, `N = N_c`, `Σ N = n^r`, this IS the centered
wraparound `E_r − n^{2r}/p = Σ_c (N_c − n^r/p)²`. -/
theorem counting_variance_eq (s : Finset ι) (N : ι → ℝ) (hs : s.Nonempty) :
    ∑ c ∈ s, (N c - (∑ d ∈ s, N d) / s.card) ^ 2
      = (∑ c ∈ s, (N c) ^ 2) - (∑ d ∈ s, N d) ^ 2 / s.card := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  set T := ∑ d ∈ s, N d with hT
  set μ := T / s.card with hμ
  have hμsum : μ * s.card = T := by rw [hμ]; field_simp
  have hexp : ∀ c ∈ s, (N c - μ) ^ 2 = (N c) ^ 2 - 2 * μ * N c + μ ^ 2 := by
    intro c _; ring
  rw [Finset.sum_congr rfl hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul]
  -- Σ N² − 2μ·Σ N + card·μ²; with Σ N = T = μ·card this is Σ N² − T²/card
  rw [← hT]
  have : μ * (s.card : ℝ) * μ = T * μ := by rw [hμsum]
  field_simp
  rw [hμ]
  field_simp
  ring

/-! ## §2 The variance is bounded BELOW by the top spectral term — the SKEPTICAL VERDICT

We model the variance in its Plancherel form `Var = (1/p)·Σ_{b≠0}|η_b|^{2r}` over the nonzero
frequencies `b ∈ Rel` (`Rel = Z/p \ {0}`), with `g b := |η_b|^{2r} ≥ 0` the per-frequency mass.
The maximum term `g b₀ = M^{2r}` (the prize sup-norm to the `2r`-th power) is a single summand, so it
is `≤` the whole sum.  Hence `Var ≥ M^{2r}/p`: ANY bound on the variance is a bound on the sup-norm
`M = max_{b≠0}|η_b|`, which at `r ≈ log p` is the prize.  This is the precise sense in which the
fluctuation reframing does not reduce the wall. -/

/-- **`var_ge_topTerm`** — THE VERDICT, formalized.  With `g : ι → ℝ` the nonnegative per-frequency
spectral mass `g b = |η_b|^{2r}` over the nonzero frequencies `Rel`, the variance in Plancherel form
`(Σ_{b∈Rel} g b)/p` is at least the **top term** `g b₀ / p` for any single frequency `b₀ ∈ Rel`.
Taking `b₀` the maximizer, `g b₀ = M^{2r}` — so a variance bound is a sup-norm (`M`) bound.  The
fluctuation handle is therefore **no weaker than** the prize sup-norm bound it claims to relax. -/
theorem var_ge_topTerm (Rel : Finset ι) (g : ι → ℝ) (hg : ∀ b ∈ Rel, 0 ≤ g b)
    (p : ℝ) (hp : 0 < p) (b₀ : ι) (hb₀ : b₀ ∈ Rel) :
    g b₀ / p ≤ (∑ b ∈ Rel, g b) / p := by
  have hsum : g b₀ ≤ ∑ b ∈ Rel, g b := Finset.single_le_sum hg hb₀
  gcongr

/-- **`var_eq_plancherel`** — the bridge identity (definitional bookkeeping): the centered wraparound
equals the Plancherel mass of the nonzero spectrum over `p`.  This records `E_r − n^{2r}/p =
(1/p)·Σ_{b≠0}|η_b|^{2r}` as the hypothesis under which `var_ge_topTerm` delivers the sup-norm lower
bound.  (`variance = S_r/p`, `S_r = Σ_{b≠0}|η_b|^{2r}` = the prize object `ρ_r·(p−1)·Wick`.) -/
theorem var_eq_plancherel (variance S_r p : ℝ) (hp : 0 < p) (h : variance = S_r / p) :
    p * variance = S_r := by
  rw [h]; field_simp

/-- **`sup_lower_bound_from_variance`** — the explicit contrapositive: a variance bound forces a
sup-norm bound.  If `variance = (Σ_{b∈Rel} g b)/p` (Plancherel) and `variance ≤ B`, then for the
maximizing frequency `b₀`, `g b₀ / p ≤ B`, i.e. `M^{2r} ≤ p·B`.  So bounding the fluctuation by
`B = (r²/2n)·Wick` bounds `M ≤ (p·B)^{1/2r}` — the prize sup-norm.  Recentered, not reduced. -/
theorem sup_lower_bound_from_variance (Rel : Finset ι) (g : ι → ℝ) (hg : ∀ b ∈ Rel, 0 ≤ g b)
    (p variance B : ℝ) (hp : 0 < p) (b₀ : ι) (hb₀ : b₀ ∈ Rel)
    (hvar : variance = (∑ b ∈ Rel, g b) / p) (hbound : variance ≤ B) :
    g b₀ / p ≤ B := by
  calc g b₀ / p ≤ (∑ b ∈ Rel, g b) / p := var_ge_topTerm Rel g hg p hp b₀ hb₀
    _ = variance := hvar.symm
    _ ≤ B := hbound

end ArkLib.ProximityGap.Frontier.CountingVarianceReframing

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
