/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-!
# A8 no-go: the container / relative-Szemerédi (transference) method cannot bound the char-`p`
vanishing-2t-subset count of `μ_n` past Johnson (#407)

ANGLE 8 (manifesto): the vanishing-2t-subset count is a count within a structured ambient (the
cyclotomic relations).  The **hypergraph container method** (Balogh–Morris–Samotij, Saxton–Thomason)
and the **relative-Szemerédi / transference principle** (Green–Tao, Conlon–Fox–Zhao) bound counts of
linear-forms patterns in **positive-relative-density subsets of pseudorandom majorants** by reducing
to a **dense model** of the same density.  NEW LEMMA attempted: the char-`p` vanishing-2t-subset count
`V_p(μ_n,t)` is bounded by its dense-model value, giving `M(μ_n) ≤ C√(n log)`.

VERDICT (narrowed by the 2026-10-28 audit, R-325): the one **directly chosen** majorant
`ν = (q/n)·1_{μ_n}` fails the linear-forms condition in the sparse regime `q = n^β`, `β > 2`;
this does **not** exclude every majorant, every dense model, or every hypergraph-container
argument (their hypotheses and carriers are not formalized here).  Probes over proper subgroups
`μ_n` (`p` prime, `n = 2^μ`, `n ∣ p−1`, `p = n^4`, never `n = p−1`;
`scripts/probes/probe_a8_container_transference.py`, `probe_a8_structured_vs_excess.py`,
`probe_a8_linearforms_precondition.py`, `probe_a8_escape_dense_model.py`) are finite evidence.
The Lean content is scalar arithmetic only.

## Obstruction A — the linear-forms condition fails for the chosen majorant `ν = (q/n)·1_{μ_n}`

Transference requires the normalized majorant `ν = (q/n)·1_{μ_n}` (`E[ν]=1`) to satisfy the
**linear-forms condition**: the normalized 4-point correlation must be `1+o(1)`.  With the
expectation over `(a,b,c) ∈ 𝔽_q³` and `E₂(μ_n) = #{(x,y,z,w) ∈ μ_n⁴ : x+y = z+w}`, the exact value is
`LF := E_{a,b,c}[ ν(a)ν(b)ν(c)ν(a+b−c) ] = (q/n)⁴ · E₂(μ_n) / q³ = q·E₂(μ_n)/n⁴`.
(Correction: earlier text used `(q/n)³·E₂/n = q³·E₂/n⁴`, which is too large by a factor `q²`.)
With the near-Sidon size `E₂ ≥ 2n²` this gives `LF ≥ 2q/n² = 2·n^{β−2}`, which diverges for
`β > 2` (`linearForms_value_ge_normalized`).  So this specific `ν` is not a pseudorandom majorant
in the sparse regime.  The earlier growth claim `n^{3β−2}` and the probe numbers quoted with it
(computed from the wrong normalization) are withdrawn.

## Obstruction B — the constant-density prediction undershoots the Wick-type count

For an alternative majorant `ν'` of support size `N` with `μ_n` at relative density `α = n/N`,
the **constant-density** prediction for the 2t-term vanishing pattern is
`α^{2t}·N^{2t}/q = n^{2t}/q`, independent of `N` (`denseModel_count_invariant`).  This is only
the prediction for the constant model `α`: a dense model of density `α` supplied by
transference need **not** be the constant function `α`, and its pattern count is not determined
by `α` alone (e.g. under the trivial majorant `ν' = 1` the bounded function `1_{μ_n}` itself is an
available dense function, with its genuine correlations).  So the scalar cancellation does not
prove that every transference model has the random count.

The comparison quantity must also be stated on the right carrier.  The Wick-type mass
`(2t−1)‼·n^t` is a leading term for ORDERED `2t`-tuple energy, not for distinct vanishing
`2t`-SUBSETS: in characteristic 0 at dyadic order `n` the distinct vanishing subsets that are unions
of antipodal pairs number `C(n/2, t)`, while ordered counts carry the extra `(2t)!`-type factor.
Full characteristic-`p` counts additionally need the known wraparound qualification (R103/R113);
the measured ratio `V_p/V_0 = 1.000` at `n ≤ 32`, `β = 4` is finite evidence only.  Granting
those carriers, the constant-density prediction `n^{2t}/q` lies below the ordered Wick-type mass by
the factor `(2t−1)‼·n^{β−t}` (`denseModel_undershoots_wick` is this exponent arithmetic), so that
particular prediction cannot serve as the needed UPPER bound.

## Net

The directly chosen subgroup majorant fails the linear-forms condition (Obstruction A, with the
corrected growth `n^{β−2}`), and the constant-density prediction is the wrong direction against the
ordered Wick-type mass (Obstruction B).  Neither statement excludes other majorants, non-constant
dense models, or container arguments with additional inputs; no method-wide verdict is claimed.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.  Issue #407.
-/

namespace ProximityGap.Frontier.A8ContainerTransferenceNoGo

/-! ## Obstruction A: the linear-forms condition is violated by a growing factor -/

/-- **Scalar inequality for the (mis-normalized) expression `(q/n)³·E₂/n`.**  From
`E₂ ≥ 2n²` this proves `(q/n)³·E₂/n ≥ 2·q³/n²`.  This is arithmetic only: `(q/n)³·E₂/n` is NOT
the normalized linear-forms correlation of `ν = (q/n)·1_{μ_n}`, which is `(q/n)⁴·E₂/q³ = q·E₂/n⁴`
(smaller by `q²`); see `linearForms_value_ge_normalized` for the correct bound. -/
theorem linearForms_value_ge
    (q n E₂ : ℝ) (hn : 0 < n) (hq : 0 < q) (hE : 2 * n ^ 2 ≤ E₂) :
    2 * q ^ 3 / n ^ 2 ≤ (q / n) ^ 3 * E₂ / n := by
  have hn2 : (0:ℝ) < n ^ 2 := by positivity
  have hn4 : (0:ℝ) < n ^ 4 := by positivity
  have hne : n ≠ 0 := ne_of_gt hn
  have hrhs : (q / n) ^ 3 * E₂ / n = (q ^ 3 * E₂) / n ^ 4 := by
    rw [div_pow]; field_simp
  rw [hrhs, div_le_iff₀ hn2, div_mul_eq_mul_div, le_div_iff₀ hn4]
  -- goal: 2 * q^3 * n^4 ≤ q^3 * E₂ * n^2; from E₂ ≥ 2 n^2 and positivity
  have hq3 : (0:ℝ) < q ^ 3 := by positivity
  nlinarith [hE, hq3, hn2, hn4, mul_pos hq3 hn2]

/-- **The normalized linear-forms correlation of the subgroup majorant.**  For
`ν = (q/n)·1_{μ_n}` and the expectation over `(a,b,c) ∈ 𝔽_q³`, the correlation is
`(q/n)⁴·E₂/q³`; from `E₂ ≥ 2n²` it is at least `2q/n²` (`= 2·n^{β−2}` at `q = n^β`). -/
theorem linearForms_value_ge_normalized
    (q n E₂ : ℝ) (hn : 0 < n) (hq : 0 < q) (hE : 2 * n ^ 2 ≤ E₂) :
    2 * q / n ^ 2 ≤ (q / n) ^ 4 * E₂ / q ^ 3 := by
  have hn2 : (0:ℝ) < n ^ 2 := by positivity
  have hn4 : (0:ℝ) < n ^ 4 := by positivity
  have hq3 : (0:ℝ) < q ^ 3 := by positivity
  have hrhs : (q / n) ^ 4 * E₂ / q ^ 3 = q * E₂ / n ^ 4 := by
    field_simp
  rw [hrhs, div_le_div_iff₀ hn2 hn4]
  nlinarith [hE, hq, hn2, mul_pos hq hn2]

/-- **Scalar fact `256 ≤ 2·n^7` for `n ≥ 2`.**  This was introduced as the growth `2·n^{3β−2}`
at `β ≥ 3` of the mis-normalized expression (`linearForms_value_ge`).  With the correct
normalization (`linearForms_value_ge_normalized`) the growth is `2·n^{β−2}`, so this
inequality is arithmetic only and does not measure the actual linear-forms violation. -/
theorem linearForms_factor_huge (n : ℕ) (hn : 2 ≤ n) :
    (256 : ℝ) ≤ 2 * (n : ℝ) ^ (7 : ℕ) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2 : (2 : ℝ) ^ (7 : ℕ) ≤ (n : ℝ) ^ (7 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hnR 7
  have hge : (128 : ℝ) ≤ (n : ℝ) ^ (7 : ℕ) := by
    calc (128 : ℝ) = (2:ℝ)^(7:ℕ) := by norm_num
      _ ≤ (n:ℝ)^(7:ℕ) := h2
  linarith

/-! ## Obstruction B: the dense-model count is an invariant underestimate (wrong direction) -/

/-- **Constant-density prediction invariance.**  For a majorant `ν'` of support size `N` with
`μ_n` at relative density `α = n/N`, the CONSTANT-density-`α` prediction for the 2t-term linear
form is `α^{2t}·N^{2t}/q = n^{2t}/q`, independent of `N`.  Formally:
`(n/N)^{2t} · N^{2t} / q = n^{2t}/q` whenever `N ≠ 0`.  A transference dense model need not be
constant, so this does not determine the count of every dense model. -/
theorem denseModel_count_invariant (n N q : ℝ) (t : ℕ) (hN : N ≠ 0) :
    ((n / N) ^ (2 * t)) * N ^ (2 * t) / q = n ^ (2 * t) / q := by
  rw [div_pow]
  congr 1
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self (pow_ne_zero _ hN), mul_one]

/-- **Exponent arithmetic: constant-density prediction versus the ordered Wick-type mass.**
The ordered-tuple Wick-type mass is `(2t−1)‼·n^t` (a leading term for ordered `2t`-tuple energy,
not the distinct vanishing-subset count, which in char 0 at dyadic order is `C(n/2, t)`); the
constant-density prediction is `n^{2t}/q`.  With `q = n^β` and `t ≤ β ≤ 2t` this records
`df·n^{β−t}·(n^{2t}/n^β) = df·n^t`, i.e. the prediction lies below the ordered mass by the factor
`(2t−1)‼·n^{β−t}`.  It says nothing about non-constant dense models or about full char-`p`
counts (which need the wraparound qualification). -/
theorem denseModel_undershoots_wick
    (n : ℕ) (t β : ℕ) (hn : 1 ≤ n) (htβ : t ≤ β) (hβ2t : β ≤ 2 * t) (df : ℕ) (hdf : 1 ≤ df) :
    (df : ℝ) * (n : ℝ) ^ (β - t) * ((n : ℝ) ^ (2 * t) / (n : ℝ) ^ β)
      = (df : ℝ) * (n : ℝ) ^ t := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hnpos
  -- n^{2t}/n^β = n^{2t-β}  (β ≤ 2t)
  have e1 : (n:ℝ) ^ (2 * t) / (n:ℝ) ^ β = (n:ℝ) ^ (2 * t - β) := by
    rw [div_eq_iff (pow_ne_zero _ hnne), ← pow_add]
    congr 1; omega
  rw [e1, mul_assoc, ← pow_add]
  congr 2
  omega

/-- **A8 packaged scalar facts.**  This bundles two arithmetic statements: (A) `256 ≤ 2·n^7`
(the growth of the mis-normalized expression; the correct normalized violation of the chosen
majorant is `2·n^{β−2}`, see `linearForms_value_ge_normalized`); (B) the constant-density
prediction `n^{2t}/q` does not depend on the majorant support size.  It does not prove that every
majorant, dense model or container argument fails; no method-wide verdict follows. -/
theorem a8_container_transference_no_go (n : ℕ) (hn : 2 ≤ n) :
    -- (A) precondition negated:
    (256 : ℝ) ≤ 2 * (n : ℝ) ^ (7 : ℕ)
    -- (B) dense-model count is choice-invariant:
    ∧ ∀ (N q : ℝ) (t : ℕ), N ≠ 0 →
        ((((n:ℝ) / N) ^ (2 * t)) * N ^ (2 * t) / q = (n:ℝ) ^ (2 * t) / q) := by
  refine ⟨linearForms_factor_huge n hn, ?_⟩
  intro N q t hN
  exact denseModel_count_invariant (n : ℝ) N q t hN

end ProximityGap.Frontier.A8ContainerTransferenceNoGo

#print axioms ProximityGap.Frontier.A8ContainerTransferenceNoGo.linearForms_value_ge
#print axioms ProximityGap.Frontier.A8ContainerTransferenceNoGo.linearForms_value_ge_normalized
#print axioms ProximityGap.Frontier.A8ContainerTransferenceNoGo.linearForms_factor_huge
#print axioms ProximityGap.Frontier.A8ContainerTransferenceNoGo.denseModel_count_invariant
#print axioms ProximityGap.Frontier.A8ContainerTransferenceNoGo.denseModel_undershoots_wick
#print axioms ProximityGap.Frontier.A8ContainerTransferenceNoGo.a8_container_transference_no_go
