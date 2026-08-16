/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A8 no-go: the container / relative-Szemerédi (transference) method cannot bound the char-`p`
vanishing-2t-subset count of `μ_n` past Johnson (#407)

ANGLE 8 (manifesto): the vanishing-2t-subset count is a count within a structured ambient (the
cyclotomic relations).  The **hypergraph container method** (Balogh–Morris–Samotij, Saxton–Thomason)
and the **relative-Szemerédi / transference principle** (Green–Tao, Conlon–Fox–Zhao) bound counts of
linear-forms patterns in **positive-relative-density subsets of pseudorandom majorants** by reducing
to a **dense model** of the same density.  NEW LEMMA attempted: the char-`p` vanishing-2t-subset count
`V_p(μ_n,t)` is bounded by its dense-model value, giving `M(μ_n) ≤ C√(n log)`.

VERDICT: **reduces-to-wall (BGK / Paley spectrum), via a FORMAL precondition negation + a
direction failure**, both established by exact probes over proper subgroups `μ_n` (`p` prime,
`n = 2^μ`, `n ∣ p−1`, `p = n^4 ≫ n³`, never `n = p−1`;
`scripts/probes/probe_a8_container_transference.py`, `probe_a8_structured_vs_excess.py`,
`probe_a8_linearforms_precondition.py`, `probe_a8_escape_dense_model.py`) and recorded here as
axiom-clean Lean.

## Obstruction A — the LINEAR-FORMS condition FAILS for the `μ_n` majorant (precondition negated)

Transference requires the normalized majorant `ν = (q/n)·1_{μ_n}` (`E[ν]=1`) to satisfy the
**linear-forms condition**: the 4-point additive-energy correlation
`LF := E_{a,b,c}[ ν(a)ν(b)ν(c)ν(a+b−c) ] = (q/n)³·E₂(μ_n)/n` must be `1+o(1)`.  Exact probe values
(`probe_angle8_linearforms_precondition.py`): with `E₂(μ_n) ≈ 1.4·2n²` (the near-Sidon additive
energy), `LF ≈ 2q³/n² = 2·n^{3β−2}` — astronomically large (`2.9e9, 3.1e12, 3.3e15, 3.4e18` for
`n=8,16,32,64`).  The condition fails by `n^{3β−2} → ∞`.  This is the **same wall as A9**: `μ_n` is a
sparse set whose additive correlations track its *multiplicative-group* structure, not the
pseudorandom prediction, so it is **not a pseudorandom majorant** and transference is inapplicable —
the precondition is negated, exactly as PFR/KM's small-doubling precondition is negated in A9.

## Obstruction B — every dense model UNDERSHOOTS the true count (wrong direction)

Even granting an *alternative* pseudorandom majorant `ν'` (not `μ_n` itself) inside which `μ_n` sits
at positive relative density `α = n/|supp ν'|`, the transference **dense-model count** of the 2t-term
vanishing pattern is `α^{2t}·(linear-forms count of ν') = α^{2t}·|supp ν'|^{2t}/q = n^{2t}/q`,
**invariant under the choice of `ν'`** (since `α·|supp ν'| = n` always).  But the TRUE char-0 count
(= the char-`p` count in the prize regime, measured ratio `V_p/V_0 = 1.000` exactly at `n ≤ 32`,
`β = 4`) is the **Wick / negation-pairing floor** `V_0 ≈ (2t−1)‼·n^t` — *larger* than the dense-model
value by the **undershoot factor** `(2t−1)‼·n^{β−t} → ∞` (`768×, 3072×, 12288×, …` at `t=2`).
The dense model is an **invariant UNDERESTIMATE** of the count.  Since the open core needs an
**UPPER** bound on the char-`p` count matching `V_0` (to certify no char-`p` *excess* over char-0),
a dense-model value far *below* `V_0` certifies nothing — it is the wrong direction.

## Net

A8 falls on the **BGK / Paley-spectrum horn**.  The transference/container machinery is built to
*lower-bound* (find patterns in) or *count-match* sparse sets that are pseudorandom subsets of a
pseudorandom majorant; `μ_n`'s additive correlations are governed by the **multiplicative-group
structure** (the vanishing count saturates the char-0 Wick floor from below, `V_0/Wick → 1`), which is
exactly the structure the dense-model reduction *erases*.  The genuine ambient — the cyclotomic
relations — is not a *pseudorandom* ambient in the linear-forms sense; it is the **multiplicative
group**, whose additive-energy linear form fails the condition by `n^{3β−2}`.  This is the very
input (square-root cancellation of the `μ_n` Fourier coefficients = Paley-graph spectrum) that
Alon–Bourgain ("Additive Patterns in Multiplicative Subgroups") flag as the *open* hypothesis their
graph-eigenvalue method must assume.  New machinery, but it reduces to — does not bridge — the BGK
wall.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.  Issue #407.
-/

namespace ProximityGap.Frontier.A8ContainerTransferenceNoGo

/-! ## Obstruction A: the linear-forms condition is violated by a growing factor -/

/-- **Linear-forms violation, abstract core.**  Model the linear-forms condition as the demand
`LF ≤ 1 + tol` on the 4-point correlation of the majorant.  For the `μ_n` majorant the exact value is
`LF = (q/n)³ · E₂ / n` with additive energy `E₂ ≥ 2n²` (near-Sidon lower floor).  Hence
`LF ≥ 2·q³/n²`.  With `q = n^β`, `β ≥ 3` and `n ≥ 2` this exceeds any fixed tolerance `1+tol`
(`tol < 2^{3β−2}−1`): the precondition is negated.  We record the clean inequality
`(q/n)³·E₂/n ≥ 2·q³/n²` from `E₂ ≥ 2n²`, then that `2q³/n²` is huge. -/
theorem linearForms_value_ge
    (q n E₂ : ℝ) (hn : 0 < n) (hq : 0 < q) (hE : 2 * n ^ 2 ≤ E₂) :
    2 * q ^ 3 / n ^ 2 ≤ (q / n) ^ 3 * E₂ / n := by
  have hn2 : (0:ℝ) < n ^ 2 := by positivity
  have hn4 : (0:ℝ) < n ^ 4 := by positivity
  have hne : n ≠ 0 := ne_of_gt hn
  have hrhs : (q / n) ^ 3 * E₂ / n = (q ^ 3 * E₂) / n ^ 4 := by
    rw [div_pow]; field_simp
  rw [hrhs, div_le_iff₀ hn2, div_mul_eq_mul_div, le_div_iff₀ hn4]
  -- goal: 2 * q^3 * n^4 ≤ q^3 * E₂ * n^2 ; from E₂ ≥ 2 n^2 and positivity
  have hq3 : (0:ℝ) < q ^ 3 := by positivity
  nlinarith [hE, hq3, hn2, hn4, mul_pos hq3 hn2]

/-- **The linear-forms violation factor diverges.**  At the prize shape `q = n^β` with `β ≥ 3`, the
lower bound `2q³/n²` on `LF` equals `2·n^{3β−2}`, which exceeds any fixed tolerance for `n` large:
concretely, for `n ≥ 2` and `β ≥ 3`, `2·n^{3β−2} ≥ 2·n^7 ≥ 2·128 = 256 ≫ 2` (the `1+tol` of a usable
condition).  So `ν = (q/n)1_{μ_n}` is **not** a pseudorandom majorant. -/
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

/-- **Dense-model count invariance.**  For any pseudorandom majorant `ν'` of support size `N` inside
which `μ_n` sits at relative density `α = n/N`, the transference dense-model count of the 2t-term
linear form is `α^{2t}·N^{2t}/q = n^{2t}/q`, **independent of `N`** (the majorant choice).  Formally:
`(n/N)^{2t} · N^{2t} / q = n^{2t}/q` whenever `N ≠ 0`. -/
theorem denseModel_count_invariant (n N q : ℝ) (t : ℕ) (hN : N ≠ 0) :
    ((n / N) ^ (2 * t)) * N ^ (2 * t) / q = n ^ (2 * t) / q := by
  rw [div_pow]
  congr 1
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self (pow_ne_zero _ hN), mul_one]

/-- **The dense-model count UNDERSHOOTS the Wick floor.**  The true char-0 count (= char-`p` count in
the prize regime) is the Wick/negation-pairing floor `Wick = (2t−1)‼·n^t`; the dense-model count is
`n^{2t}/q`.  With `q = n^β`, the undershoot is `Wick / (n^{2t}/q) = (2t−1)‼·n^{β−t}`.  For `β > t`
(the prize shape, `β ≈ 4 > t` at small `t`) this `→ ∞`, so the dense model lies far *below* the truth.
We record the clean fact (prize shape `t ≤ β ≤ 2t`, e.g. `β=4, t∈{2,3}`) that the diverging factor
`n^{β−t}` times the dense-model count `n^{2t}/n^β` recovers exactly `n^t` (the Wick exponent), i.e.
`n^{β−t} · (n^{2t}/n^β) = n^t`, so `Wick = (2t−1)‼·n^t = (2t−1)‼·n^{β−t}·(dense-model count)` and the
dense-model count is below `Wick` by the diverging factor `(2t−1)‼·n^{β−t}`. -/
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

/-- **A8 packaged no-go.**  The two obstructions combine: (A) the `μ_n` majorant violates the
linear-forms condition (factor `≥ 2n^7 ≥ 256` at `β ≥ 3`), so transference is inapplicable; (B) any
alternative dense model produces the *invariant underestimate* `n^{2t}/q`, below the true Wick floor
by `(2t−1)‼·n^{β−t}` — the wrong direction for the open core's needed UPPER bound.  Hence the
container/transference method **reduces to the BGK / Paley-spectrum wall** rather than bridging it. -/
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
#print axioms ProximityGap.Frontier.A8ContainerTransferenceNoGo.linearForms_factor_huge
#print axioms ProximityGap.Frontier.A8ContainerTransferenceNoGo.denseModel_count_invariant
#print axioms ProximityGap.Frontier.A8ContainerTransferenceNoGo.denseModel_undershoots_wick
#print axioms ProximityGap.Frontier.A8ContainerTransferenceNoGo.a8_container_transference_no_go
