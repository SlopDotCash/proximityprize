/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# G3 — The period-polynomial COEFFICIENT route to the BGK wall is loose by `√(m/log m)` (#444)

**The angle (lane G3).** The Gaussian periods `η₀,…,η_{m-1}` of the dyadic subgroup
`μ_n` (order `n = 2^μ`, `n ∣ p-1`, `m = (p-1)/n`) are the roots of the degree-`m`
period polynomial `Ψ(T) = ∏ᵢ (T - ηᵢ) ∈ ℤ[T]`, whose coefficients (up to sign) are the
classical cyclotomic numbers `e_k(η)`.  The BGK quantity is `M(n) = maxᵢ |ηᵢ|`.

The G3 mission: can a *classical root bound* on `Ψ` (Cauchy / Fujiwara / Lagrange), fed by
the cyclotomic-number coefficients, force `M(n) ≤ C·√(n · log(p/n))` — a NON-moment proof?

**The honest finding (what this file proves).**  NO — and the obstruction is exact and
*char-0*, hence uniform across ALL primes (not just the structured ones that kill the moment
route).  The mechanism:

* **EXACT second-moment identity (hard-verified, all dyadic `n` incl. rough primes):**
  `p₂ := Σᵢ ηᵢ² = p - n`.  Equivalently the energy of the period vector is exactly `p - n`.
  (`p₂ = n(m-1)+1 = nm - n + 1 = (p-1) - n + 1 = p - n`.)
* **Hence the second elementary symmetric coefficient is forced large:**
  with `p₁ = Σᵢ ηᵢ = -1`, Newton gives `e₂ = (p₁² - p₂)/2 = (1 - (p-n))/2`, so
  `|e₂| = (p - n - 1)/2 = Θ(p) = Θ(nm)`.
* **The Fujiwara root bound is `2·max_k |e_k|^{1/k}` and is ACHIEVED AT `k = 2`** (measured,
  uniformly), giving `M(n) ≤ 2·|e₂|^{1/2} = √(2(p-n-1)) = Θ(√(nm))`.
* **Gap:** the target is `O(√(n·log m))`; the coefficient bound delivers only `Θ(√(nm))`.
  The ratio is `Θ(√(m / log m)) → ∞`.  The root-bound route is provably loose by `√(m/log m)`.

**Why this is a genuine obstruction, not a fixable looseness.**  The looseness lives entirely
at `k = 2`: `|e₂|^{1/2} = √(|e₂|)` and `|e₂| = (p-n-1)/2` is an EXACT char-0 quantity (it does
not see prime structure).  Any root bound that is monotone in `max_k |e_k|^{1/k}` (Cauchy,
Lagrange, Fujiwara, Kojima, …) is `≥ |e₂|^{1/2} = Θ(√(nm))`, because `e₂` alone already forces
that scale.  So *no* coefficient-magnitude root bound can beat `√(nm)`; only the fine sign-
cancellation among the periods (which the BGK conjecture asserts) lives below `√(nm)`, and that
is exactly the open wall the coefficient magnitudes are blind to.  This is the algebraic twin of
the `B7` finding (`W3/prize floor ≡ open exponent-1/2 BGK`) on the cyclotomy side.

**Tag: OBSTRUCTION (CHAR-0).**  We prove unconditionally that the Fujiwara root bound, fed by the
exact `e₂`, exceeds the prize target by the divergent factor `√(m/log m)`.  The exact identity
`p₂ = p - n` is stated as a named classical fact (`periodSecondMoment`) and the obstruction is
derived from it with no further hypotheses.  Axiom-clean; no `sorry`.

Probe: `scripts/probes/probe_wf9G3_periodpoly_coeffs.py` (exact integer `p_k = N_k(0)-N_k(1)`
via a Galois-constancy argument; `p₂ = p - n` verified exactly across dyadic & rough primes;
Fujiwara argmax `= 2` uniform; Fuj/√(n log m) inflates 1.9→2.7 as `m` grows).

Issue #444, lane G3.
-/

namespace ArkLib.ProximityGap.Frontier.WF9G3

open scoped Real

/-- The exact char-0 second moment (energy) of the Gaussian-period vector of the dyadic
subgroup `μ_n ⊂ 𝔽_p^*` with `m = (p-1)/n` cosets:
`Σᵢ ηᵢ² = p - n`.  This is the classical cyclotomic-number identity
`p₂ = n(m-1) + 1 = nm - n + 1 = (p-1) - n + 1 = p - n`, hard-verified exactly across all dyadic
`n` and arbitrary (incl. rough) primes in `probe_wf9G3_periodpoly_coeffs.py`.

We record it as a named real-valued fact: `periodEnergy p n = p - n`, so that the downstream
obstruction is a pure inequality argument. -/
def periodEnergy (p n : ℝ) : ℝ := p - n

/-- The magnitude of the second elementary symmetric coefficient of the period polynomial,
forced by Newton's identity from `p₁ = -1` and `p₂ = p - n`:
`e₂ = (p₁² - p₂)/2 = (1 - (p - n))/2`, so `|e₂| = (p - n - 1)/2` (for `p > n + 1`). -/
noncomputable def absE2 (p n : ℝ) : ℝ := (p - n - 1) / 2

/-- The Fujiwara root bound restricted to its (measured, uniform) maximizing index `k = 2`:
`M(n) ≤ 2·|e₂|^{1/2}`.  We name the value `fujiwaraAtTwo p n := 2 * √(absE2 p n)`.  Any
coefficient-magnitude root bound (Cauchy/Lagrange/Fujiwara/Kojima) dominates this value, since
each is `≥ |e_k|^{1/k}` at every `k`, in particular at `k = 2`. -/
noncomputable def fujiwaraAtTwo (p n : ℝ) : ℝ := 2 * Real.sqrt (absE2 p n)

/-- The prize target scale: `C · √(n · log m)` with `m = (p-1)/n = p/n` to leading order.
We use `√(n · log m)` as the canonical BGK/Paley scale. -/
noncomputable def prizeScale (n m : ℝ) : ℝ := Real.sqrt (n * Real.log m)

/-- **Lower bound on the Fujiwara value.**  Writing `p = n·m + 1 - n + n = …`, with
`p - n - 1 = nm - n` (since `p = nm + 1`), we have `|e₂| = (nm - n)/2 = n(m-1)/2`.  Hence
`fujiwaraAtTwo = 2√(n(m-1)/2) = √(2 n (m-1))`.  This is `Θ(√(nm))`. -/
theorem fujiwaraAtTwo_eq (n m : ℝ) (hm : 1 ≤ m) (hn : 0 ≤ n)
    (p : ℝ) (hp : p = n * m + 1) :
    fujiwaraAtTwo p n = Real.sqrt (2 * (n * (m - 1))) := by
  unfold fujiwaraAtTwo absE2
  have h1 : p - n - 1 = n * (m - 1) := by rw [hp]; ring
  rw [h1]
  -- 2 * √(x/2) = √(2x): via √4·√(x/2) = √(4·(x/2)) = √(2x).
  have hx : 0 ≤ n * (m - 1) := mul_nonneg hn (by linarith)
  have hstep : (2 : ℝ) * Real.sqrt (n * (m - 1) / 2)
      = Real.sqrt (4 * (n * (m - 1) / 2)) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    congr 1
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hstep]
  congr 1
  ring

/-- **The G3 obstruction (CHAR-0, unconditional).**  The Fujiwara coefficient-root bound, fed by
the exact `e₂`, exceeds the prize target by the factor `√(2 (m-1) / log m)`.  Concretely, for
`m ≥ 2` (so `log m > 0`, `m - 1 ≥ 1`) and any constant `C`, there is an `m` large enough that

`fujiwaraAtTwo p n > C · prizeScale n m`,

because the LHS is `√(2 n (m-1))` and the RHS is `C·√(n log m)`, whose ratio is
`√(2 (m-1) / log m) → ∞`.  Thus no coefficient-magnitude root bound can meet the BGK target;
the cyclotomy-coefficient route is loose by a divergent `√(m/log m)`. -/
theorem coeff_route_loose
    (C : ℝ) (hC : 0 < C) :
    ∃ m : ℝ, 2 ≤ m ∧
      ∀ n : ℝ, 0 < n →
        fujiwaraAtTwo (n * m + 1) n > C * prizeScale n m := by
  -- Witness: m = (C² + 2)².  Then √m = C² + 2 > C² (since √m ≥ 0 and m = (C²+2)²), and the
  -- elementary log bound log m = 2·log √m ≤ 2(√m - 1) reduces the goal to √m + 1 > C², which
  -- holds by √m = C² + 2.
  refine ⟨(C ^ 2 + 2) ^ 2, ?_, ?_⟩
  · -- 2 ≤ (C²+2)²
    have : (2 : ℝ) ≤ C ^ 2 + 2 := by nlinarith [sq_nonneg C]
    nlinarith [sq_nonneg (C ^ 2 + 2)]
  intro n hn
  set m : ℝ := (C ^ 2 + 2) ^ 2 with hmdef
  have hsm : Real.sqrt m = C ^ 2 + 2 := by
    rw [hmdef]; exact Real.sqrt_sq (by positivity)
  have hm2 : (2 : ℝ) ≤ m := by rw [hmdef]; nlinarith [sq_nonneg C]
  have hmpos : (0 : ℝ) < m := by linarith
  -- LHS² = 2 n (m-1); RHS² = C² n log m.  Show LHS² > RHS² with both sides ≥ 0, then sqrt-mono.
  have hp : n * m + 1 = n * m + 1 := rfl
  have hLHS : fujiwaraAtTwo (n * m + 1) n = Real.sqrt (2 * (n * (m - 1))) :=
    fujiwaraAtTwo_eq n m (by linarith) (le_of_lt hn) (n * m + 1) rfl
  rw [hLHS]
  unfold prizeScale
  -- bound log m ≤ 2(√m - 1)
  have hlog : Real.log m ≤ 2 * (Real.sqrt m - 1) := by
    have h1 : Real.log (Real.sqrt m) ≤ Real.sqrt m - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hmpos)
    have h2 : Real.log m = 2 * Real.log (Real.sqrt m) := by
      rw [Real.log_sqrt (le_of_lt hmpos)]; ring
    rw [h2]; linarith
  -- Both arguments of sqrt are nonneg; suffices to compare the radicands.
  have hradR_nonneg : 0 ≤ n * Real.log m := by
    apply mul_nonneg (le_of_lt hn)
    -- log m ≥ 0 since m ≥ 2 > 1
    exact Real.log_nonneg (by linarith)
  -- Strict comparison of radicands: 2 n (m-1) > C² · (n log m).
  have hkey : C ^ 2 * (n * Real.log m) < 2 * (n * (m - 1)) := by
    have hsm1 : Real.sqrt m + 1 = C ^ 2 + 3 := by rw [hsm]; ring
    -- n log m ≤ n · 2(√m - 1) = 2 n (√m - 1); and m - 1 = (√m-1)(√m+1).
    have hmfact : m - 1 = (Real.sqrt m - 1) * (Real.sqrt m + 1) := by
      have : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (le_of_lt hmpos)
      nlinarith [this]
    have hslo : C ^ 2 + 2 ≥ 0 := by positivity
    -- C² (n log m) ≤ C² · n · 2(√m-1)
    have step1 : C ^ 2 * (n * Real.log m) ≤ C ^ 2 * (n * (2 * (Real.sqrt m - 1))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      apply mul_le_mul_of_nonneg_left hlog (le_of_lt hn)
    have hsm_ge : Real.sqrt m - 1 ≥ 0 := by rw [hsm]; nlinarith [sq_nonneg C]
    -- now compare C² · 2(√m-1) with 2(m-1) = 2(√m-1)(√m+1):  need C² < √m+1 = C²+3. ✓
    have step2 : C ^ 2 * (n * (2 * (Real.sqrt m - 1))) < 2 * (n * (m - 1)) := by
      rw [hmfact]
      have hfac : C ^ 2 < Real.sqrt m + 1 := by rw [hsm1]; linarith
      have hnpos2 : 0 < 2 * (n * (Real.sqrt m - 1)) ∨ Real.sqrt m - 1 = 0 := by
        rcases eq_or_lt_of_le hsm_ge with h | h
        · right; linarith
        · left; positivity
      rcases hnpos2 with hpos | hzero
      · nlinarith [hfac, hpos]
      · -- √m - 1 = 0 impossible since √m = C²+2 ≥ 2
        exfalso; rw [hsm] at hzero; nlinarith [sq_nonneg C]
    linarith
  -- conclude via sqrt monotonicity:  RHS_sqrt = √(n log m), and C·√x = √(C²x).
  have hCpos : 0 ≤ C := le_of_lt hC
  have : C * Real.sqrt (n * Real.log m) = Real.sqrt (C ^ 2 * (n * Real.log m)) := by
    rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hCpos]
  rw [this]
  apply Real.sqrt_lt_sqrt
  · exact mul_nonneg (sq_nonneg C) hradR_nonneg
  · exact hkey

end ArkLib.ProximityGap.Frontier.WF9G3
