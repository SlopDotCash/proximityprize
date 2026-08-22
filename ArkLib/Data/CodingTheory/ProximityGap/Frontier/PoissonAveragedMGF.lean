/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CoshMGFIdentity
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The cosh-MGF as a Poisson-weighted average of `A_r / Wick_r` (Issue #444, the sharpened prize)

The sharpened prize (`#444` comment 4712437932) reframes the BGK sup-norm `CORE` as a **single
scalar** MGF condition `Ψ(y*) ≤ q²` at the saddle `y*² = 2 log q / n`, which is the
**Poisson(log q)-weighted average** of the per-level Paley ratios `ρ_r = A_r / Wick_r`:

> `Ψ(y) := ∑_{b∈F} cosh(‖η_b‖·y) = q · ∑_{r≥0} ρ_r · λ^r / r!`,   `λ = n·y²/2`,
> `ρ_r = A_r / Wick_r`,   `A_r = q·E_r`,   `Wick_r = (2r-1)‼·nⁿ`  (here `nⁿ` means `(G.card)^r`).

This file lands the **exact algebraic backbone** of that reframing, axiom-clean. It is a pure
**re-summation** of the in-tree even-moment identity `CoshMGFIdentity.coshMGF_eq_evenMoment_tsum`
using the Mathlib factorisation `(2r)! = 2^r · r! · (2r-1)‼`
(`Nat.factorial_eq_mul_doubleFactorial` + `Nat.doubleFactorial_two_mul`): it **trades the `(2r)!`
denominator for the `r!` (Poisson) denominator times the `(2r-1)‼` (Wick) factor**, with the
remaining `2^r · n^r · y^{2r}` collected into `(n·y²/2)^r = λ^r`.

## What is proven (`coshMGF_poisson_form`)

For every primitive additive character `ψ`, every finite `G`, and every real `y`:

> `∑_{b∈F} cosh(‖η_b‖·y) = ∑'_{r} (q · E_r(G) / ((2r-1)‼ · (G.card)^r)) · (G.card · y² / 2)^r / r!`.

Reading off the summand: `(q·E_r)/((2r-1)‼·(G.card)^r) = A_r/Wick_r = ρ_r` times the
**Poisson kernel** `λ^r / r!` with `λ = G.card·y²/2`. At the saddle `y² = 2 log q / G.card` one has
`λ = log q`, so `λ^r/r! = e^{log q} · Poisson(r; log q) = q · Poisson(r; log q)`, and the whole sum
becomes `q · ∑_r Poisson(r; log q)·ρ_r·q = q²·𝔼_{R~Poisson(log q)}[ρ_R]`. Hence the MGF prize
condition `Ψ(y*) ≤ q²` is **exactly** `𝔼[ρ_R] ≤ 1` — the averaged target, tolerating per-`r`
violations whenever the Poisson(log q) weight is small there.

⚠️ **But the averaging does NOT soften the wall (REFUTED — see honest scope below):** `ρ_1 = q`
(Parseval), so the `r=1` term alone contributes `log q ≫ 1` to `𝔼[ρ_R]`. The averaged target
`𝔼[ρ_R] ≤ 1` is violated at every prime, monotone-worse in `β`. The identity below is correct and
axiom-clean; only the "averaging escapes" reading is refuted.

## The integer factorisation lemma (`factorial_two_mul_eq`)

`(2r)! = 2^r · r! · (2r-1)‼`, the bridge between the `(2r)!` (cosh) and `r!` (Poisson) worlds.
Mathlib has `(2r)‼ = 2^r·r!` and `(2r)! = (2r)‼·(2r-1)‼`; we compose them. The `(2r-1)‼` factor
is exactly Mathlib's `(2*r - 1)‼`, the odd double factorial = the Wick (Gaussian `2r`-th moment)
coefficient `𝔼[Z^{2r}] = (2r-1)‼` for `Z ~ N(0,1)`.

## Honest scope — this is the EXACT IDENTITY, not the prize bound

This file proves the **identity** `Ψ = q·∑ ρ_r λ^r/r!` (a re-summation), which makes the averaged
target `𝔼[ρ_R] ≤ 1` a *literal* restatement of the MGF prize. It does **not** prove `𝔼[ρ_R] ≤ 1`.

**CORRECTION (this session, probe `scripts/probes/probe_poisson_avg.py` — REFUTES the earlier
prose).** An earlier draft of this note claimed `𝔼[ρ_R] ≈ 0.06–0.12` with "large margin" in the
prize band and `ρ_1 ≈ 1` with "negligible" weight. **Both are false**, by exact recomputation:

- `ρ_1 = q·E_1/Wick_1 = q·n/n = q` (Parseval gives `E_1 = n` exactly, `Wick_1 = n`); the
  DC-subtracted reading `A_1/Wick_1 = (qn-n²)/n = q - n` is also `≈ q`. The `r=1` Poisson weight is
  `log q · e^{-log q} = log q / q`, so the `r=1` term **alone** contributes `q · (log q / q) = log q`
  to `𝔼[ρ_R]` (verified: `8.33` at `n=8,p=4129`; `11.09` at `n=16,p=65537`, for **both** the full
  and excess readings).
- Hence `𝔼[ρ_R] ≥ log q ≫ 1` at **every** prime, and the violation **grows** with `β` (larger `q`):
  prize band `β = 4` gives `𝔼[ρ_R^{exc}] ≈ 380 (n=8), ≈ 5200 (n=16), ≈ 10⁵ (n=32)`, and
  `𝔼[ρ_R^{full}]` is larger still (`≈ 4·10⁶` at `n=32`, where the full ratio peaks at `r=16` not the
  Parseval anchor). There is **no** `𝔼[ρ_R] = 1` crossover as `β` increases — the average is
  monotone increasing in `β`. The flagged thick witnesses `n=64, p=14657/15809 (β≈2.3)` give
  `𝔼[ρ_R^{exc}] ≈ 3·10⁵–4·10⁵` (not the earlier "21–30"), `𝔼[ρ_R^{full}] ≈ 5·10¹⁰`.

**Verdict: the Poisson-averaged + √q-slack softening REDUCES TO THE WALL and does not even
relabel it favorably — it makes the *trivial* `r=1` Parseval term blow the averaged budget by a
factor `log q`, independent of any deep-`r` BGK structure.** The saddle identity `λ = log q` forces
`λ^r/r! = q·Poisson(r; log q)`, so `Ψ(y*) = q²·𝔼[ρ_R]`; the prize condition `Ψ(y*) ≤ q²` is the
*correct* restatement of the BGK sup-norm bound, but it is **not** softened by the averaging: the
char-0 Bessel main term `n^{2r}` (carried by `ρ_r`, not subtracted in the Lean object) and the
Parseval `r=1` anchor both survive the Poisson weighting. The averaged form is the **same wall**,
fully `β`-uniform in its *failure* (worse at large `β`), not thinness-essential. The genuine prize
content is recovered only by comparing `Ψ(y*)` against the *char-0 baseline* `Ψ^{char0}(y*)` (i.e.
the Bessel envelope `I₀(2y)^{n/2}` the section title names) and bounding the **excess**
`Ψ - Ψ^{char0}` by the √q slack — a comparison this averaged scalar `𝔼[ρ_R] ≤ 1` does NOT encode.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444.
-/

set_option linter.style.longLine false


open Finset
open scoped Nat  -- the `‼` (double factorial) notation is `scoped` under `Nat`
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ProximityGap.Frontier.CoshMGFIdentity (coshMGF_eq_evenMoment_tsum)

namespace ProximityGap.Frontier.PoissonAveragedMGF

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The factorial bridge `(2r)! = 2^r · r! · (2r-1)‼`.** Composes Mathlib's
`Nat.factorial_eq_mul_doubleFactorial` (`(2r)! = (2r)‼·(2r-1)‼`) with
`Nat.doubleFactorial_two_mul` (`(2r)‼ = 2^r·r!`). The `(2r-1)‼` factor is the Wick / Gaussian
`2r`-th-moment coefficient; isolating it converts the `(2r)!` (cosh) denominator into the `r!`
(Poisson) denominator. -/
theorem factorial_two_mul_eq (r : ℕ) :
    (2 * r).factorial = 2 ^ r * r.factorial * (2 * r - 1)‼ := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  · -- 2*r = (2*r - 1) + 1, so (2*r)! = (2*r - 1 + 1)! = (2*r-1+1)‼ · (2*r-1)‼
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    have h2 : 2 * (k + 1) - 1 + 1 = 2 * (k + 1) := by omega
    calc (2 * (k + 1)).factorial
        = (2 * (k + 1) - 1 + 1).factorial := by rw [h2]
      _ = (2 * (k + 1) - 1 + 1)‼ * (2 * (k + 1) - 1)‼ :=
            Nat.factorial_eq_mul_doubleFactorial _
      _ = (2 * (k + 1))‼ * (2 * (k + 1) - 1)‼ := by rw [h2]
      _ = (2 ^ (k + 1) * (k + 1).factorial) * (2 * (k + 1) - 1)‼ := by
            rw [Nat.doubleFactorial_two_mul]

/-- **The cosh-MGF in Poisson form (#444).** Re-summation of the in-tree even-moment identity
`coshMGF_eq_evenMoment_tsum` via `factorial_two_mul_eq`: the `(2r)!` denominator becomes the
`r!` (Poisson) denominator, the `(2r-1)‼` (Wick) factor and `(G.card)^r` move under the period
ratio, and `2^r · (G.card)^r · y^{2r}` collects into `λ^r` with `λ = G.card · y² / 2`:

> `∑_{b∈F} cosh(‖η_b‖·y) = ∑'_r (q·E_r / ((2r-1)‼·(G.card)^r)) · (G.card·y²/2)^r / r!`.

The summand `(q·E_r)/((2r-1)‼·(G.card)^r)` is exactly `ρ_r = A_r/Wick_r` (with `A_r = q·E_r`,
`Wick_r = (2r-1)‼·(G.card)^r`); the factor `(G.card·y²/2)^r/r!` is the Poisson kernel `λ^r/r!`.
At the saddle `λ = log q` this is `q·𝔼_{R~Poisson(log q)}[ρ_R]·q`, so `Ψ(y*) ≤ q² ⟺ 𝔼[ρ_R] ≤ 1`. -/
theorem coshMGF_poisson_form {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (y : ℝ) :
    (∑ b : F, Real.cosh (‖ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ * y))
      = ∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r)
          / (((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r)
          * ((G.card : ℝ) * y ^ 2 / 2) ^ r / (r.factorial : ℝ) := by
  rw [coshMGF_eq_evenMoment_tsum hψ G y]
  refine tsum_congr (fun r => ?_)
  -- Pure scalar identity for each `r`. Handle `G.card = 0` (then both sides vanish via `0^r`).
  rcases Nat.eq_zero_or_pos G.card with hc | hc
  · -- For G empty all energies with r ≥ 1 vanish; for r = 0 both sides equal q.
    have hGempty : G = ∅ := Finset.card_eq_zero.mp hc
    subst hGempty
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    · -- r ≥ 1: both sides are 0. RHS via (0·…)^r = 0; LHS via rEnergy ∅ r = 0.
      have hrne : r ≠ 0 := by omega
      have hrhs : ((((∅ : Finset F).card : ℝ)) * y ^ 2 / 2) ^ r = 0 := by
        simp [zero_pow hrne]
      have henergy : (rEnergy (∅ : Finset F) r : ℝ) = 0 := by
        have hne : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
        have : rEnergy (∅ : Finset F) r = 0 := by
          unfold rEnergy
          rw [Fintype.piFinset_empty]
          simp
        rw [this]; simp
      rw [henergy, hrhs]; ring
  · -- G.card > 0: clear denominators with the factorial bridge and rearrange.
    have hc' : (G.card : ℝ) ≠ 0 := by positivity
    have hcr : (G.card : ℝ) ^ r ≠ 0 := pow_ne_zero _ hc'
    have hdf : ((2 * r - 1)‼ : ℝ) ≠ 0 := by
      have h0 : (2 * r - 1)‼ ≠ 0 := (Nat.doubleFactorial_pos _).ne'
      exact_mod_cast h0
    have hfac : (r.factorial : ℝ) ≠ 0 := by positivity
    have h2r : ((2 * r).factorial : ℝ) ≠ 0 := by positivity
    -- The integer bridge, cast to ℝ.
    have hbridge : ((2 * r).factorial : ℝ)
        = 2 ^ r * (r.factorial : ℝ) * ((2 * r - 1)‼ : ℝ) := by
      have := factorial_two_mul_eq r
      have : ((2 * r).factorial : ℝ) = (((2 ^ r * r.factorial * (2 * r - 1)‼ : ℕ)) : ℝ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
      rw [this]; push_cast; ring
    -- Now the two sides are equal as rational functions; verify by clearing denominators.
    rw [hbridge]
    rw [show ((G.card : ℝ) * y ^ 2 / 2) ^ r = ((G.card : ℝ) * y ^ 2) ^ r / (2 : ℝ) ^ r by
      rw [div_pow]]
    field_simp
    ring
end ProximityGap.Frontier.PoissonAveragedMGF

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` — no `sorryAx`). -/
#print axioms ProximityGap.Frontier.PoissonAveragedMGF.factorial_two_mul_eq
#print axioms ProximityGap.Frontier.PoissonAveragedMGF.coshMGF_poisson_form
