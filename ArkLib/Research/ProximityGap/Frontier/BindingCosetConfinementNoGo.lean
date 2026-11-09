/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# #444 [binding-restriction] lens: O(n)-confinement of the worst Gauss-period coset (probe
# evidence against a preselected set; no formal asymptotic no-go)

## The lens (deliberately outside the 12 dead lenses)

The house is `M(n) = max_{b ≢ 0 mod p} |Σ_{x∈μ_n} e_p(b·x)| = max_b |η_b|`, the sup-norm of the
Gauss period `η_b`. Because `x` ranges over the **subgroup** `μ_n`, the sum depends on `b` only
through its coset `b·μ_n ∈ F_p^* / μ_n`; so `M(n)` is *already* a max over the `m = (p−1)/n`
cosets (the Gauss-period structure — `m = 2^128` at the prize).

The lens **hoped**: the worst (binding) coset is confined to an `O(n)`-sized, `p`-independent,
group-theoretically distinguished subset of cosets (the dilation / monomial-extremal directions
`b = 1 − ζ`, `ζ ∈ μ_n`). If so, the union bound producing `√(n·log m)` would only range over
`O(n)` effective directions, giving the prize-cracking `√(n·log n)`.

## What the probes found (exact, `scripts/probes/probe_444_binding_*.py`; never the full group)

This file records probe evidence against that hope plus the elementary closed-form artifacts. Three
finite probe measurements (computational evidence, not Lean theorems):

* **part 1** (`probe_444_binding_coset_confinement.py`): the *maximum* house is attained on
  `O(1)` cosets (`N(20%) ∈ {1,…,4}`, `N(20%)/n → 0`). Tempting — but this is the spread of the
  argmax, not the union-bound-relevant tail.

* **part 2** (`probe_444_binding_tailmech.py`): for the `O(n)` distinguished subset
  `D = {coset(1−ζ) : ζ∈μ_n}` (the only `p`-independent `O(n)` candidate), the argmax coset
  **falls OUTSIDE `D`** in ≈ half of the probed primes, and there `max_{b∈D}|η_b| / M(n)` drops as
  low as `0.26`. So restricting the house to this particular preselected `D` loses house. This does
  NOT exclude every `O(n)`-sized candidate set: a singleton containing the actual argmax always
  exists, so any restriction claim must specify a selection/information class (e.g. sets chosen
  without knowledge of `p`), which this file does not formalize.

* **part 3** (`probe_444_binding_tailgrowth.py`): in the probed range the proxy
  `M_eff = exp((M/√n)²/2)` grew with `m` at fixed `n`, and `M(n)/√n ≈ √(2 log m)`. In `79/125`
  probed primes `M(n) > 1.1·√(n log n)`. These are finite observations.

**Corrections (audit R-308).** An earlier version of this header claimed that increasing `m` at
fixed `n = 16` refutes confinement for EVERY fixed `C`. That is false: for a genuine size-`n` period
the triangle inequality gives `M ≤ n`, hence `Neff = exp((M/√n)²/2) ≤ exp(n/2)` and
`Neff/n ≤ exp(n/2)/n` (`exp 8/16` at `n = 16`), regardless of how large `m` gets. So at any fixed `n`
confinement HOLDS with `C = exp(n/2)/n` (`confinement_at_fixed_n`), and Gaussian-max growth in `m`
cannot continue indefinitely at fixed `n`. A meaningful asymptotic no-go needs a stated joint
`(n, m)` growth regime, which this file does not supply. Also, `Neff` is a nonlinear renaming of `M`
(a heuristic proxy), not an independently proved number of directions; its log inversion
`house_eq_log_Neff` is an identity, not a new house lower bound.

## What is formalized here (axiom-clean)

The lens is a structural claim about the **effective-count proxy** `Neff`
(the inverted max-of-Gaussians count, `Neff = exp((M/√n)²/2)`). We state the lens as a `Prop` and
prove only elementary scalar facts: the identity `M² = 2n·log Neff`, the implication
confinement ⟹ `m`-free house bound, the physical-range bound `Neff ≤ exp(n/2)` (given `M ≤ n`) and
hence fixed-`n` confinement, and the monotonicity `√(n log n) ≤ √(n log m)` for `n ≤ m`.

None of these proves the announced asymptotic refutation: the lens is NOT refuted in Lean, and at
fixed `n` it is in fact satisfied (with a constant depending on `n`). This is a named hypothesis
plus elementary consequences, NOT a no-go theorem and NOT a closure of the open core.
-/

namespace ProximityGap.BindingCosetConfinement

open scoped Real

/-- Abstract data of the lens at a fixed instance `(n, m, M)`:
`n = |μ_n|`, `m = (p−1)/n` (the number of cosets / Gauss periods),
`M = max_{b≢0} |η_b|` the house (a real ≥ 0). -/
structure Instance where
  /-- subgroup size `n = 2^μ`. -/
  n : ℕ
  /-- coset count / number of distinct Gauss periods, `m = (p−1)/n`. -/
  m : ℕ
  /-- the house `M(n) = max_{b≢0 mod p} |Σ_{x∈μ_n} e_p(b x)|`. -/
  M : ℝ
  hn : 2 ≤ n
  hm : 2 ≤ m
  hM : 0 ≤ M

/-- The **effective-count proxy** read off from the house via the heuristic max-of-Gaussians
inversion `M/√n ≈ √(2 log Neff)`, i.e. `Neff = exp((M/√n)² / 2)`. This is a nonlinear renaming of
`M`, NOT an independently proved number of directions or independence parameter. For a genuine
period (`M ≤ n`) it is at most `exp(n/2)` (`Neff_le_exp_half_n`). -/
noncomputable def Neff (I : Instance) : ℝ := Real.exp ((I.M / Real.sqrt I.n) ^ 2 / 2)

/-- **The lens, as a falsifiable `Prop`.** `BindingCosetConfinement C` asserts the effective
direction count is `O(n)` *uniformly* (constant `C`, independent of the coset count `m`):
the worst binding coset lives in a `C·n`-sized set, so the union bound only pays `√log(C·n)`
rather than `√log m`. At any fixed `n` this holds on physical instances (`M ≤ n`) with
`C = exp(n/2)/n` (`confinement_at_fixed_n`), so a refutation must let `n` grow jointly with `m`;
no such refutation is proved here. -/
def BindingCosetConfinement (C : ℝ) (S : Set Instance) : Prop :=
  ∀ I ∈ S, Neff I ≤ C * (I.n : ℝ)

/-- **The definitional log inversion** (exact, no approximation): `M² = n · 2 · log Neff`. Since
`Neff` is defined from `M`, this is an identity, not a new house lower bound; the probe observation
`log Neff ≈ log m` (equivalently `M ≈ √(2 n log m)`) is finite evidence only. -/
theorem house_eq_log_Neff (I : Instance) :
    I.M ^ 2 = (I.n : ℝ) * (2 * Real.log (Neff I)) := by
  have hnpos : (0 : ℝ) < I.n := by
    have : (2 : ℝ) ≤ (I.n : ℝ) := by exact_mod_cast I.hn
    linarith
  have hsqrt : Real.sqrt I.n ^ 2 = (I.n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
  have hlog : Real.log (Neff I) = (I.M / Real.sqrt I.n) ^ 2 / 2 := by
    unfold Neff; exact Real.log_exp _
  have hnne : (I.n : ℝ) ≠ 0 := ne_of_gt hnpos
  rw [hlog]
  rw [div_pow, hsqrt]
  field_simp

/-- **Confinement ⟹ `m`-free house bound** (structural implication only). If the lens held for
some constant `C` on a set `S` of instances, then on `S` every instance would satisfy
`M(n)² ≤ n · 2 · log(C·n)` — i.e. `M(n) ≤ √(2 n log(C n))`, with NO dependence on `m`. This is NOT a
refutation: at fixed `n` the physical bound `M ≤ n` already implies such an `m`-free bound with
`C = exp(n/2)/n`, so instances at fixed `n` (e.g. `n = 16`) cannot violate it for every fixed `C`.
Contradicting it requires a family with `n` growing jointly with `m`. -/
theorem confinement_forces_m_free_bound
    {C : ℝ} {S : Set Instance} (hC : BindingCosetConfinement C S)
    (I : Instance) (hI : I ∈ S) (hCn : 0 < C * (I.n : ℝ)) :
    I.M ^ 2 ≤ (I.n : ℝ) * (2 * Real.log (C * (I.n : ℝ))) := by
  have hbound : Neff I ≤ C * (I.n : ℝ) := hC I hI
  have hNpos : 0 < Neff I := Real.exp_pos _
  have hmono : Real.log (Neff I) ≤ Real.log (C * (I.n : ℝ)) :=
    Real.log_le_log hNpos hbound
  have heq := house_eq_log_Neff I
  have hnpos : (0 : ℝ) ≤ I.n := by
    have : (2 : ℝ) ≤ (I.n : ℝ) := by exact_mod_cast I.hn
    linarith
  rw [heq]
  have : (2 : ℝ) * Real.log (Neff I) ≤ 2 * Real.log (C * (I.n : ℝ)) := by linarith
  exact mul_le_mul_of_nonneg_left this hnpos

/-- **Physical-range bound on the proxy** (audit R-308). For a genuine size-`n` period the
triangle inequality gives `M ≤ n`; then `Neff = exp((M/√n)²/2) ≤ exp(n/2)`, independently of `m`. -/
theorem Neff_le_exp_half_n (I : Instance) (hMn : I.M ≤ (I.n : ℝ)) :
    Neff I ≤ Real.exp ((I.n : ℝ) / 2) := by
  have hnpos : (0 : ℝ) < I.n := by
    have : (2 : ℝ) ≤ (I.n : ℝ) := by exact_mod_cast I.hn
    linarith
  unfold Neff
  apply Real.exp_le_exp.mpr
  rw [div_pow, Real.sq_sqrt hnpos.le]
  have hM2 : I.M ^ 2 ≤ (I.n : ℝ) * I.n := by nlinarith [I.hM, hMn]
  have hdiv : I.M ^ 2 / (I.n : ℝ) ≤ I.n := by
    rw [div_le_iff₀ hnpos]; exact hM2
  linarith

/-- **Fixed-`n` confinement holds** (audit R-308). On the physical instances of a fixed subgroup
size `n₀` (those with `M ≤ n`), `BindingCosetConfinement` holds with the `m`-independent constant
`C = exp(n₀/2)/n₀`. Hence increasing the coset count `m` at fixed `n` can never refute confinement
for every fixed `C`; any no-go must be stated in a joint `(n, m)` growth regime. -/
theorem confinement_at_fixed_n (n₀ : ℕ) (hn₀ : 2 ≤ n₀) :
    BindingCosetConfinement (Real.exp ((n₀ : ℝ) / 2) / n₀)
      {I : Instance | I.n = n₀ ∧ I.M ≤ (I.n : ℝ)} := by
  rintro I ⟨hIn, hMn⟩
  have h := Neff_le_exp_half_n I hMn
  have hn₀pos : (0 : ℝ) < n₀ := by exact_mod_cast (by omega : 0 < n₀)
  rw [hIn] at h ⊢
  rw [div_mul_cancel₀ _ hn₀pos.ne']
  exact h

/-- **The conjectural `log m` house bound (open; not proved here).**
In the probed range `M(n) ≈ √(2 n log m)` with `sup M/√(n log m) ≈ 1.33–1.65` (finite evidence).
We state the *conjectural upper bound* in this normalization as a named `Prop` (its truth = the
open prize core; this file does NOT claim to prove it). The probes do not show that a `log n`
normalization is impossible asymptotically; they only show it was not attained with small constants
in the probed cells. -/
def HouseBoundLogM (C : ℝ) (S : Set Instance) : Prop :=
  ∀ I ∈ S, I.M ≤ C * Real.sqrt ((I.n : ℝ) * Real.log I.m)

/-- **Scale monotonicity** (direction corrected per audit R-308). When `n ≤ m`,
`√(n log n) ≤ √(n log m)`. Consequently, with the same nonnegative constant `C`, a `log n` house
bound `M ≤ C√(n log n)` DOES imply the weaker `log m` bound `M ≤ C√(n log m)`; the converse is what
fails in general. (An earlier docstring stated the implication backwards.) At the prize
`m = 2^128 ≫ n = 2^30`, so the `log n` bound would be the strictly stronger target. -/
theorem logM_dominates_logN_when_m_ge_n
    (I : Instance) (hmn : (I.n : ℝ) ≤ (I.m : ℝ)) :
    Real.sqrt ((I.n : ℝ) * Real.log (I.n : ℝ))
      ≤ Real.sqrt ((I.n : ℝ) * Real.log (I.m : ℝ)) := by
  have hnpos : (0 : ℝ) < I.n := by
    have : (2 : ℝ) ≤ (I.n : ℝ) := by exact_mod_cast I.hn
    linarith
  have hlog : Real.log (I.n : ℝ) ≤ Real.log (I.m : ℝ) := Real.log_le_log hnpos hmn
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left hlog (le_of_lt hnpos)

end ProximityGap.BindingCosetConfinement
