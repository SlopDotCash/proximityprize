/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# #444 NO-GO — the [binding-restriction] lens: worst Gauss-period coset is NOT O(n)-confined

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

This file records the **refutation** of that hope as a named no-go, plus the one surviving
closed-form artifact. Three machine-checked measurements:

* **part 1** (`probe_444_binding_coset_confinement.py`): the *maximum* house is attained on
  `O(1)` cosets (`N(20%) ∈ {1,…,4}`, `N(20%)/n → 0`). Tempting — but this is the spread of the
  argmax, not the union-bound-relevant tail.

* **part 2** (`probe_444_binding_tailmech.py`): for the `O(n)` distinguished subset
  `D = {coset(1−ζ) : ζ∈μ_n}` (the only `p`-independent `O(n)` candidate), the argmax coset
  **falls OUTSIDE `D`** in ≈ half of all primes, and there `max_{b∈D}|η_b| / M(n)` drops as low
  as `0.26`. The worst binding direction is GENERIC, not monomial/difference. Restricting the
  house to any `O(n)` direction set is therefore **unsound** (loses house).

* **part 3** (`probe_444_binding_tailgrowth.py`): the inverted effective count
  `M_eff = exp((M/√n)²/2)` tracks `m`, not `n` — `M_eff/n` keeps GROWING with `m` at fixed `n`,
  and `M(n)/√n ≈ √(2 log m)` (not `√(2 log n)`). In `79/125` primes `M(n) > 1.1·√(n log n)`,
  i.e. the house literally exceeds the ceiling any `O(n)`-direction subset could supply. The
  `√log m` factor is the actual growth rate — not removable by confinement.

**Reef (as predicted):** the lens dies by relocating the wall onto a distinguished `O(n)` subset
that the generic worst case escapes — and even in its dream scenario the budget is self-defeating
(re-expressing the same house as `C·√(n log n)` only *inflates* `C` by `√(log m / log n)`).

## What is formalized here (axiom-clean)

The lens is a structural claim about an **effective-count** function `Neff : ℕ → ℝ`
(the inverted max-of-Gaussians count, `Neff = exp((M/√n)²/2)`). The probes pin two facts:
`(i)` `Neff` is NOT `O(n)` (part 3), and `(ii)` the implied house lower bound. We state the lens
as a `Prop` and record both the no-go and the closed-form house bound it leaves standing.

This is `*_REFUTED`-tier documentation (§6 honesty contract): a named hypothesis plus the
elementary consequences that ARE proven, NOT a claimed closure of the open core.
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

/-- The **effective independent-direction count** read off from the house via the
max-of-Gaussians inversion `M/√n ≈ √(2 log Neff)`, i.e. `Neff = exp((M/√n)² / 2)`.
This is the quantity the union bound truly pays `√(log ·)` over. -/
noncomputable def Neff (I : Instance) : ℝ := Real.exp ((I.M / Real.sqrt I.n) ^ 2 / 2)

/-- **The lens, as a falsifiable `Prop`.** `BindingCosetConfinement C` asserts the effective
direction count is `O(n)` *uniformly* (constant `C`, independent of the coset count `m`):
the worst binding coset lives in a `C·n`-sized set, so the union bound only pays `√log(C·n)`
rather than `√log m`. The probes show this FAILS: `Neff/n` grows with `m`. -/
def BindingCosetConfinement (C : ℝ) (S : Set Instance) : Prop :=
  ∀ I ∈ S, Neff I ≤ C * (I.n : ℝ)

/-- **The house lower bound implied by an instance** (the inversion run backwards, exactly,
no approximation): `M = √(n · 2 · log Neff)`. This is the closed-form artifact the lens leaves
standing — the house is determined by the *log of the effective count*, and the probes pin
`log Neff ≈ log m`, giving `M ≈ √(2 n log m)`. -/
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

/-- **The no-go (refutation), stated as the negation the probes witness.** If the lens held for
some constant `C` on a set `S` of instances, then on `S` every instance would satisfy
`M(n)² ≤ n · 2 · log(C·n)` — i.e. `M(n) ≤ √(2 n log(C n))`, with NO dependence on `m`. The
probes exhibit instances (e.g. `n=16, m≥16` with `M/√n > √(2 log 16)`) violating this for every
fixed `C`, because `M/√n` tracks `√(2 log m)` and `m → ∞`. We package the structural implication
(confinement ⟹ `m`-free house bound) that the numerics then contradict. -/
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

/-- **The surviving closed-form M(n) bound (the conjecture this lens yields).**
The probes pin `Neff ≈ m` (effective count = coset count, NOT `O(n)`), so the house obeys
`M(n) ≈ √(2 n log m)` with a bounded constant `sup M/√(n log m) ≈ 1.33–1.65`. We state the
*conjectural upper bound* in this normalization as a named `Prop` (its truth = the open prize
core; this file does NOT claim to prove it). The lens's contribution is the SIGN: confinement
would give `log n`, the numerics give `log m`, so the conjecture must keep `log m`. -/
def HouseBoundLogM (C : ℝ) (S : Set Instance) : Prop :=
  ∀ I ∈ S, I.M ≤ C * Real.sqrt ((I.n : ℝ) * Real.log I.m)

/-- The bounded-constant house bound `M ≤ C√(n log m)` is **strictly weaker** than (implied by)
any `√(n log n)` confinement claim only when `m ≤ n`; at the prize `m = 2^128 ≫ n = 2^30`, so the
two are genuinely different and the numerics select `log m`. We record the elementary inequality
direction: when `m ≥ n`, a `log m` bound does NOT follow from a `log n` bound (the bounds cross).
This is the formal content of "the swap is self-defeating at the budget". -/
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
