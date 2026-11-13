/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The Delsarte / LP method NO-GO for the Gauss-period house (#444)

The $1M open core is the house
`M(μ_n) = max_{b≠0} |Σ_{z∈μ_n} e_p(bz)| = max_J √(τ_J)`.
Here `τ_J ≥ 0` are the `m = (p−1)/n` squared period magnitudes: the spectral
measure on the cosets.  Thus `house² = max_J τ_J`. The exact degree-1
(Parseval) moment is `∑_J τ_J = p − n`; numerically:
`n=8,p=337 → 2632 = 8·329` and `n=16,p=1297 → 20496 = 16·1281`.

**The no-go.** Any Delsarte / linear-programming / positive-semidefinite /
Beurling-Selberg dual certificate for an upper bound on `house² = max_J τ_J`
can only use **linear** functionals of the spectral vector that are certified by
the moment data.  The only degree-1 moment available is the total mass
`∑_J τ_J = p − n`. The LP relaxation optimum of `max_J τ_J` subject to
`τ ≥ 0` and `∑_J τ_J = S` is **exactly `S`**, achieved by putting all mass on
one coset. Hence the best bound any such method yields is

  `house² ≤ p − n`,  i.e.  `house ≤ √(p − n) ≈ √(n·m)`,

the trivial Parseval / `√m`-loss ceiling: a factor `√(m / (2 log m)) ≈ 2^63`
at prize scale `m ≈ 2^128` above the conjectural `house ≤ √(2 n log m)`.
Beating Parseval requires the **degree-2** moment `∑_J τ_J² = E₂`, the additive
energy.  This is **not a linear functional of the `τ_J`**, and is therefore
structurally invisible to any LP/psd dual.  So the entire Delsarte-LP method
class cannot reach the prize window; the live handle remains the nonlinear
additive-energy/moment wall `E_r`.

This file formalizes the load-bearing core as an elementary, fully general
fact: the LP relaxation optimum of `max_J τ_J` under the single mass constraint
is exactly the total mass. It is a **method no-go**, companion to
`BlockSumNormNoGo.lean` and the disc(Ψ) no-go, NOT a closure of the house.
It proves that a class of approaches cannot work, isolating the wall further.
CORE `M(μ_n) ≤ C√(n log(p/n))` UNCHANGED/OPEN.

Axiom-clean: `⊆ {propext, Classical.choice, Quot.sound}`. No `sorry`/`axiom`/`native_decide`.
-/

namespace ArkLib.ProximityGap.DelsarteLPNoGo

open Finset

variable {m : ℕ}

/-- A single nonnegative spectral coordinate is at most the total mass:
`τ_J ≤ ∑_K τ_K`. This is the only inequality on `max_J τ_J` that the degree-1
total-mass moment supplies. -/
theorem coord_le_sum (τ : Fin m → ℝ) (hτ : ∀ J, 0 ≤ τ J) (J : Fin m) :
    τ J ≤ ∑ K, τ K :=
  Finset.single_le_sum (f := τ) (fun K _ => hτ K) (Finset.mem_univ J)

/-- **The Delsarte/LP relaxation optimum for the house equals Parseval.**
Over all nonnegative spectral vectors `τ : Fin m → ℝ` with fixed total mass
`∑_J τ_J = S`, the single degree-1 moment any LP/psd dual can certify, the
maximum coordinate `max_J τ_J = house²`:

* is **bounded above by `S`** for every feasible `τ` (first conjunct), and
* **attains `S`** at the extremal "all mass on one coset" point (second conjunct).

Hence the LP optimum is exactly `S`: no certificate using only the total mass
can prove `house² < S = p−n`.  Beating the trivial Parseval ceiling
`house ≤ √(p−n)` is impossible by any such method.  It requires the degree-2
moment `∑_J τ_J² = E₂`, which is not linear in `τ`. -/
theorem parseval_lp_extremal (hm : 0 < m) (S : ℝ) (hS : 0 ≤ S) :
    (∀ τ : Fin m → ℝ, (∀ J, 0 ≤ τ J) → (∑ J, τ J = S) → ∀ J, τ J ≤ S) ∧
      (∃ τ : Fin m → ℝ, (∀ J, 0 ≤ τ J) ∧ (∑ J, τ J = S) ∧ ∃ J, τ J = S) := by
  refine ⟨fun τ hτ hsum J => ?_, ?_⟩
  · -- upper bound: every coordinate ≤ total mass = S
    have h := coord_le_sum τ hτ J
    rwa [hsum] at h
  · -- extremal feasible point: all mass S on coordinate ⟨0, hm⟩
    refine ⟨fun J => if J = ⟨0, hm⟩ then S else 0, fun J => ?_, ?_, ⟨0, hm⟩, ?_⟩
    · change 0 ≤ if J = ⟨0, hm⟩ then S else 0
      split_ifs with h
      · exact hS
      · exact le_refl 0
    · change (∑ J : Fin m, if J = ⟨0, hm⟩ then S else 0) = S
      rw [Finset.sum_eq_single_of_mem (⟨0, hm⟩ : Fin m) (Finset.mem_univ _)
        (fun b _ hb => if_neg hb)]
      simp
    · change (if (⟨0, hm⟩ : Fin m) = ⟨0, hm⟩ then S else 0) = S
      simp

/-! ## Domain-blind certificate transfer

The Krawtchouk / MacWilliams weight-distribution variant of the LP idea has a second
obstruction: for Reed-Solomon codes over any `n` distinct evaluation points, the MDS weight
enumerator, and therefore its MacWilliams/Krawtchouk transform, depends only on `(n, k, q)`.
Any certificate whose input is only such an invariant transfers unchanged to every evaluation
domain with the same invariant.  Thus it cannot prove a smooth-subgroup-only floor unless the
same certified ceiling is valid for all domains sharing the invariant.
-/

/-- A certificate using only an invariant transfers its bound across domains with the same
invariant.  This is the formal core of the MacWilliams/Krawtchouk domain-blind no-go: once the
weight enumerator has forgotten the evaluation points, the produced ceiling is identical for the
smooth subgroup, a random domain, or an arithmetic-progression domain with the same MDS
parameters. -/
theorem domainBlind_bound_transfers
    {Domain Invariant : Type*} (inv : Domain → Invariant) (target : Domain → ℝ)
    (ceiling : Invariant → ℝ)
    (hcert : ∀ D, target D ≤ ceiling (inv D))
    {smooth reference : Domain} (hsame : inv smooth = inv reference) :
    target smooth ≤ ceiling (inv reference) := by
  simpa [hsame] using hcert smooth

/-- If one domain sharing the invariant violates the proposed ceiling, then no certificate that
uses only that invariant can be a valid uniform upper-bound proof.  For the RS weight-distribution
route, `inv` is the MDS/MacWilliams/Krawtchouk data, so a past-Johnson proof must add
domain-sensitive information beyond the weight enumerator. -/
theorem domainBlind_counterexample_refutes
    {Domain Invariant : Type*} (inv : Domain → Invariant) (target : Domain → ℝ)
    (ceiling : Invariant → ℝ)
    {smooth reference : Domain} (hsame : inv smooth = inv reference)
    (hbad : ceiling (inv smooth) < target reference) :
    ¬ ∀ D, target D ≤ ceiling (inv D) := by
  intro hcert
  have hle : target reference ≤ ceiling (inv reference) := hcert reference
  rw [← hsame] at hle
  exact not_lt_of_ge hle hbad

end ArkLib.ProximityGap.DelsarteLPNoGo

#print axioms ArkLib.ProximityGap.DelsarteLPNoGo.parseval_lp_extremal
#print axioms ArkLib.ProximityGap.DelsarteLPNoGo.domainBlind_bound_transfers
#print axioms ArkLib.ProximityGap.DelsarteLPNoGo.domainBlind_counterexample_refutes
