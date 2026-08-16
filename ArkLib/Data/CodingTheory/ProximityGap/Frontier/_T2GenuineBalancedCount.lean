/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444 / #389, thread T2-recursion-lean)
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxHeartbeats 4000000

/-!
# T2: the GENUINE balanced-config count as a `Finset.card` (#444 / #389)

The AVENUE A reduction (`Frontier/CharZeroEnergyThreeExact.lean`) solves the depth-3 char-0
additive energy `E₃(μ_n) = 15n³ − 45n² + 40n` from an ABSTRACT carrier `B : ℕ → ℕ → ℤ` satisfying
the named `BalancedCount` predicate (base case + the add-one-class recursions `rec2`, `rec4`,
`rec6`). `Frontier/BalancedCountConcrete.lean` then exhibits a concrete witness — but it defines
that witness **by the convolution recursion itself**, so its `rec2/rec4/rec6` are essentially
definitional unfoldings of the convolution; nothing in tree connected the carrier to the **actual
combinatorial object it is supposed to count**: the set of *balanced sign-configurations*.

This file lands that genuine object. It defines

  `B k m := #{ c : Fin k → Fin m × Bool  |  ∀ class j, #(c⁻¹(j,+)) = #(c⁻¹(j,−)) }`

as a real `Finset.card` (the count of length-`k` tuples over `m` antipodal classes, each class
used with equal `+`/`−` multiplicity — exactly the zero-sum count `E_{k/2}(μ_{2m})` under the
Lam–Leung balance characterization), and proves, **axiom-clean** (`propext, Classical.choice,
Quot.sound`; verified by `#print axioms`; the `decide`-checked value lemmas are KERNEL-checked, not
`native_decide`, so they carry no `Lean.ofReduceBool`):

* `B_zero_len`        : `B 0 m = 1`        — the empty tuple is balanced over any classes;
* `B_zero_class_pos`  : `B k 0 = 0` (`k ≥ 1`) — no nonempty tuple over zero classes (`base0`);
* `B_fiber_decomp`    : the **add-one-class FIBRATION** — `B k (m+1)` is the sum, over subsets
  `S ⊆ Fin k` of positions, of the number of balanced configs whose last-class preimage is `S`
  (proven on the genuine count via `Finset.card_eq_sum_card_fiberwise`);
* `B2_vals`,`B4_vals`,`B6_val1` : the genuine count MATCHES the convolution closed forms
  (`B 2 m = 2m`, `B 4 m = 12m²−6m`, `B 6 1 = 20`) at the load-bearing instances.

## Why this is the genuine object (and what `BalancedCountConcrete` lacked)

`BalancedCountConcrete.balancedCount` is *defined* by the convolution `B k (m+1) = Σ_j C(k,2j)
C(2j,j) B (k−2j) m`, so its satisfaction of `rec2/rec4/rec6` is tautological. Here `B` is the
honest enumeration `Finset.card`, with NO recursion baked in; the structural facts (`base0`, the
fibration, and the value matches) are *theorems about the count*, established from the `Finset`
definition. This is the object the open thread T2 asks for ("define `B k m = #{balanced configs}
over `Fin`/`Finset` and prove the recursion").

## Honest scope — what is PROVEN here and what remains

PROVEN axiom-clean on the genuine count: the two base cases (`base0`/`B 0 m = 1`), the
add-one-class **fibration** `B_fiber_decomp` (the count splits as a sum over last-class
position-subsets), and the genuine count = convolution closed form at the load-bearing
evaluations.

The **REMAINING residual** to obtain the full general `BalancedCount` recursion from
`B_fiber_decomp` is the *fiber-cardinality bijection* + *binomial regrouping*: each fiber
(configs with last-class subset `S`) has cardinality `C(|S|,|S|/2)·B(k−|S|) m` when `|S|` is even
(choose `|S|/2` of the `|S|` last-class positions to be `+`; the complement is a balanced config
over the first `m` classes), `0` otherwise; regrouping `Σ_S g(|S|) = Σ_j C(k,2j) g(2j)` then gives
`Σ_j C(k,2j) C(2j,j) B(k−2j) m`. That fiber bijection (reindexing `Sᶜ → Fin (k−|S|)` and the
sign-balance split) is a standard but nontrivial multiset-enumeration; it is NOT proven here, so
this file does NOT yet discharge AVENUE A's `BalancedCount` input — it **grounds the carrier in the
genuine `Finset` object** and proves the fibration backbone, narrowing the remaining work to that
one named bijection. The deep BGK/Paley char-`p` wall at depth `r ≈ log m` is untouched; CORE
(`M(μ_n) ≤ C√(n log(p/n))`) stays OPEN.

Issue #444 / #389, thread T2-recursion-lean.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.T2GenuineBalancedCount

/-- **Balanced sign-configuration.** A config of length `k` over `m` antipodal classes assigns each
position `i : Fin k` a class `(c i).1 : Fin m` and a sign `(c i).2 : Bool` (`true = +`). It is
*balanced* iff every class is used with equally many `+`'s and `−`'s. -/
def IsBalanced {k m : ℕ} (c : Fin k → Fin m × Bool) : Prop :=
  ∀ j : Fin m, (univ.filter (fun i => c i = (j, true))).card
             = (univ.filter (fun i => c i = (j, false))).card

instance {k m : ℕ} (c : Fin k → Fin m × Bool) : Decidable (IsBalanced c) := by
  unfold IsBalanced; infer_instance

/-- **The genuine balanced-config count** as a `Finset.card`: the number of length-`k` tuples over
`m` antipodal classes each used with equal `+`/`−` multiplicity. Under the Lam–Leung balance
characterization this is the zero-sum count `E_{k/2}(μ_{2m})`. NO recursion is baked in — it is the
honest enumeration. -/
def B (k m : ℕ) : ℕ :=
  (univ.filter (fun c : Fin k → Fin m × Bool => IsBalanced c)).card

/-- **`base0`** on the genuine count: no nonempty tuple over zero classes (`Fin 0 × Bool` is empty,
so a config `Fin k → Fin 0 × Bool` with `k ≥ 1` cannot exist). -/
theorem B_zero_class_pos {k : ℕ} (hk : 1 ≤ k) : B k 0 = 0 := by
  unfold B
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c _
  exact absurd (c ⟨0, by omega⟩).1.elim0 (fun h => h)

/-- **`B 0 m = 1`** on the genuine count: the unique empty config is vacuously balanced. -/
theorem B_zero_len (m : ℕ) : B 0 m = 1 := by
  unfold B
  rw [Finset.card_eq_one]
  refine ⟨fun i => i.elim0, ?_⟩
  ext c
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨fun _ => funext fun i => i.elim0, fun h => by subst h; intro j; simp⟩

/-- **The last-class preimage** of a config over `Fin (m+1)`: the set of positions whose class is
the `(m+1)`-st (`Fin.last m`). The fibration variable for the add-one-class recursion. -/
def lastSet {k m : ℕ} (c : Fin k → Fin (m+1) × Bool) : Finset (Fin k) :=
  univ.filter (fun i => (c i).1 = Fin.last m)

/-- **The add-one-class FIBRATION** (genuine-count backbone of the recursion). The balanced configs
over `m+1` classes partition by their last-class preimage `S ⊆ Fin k`: `B k (m+1)` is the sum over
all position-subsets `S` of the number of balanced configs with `lastSet c = S`. Proven on the
genuine `Finset.card` object via `Finset.card_eq_sum_card_fiberwise`. The remaining step to the full
recursion is the per-fiber cardinality `= C(|S|,|S|/2)·B(k−|S|) m` (even `|S|`) and the binomial
regrouping — see the module docstring. -/
theorem B_fiber_decomp (k m : ℕ) :
    B k (m+1) = ∑ S ∈ (univ : Finset (Fin k)).powerset,
      ((univ.filter (fun c : Fin k → Fin (m+1) × Bool => IsBalanced c)).filter
        (fun c => lastSet c = S)).card := by
  unfold B
  rw [Finset.card_eq_sum_card_fiberwise (f := lastSet) (t := (univ : Finset (Fin k)).powerset)]
  intro c _
  simp

/-- The genuine count `B 2 m` matches the convolution closed form `2m` at `m = 1,2,3`
(`E_1(μ_{2m}) = n`). Kernel-`decide` (not `native_decide`): axiom-clean. -/
theorem B2_vals : B 2 1 = 2 ∧ B 2 2 = 4 ∧ B 2 3 = 6 := by decide

/-- The genuine count `B 4 m` matches the convolution closed form `12m²−6m` at `m = 1,2`
(`E_2(μ_{2m}) = 3n²−3n`). Kernel-`decide`: axiom-clean. -/
theorem B4_vals : B 4 1 = 6 ∧ B 4 2 = 36 := by decide

/-- The genuine count `B 6 1 = 20` matches the depth-3 convolution value (`E_3(μ_2)`). Kernel-
`decide`: axiom-clean. -/
theorem B6_val1 : B 6 1 = 20 := by decide

end ArkLib.ProximityGap.Frontier.T2GenuineBalancedCount

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx, NO ofReduceBool) -/
#print axioms ArkLib.ProximityGap.Frontier.T2GenuineBalancedCount.B_zero_class_pos
#print axioms ArkLib.ProximityGap.Frontier.T2GenuineBalancedCount.B_zero_len
#print axioms ArkLib.ProximityGap.Frontier.T2GenuineBalancedCount.B_fiber_decomp
#print axioms ArkLib.ProximityGap.Frontier.T2GenuineBalancedCount.B2_vals
#print axioms ArkLib.ProximityGap.Frontier.T2GenuineBalancedCount.B4_vals
#print axioms ArkLib.ProximityGap.Frontier.T2GenuineBalancedCount.B6_val1
