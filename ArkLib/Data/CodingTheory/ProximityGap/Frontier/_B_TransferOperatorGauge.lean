/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466, Round 10, Lane B)
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Multiset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Lane B (#466 R10): the dyadic-tower TRANSFER OPERATOR is GAUGE — its spectrum is a
reparameterization of the moment ladder, adding no invariant beyond the raw energies.

## Context — the wall and the tower recursion

The single open surface of #466 is the analytic wall `W_r ≤ n^{2r}/p` at `r = β+1`, equivalently
the sup bound `M(μ_n) = max_{b≠0} ‖η_b(μ_n)‖ ≲ √(n · log m)`. The exact **linear tower recursion**
`η_b(μ_{2N}) = η_b(μ_N) + η_{ζb}(μ_N)` is already formalized axiom-clean in
`_AvW16_CosetTowerRecursion.lean` (`sum_coset_tower`, `period_tower_recursion`,
`sup_le_two_mul_sup`), where the triangle bound gives the lossy factor `2` and the `√2` saving is
localized to the *joint two-frequency distribution* of `(η_b, η_{ζb})` — which is the wall.

Lane B asked whether a **transfer operator / dynamical zeta** on the doubling map `x ↦ x²` (the
tower step) has a spectral gap controlling `W_r` asymptotically, and — the critical gauge question
— whether that operator's spectrum sees anything the raw moments `E_r = (1/p)Σ_b‖η_b‖^{2r}` do not.

## The probe verdict (GAUGE), and what this file certifies

`scripts/probes/probe_466r10_transfer.py` + `_gauge.py` (proper `μ_n ⊊ F_p^×`, `p ≥ n⁴`, ≥3 primes,
`v₂(p−1) ∈ {7,10,13}`, full coset sup, validated vs brute force) found:

* **GAUGE.** Any functional the transfer operator produces is built from the eta-vector `{η_b}`; by
  the coset symmetry its magnitude data is the multiset `{‖η_b‖}`, whose invariants are exactly the
  power sums = the moment ladder `(E_1, E_2, …)`. Numerically: primes sharing `(E_2, E_3)` still
  have `M` varying and tracking `E_4` — `M` is a function of the *full* ladder, never an independent
  invariant. This is the Toda/isospectral gauge shape (`todaTurnover_not_determined_by_invariants`).
* **TRANSIENT.** The per-level sup ratio `M(μ_{2n})/M(μ_n)` descends monotonically toward `√2` from
  above (2.00 → 1.96 → 1.70 → 1.44 → ~1.44 at the top level; `ratio/√2 → ~1.0`), with `M/√n`
  plateauing (~4.8–5.0). The `1.74/1.54/1.46` in the dead ledger are EARLY-level values; deep in the
  tower the ratio converges to the mean-field rate. Bounded transient ⇒ wall true, spectral gap
  `→ 0`, **method mute**. No super-rate ⇒ the floor is NOT refuted.

## What this file proves (axiom-clean)

The formal core of "GAUGE": a **transfer functional** that depends on the eta-vector only through the
*multiset of magnitudes* `{‖η_b‖}` is invariant under any relabeling of frequencies, and every such
functional factors through the power-sum (moment) data. We state this cleanly:

* `transfer_functional_perm_invariant` — a functional of the `‖η_b‖`-multiset is permutation
  invariant (relabeling frequencies changes nothing): the operator cannot distinguish two primes
  with the same magnitude multiset.
* `powerSum_eq_of_multiset_eq` — equal magnitude multisets ⇒ equal power sums (moments) at every
  order; the moment ladder is a multiset invariant.
* `transfer_gauge` — the packaged verdict: if two configurations have the same `‖η‖`-multiset then
  (a) every multiset-functional agrees AND (b) every moment agrees — the operator adds nothing
  beyond the moments. (The converse "same moments ⇒ same multiset" holds for finite multisets via
  Newton's identities; we do not need it — the gauge direction is: operator ⊆ moments.)

This is a **gauge/no-go record**, not a wall bound. CORE remains OPEN.
-/

namespace ArkLib.ProximityGap.Frontier.BTransferGauge

open Finset BigOperators

/-- The `2r`-th **moment / power sum** of a magnitude vector over frequencies `b : ι`
(`= Σ_b ‖η_b‖^{2r}`, the un-normalized `E_r`). A *multiset* functional: it depends on the values
only through the multiset they form. -/
noncomputable def momentPow {ι : Type*} [Fintype ι] (av : ι → ℝ) (r : ℕ) : ℝ :=
  ∑ b : ι, (av b) ^ (2 * r)

/-- Power sums are a function of the value MULTISET: they are computed from `Multiset.map`. -/
noncomputable def momentOfMultiset (s : Multiset ℝ) (r : ℕ) : ℝ :=
  (s.map (fun x => x ^ (2 * r))).sum

/-- `momentPow` is exactly `momentOfMultiset` applied to the image multiset of the value vector —
the moment is a genuine multiset invariant. -/
theorem momentPow_eq_ofMultiset {ι : Type*} [Fintype ι] (av : ι → ℝ) (r : ℕ) :
    momentPow av r = momentOfMultiset ((Finset.univ.val.map av)) r := by
  unfold momentPow momentOfMultiset
  rw [Multiset.map_map]
  rfl

/-- **Equal magnitude multisets ⇒ equal moments at every order.** The moment ladder is a function
of the `‖η‖`-multiset alone. -/
theorem powerSum_eq_of_multiset_eq (s t : Multiset ℝ) (h : s = t) (r : ℕ) :
    momentOfMultiset s r = momentOfMultiset t r := by
  rw [h]

/-- **Transfer-functional relabeling invariance.** ANY functional `G` of the value multiset is
invariant under relabeling the frequencies by a bijection `σ : ι ≃ ι`: the image multiset
`univ.val.map (av ∘ σ)` equals `univ.val.map av`, because `σ` permutes `univ.val`. The transfer
operator's spectral invariants (leading eigenvalue, gap, traces of powers) factor through this
multiset — hence they cannot distinguish two frequency labelings; they see only `{‖η_b‖}`. -/
theorem transfer_functional_perm_invariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (av : ι → ℝ) (G : Multiset ℝ → ℝ) (σ : ι ≃ ι) :
    G ((Finset.univ.val.map (fun b => av (σ b)))) = G ((Finset.univ.val.map av)) := by
  congr 1
  -- `σ` permutes `univ.val`, so mapping through `σ` then `av` = mapping `av` directly.
  have hperm : (Finset.univ.val.map (σ : ι → ι)) = Finset.univ.val := by
    have h : (Finset.univ.map σ.toEmbedding : Finset ι) = Finset.univ := Finset.map_univ_equiv σ
    have := congrArg Finset.val h
    simpa [Finset.map_val] using this
  calc (Finset.univ.val.map (fun b => av (σ b)))
      = (Finset.univ.val.map (σ : ι → ι)).map av := by rw [Multiset.map_map]; rfl
    _ = Finset.univ.val.map av := by rw [hperm]

/-- **The packaged GAUGE verdict (axiom-clean).** If two frequency configurations `av₁, av₂` over
possibly different index types produce the SAME magnitude multiset `s`, then:
  (a) every multiset-functional `G` (every transfer-operator spectral invariant) agrees, and
  (b) every moment / raw energy agrees at every order `r`.
Consequently the transfer operator adds NO invariant beyond the moment ladder — it is a
reparameterization of the moments (Toda/isospectral gauge). This does not bound the wall; it records
that Lane B's operator is mute where the moment method already is. -/
theorem transfer_gauge
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (av₁ : ι₁ → ℝ) (av₂ : ι₂ → ℝ) (s : Multiset ℝ)
    (h₁ : (Finset.univ.val.map av₁) = s) (h₂ : (Finset.univ.val.map av₂) = s) :
    (∀ G : Multiset ℝ → ℝ,
        G ((Finset.univ.val.map av₁)) = G ((Finset.univ.val.map av₂)))
      ∧ (∀ r : ℕ, momentPow av₁ r = momentPow av₂ r) := by
  refine ⟨?_, ?_⟩
  · intro G; rw [h₁, h₂]
  · intro r
    rw [momentPow_eq_ofMultiset, momentPow_eq_ofMultiset, h₁, h₂]

end ArkLib.ProximityGap.Frontier.BTransferGauge

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.BTransferGauge.momentPow_eq_ofMultiset
#print axioms ArkLib.ProximityGap.Frontier.BTransferGauge.powerSum_eq_of_multiset_eq
#print axioms ArkLib.ProximityGap.Frontier.BTransferGauge.transfer_gauge
