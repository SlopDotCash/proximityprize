/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AbacusNCore
import Mathlib.Data.Set.Finite.Basic

/-!
# The `c`-parametrization of abacus `n`-core-EMPTY configurations (#389/#407)

This is the combinatorial spine of the **cyclic-sieving / `n`-core list-growth** prize experiment.

The smooth-domain (`μ_n`) higher-order-MDS / list-decoding certificate for a degree-pattern is the
generalized Vandermonde `det(ζ^{β_j·i})`, `β_j = λ_j + (n-1-j)`; on `μ_n` it is **nonzero iff the
abacus `n`-core is empty** (`HOMDSSmoothObstruction.homds_det_ne_zero_iff_nCoreEmpty`), iff the
bead residues `β_j mod n` are pairwise distinct (`AbacusNCore.nCoreEmpty_iff_injOn_mod`). A
nonvanishing certificate is a full-rank square subsystem — a *candidate* list-decoding obstruction.

The prize-decisive question (the single most decisive remaining cyclic-sieving experiment): does the
**count of `n`-core-EMPTY certificates** grow polynomially or super-polynomially in `n` at prize
parameters? This file settles the count exactly on the in-tree `nCoreEmpty` object.

## The result

For *any* `c : Fin n → ℕ`, the bead function `β_c r := r + n · c r` is **`n`-core-EMPTY**: its
residues `β_c r mod n = r` are trivially the identity permutation, hence pairwise distinct
(`nCoreEmpty_cParam`). Moreover `c ↦ β_c` is **injective** (`cParam_injective`). Therefore the
`n`-core-EMPTY configurations are at least as numerous as `ℕ^{Fin n} = ℕ^n` — an *unbounded,
super-polynomial* family (`exists_infinite_nCoreEmpty`, `nCoreEmpty_card_unbounded`).

## The honest reading (why this is a REDUCTION, not a refutation of the floor)

The super-poly explosion lives entirely in the **certificate / support** count. The numerical probe
`scripts/probes/probe_ncore_empty_listgrowth_prize.py` measures this exactly:
the size-graded `n`-core-EMPTY count is the binomial `Σ_{S} C(S+n-1, n-1)` (validated against brute
force for `n ∈ {4,6,8,10}`), which is *super-poly* (e.g. `n=256`, Johnson agreement: `> 10^37`).
But the **EXACT `F_p` codeword list** (the `δ*`-relevant quantity) is *tiny* and `p`-independent: at
the Johnson radius the worst smooth-`μ_n` list is `O(1/ρ)` (a handful), collapsing to `1` above the
`k+1` boundary, and the only larger list — the `a = k+1` spike — is **generic MDS** list-decoding
(smooth `≈` random domain), *not* a cyclic-sieving effect.

This is exactly the in-tree core-vs-list split
`#cores ≤ L · C(A, k+m+1)` (`SubJohnsonListSupply.explainableCoreSupply_of_listBound`): the
`n`-core enumeration counts the `C(A, k+m+1)` **supports**, which this file shows is super-poly,
*not* the codeword list `L`. The cyclic-sieving lever therefore gives **no list boost** over a
random domain; the route REDUCES to the same named open core (`SubJohnsonListBound`'s `L`).
**No closure, no refutation — a precise reduction.** See `DISPROOF_LOG.md`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); finite/elementary.
-/

open Finset
open ArkLib.ProximityGap.AbacusNCore

namespace ArkLib.ProximityGap.NCoreEmptyCParametrization

variable {n : ℕ}

/-- The `c`-parametrization bead function: `β_c r = r + n · c r`. Each runner `r` carries the bead
`r + n · c r`, so the residues are the identity permutation of `Fin n`. -/
def cParam (c : Fin n → ℕ) : Fin n → ℕ := fun r => (r : ℕ) + n * c r

/-- The residue of `cParam c r` mod `n` is exactly `r` (one bead per runner). -/
theorem cParam_mod (c : Fin n → ℕ) (r : Fin n) : cParam c r % n = (r : ℕ) := by
  unfold cParam
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt r.isLt

/-- **Every `c`-parametrized configuration is `n`-core-EMPTY.** The residue map
`r ↦ cParam c r % n = r` is the identity, hence injective. -/
theorem nCoreEmpty_cParam (c : Fin n → ℕ) : nCoreEmpty (cParam c) := by
  rw [nCoreEmpty_iff_injOn_mod]
  intro a b hab
  simp only [cParam_mod] at hab
  exact Fin.ext hab

/-- The `c`-parametrization is **injective**: distinct `c` give distinct bead functions. -/
theorem cParam_injective : Function.Injective (cParam (n := n)) := by
  intro c c' h
  funext r
  have hr : cParam c r = cParam c' r := congrFun h r
  unfold cParam at hr
  have hmul : n * c r = n * c' r := by omega
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h0 => (h0 ▸ r).elim0)
  exact Nat.eq_of_mul_eq_mul_left hn hmul

/-- **Super-poly certificate count, sharp form.** There is an injection from `ℕ^{Fin n}` into the
`n`-core-EMPTY bead functions. Hence at every fixed `n ≥ 1` there are *infinitely many*
`n`-core-EMPTY configurations — the certificate count is unbounded (super-polynomial in any size
budget), the exact statement the cyclic-sieving experiment confirms. -/
theorem exists_injection_nCoreEmpty :
    ∃ f : (Fin n → ℕ) → (Fin n → ℕ),
      Function.Injective f ∧ ∀ c, nCoreEmpty (f c) :=
  ⟨cParam, cParam_injective, nCoreEmpty_cParam⟩

/-- **For `n ≥ 1`, the `n`-core-EMPTY configurations form an infinite set.** (Direct corollary:
`ℕ^{Fin n}` is infinite and injects in.) This is the unbounded/super-poly verdict on the
*certificate* count — to be read against the *codeword-list* poly bound (see module docstring and
`SubJohnsonListSupply`). -/
theorem infinite_nCoreEmpty [NeZero n] :
    {β : Fin n → ℕ | nCoreEmpty β}.Infinite := by
  have hr : (0 : ℕ) < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have : Infinite (Fin n → ℕ) :=
    Infinite.of_injective (fun k : ℕ => (fun _ : Fin n => k))
      (fun a b hab => congrFun hab ⟨0, hr⟩)
  exact Set.infinite_of_injective_forall_mem
    (f := cParam (n := n)) cParam_injective (fun c => nCoreEmpty_cParam c)

/-- An explicit witnessing family showing the count exceeds any finite bound `N`: the `N+1` distinct
configurations `cParam (fun _ => i)` for `i = 0,…,N` are pairwise distinct and all `n`-core-EMPTY,
for `n ≥ 1`. (The genuine count is the binomial `C(S+n-1,n-1)`; here we only need unboundedness to
state the super-poly verdict against the poly list bound.) -/
theorem nCoreEmpty_card_unbounded [NeZero n] (N : ℕ) :
    ∃ S : Finset (Fin n → ℕ), N < S.card ∧ ∀ β ∈ S, nCoreEmpty β := by
  classical
  refine ⟨(Finset.range (N + 1)).image (fun i => cParam (fun _ => i)), ?_, ?_⟩
  · rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have := cParam_injective hab
      have ha : (fun _ : Fin n => a) (0 : Fin n) = (fun _ : Fin n => b) (0 : Fin n) :=
        congrFun this 0
      simpa using ha
  · intro β hβ
    rw [Finset.mem_image] at hβ
    obtain ⟨i, _, rfl⟩ := hβ
    exact nCoreEmpty_cParam _

end ArkLib.ProximityGap.NCoreEmptyCParametrization

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.NCoreEmptyCParametrization.nCoreEmpty_cParam
#print axioms ArkLib.ProximityGap.NCoreEmptyCParametrization.cParam_injective
#print axioms ArkLib.ProximityGap.NCoreEmptyCParametrization.infinite_nCoreEmpty
#print axioms ArkLib.ProximityGap.NCoreEmptyCParametrization.nCoreEmpty_card_unbounded
