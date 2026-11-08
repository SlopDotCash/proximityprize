/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ExplainableCoreExactCount

/-!
# The low-degree structured-word core dichotomy

Issue #389, on the architecture of the supply route. The reduction theorem
`deep_band_badSet_card_of_supply` invokes the supply at the words `w = (Q₀ + γ·Xᵏ).eval`, where
`Q₀` is the polynomial produced by `DeepBandCoherence.deep_band_witness_mass`.

**Scope caveat (degree range of the actual generator).** The generator in
`deep_band_witness_mass` takes `Q₀ = ∑_{j < M} c_j Xʲ` with `M = 2k+m+2`, so `deg Q₀` can be as
large as `2k+m+1`; neither `deep_band_witness_mass` nor `deep_band_badSet_card_of_supply`
imposes `deg Q₀ ≤ k+m`. The theorems below are proved **only** for words of degree `≤ k+m`
(resp. `< k`), so they do not describe every word the supply route actually consumes.

For words of degree `≤ k+m` the explainable-core count obeys a sharp **degree dichotomy**:

> **`structuredWord_no_deep_cores`** — if `k ≤ deg Q ≤ k+m` and `k+m+1 ≤ n`, the explainable
> `(k+m+1)`-cores of `Q.eval` are **exactly empty**.
>
> **`structuredWord_all_cores`** — if `deg Q < k`, then `Q.eval` is a codeword and **every**
> `(k+m+1)`-core is explainable (count `C(n, k+m+1)`).

The mechanism: a degree-`< k` codeword agreeing with `Q.eval` on `≥ k+m+1` points forces
`(codeword − Q)` — of degree `≤ k+m` — to vanish on `k+m+1` distinct points, hence to be the
zero polynomial; so the codeword equals `Q`, impossible once `deg Q ≥ k`.

**Consequence, restricted to degree `≤ k+m`.** For a word `Q.eval` with `deg Q ≤ k+m` (and
`k+m+1 ≤ n`), the explainable-core count is **all-or-nothing**: `0` when `k ≤ deg Q`, and
`C(n,k+m+1)` when `deg Q < k`. It is never "subexponential-and-positive" in that range.

This does **not** show that the supply route is all-or-nothing on the words the generator
actually produces, because `deg Q₀` may lie in `(k+m, 2k+m+1]`, where the dichotomy fails.
Concrete example: on the full domain of `F₇` with `k = 2`, `m = 0`, `Q = X³` (degree
`3 ≤ 2k+m+1 = 5`), a 3-subset is explainable by an affine polynomial exactly when its elements
sum to `0`; translation by `c ∈ F₇` permutes triples and shifts the sum by `3c`, so `5` of the
`35` triples are explainable — neither `0` nor all. (This does not claim the existential
witness `Q₀` of `deep_band_witness_mass` is `X³`.) Hence the earlier claim that the per-word
supply route "cannot by itself prove a strong deep-band failure" is **not established** by
this file; it holds only under the extra hypothesis `deg Q₀ ≤ k+m`, which the generator does not
provide. The uncapped uniform supply hypothesis `ExplainableCoreSupply` has its own separate
obstruction (audit finding PG-079). The second-moment route (`DeepBandSecondMoment.lean`,
`deep_band_failure_closed_form`), which counts distinct coherent-core values, is an independent
route and is unaffected. (Originally recorded in DISPROOF_LOG 2026-06-13; scope corrected per
audit finding PG-140.)

## References

* Issue #389; `DeepBandMultiplicity.lean` (`deep_band_badSet_card_of_supply`,
  `ExplainableOn`), `ExplainableCoreExactCount.lean`, `LineListDimensionLift.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **Words of degree in `[k, k+m]` have no deep explainable cores.** If
`k ≤ deg Q ≤ k+m` and `k+m+1 ≤ n`, then `Q.eval` admits no explainable `(k+m+1)`-core.
The upper bound `deg Q ≤ k+m` is essential and is not supplied by the deep-band generator,
whose polynomials can have degree up to `2k+m+1` (see the module docstring). -/
theorem structuredWord_no_deep_cores (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    {Q : F[X]} (hkdeg : k ≤ Q.natDegree) (hdeg : Q.natDegree ≤ k + m)
    (hn : k + m + 1 ≤ n) :
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn dom k (fun i => Q.eval (dom i)) T)) = ∅ := by
  classical
  rw [Finset.filter_eq_empty_iff]
  intro T hT hexp
  obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
  obtain ⟨c, hc, hcw⟩ := hexp
  obtain ⟨Pc, hPcdeg, hPcev⟩ := hc
  -- the difference polynomial vanishes on dom(T) (k+m+1 points) and has degree ≤ k+m
  set D : F[X] := Pc - Q with hD
  have hDvanish : ∀ i ∈ T, D.eval (dom i) = 0 := by
    intro i hi
    have key : Pc.eval (dom i) = Q.eval (dom i) := by
      have e := congrFun hPcev i
      rw [← e]; exact hcw i hi
    rw [hD, Polynomial.eval_sub, key]; ring
  have hDdeg : D.degree < ((k + m + 1 : ℕ) : WithBot ℕ) := by
    have hPc' : Pc.degree < ((k + m + 1 : ℕ) : WithBot ℕ) :=
      lt_of_lt_of_le hPcdeg (by exact_mod_cast by omega : ((k : ℕ) : WithBot ℕ) ≤ ((k+m+1 : ℕ) : WithBot ℕ))
    have hQ' : Q.degree < ((k + m + 1 : ℕ) : WithBot ℕ) := by
      have := Polynomial.degree_le_natDegree (p := Q)
      calc Q.degree ≤ (Q.natDegree : WithBot ℕ) := this
        _ ≤ ((k + m : ℕ) : WithBot ℕ) := by exact_mod_cast hdeg
        _ < ((k + m + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self _
    calc D.degree ≤ max Pc.degree Q.degree := Polynomial.degree_sub_le _ _
      _ < ((k + m + 1 : ℕ) : WithBot ℕ) := max_lt hPc' hQ'
  -- a poly of degree < |T| vanishing on dom(T) is zero
  have hD0 : D = 0 := by
    by_contra hne
    have hdomroots : T.image (fun i => dom i) ⊆ D.roots.toFinset := by
      intro x hx
      obtain ⟨i, hiT, rfl⟩ := Finset.mem_image.mp hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hDvanish i hiT
    have hle : (k + m + 1 : ℕ) ≤ D.natDegree := by
      calc k + m + 1 = T.card := hTcard.symm
        _ = (T.image (fun i => dom i)).card :=
            (Finset.card_image_of_injective _ dom.injective).symm
        _ ≤ D.roots.toFinset.card := Finset.card_le_card hdomroots
        _ ≤ Multiset.card D.roots := Multiset.toFinset_card_le _
        _ ≤ D.natDegree := Polynomial.card_roots' _
    have hnd : D.natDegree < k + m + 1 :=
      (Polynomial.natDegree_lt_iff_degree_lt hne).mpr hDdeg
    omega
  -- D = 0 ⟹ Pc = Q ⟹ deg Q < k, contradicting k ≤ deg Q
  have hPcQ : Pc = Q := sub_eq_zero.mp (hD ▸ hD0)
  have hQne : Q ≠ 0 := by
    rintro rfl
    simp only [Polynomial.natDegree_zero] at hkdeg
    omega
  have hQk : Q.natDegree < k := by
    rw [← hPcQ]
    exact (Polynomial.natDegree_lt_iff_degree_lt (hPcQ ▸ hQne)).mpr hPcdeg
  omega

open Classical in
/-- **Low-degree structured words are codewords: every core is explainable.** If `deg Q < k`
then `Q.eval ∈ rsCode dom k`, so all `(k+m+1)`-cores are explainable. -/
theorem structuredWord_all_cores (dom : Fin n ↪ F) {k m : ℕ}
    {Q : F[X]} (hdeg : Q.degree < (k : ℕ)) :
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn dom k (fun i => Q.eval (dom i)) T))
      = (Finset.univ : Finset (Fin n)).powersetCard (k + m + 1) := by
  classical
  rw [Finset.filter_eq_self]
  intro T _
  exact ⟨fun i => Q.eval (dom i), ⟨Q, hdeg, rfl⟩, fun i _ => rfl⟩

/-! ## Source audit -/

#print axioms structuredWord_no_deep_cores
#print axioms structuredWord_all_cores

end ProximityGap.Ownership
