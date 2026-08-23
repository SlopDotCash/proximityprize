/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ExplainableCoreExactCount

/-!
# The structured-word core dichotomy: the per-word supply is all-or-nothing

Issue #389, resolving the architecture of the supply route. The reduction theorem
`deep_band_badSet_card_of_supply` only ever invokes the supply at the **structured words**
`w = Q.eval` (a polynomial evaluation of degree `≤ k+m` — the generated-stack rows and their
bad-scalar-line shifts `Q₀ + γ·xᵏ`). For such words the explainable-core count is governed by
a sharp **degree dichotomy**, not a subexponential bound:

> **`structuredWord_no_deep_cores`** — if `k ≤ deg Q ≤ k+m` and `k+m+1 ≤ n`, the explainable
> `(k+m+1)`-cores of `Q.eval` are **exactly empty**.
>
> **`structuredWord_all_cores`** — if `deg Q < k`, then `Q.eval` is a codeword and **every**
> `(k+m+1)`-core is explainable (count `C(n, k+m+1)`).

The mechanism: a degree-`< k` codeword agreeing with `Q.eval` on `≥ k+m+1` points forces
`(codeword − Q)` — of degree `≤ k+m` — to vanish on `k+m+1` distinct points, hence to be the
zero polynomial; so the codeword equals `Q`, impossible once `deg Q ≥ k`.

**Consequence (a refutation, not a closure).** The per-word explainable-core supply `B` of the
words that actually arise is therefore **all-or-nothing**: `0` when `Q` carries genuine
deep-band degree, `C(n,k+m+1)` when `Q` collapses to a codeword. It is never
"subexponential-and-positive", so the original per-word-core supply route
(`deep_band_badSet_card_of_supply`) **cannot by itself prove a strong (large-`#badSet`)
deep-band failure** — when it is positive it is maximal, giving only `#badSet ≥ 1`. The strong
failure necessarily comes from the *second-moment* route (`DeepBandSecondMoment.lean`,
`deep_band_failure_closed_form`), which counts *distinct* coherent-core values rather than a
single word's cores. This pins precisely why the supply framing had to be replaced by the
moment framing. (DISPROOF_LOG 2026-06-13.)

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
/-- **Structured words of genuine deep-band degree have no deep explainable cores.** If
`k ≤ deg Q ≤ k+m` and `k+m+1 ≤ n`, then `Q.eval` admits no explainable `(k+m+1)`-core. -/
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
      simp only [] at e
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
