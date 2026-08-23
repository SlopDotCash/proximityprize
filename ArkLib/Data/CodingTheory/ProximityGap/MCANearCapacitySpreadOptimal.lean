/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCANearCapacitySharpSpread

/-!
# Optimality of the arithmetic-domain near-capacity spread (Proximity Prize, #232)

`MCANearCapacitySharpSpread.lean` proved the lower bound `ε_mca ≥ ((k+1)(n-k-1)+1)/|F|` by *realizing*
`(k+1)(n-k-1)+1` windows with distinct node-sums on the arithmetic domain `{0,…,n-1}`. Its docstring
claims this is **tight** — no `(k+1)`-window family on `{0,…,n-1}` can do better. This file proves
that matching **upper bound**, turning the claim into a theorem:

* `subsetSum_ge` — every `m`-subset of `{0,…,n-1}` has node-sum `≥ 0+1+⋯+(m-1)` (the `m` smallest),
  via the strictly-monotone enumeration `Finset.orderEmbOfFin`.
* `subsetSum_mem_Icc` — hence every `(k+1)`-subset sum lies in `[T, U]`, `T = ∑_{j<k+1} j`,
  `U = (∑_{i<n} i) − ∑_{j<n-k-1} j` (the upper end via the lower bound on the *complement*).
* `card_arithmeticSpread_le` — the number of distinct `(k+1)`-subset sums of `{0,…,n-1}` is at most
  `(k+1)(n-k-1)+1`, the length of `[T, U]`.

Combined with the realization in `MCANearCapacitySharpSpread`, the arithmetic-domain MCA witness
spread is **exactly** `(k+1)(n-k-1)+1`: the single-line, single-domain method tops out precisely
there. (Breaking past this needs an exponential spread — distinct subset sums on a Sidon domain would
require `q ≳ n^{k+1}`, which cancels the gain — so the open prize lives genuinely beyond this ceiling,
via multiplicity / Guruswami–Sudan.)

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232 / #141.
-/

open BigOperators

namespace ProximityGap.MCANearCapacitySpreadOptimal

/-! ## A strictly monotone `Fin m → ℕ` dominates the identity -/

/-- For a strictly monotone `f : Fin m → ℕ`, `f j ≥ j` (the `j`-th value is at least `j`). -/
theorem fin_val_le_strictMono {m : ℕ} {f : Fin m → ℕ} (hf : StrictMono f) (j : Fin m) :
    (j : ℕ) ≤ f j := by
  suffices H : ∀ jv (h : jv < m), jv ≤ f ⟨jv, h⟩ by
    obtain ⟨jv, hjv⟩ := j; exact H jv hjv
  intro jv
  induction jv with
  | zero => intro _; exact Nat.zero_le _
  | succ i ih =>
    intro h
    have hi : i < m := by omega
    have hlt : f ⟨i, hi⟩ < f ⟨i + 1, h⟩ := hf (Fin.mk_lt_mk.mpr (by omega))
    have hib := ih hi
    omega

/-! ## Extremal subset sums over `{0,…,n-1}` -/

variable {n : ℕ}

/-- The total node-sum over all of `Fin n` is `0+1+⋯+(n-1)`. -/
theorem total_sum : (∑ i : Fin n, (i : ℕ)) = ∑ j ∈ Finset.range n, j := by
  simpa using Fin.sum_univ_eq_sum_range (fun x => x) n

/-- **Lower extremal bound.** The node-sum of any `m`-subset of `Fin n` is at least the sum of the
`m` smallest nodes `0+1+⋯+(m-1)`. -/
theorem subsetSum_ge (S : Finset (Fin n)) :
    (∑ j ∈ Finset.range S.card, j) ≤ ∑ i ∈ S, (i : ℕ) := by
  set m := S.card with hm
  have hmap : (∑ i ∈ S, (i : ℕ)) = ∑ j : Fin m, ((S.orderEmbOfFin hm.symm j : Fin n) : ℕ) := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ S hm.symm]
    rw [Finset.sum_map]
    rfl
  have hsm : StrictMono (fun j : Fin m => ((S.orderEmbOfFin hm.symm j : Fin n) : ℕ)) :=
    Fin.val_strictMono.comp (S.orderEmbOfFin hm.symm).strictMono
  rw [hmap, ← Fin.sum_univ_eq_sum_range (fun x => x) m]
  exact Finset.sum_le_sum (fun j _ => fin_val_le_strictMono hsm j)

/-- **Two-sided bound.** Every `(k+1)`-subset sum lies in `[T, U]` with `T = ∑_{j<k+1} j` and
`U = (∑_{i<n} i) − ∑_{j<n-k-1} j`. -/
theorem subsetSum_mem_Icc {k : ℕ} (S : Finset (Fin n)) (hS : S.card = k + 1) :
    (∑ j ∈ Finset.range (k + 1), j) ≤ ∑ i ∈ S, (i : ℕ) ∧
      (∑ i ∈ S, (i : ℕ))
        ≤ (∑ j ∈ Finset.range n, j) - ∑ j ∈ Finset.range (n - (k + 1)), j := by
  refine ⟨?_, ?_⟩
  · have := subsetSum_ge S; rwa [hS] at this
  · have hpart : (∑ i ∈ S, (i : ℕ)) + ∑ i ∈ Sᶜ, (i : ℕ) = ∑ i : Fin n, (i : ℕ) :=
      Finset.sum_add_sum_compl S _
    have hcompl_card : Sᶜ.card = n - (k + 1) := by
      rw [Finset.card_compl, hS, Fintype.card_fin]
    have hge : (∑ j ∈ Finset.range (n - (k + 1)), j) ≤ ∑ i ∈ Sᶜ, (i : ℕ) := by
      have := subsetSum_ge Sᶜ; rwa [hcompl_card] at this
    rw [total_sum] at hpart
    omega

/-! ## The interval length is `(k+1)(n-k-1)+1` -/

/-- Telescoping identity: `∑_{i<k+1+t} i = ∑_{i<t} i + ∑_{i<k+1} i + (k+1)·t`. -/
theorem sum_range_split (k : ℕ) :
    ∀ t, (∑ i ∈ Finset.range (k + 1 + t), i)
        = (∑ i ∈ Finset.range t, i) + (∑ i ∈ Finset.range (k + 1), i) + (k + 1) * t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show k + 1 + (t + 1) = (k + 1 + t) + 1 by ring, Finset.sum_range_succ, ih,
      Finset.sum_range_succ (n := t), Nat.mul_succ]
    omega

/-- The interval `[T, U]` has length `(k+1)(n-k-1)`. -/
theorem Icc_length {k : ℕ} (hkn : k + 1 ≤ n) :
    ((∑ j ∈ Finset.range n, j) - ∑ j ∈ Finset.range (n - (k + 1)), j)
        - (∑ j ∈ Finset.range (k + 1), j) = (k + 1) * (n - 1 - k) := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hkn
  subst ht
  have hn1 : k + 1 + t - (k + 1) = t := by omega
  have hn2 : k + 1 + t - 1 - k = t := by omega
  rw [hn1, hn2, sum_range_split k t]
  omega

/-! ## The spread is at most the interval length -/

/-- **Upper bound on the spread.** The number of distinct `(k+1)`-subset sums of `{0,…,n-1}` is at
most `(k+1)(n-k-1)+1` — the matching ceiling for the arithmetic-domain MCA witness spread, so the
realization in `MCANearCapacitySharpSpread.epsMCA_sharp_ge` is tight. -/
theorem card_arithmeticSpread_le {k : ℕ} (hkn : k + 1 ≤ n) :
    ((Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin n))).image
        (fun S : Finset (Fin n) => ∑ i ∈ S, (i : ℕ))).card ≤ (k + 1) * (n - 1 - k) + 1 := by
  set T : ℕ := ∑ j ∈ Finset.range (k + 1), j with hT
  set U : ℕ := (∑ j ∈ Finset.range n, j) - ∑ j ∈ Finset.range (n - (k + 1)), j with hU
  have hsub : (Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin n))).image
      (fun S : Finset (Fin n) => ∑ i ∈ S, (i : ℕ)) ⊆ Finset.Icc T U := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨S, hS, rfl⟩ := hx
    rw [Finset.mem_powersetCard] at hS
    rw [Finset.mem_Icc]
    exact subsetSum_mem_Icc S hS.2
  -- a witness window shows the interval is non-empty, hence `T ≤ U`
  have hTU : T ≤ U := by
    obtain ⟨S, hS⟩ := (Finset.powersetCard_nonempty (n := k + 1)
      (s := (Finset.univ : Finset (Fin n)))).mpr (by rw [Finset.card_univ, Fintype.card_fin]; exact hkn)
    rw [Finset.mem_powersetCard] at hS
    exact le_trans (subsetSum_mem_Icc S hS.2).1 (subsetSum_mem_Icc S hS.2).2
  calc ((Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin n))).image
          (fun S : Finset (Fin n) => ∑ i ∈ S, (i : ℕ))).card
      ≤ (Finset.Icc T U).card := Finset.card_le_card hsub
    _ = U + 1 - T := Nat.card_Icc T U
    _ = (k + 1) * (n - 1 - k) + 1 := by
        have h := Icc_length (n := n) hkn
        rw [← hU, ← hT] at h
        omega

#print axioms subsetSum_ge
#print axioms subsetSum_mem_Icc
#print axioms card_arithmeticSpread_le

end ProximityGap.MCANearCapacitySpreadOptimal
