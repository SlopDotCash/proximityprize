/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# GCXK25 second-moment counting core (verified backbone of GCXK25 Lemma 3)

This file isolates and proves, **kernel-clean**, the second-moment counting argument that
sits at the heart of [GCXK25] *From List-Decodability to Proximity Gaps* (Gao, Cai, Xu,
Kan; eprint 2025/870). It is the in-tree-provable combinatorial backbone of the bound

  `ε_mca(C, 1 − √(1 − δ + η)) ≤ (L²·δ·n + 1/η)/|F|`

stated (as an external admit) in
`CodingTheory.linear_listSize_to_epsMCA_gcxk25` (ABF26 Theorem 5.1 = GCXK25 Theorem 3),
in `Connections/ListDecodingAndCA.lean`.

## What GCXK25 prove and how this file fits

GCXK25 partition the "bad combining points" `Bad(π₁,π₂,δ)` of a `(p,L)`-list-decodable
linear code into two parts and bound each:

* `|Bad¹| ≤ p·n` — the per-domain disjointness count (their Corollary 2, via the
  GKL24 agree-domain intersection Lemma 1 / Corollary 1).
* `|Bad²| < 1/ε` — the **second-moment / Cauchy–Schwarz count** (their Lemma 3).

This file formalizes the second of these two and, with the `L² ≤` list-size factor, gives
the `L²pn + 1/ε` shape. Concretely, the elements of `Bad²` come with `δ`-agreement domains
`A_α ⊆ [n]` that are

* **large**: `|A_α| ≥ √(1−p+ε)·n` (a bad point is at least `δ = 1−√(1−p+ε)`-close), and
* **pairwise almost disjoint**: `|A_α ∩ A_β| ≤ (1−p)·n` for distinct `α, β`
  (two distinct large agree-domains can share at most `(1−p)·n` coordinates,
  else they would coincide by unique decoding).

GCXK25 count over the coordinates `x ∈ [n]` with multiplicities `d(x) = #{α : x ∈ A_α}`,
apply Cauchy–Schwarz `(∑ d(x))² ≤ n·∑ d(x)²`, and conclude `|Bad²| < 1/ε`. We reproduce
this exactly, abstractly over an arbitrary finite family of subsets.

## Main results

* `sum_card_eq_sum_mult` — double counting: `∑_α |A_α| = ∑_x d(x)`.
* `sum_sum_card_inter_eq_sum_mult_sq` — second moment: `∑_α ∑_β |A_α ∩ A_β| = ∑_x d(x)²`.
* `sq_sum_card_le_card_mul_sum_sum_card_inter` — the Cauchy–Schwarz step
  `(∑_α |A_α|)² ≤ n·∑_α∑_β |A_α ∩ A_β|`.
* `card_le_of_second_moment` — the master real inequality `N·S² ≤ n·(S + (N−1)·B)`
  from "all members `≥ S`, all distinct pairwise intersections `≤ B`".
* `card_lt_inv_of_second_moment_rs` — the GCXK25 Lemma 3 specialization
  `|T|·ε < 1` (i.e. `|T| < 1/ε`) at `S = √(1−p+ε)·n`, `B = (1−p)·n`, under `ε ≤ p < 1`.
  The `ε ≤ p` hypothesis is exactly the `η ≤ δ` constraint already added to
  `linear_listSize_to_epsMCA_gcxk25` (so that `1 − √(1−δ+η)` stays in `[0,1]`).
* `card_lt_one_div_of_second_moment_rs` — the same result in the direct reciprocal form
  `|T| < 1 / ε`, matching the usual Lemma 3 statement.

## What this file does *not* close

The target `linear_listSize_to_epsMCA_gcxk25` remains an external admit. Bridging this
counting core to it additionally requires (neither in-tree):

1. the GKL24 maximal-correlated-agree-domain intersection lemma and the `|Bad¹| ≤ pn`
   per-domain count (the `Bad`-set / `A_{δ,{π₁,π₂},C}` machinery is not connected to
   ArkLib's `Lambda` / `epsMCA`); and
2. the reduction from ArkLib's `epsMCA` (a supremum over **arbitrary** word stacks `u`,
   with the single-witness-set `mcaEvent` of ABF26 Definition 4.3) to GCXK25's
   per-**codeword-pair** `Bad(π₁,π₂,δ)` count — the content of ABF26 §5.

This file is the verified piece; those two are the genuinely external pieces.

## References

* [GCXK25] Gao, Cai, Xu, Kan. *From List-Decodability to Proximity Gaps*. eprint 2025/870.
  Theorem 3, Lemma 3, Corollary 2.
* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. Theorem 5.1.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace GCXK25SecondMoment

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [DecidableEq κ]

/-- Per-coordinate multiplicity: how many of the sets `A α` (for `α ∈ T`) contain `x`. -/
noncomputable def mult (T : Finset κ) (A : κ → Finset ι) (x : ι) : ℕ :=
  (T.filter (fun α => x ∈ A α)).card

theorem mult_eq_sum (T : Finset κ) (A : κ → Finset ι) (x : ι) :
    mult T A x = ∑ α ∈ T, (if x ∈ A α then 1 else 0) := by
  classical
  unfold mult
  rw [Finset.card_filter]

theorem card_eq_sum_indicator (s : Finset ι) :
    s.card = ∑ x : ι, (if x ∈ s then 1 else 0) := by
  classical
  rw [← Finset.card_filter (· ∈ s) univ]
  congr 1
  ext x
  simp

/-- **Double counting (rows = columns).** Total size of the family equals the sum of
per-coordinate multiplicities. -/
theorem sum_card_eq_sum_mult (T : Finset κ) (A : κ → Finset ι) :
    ∑ α ∈ T, (A α).card = ∑ x : ι, mult T A x := by
  classical
  have hL : ∑ α ∈ T, (A α).card
      = ∑ α ∈ T, ∑ x : ι, (if x ∈ A α then 1 else 0) :=
    Finset.sum_congr rfl (fun α _ => card_eq_sum_indicator (A α))
  have hR : ∑ x : ι, mult T A x
      = ∑ x : ι, ∑ α ∈ T, (if x ∈ A α then 1 else 0) :=
    Finset.sum_congr rfl (fun x _ => mult_eq_sum T A x)
  rw [hL, hR, Finset.sum_comm]

/-- **Second moment = pairwise intersections.** `∑_α ∑_β |A_α ∩ A_β| = ∑_x d(x)²`. -/
theorem sum_sum_card_inter_eq_sum_mult_sq (T : Finset κ) (A : κ → Finset ι) :
    ∑ α ∈ T, ∑ β ∈ T, (A α ∩ A β).card = ∑ x : ι, (mult T A x) ^ 2 := by
  classical
  have hinter : ∀ α β : κ, (A α ∩ A β).card
      = ∑ x : ι, (if x ∈ A α then 1 else 0) * (if x ∈ A β then 1 else 0) := by
    intro α β
    rw [card_eq_sum_indicator (A α ∩ A β)]
    refine Finset.sum_congr rfl ?_
    intro x _
    by_cases ha : x ∈ A α <;> by_cases hb : x ∈ A β <;>
      simp [Finset.mem_inter, ha, hb]
  calc ∑ α ∈ T, ∑ β ∈ T, (A α ∩ A β).card
      = ∑ α ∈ T, ∑ β ∈ T, ∑ x : ι,
          (if x ∈ A α then 1 else 0) * (if x ∈ A β then 1 else 0) := by
        refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => hinter α β))
    _ = ∑ α ∈ T, ∑ x : ι, ∑ β ∈ T,
          (if x ∈ A α then 1 else 0) * (if x ∈ A β then 1 else 0) := by
        refine Finset.sum_congr rfl ?_
        intro α _
        rw [Finset.sum_comm]
    _ = ∑ x : ι, ∑ α ∈ T, ∑ β ∈ T,
          (if x ∈ A α then 1 else 0) * (if x ∈ A β then 1 else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ x : ι, (∑ α ∈ T, (if x ∈ A α then 1 else 0))
          * (∑ β ∈ T, (if x ∈ A β then 1 else 0)) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [Finset.sum_mul_sum]
    _ = ∑ x : ι, (mult T A x) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [mult_eq_sum, sq]

/-- **Cauchy–Schwarz / Chebyshev second-moment bound (ℕ form).** The square of the total
size of the family is at most `n` times the sum of all pairwise intersection sizes. This
is the first inequality `(5)–(6)` of the GCXK25 second-moment count, packaged over the
ambient coordinate set `ι` (so the union bound `r ≤ n` is automatic). -/
theorem sq_sum_card_le_card_mul_sum_sum_card_inter (T : Finset κ) (A : κ → Finset ι) :
    (∑ α ∈ T, (A α).card) ^ 2
      ≤ Fintype.card ι * ∑ α ∈ T, ∑ β ∈ T, (A α ∩ A β).card := by
  classical
  rw [sum_card_eq_sum_mult, sum_sum_card_inter_eq_sum_mult_sq]
  have hcs : (∑ x : ι, mult T A x) ^ 2 ≤ (univ : Finset ι).card * ∑ x : ι, (mult T A x) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  simpa [Finset.card_univ] using hcs

/-- The total second moment splits into the diagonal (`∑ |A α|`) plus the off-diagonal
pairwise intersections. -/
theorem sum_sum_card_inter_eq_diag_add_offdiag (T : Finset κ) (A : κ → Finset ι) :
    ∑ α ∈ T, ∑ β ∈ T, (A α ∩ A β).card
      = ∑ α ∈ T, (A α).card
        + ∑ α ∈ T, ∑ β ∈ T.erase α, (A α ∩ A β).card := by
  classical
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro α hα
  rw [← Finset.sum_erase_add T _ hα, Finset.inter_self, add_comm]

/-- **Off-diagonal pairwise bound (ℕ form).** If every distinct pair `α ≠ β` (both in `T`)
has `|A α ∩ A β| ≤ B`, the off-diagonal sum is at most `N·(N-1)·B`, where `N = |T|`. -/
theorem offdiag_le (T : Finset κ) (A : κ → Finset ι) {B : ℕ}
    (hB : ∀ α ∈ T, ∀ β ∈ T, α ≠ β → (A α ∩ A β).card ≤ B) :
    ∑ α ∈ T, ∑ β ∈ T.erase α, (A α ∩ A β).card ≤ T.card * (T.card - 1) * B := by
  classical
  calc ∑ α ∈ T, ∑ β ∈ T.erase α, (A α ∩ A β).card
      ≤ ∑ α ∈ T, ∑ _β ∈ T.erase α, B := by
        refine Finset.sum_le_sum ?_
        intro α hα
        refine Finset.sum_le_sum ?_
        intro β hβ
        exact hB α hα β (Finset.mem_of_mem_erase hβ) (Finset.ne_of_mem_erase hβ).symm
    _ = ∑ α ∈ T, (T.card - 1) * B := by
        refine Finset.sum_congr rfl ?_
        intro α hα
        rw [Finset.sum_const, Finset.card_erase_of_mem hα, smul_eq_mul]
    _ = T.card * (T.card - 1) * B := by
        rw [Finset.sum_const, smul_eq_mul, mul_assoc]

/-- **GCXK25 second-moment master inequality (real form).** Let `T` be a nonempty index
set with `N := |T|` members, and `A : κ → Finset ι` a family of subsets of an ambient
coordinate set of size `n`. Suppose

* each member is large: `S ≤ |A α|` for all `α ∈ T` (with `S ≥ 0`);
* distinct members overlap little: `|A α ∩ A β| ≤ B` for all distinct `α, β ∈ T`.

Then
`N · S² ≤ n · (S + (N − 1) · B)`.

This is the inequality the GCXK25 proof of Lemma 3 extracts from Cauchy–Schwarz right
before substituting the Reed–Solomon values `S = √(1−p+ε)·n`, `B = (1−p)·n` (which then
yield `N < 1/ε`). Proven via the double-counting identities, the Chebyshev/Cauchy–Schwarz
second-moment bound, the off-diagonal pairwise cap, and the monotonicity of `s ↦ s²/(s+c)`
(`s = ∑ |A α| ≥ N·S`, `c = N(N−1)B`). -/
theorem card_le_of_second_moment
    (T : Finset κ) (A : κ → Finset ι) (hT : T.Nonempty)
    (S B : ℝ) (hS0 : 0 ≤ S) (hB0 : 0 ≤ B)
    (hSle : ∀ α ∈ T, S ≤ (A α).card)
    (hBle : ∀ α ∈ T, ∀ β ∈ T, α ≠ β → ((A α ∩ A β).card : ℝ) ≤ B) :
    (T.card : ℝ) * S ^ 2
      ≤ (Fintype.card ι : ℝ) * (S + ((T.card : ℝ) - 1) * B) := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  set N : ℝ := (T.card : ℝ) with hNdef
  set s : ℝ := ((∑ α ∈ T, (A α).card : ℕ) : ℝ) with hs
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hNdef]; exact_mod_cast hT.card_pos
  have hn0 : 0 ≤ n := by rw [hn]; exact_mod_cast Nat.zero_le _
  -- Cauchy–Schwarz second moment: s² ≤ n · (total pairwise intersection).
  have hcs : s ^ 2 ≤ n * ((∑ α ∈ T, ∑ β ∈ T, (A α ∩ A β).card : ℕ) : ℝ) := by
    have := sq_sum_card_le_card_mul_sum_sum_card_inter T A
    have hcast : (((∑ α ∈ T, (A α).card) ^ 2 : ℕ) : ℝ)
        ≤ ((Fintype.card ι * ∑ α ∈ T, ∑ β ∈ T, (A α ∩ A β).card : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [hs, hn]; push_cast at hcast ⊢; linarith [hcast]
  -- Split the pairwise total into diagonal + off-diagonal.
  have hsplit : ((∑ α ∈ T, ∑ β ∈ T, (A α ∩ A β).card : ℕ) : ℝ)
      = s + ((∑ α ∈ T, ∑ β ∈ T.erase α, (A α ∩ A β).card : ℕ) : ℝ) := by
    rw [sum_sum_card_inter_eq_diag_add_offdiag]; push_cast [hs]; ring
  -- Off-diagonal ≤ N·(N-1)·B  (over reals).
  have hoff : ((∑ α ∈ T, ∑ β ∈ T.erase α, (A α ∩ A β).card : ℕ) : ℝ)
      ≤ N * (N - 1) * B := by
    calc ((∑ α ∈ T, ∑ β ∈ T.erase α, (A α ∩ A β).card : ℕ) : ℝ)
        = ∑ α ∈ T, ∑ β ∈ T.erase α, ((A α ∩ A β).card : ℝ) := by push_cast; ring
      _ ≤ ∑ α ∈ T, ∑ _β ∈ T.erase α, B := by
            refine Finset.sum_le_sum ?_
            intro α hα
            refine Finset.sum_le_sum ?_
            intro β hβ
            exact hBle α hα β (Finset.mem_of_mem_erase hβ) (Finset.ne_of_mem_erase hβ).symm
      _ = ∑ α ∈ T, ((T.card - 1 : ℕ) : ℝ) * B := by
            refine Finset.sum_congr rfl ?_
            intro α hα
            rw [Finset.sum_const, Finset.card_erase_of_mem hα, nsmul_eq_mul]
      _ = N * (N - 1) * B := by
            rw [Finset.sum_const, nsmul_eq_mul]
            have hcard : ((T.card - 1 : ℕ) : ℝ) = N - 1 := by
              rw [hNdef, Nat.cast_sub hT.card_pos]; norm_num
            rw [hcard, hNdef]; ring
  -- Lower bound on the diagonal: s ≥ N·S.
  have hslow : N * S ≤ s := by
    rw [hs, hNdef]
    have hconst : (T.card : ℝ) * S = ∑ _α ∈ T, S := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    calc (∑ _α ∈ T, S) ≤ ∑ α ∈ T, ((A α).card : ℝ) :=
          Finset.sum_le_sum (fun α hα => hSle α hα)
      _ = ((∑ α ∈ T, (A α).card : ℕ) : ℝ) := by push_cast; ring
  -- Combine: s² ≤ n·(s + N(N-1)B).
  have hkey : s ^ 2 ≤ n * (s + N * (N - 1) * B) := by
    have h1 : ((∑ α ∈ T, ∑ β ∈ T, (A α ∩ A β).card : ℕ) : ℝ)
        ≤ s + N * (N - 1) * B := by rw [hsplit]; linarith [hoff]
    calc s ^ 2 ≤ n * ((∑ α ∈ T, ∑ β ∈ T, (A α ∩ A β).card : ℕ) : ℝ) := hcs
      _ ≤ n * (s + N * (N - 1) * B) := mul_le_mul_of_nonneg_left h1 hn0
  have hs0 : 0 ≤ s := le_trans (by positivity) hslow
  set c : ℝ := N * (N - 1) * B with hc
  have hc0 : 0 ≤ c := by
    rw [hc]; have : 0 ≤ N - 1 := by linarith
    positivity
  -- Monotonicity of `s ↦ s²/(s+c)`: from `s ≥ N·S` derive `(N·S)²(s+c) ≤ s²(N·S+c)`.
  have hmono : (N * S) ^ 2 * (s + c) ≤ s ^ 2 * (N * S + c) := by
    have hNS0 : 0 ≤ N * S := mul_nonneg (by linarith) hS0
    have hd1 : 0 ≤ s - N * S := by linarith
    have hd2 : 0 ≤ s * (N * S) + c * (s + N * S) :=
      add_nonneg (mul_nonneg hs0 hNS0) (mul_nonneg hc0 (by linarith))
    -- s²(NS+c) − (NS)²(s+c) = (s − NS)·(s·NS + c·(s + NS)) ≥ 0
    nlinarith [mul_nonneg hd1 hd2]
  -- Cancel `(s+c)` from `(NS)²(s+c) ≤ s²(NS+c) ≤ n(s+c)(NS+c)`.
  have hNSc0 : 0 ≤ N * S + c := by
    have : 0 ≤ N * S := mul_nonneg (by linarith) hS0
    linarith
  have hfinal : (N * S) ^ 2 ≤ n * (N * S + c) := by
    rcases lt_or_eq_of_le (by linarith : (0 : ℝ) ≤ s + c) with hsc | hsc
    · have hk2 : s ^ 2 * (N * S + c) ≤ n * (s + c) * (N * S + c) :=
        mul_le_mul_of_nonneg_right hkey hNSc0
      have chain : (N * S) ^ 2 * (s + c) ≤ (n * (N * S + c)) * (s + c) := by
        calc (N * S) ^ 2 * (s + c) ≤ s ^ 2 * (N * S + c) := hmono
          _ ≤ n * (s + c) * (N * S + c) := hk2
          _ = (n * (N * S + c)) * (s + c) := by ring
      exact le_of_mul_le_mul_right chain hsc
    · have hs00 : s = 0 := by linarith
      have hc00 : c = 0 := by linarith
      have hNS0 : N * S = 0 :=
        le_antisymm (by linarith [hslow]) (mul_nonneg (by linarith) hS0)
      rw [hNS0, hc00]; simp
  -- Expand `(NS)² ≤ n(NS + N(N−1)B) = nN(S + (N−1)B)` and cancel one factor `N`.
  have hNpos : 0 < N := by linarith
  have hfinal2 : N ^ 2 * S ^ 2 ≤ N * (n * (S + (N - 1) * B)) := by
    have hcfac : N * S + c = N * (S + (N - 1) * B) := by rw [hc]; ring
    rw [hcfac] at hfinal
    calc N ^ 2 * S ^ 2 = (N * S) ^ 2 := by ring
      _ ≤ n * (N * (S + (N - 1) * B)) := hfinal
      _ = N * (n * (S + (N - 1) * B)) := by ring
  refine le_of_mul_le_mul_left ?_ hNpos
  calc N * (N * S ^ 2) = N ^ 2 * S ^ 2 := by ring
    _ ≤ N * (n * (S + (N - 1) * B)) := hfinal2

/-- **GCXK25 Lemma 3 (second-moment count of bad second-part points).** Specialization of
`card_le_of_second_moment` to the Reed–Solomon values `S = √(1−p+ε)·n` (member lower bound:
a bad second-part point is at least `1−√(1−p+ε)`-close, so its `δ`-agreement domain has
`≥ √(1−p+ε)·n` coordinates) and `B = (1−p)·n` (distinct agreement domains share
`≤ (1−p)·n` coordinates). Under `0 < ε`, `ε ≤ p < 1`, and `0 < n`,

`|T| · ε < √(1−p+ε) − (1−p) + ε ≤ 1`,

i.e. `|T| < 1/ε`. This is exactly the bound `|Bad(π₁,π₂,δ)²| < 1/ε` of GCXK25 Lemma 3,
packaged abstractly over the agree-domain family `T`. The hypothesis `ε ≤ p` is the same
`η ≤ δ` constraint already imposed on `linear_listSize_to_epsMCA_gcxk25`. -/
theorem card_lt_inv_of_second_moment_rs
    (T : Finset κ) (A : κ → Finset ι) (hT : T.Nonempty)
    (p ε : ℝ) (hε : 0 < ε) (hεp : ε ≤ p) (hp1 : p < 1)
    (hn : 0 < Fintype.card ι)
    (hSle : ∀ α ∈ T, ((1 - p + ε) ^ ((1 : ℝ) / 2)) * (Fintype.card ι : ℝ) ≤ (A α).card)
    (hBle : ∀ α ∈ T, ∀ β ∈ T, α ≠ β →
        ((A α ∩ A β).card : ℝ) ≤ (1 - p) * (Fintype.card ι : ℝ)) :
    (T.card : ℝ) * ε < 1 := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hndef
  set N : ℝ := (T.card : ℝ) with hNdef
  set a : ℝ := 1 - p + ε with hadef
  set r : ℝ := a ^ ((1 : ℝ) / 2) with hrdef   -- r = √a
  have hn0 : 0 < n := by rw [hndef]; exact_mod_cast hn
  have ha0 : 0 < a := by rw [hadef]; linarith
  have ha1 : a ≤ 1 := by rw [hadef]; linarith
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hrsq : r ^ 2 = a := by
    rw [hrdef, ← Real.rpow_natCast _ 2, ← Real.rpow_mul ha0.le]
    norm_num
  have hr1 : r ≤ 1 := by
    rw [hrdef]
    calc a ^ ((1 : ℝ) / 2) ≤ (1 : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow ha0.le ha1 (by norm_num)
      _ = 1 := by norm_num
  -- Apply the master inequality with S = r·n, B = (1−p)·n.
  have hmaster := card_le_of_second_moment T A hT (r * n) ((1 - p) * n)
    (mul_nonneg hr0 hn0.le) (mul_nonneg (by linarith) hn0.le)
    hSle hBle
  -- Divide by n² > 0: N·r² ≤ r + (N−1)(1−p), i.e. N·a ≤ r + (N−1)(a−ε).
  have hb_eq : (1 : ℝ) - p = a - ε := by rw [hadef]; ring
  have hdiv : N * a ≤ r + (N - 1) * (a - ε) := by
    have hn2 : 0 < n ^ 2 := by positivity
    have hexp : N * (r * n) ^ 2 = (N * r ^ 2) * n ^ 2 := by ring
    have hexp2 : n * (r * n + (N - 1) * ((1 - p) * n))
        = (r + (N - 1) * (1 - p)) * n ^ 2 := by ring
    rw [hexp, hexp2] at hmaster
    have hcancel := le_of_mul_le_mul_right hmaster hn2
    rw [hrsq, hb_eq] at hcancel
    linarith [hcancel]
  -- Rearrange to N·ε ≤ r − a + ε, then r − a + ε = r − (1−p) < p ≤ 1.
  have hNε : N * ε ≤ r - a + ε := by nlinarith [hdiv]
  have hbound : r - a + ε < 1 := by rw [hadef]; linarith
  linarith [hNε, hbound]

/-- Reciprocal form of `card_lt_inv_of_second_moment_rs`, matching the usual statement
`|Bad²| < 1 / ε` of GCXK25 Lemma 3. -/
theorem card_lt_one_div_of_second_moment_rs
    (T : Finset κ) (A : κ → Finset ι) (hT : T.Nonempty)
    (p ε : ℝ) (hε : 0 < ε) (hεp : ε ≤ p) (hp1 : p < 1)
    (hn : 0 < Fintype.card ι)
    (hSle : ∀ α ∈ T, ((1 - p + ε) ^ ((1 : ℝ) / 2)) * (Fintype.card ι : ℝ) ≤ (A α).card)
    (hBle : ∀ α ∈ T, ∀ β ∈ T, α ≠ β →
        ((A α ∩ A β).card : ℝ) ≤ (1 - p) * (Fintype.card ι : ℝ)) :
    (T.card : ℝ) < 1 / ε := by
  rw [lt_div_iff₀ hε]
  exact card_lt_inv_of_second_moment_rs T A hT p ε hε hεp hp1 hn hSle hBle

end GCXK25SecondMoment

/- Axiom audit: the key results in this file were checked with `#print axioms`
and reduce only to `propext`, `Classical.choice`, and `Quot.sound`. -/
