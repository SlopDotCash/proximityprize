/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Partition-rank / multiplicative-CLP is VACUOUS on the relation count `N₀` (#407, lane wf-NG)

**Method swept (NEW, distinct from `SliceRankDiagonalVacuous.lean`):** the polynomial method
*beyond* the diagonal slice-rank — Croot–Lev–Pach with **multiplicative** (cyclic `ℤ/n`)
indexing, Naslund **partition rank**, and the **analytic rank** (Lovett) of the cyclotomic
relation tensor

`S : (ℤ/n)ʳ → {0,1}`, `S(a₁,…,aᵣ) = 1 ⟺ ζ^{a₁} + ⋯ + ζ^{aᵣ} = 0` in `ℂ` (`ζ = ` primitive
`n`-th root, `n = 2^μ`), whose support count is exactly the §407 open object
`N₀(μ_n, r) = #{(x₁,…,xᵣ) ∈ μ_nʳ : ∑ xᵢ = 0}`.

The prior no-go (`SliceRankDiagonalVacuous`) killed the *additive diagonal* slice rank. This file
records the THREE further, machine-verified reasons (probes
`scripts/probes/probe_wf2NG_{relation_tensor_rank,partition_rank,diagonal_free,clp_count_lemma}.py`,
all exact, char-0 ＝ char-p in the clean regime `p ≈ n⁵`) that the **multiplicative / partition /
analytic** variants — the genuinely distinct, stronger tensor methods — also give NOTHING:

1. **Off-diagonal, again — but now after multiplicative re-indexing.** Re-coordinatising the
   relation by the cyclic index `ℤ/n` (the multiplicative-CLP move) leaves the support 100 %
   off the diagonal `{(a,…,a)}` (`diag_support = 0` at every `n,r`): the Tao/Naslund **count**
   theorem (`|X| ≤ r·rank` for a tensor supported *on the diagonal of `X`*) bounds the EMPTY
   diagonal, `0 ≤ r·n`. Multiplicative indexing does not move the support off zero.

2. **The single-mode line-size is `≤ 1`, yet the rank is FULL `= n`.** Along every single index
   mode the support is a partial permutation (probe `maxLineSize = 1`): fixing `r−1` indices
   forces `ζ^{aᵢ} = −P`, at most one `aᵢ`. So the mode-unfold is a 0/1 matrix of full rank `n`,
   giving the partition/slice rank `= n`. The only count the rank method then yields is `r·n`
   (linear in `n`) — and that is a **FALSE upper bound on `N₀`**: measured `N₀(μ₈,4) = 168 >
   r·n = 32`. The "beats-trivial" appearance (`32 < 512`) is a phantom; the bound does not hold.

3. **The index group is CYCLIC, not a cube — zero CLP/EG exponent saving.** The Croot–Lev–Pach /
   Ellenberg–Gijswijt sub-trivial saving requires the ground set to be a high-dimensional cube
   `ℤ_m^d`, `d → ∞`. The multiplicative index of `μ_n = μ_{2^μ}` is `ℤ/2^μ`, which is **cyclic**
   (`d = 1`), not `(ℤ/2)^μ`. This is the *index-side* analogue of the additive-side
   "no-cube / Sidon-like" no-go of `SliceRankDiagonalVacuous`: thinner ⇒ more cyclic ⇒ less cube
   ⇒ no CLP saving, on BOTH the additive embedding and the multiplicative index.

So the partition/analytic-rank / multiplicative-CLP route is pinned for a NEW reason that the
diagonal no-go did not cover: even granting the favorable single-mode matching structure
(line-size `≤ 1`), the rank method's only output `r·n` provably fails to bound `N₀`.

## What this file PROVES (axiom-clean: `propext, Classical.choice, Quot.sound`)

The load-bearing FALSIFICATION of obstruction 2, made fully general and char-free. A tensor
support that is a **single-mode partial permutation** — fixing all but one coordinate forces the
tuple (Naslund/CLP's favorable "matching" hypothesis, which the relation tensor *satisfies*
(`maxLineSize ≤ 1`)) — can nonetheless have cardinality far above `r · n`, so the matching
hypothesis does NOT yield any `r·n`-style count bound.

Witness: the **parity-check / sum-zero** support `A_{n,r} = {f : (∑ᵢ f i) = 0 in ℤ/n}`. Fixing any
`r−1` coordinates determines the last uniquely (it is an MDS code of one parity check), so `A` is
single-mode matching; and `#A = n^{r−1}`. For `r ≥ 3, n ≥ 2` (e.g. `n=4, r=4`: `n^{r-1}=64 > r·n
=16`) we have `#A > r·n`. This is the exact, machine-checked sense in which the partition/analytic
rank method gives no bound on the off-diagonal fiber count `N₀`: its hypothesis is met, its
conclusion fails. (`A_{n,r}` is the *linear* analogue of the cyclotomic relation support, and a
strict lower bound on the true `N₀` phenomenon since the cyclotomic support is also matching.)

## References
- [Naslund 2020] *The partition rank of a tensor and k-right-corners…*.
- [Lovett 2019] *The analytic rank of tensors and its applications.*
- [Tao 2016] *A symmetric formulation of the CLP–EG capset bound.*
- in-tree `Frontier/SliceRankDiagonalVacuous.lean` (the additive-diagonal predecessor).
- [BCHKS25] ePrint 2025/2055 Conj 1.12; [ABF26] 2026/680 (#407).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.PartitionRankVacuous

variable {n r : ℕ}

/-- A tensor support `A ⊆ (Fin r → ZMod n)` is a **single-mode partial permutation**
("line-size `≤ 1`", the Naslund/CLP-favorable matching hypothesis) if, fixing all coordinates
except one, at most one value of that coordinate keeps the tuple in `A` — equivalently any two
members agreeing off one coordinate are equal. The cyclotomic relation support satisfies this
(`maxLineSize = 1`, probe-verified). -/
def SingleModeMatching (A : Finset (Fin r → ZMod n)) : Prop :=
  ∀ (i : Fin r) (f g : Fin r → ZMod n), f ∈ A → g ∈ A →
    (∀ j, j ≠ i → f j = g j) → f = g

/-- The **sum-zero parity-check support** `A_{n,r} = {f : ∑ᵢ f i = 0}` — the single-parity MDS
code, the linear analogue (and a matching lower-witness) of the cyclotomic relation support. -/
def sumZeroSupport (n r : ℕ) [NeZero n] : Finset (Fin r → ZMod n) :=
  Finset.univ.filter (fun f => (∑ i, f i) = 0)

/-- **The sum-zero support is single-mode matching.** Fixing all coordinates but one pins the last
via the single parity check `∑ f = 0`: two sum-zero tuples agreeing off coordinate `i` agree at `i`
too (the missing entry is `-∑_{j≠i}`), hence are equal. This is exactly the `maxLineSize ≤ 1`
structure the rank method's count lemma wants — and which the cyclotomic relation also has. -/
theorem sumZeroSupport_singleModeMatching (n r : ℕ) [NeZero n] :
    SingleModeMatching (sumZeroSupport n r) := by
  classical
  intro i f g hf hg hagree
  simp only [sumZeroSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hf hg
  -- f and g agree off i; their full sums are both 0, so they agree at i, hence everywhere.
  have hfi : f i = g i := by
    -- ∑ f = f i + ∑_{j≠i} f j and likewise for g; the off-i sums are equal.
    have hsum_split_f : (∑ j, f j) = f i + ∑ j ∈ Finset.univ.erase i, f j := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hsum_split_g : (∑ j, g j) = g i + ∑ j ∈ Finset.univ.erase i, g j := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hoff : (∑ j ∈ Finset.univ.erase i, f j) = ∑ j ∈ Finset.univ.erase i, g j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hagree j (Finset.ne_of_mem_erase hj)
    have : f i + ∑ j ∈ Finset.univ.erase i, f j = g i + ∑ j ∈ Finset.univ.erase i, g j := by
      rw [← hsum_split_f, ← hsum_split_g, hf, hg]
    rw [hoff] at this
    exact add_right_cancel this
  funext j
  by_cases hji : j = i
  · rw [hji]; exact hfi
  · exact hagree j hji

/-- **`#A_{n,r} = n^{r-1}`** (the parity-check code has codimension 1): the count of sum-zero
tuples over `ZMod n` is `n^{r-1}` for `n ≥ 1`. (Proved for `r ≥ 1` via the bijection forgetting the
last coordinate, which is determined by the parity check.) We state the consumed direction as the
strict lower bound needed in the falsification. -/
theorem sumZeroSupport_card_eq (n r : ℕ) [NeZero n] :
    (sumZeroSupport n (r + 1)).card = n ^ r := by
  classical
  -- Bijection: a sum-zero tuple on Fin (r+1) ↔ a free tuple on Fin r (drop the last coord, which
  -- is forced to -(∑ first r)). Count via card_bij' to (univ : Finset (Fin r → ZMod n)).
  have hcard : (sumZeroSupport n (r + 1)).card
      = (Finset.univ : Finset (Fin r → ZMod n)).card := by
    apply Finset.card_bij'
      (fun (f : Fin (r+1) → ZMod n) _ => fun i : Fin r => f i.castSucc)
      (fun (h : Fin r → ZMod n) _ => Fin.snoc h (-(∑ i : Fin r, h i)))
    · -- forward maps into univ
      intro f _; exact Finset.mem_univ _
    · -- backward maps into sumZeroSupport
      intro h _
      simp only [sumZeroSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Fin.sum_univ_castSucc]
      simp [Fin.snoc_castSucc, Fin.snoc_last]
    · -- left inverse on sumZeroSupport: snoc of dropped tuple = f
      intro f hf
      simp only [sumZeroSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      funext k
      rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
      · simp [Fin.snoc_castSucc]
      · rw [Fin.sum_univ_castSucc] at hf
        rw [Fin.snoc_last]
        have : f (Fin.last r) = -(∑ i : Fin r, f i.castSucc) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]; exact hf
        exact this.symm
    · -- right inverse: dropping the snoc'd tuple returns the original
      intro h _
      funext i; simp [Fin.snoc_castSucc]
  rw [hcard, Finset.card_univ, Fintype.card_pi]
  simp [ZMod.card n]

/-- **Obstruction 2, FALSIFIED (the headline).** The single-mode matching hypothesis — which the
cyclotomic relation tensor SATISFIES — does NOT imply the partition/slice-rank count bound
`#support ≤ r · n`. Witness: a single-mode-matching support `A` with `r · n < #A`. Concretely
`A = sumZeroSupport 4 4` has `#A = 4³ = 64 > r·n = 16`. Therefore the rank method, even granted
its favorable matching structure, yields no valid bound on the off-diagonal fiber count `N₀`. -/
theorem matching_does_not_bound_count :
    ∃ (n r : ℕ) (A : Finset (Fin r → ZMod n)),
      SingleModeMatching A ∧ r * n < A.card := by
  refine ⟨4, 4, sumZeroSupport 4 4, sumZeroSupport_singleModeMatching 4 4, ?_⟩
  have h : (sumZeroSupport 4 4).card = 4 ^ 3 :=
    sumZeroSupport_card_eq 4 3
  rw [h]
  decide

end ArkLib.ProximityGap.PartitionRankVacuous
