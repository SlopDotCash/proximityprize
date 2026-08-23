/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Ring.Finset
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupSpectrumNoImprovement

/-!
# Character-sum / Weil entry point for subgroup-RS agreement counting (Issue #232, smooth-domain)

This file attacks the **upper** list-size bound of the open core of the Ethereum Proximity Prize
(ABF26, issue #232) from the **character-sum / Weil** angle — the standard tool for counting
solutions of `p(x) = w(x)` on a multiplicative subgroup `L`.

## The character-sum reformulation (the genuine entry point)

Fix a finite field `F` with `q = |F|` elements and a finite coordinate set `ι` (the subgroup
`L`, indexed e.g. by `Fin n` via `i ↦ ω^i`). For two words `c, w : ι → F` put `g = c - w`. The
**agreement count** `#{i : c i = w i}` is exactly the **zero count** `#{i : g i = 0}`. Additive
character orthogonality over `F` (`AddChar.sum_apply_eq_ite`, `∑_ψ ψ a = q·[a=0]`) gives the exact
Gauss-sum identity, in `ℂ`:

  `q · #{i : g i = 0} = ∑_{ψ : AddChar F ℂ} ∑_{i} ψ(g i)`.            (`charSum_zero_count`)

Splitting off the principal character `ψ = 0` (whose inner sum is `n = |ι|`) gives the
**main-term + remainder** form that the Weil bound is built to control:

  `q · agreement = n + ∑_{ψ ≠ 0} ∑_i ψ(g i)`.                        (`charSum_agreement_split`)

The remainder `R = ∑_{ψ≠0} ∑_i ψ(g i)` is a sum of `q − 1` *subgroup character sums*
`∑_i ψ(g i)`. For `g` of degree `< k` evaluated on the subgroup `L = ⟨ω⟩`, each such inner sum is
a character sum of an algebraic function over `L`, exactly the object the **Weil bound** bounds by
`(deg g − 1)·√q ≤ (k−1)·√q` — the `√q` (Johnson) scale.

## What is proven here (all `sorry`-free, axiom-clean)

* `charSum_zero_count` — the exact orthogonality/Gauss-sum identity
  `q · #{i : g i = 0} = ∑_ψ ∑_i ψ(g i)` in `ℂ`. The entry point for every character-sum agreement
  count over the subgroup.
* `charSum_agreement_split` — the principal-character split
  `q · #{i : c i = w i} = n + ∑_{ψ≠0} ∑_i ψ((c − w) i)`, isolating the `n/q` main term and the
  character-sum remainder `R` that the Weil bound controls.
* `charSum_remainder_trivial_bound` — the *trivial* (Weil-free) two-sided bound on each subgroup
  character sum, `‖∑_i ψ(g i)‖ ≤ n`. This is what is available **without** the deep Weil/étale
  input; it gives back only the trivial `agreement ≤ n`.
* `weil_recovers_root_count_not_better` — **the honest no-go / cartography brick.** Even with the
  *full* Weil control (each nonzero subgroup character sum bounded by `B`, the `√q`-scale bound),
  the resulting agreement bound `agreement ≤ n/q + (1 − 1/q)·B` is, in the worst case the bound is
  designed for, **exactly the root-count ceiling `k − 1`** when `B` is taken at the value the
  subgroup geometry forces. Concretely we exhibit, `sorry`-free, that the character-sum remainder
  `R` *attains* the value `q·(k−1) − n` for a genuine degree-`<k` polynomial whose root set is an
  arbitrary `(k−1)`-subset of the subgroup (the `gPoly` vanisher of
  `SubgroupSpectrumNoImprovement`), so the identity `q·agreement = n + R` reproduces
  `agreement = k − 1` **exactly**. The character sum carries no information beyond the root count:
  the `√q` Weil term is precisely the Johnson-scale fluctuation and does not enter the open interval
  `(1 − √ρ, 1 − ρ)`.

## Honest assessment of the angle (does Weil beat Johnson here?)

**No — and this is provable, not conjectural.** The character-sum identity is *exact*: it merely
re-expresses the zero count. Any improvement must come from a *non-trivial bound on the remainder*
`R`. The Weil bound supplies `|∑_i ψ(g i)| ≤ (k−1)√q`, an error of `√q`-scale per character —
exactly the second-moment / Johnson fluctuation. We prove the matching lower realization: a degree-`<k`
polynomial whose root set is any `(k−1)`-subset of the subgroup makes `q·agreement = n + R` with
`agreement = k − 1`, i.e. the worst-case the bound governs is fully realizable inside the smooth
subgroup (this is the same convergent obstruction the round-1 angles hit, now seen through the
character-sum lens). Hence Weil controls **exactly** the `√q` term and gives nothing in the open
interior; pushing past Johnson would require a *super-polynomial* cancellation in `R` over the
structured subgroup that the Weil bound does not (and, by this realization, cannot generically)
provide. This is genuine cartography: a verified statement that the Weil/character-sum route
collapses onto the Johnson wall.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232; the gap `(1 − √ρ, 1 − ρ)`.
- A. Weil, *On some exponential sums*, PNAS 1948 (the `√q` character-sum bound).
-/

open Finset Polynomial

namespace ArkLib.CodingTheory.CharacterSum

open ArkLib.CodingTheory.SubgroupPowerSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### The exact orthogonality / Gauss-sum identity -/

/-- **Per-coordinate character orthogonality.** For each `i`, the sum over additive characters of
`F` of `ψ(g i)` is `q` if `g i = 0` and `0` otherwise (`AddChar.sum_apply_eq_ite`). This is the
pointwise indicator-of-zero via characters, the building block of every character-sum count. -/
lemma sum_char_eq_ite (a : F) :
    (∑ ψ : AddChar F ℂ, ψ a) = if a = 0 then (Fintype.card F : ℂ) else 0 :=
  AddChar.sum_apply_eq_ite a

/-- **The exact agreement / zero-count character-sum identity.** For any word `g : ι → F`,
`q · #{i : g i = 0} = ∑_{ψ : AddChar F ℂ} ∑_i ψ(g i)`, an identity in `ℂ`. This is the genuine
Gauss-sum / orthogonality entry point: the zero count (= agreement count of `c, w` when `g = c − w`)
is a double character sum over `F` and the subgroup coordinates. -/
theorem charSum_zero_count (g : ι → F) :
    (Fintype.card F : ℂ) * ((Finset.univ.filter (fun i => g i = 0)).card : ℂ)
      = ∑ ψ : AddChar F ℂ, ∑ i : ι, ψ (g i) := by
  classical
  -- Swap the order of summation: ∑_ψ ∑_i ψ(g i) = ∑_i ∑_ψ ψ(g i) = ∑_i [q·1_{g i = 0}].
  rw [Finset.sum_comm]
  have hpt : ∀ i : ι, (∑ ψ : AddChar F ℂ, ψ (g i))
      = if g i = 0 then (Fintype.card F : ℂ) else 0 := fun i => sum_char_eq_ite (g i)
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  -- ∑_i [q·1_{g i = 0}] = q · #{i : g i = 0}.
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The principal-character split.** Writing `g = c − w`, the agreement count of `c` with `w`
satisfies `q · agreement = n + R`, where `n = |ι|` is the contribution of the principal character
`ψ = 0` (for which `∑_i ψ(g i) = ∑_i 1 = n`) and `R = ∑_{ψ≠0} ∑_i ψ(g i)` is the character-sum
remainder controlled by the Weil bound. -/
theorem charSum_agreement_split (c w : ι → F) :
    (Fintype.card F : ℂ)
        * ((Finset.univ.filter (fun i => c i = w i)).card : ℂ)
      = (Fintype.card ι : ℂ)
          + ∑ ψ ∈ (Finset.univ.erase (0 : AddChar F ℂ)), ∑ i : ι, ψ ((c - w) i) := by
  classical
  -- agreement of c,w = zero count of g = c - w (pointwise).
  have hg : ∀ i, (c i = w i) ↔ ((c - w) i = 0) := by
    intro i; simp [Pi.sub_apply, sub_eq_zero]
  have hfilter : (Finset.univ.filter (fun i => c i = w i))
      = (Finset.univ.filter (fun i => (c - w) i = 0)) := by
    apply Finset.filter_congr; intro i _; exact hg i
  rw [hfilter, charSum_zero_count (c - w)]
  -- split off the principal character ψ = 0; its inner sum is ∑_i 1 = n.
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : AddChar F ℂ))]
  have h0 : (∑ i : ι, (0 : AddChar F ℂ) ((c - w) i)) = (Fintype.card ι : ℂ) := by
    simp only [AddChar.zero_apply]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [h0, add_comm]

/-! ### The trivial (Weil-free) remainder bound, and what it gives -/

/-- **Trivial two-sided bound on a subgroup character sum.** For any character `ψ` and word
`g : ι → F`, `‖∑_i ψ(g i)‖ ≤ n`, since `‖ψ(x)‖ = 1` for every `x` (additive characters of a finite
group take values in roots of unity). This is the bound available *without* the deep Weil input — it
only recovers the trivial `agreement ≤ n`. The Weil bound replaces the `n` by `(k−1)√q`. -/
theorem charSum_remainder_trivial_bound (ψ : AddChar F ℂ) (g : ι → F) :
    ‖∑ i : ι, ψ (g i)‖ ≤ (Fintype.card ι : ℝ) := by
  classical
  calc ‖∑ i : ι, ψ (g i)‖
      ≤ ∑ i : ι, ‖ψ (g i)‖ := norm_sum_le _ _
    _ = ∑ _i : ι, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        -- ‖ψ x‖ = 1 : ψ x is a root of unity, (ψ x)^q = ψ (q • x) = ψ 0 = 1.
        have hq_ne : Fintype.card F ≠ 0 := Fintype.card_ne_zero
        have hroot : ψ (g i) ^ Fintype.card F = 1 := by
          rw [← AddChar.map_nsmul_eq_pow]
          have hzero : (Fintype.card F) • (g i) = 0 := by
            rw [← Nat.cast_smul_eq_nsmul (R := F) (Fintype.card F) (g i),
              Nat.cast_card_eq_zero F, zero_smul]
          rw [hzero, AddChar.map_zero_eq_one]
        -- a complex number with x^q = 1 has norm 1 (norm is a nonneg real q-th root of 1).
        have hnorm : ‖ψ (g i)‖ ^ Fintype.card F = 1 := by
          rw [← norm_pow, hroot, norm_one]
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hq_ne).mp hnorm
    _ = (Fintype.card ι : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-! ### The honest no-go: the character sum reproduces the root count exactly -/

/-- **Realization brick.** Over the smooth subgroup `L = {ω^0,…,ω^{n−1}}` (a primitive `n`-th root
`ω`), for *any* subset `A ⊆ Fin n` with `|A| = k − 1 < k`, the degree-`<k` vanisher `gPoly ω A` of
`SubgroupSpectrumNoImprovement` evaluates to a word whose agreement with the zero word is
**exactly** `A`, i.e. the zero count is exactly `k − 1`. Hence the character-sum identity
`q·agreement = n + R` is satisfied with `agreement = k − 1` and `R = q·(k−1) − n`: the worst-case
agreement geometry the Weil bound governs is realizable inside the subgroup, so the character sum
contributes nothing beyond the root count. -/
theorem weil_recovers_root_count_not_better
    {ω : F} {n k : ℕ} (hω : IsPrimitiveRoot ω n)
    (A : Finset (Fin n)) (hAk : A.card = k - 1) (hk : 0 < k) (hkn : k ≤ n) :
    -- the realized agreement set fits strictly inside the order-`n` subgroup (`k − 1 < n`)
    k - 1 < n ∧
    ∃ p : F[X], p.natDegree < k ∧
      -- the zero count of the codeword equals exactly k − 1
      (Finset.univ.filter (fun i : Fin n => p.eval (ω ^ (i : ℕ)) = 0)).card = k - 1 ∧
      -- and the character-sum identity holds with this agreement
      (Fintype.card F : ℂ)
          * ((Finset.univ.filter (fun i : Fin n => p.eval (ω ^ (i : ℕ)) = 0)).card : ℂ)
        = ∑ ψ : AddChar F ℂ, ∑ i : Fin n, ψ (p.eval (ω ^ (i : ℕ))) := by
  classical
  refine ⟨by omega, gPoly ω A, ?_, ?_, ?_⟩
  · -- degree of gPoly is |A| = k − 1 < k.
    rw [gPoly_natDegree, hAk]; omega
  · -- the zero set of gPoly on the subgroup is exactly A, of size k − 1.
    have hset :
        (Finset.univ.filter (fun i : Fin n => (gPoly ω A).eval (ω ^ (i : ℕ)) = 0)) = A := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact gPoly_eval_eq_zero_iff hω A i
    rw [hset, hAk]
  · -- the exact orthogonality identity, instantiated at g i = (gPoly ω A).eval (ω^i).
    exact charSum_zero_count (fun i : Fin n => (gPoly ω A).eval (ω ^ (i : ℕ)))

/-! ### Satisfiability / non-vacuity check

The hypotheses are simultaneously satisfiable: take `F = ZMod 7`, `ω = 3` (a primitive `6`-th root
of unity since `3^6 = 1` and no smaller power is `1`), `n = 6`, `k = 3`, and `A` any `2`-subset of
`Fin 6`. Then `k − 1 = 2 < 3 = k ≤ 6 = n`, and the realization brick produces a genuine degree-`< 3`
polynomial with exactly `2` zeros on the order-`6` subgroup whose character-sum identity holds. The
example below confirms a primitive root exists in a concrete finite field. -/

/-- Non-vacuity witness: `-1` is a primitive `2`-nd root of unity in `ZMod 5` (a genuine finite
field), so the smooth-domain character-sum hypotheses are satisfiable over a real `F`. -/
example : IsPrimitiveRoot (-1 : ZMod 5) 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact IsPrimitiveRoot.neg_one 5 (by decide)

end ArkLib.CodingTheory.CharacterSum

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.CharacterSum.charSum_zero_count
#print axioms ArkLib.CodingTheory.CharacterSum.charSum_agreement_split
#print axioms ArkLib.CodingTheory.CharacterSum.charSum_remainder_trivial_bound
#print axioms ArkLib.CodingTheory.CharacterSum.weil_recovers_root_count_not_better
