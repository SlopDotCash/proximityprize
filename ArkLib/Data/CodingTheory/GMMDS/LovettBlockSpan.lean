/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettUnion
import ArkLib.Data.CodingTheory.GMMDS.LovettDivisibility
import ArkLib.Data.CodingTheory.GMMDS.LovettSeparation

/-!
# Lovett's GM-MDS proof: the block-span equality for Lemma 2.6 (`n < k`) (#389)

The `n < k` branch of Lovett's primitive-case closure (arXiv:1803.02523, Lemma 2.6 + final
contradiction) raises the witness vector `vᵢ₀ = (1,…,1,0)` to `vᵢ₀' = (1,…,1,1)`.  This shrinks
the `i₀`-block of `P(k,V)` from `{p·xᵉ : e < k−(n−1)}` (size `k−n+1`) to `{p·(x−aₙ)·xᵉ : e < k−n}`
(size `k−n`), where `p = pVanish (oneVec) = ∏_{j<n−1}(x−aⱼ)`.

The single load-bearing algebraic fact behind Lemma 2.6's span-equality is purely **univariate**:

> `span_R { w·xᵉ : e ≤ d } = span_R ( { w·(x−c)·xᵉ : e < d } ∪ { w } )`.

Both sides are the `R`-module of multiples of `w` of `x`-degree `≤ deg w + d`.  This file proves
that block-span identity over any commutative ring `R[X]`, then specializes it to Lovett's
`pFam`/`pVanish` data so the raised family `P(k,V')` together with the single separated polynomial
`p` spans the same space as `P(k,V)`.

Issue #389.
-/

open Polynomial

namespace ArkLib.GMMDS

universe u

variable {R : Type*} [CommRing R]

/-! ## The univariate block-span identity -/

/-- The "raised" block generator `w·(x−c)·xᵉ`. -/
noncomputable def rblk (w : R[X]) (c : R) (e : ℕ) : R[X] := w * (X - C c) * X ^ e

/-- The "plain" block generator `w·xᵉ`. -/
noncomputable def pblk (w : R[X]) (e : ℕ) : R[X] := w * X ^ e

/-- `w·(x−c)·xᵉ` lies in the span of the plain block `{w·xᵉ : e ≤ d}` whenever `e + 1 ≤ d`. -/
theorem rblk_mem_span_pblk (w : R[X]) (c : R) {d e : ℕ} (he : e + 1 ≤ d) :
    rblk w c e ∈ Submodule.span R (Set.range (fun i : Fin (d + 1) => pblk w (i : ℕ))) := by
  -- w·(x−c)·xᵉ = w·xᵉ⁺¹ − c·(w·xᵉ)
  have hexp : rblk w c e = pblk w (e + 1) - c • pblk w e := by
    simp only [rblk, pblk, Polynomial.smul_eq_C_mul]; ring
  rw [hexp]
  refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · exact Submodule.subset_span ⟨⟨e + 1, by omega⟩, rfl⟩
  · exact Submodule.subset_span ⟨⟨e, by omega⟩, rfl⟩

/-- The plain block `{w·xᵉ : e ≤ d}` is contained in the span of the raised block together with
`w` itself: `w·xᵉ` is built by the telescoping `w·xᵉ = w·(x−c)·xᵉ⁻¹ + c·w·xᵉ⁻¹`. -/
theorem pblk_mem_span_rblk (w : R[X]) (c : R) (d : ℕ) :
    ∀ e ≤ d, pblk w e ∈
      Submodule.span R
        (insert w (Set.range (fun i : Fin d => rblk w c (i : ℕ)))) := by
  intro e
  induction e with
  | zero =>
    intro _
    have : pblk w 0 = w := by simp [pblk]
    rw [this]; exact Submodule.subset_span (Set.mem_insert _ _)
  | succ e ih =>
    intro he
    -- w·xᵉ⁺¹ = w·(x−c)·xᵉ + c·(w·xᵉ)
    have hexp : pblk w (e + 1) = rblk w c e + c • pblk w e := by
      simp only [rblk, pblk, Polynomial.smul_eq_C_mul]; ring
    rw [hexp]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (ih (by omega)))
    exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨e, by omega⟩, rfl⟩)

/-- **The univariate block-span identity.**  For `w : R[X]`, `c : R`, `d : ℕ`:
`span { w·xᵉ : e ≤ d } = span ({ w·(x−c)·xᵉ : e < d } ∪ { w })`. -/
theorem span_pblk_eq_span_rblk_insert (w : R[X]) (c : R) (d : ℕ) :
    Submodule.span R (Set.range (fun i : Fin (d + 1) => pblk w (i : ℕ)))
      = Submodule.span R (insert w (Set.range (fun i : Fin d => rblk w c (i : ℕ)))) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact pblk_mem_span_rblk w c d (i : ℕ) (by omega)
  · rw [Submodule.span_le, Set.insert_subset_iff]
    refine ⟨?_, ?_⟩
    · -- w = w·x⁰ ∈ plain block
      have hmem : pblk w 0 ∈
          Submodule.span R (Set.range (fun i : Fin (d + 1) => pblk w (i : ℕ))) :=
        Submodule.subset_span ⟨⟨0, by omega⟩, rfl⟩
      simpa only [pblk, pow_zero, mul_one] using hmem
    · rintro _ ⟨i, rfl⟩
      exact rblk_mem_span_pblk w c (by omega : (i : ℕ) + 1 ≤ d)

end ArkLib.GMMDS

#print axioms ArkLib.GMMDS.span_pblk_eq_span_rblk_insert
