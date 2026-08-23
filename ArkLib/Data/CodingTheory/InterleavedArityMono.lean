/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.InterleavedLambdaGe
import ArkLib.Data.CodingTheory.InterleavedListSize

/-!
# The interleaved list size is monotone in the arity (#232)

The in-tree development brackets the `m`-interleaved list size by
`Λ(C, δ) ≤ Λ(C^{≡m}, δ) ≤ (Λ(C, δ))^m` (`Lambda_interleaved_ge` / `Lambda_interleaved_le_pow`),
and collapses the two ABF26 §5 challenges up to a fixed `m`-power on the polynomial threshold
(`ListRecoveryInterleavedGap`).  The arity itself, however, was only ever compared against the
base code (`m = 1`).  This file proves the missing **monotonicity in the arity**:

  `Lambda_interleaved_arity_mono` — for `1 ≤ m ≤ n`,
  `Λ(C^{≡m}, δ) ≤ Λ(C^{≡n}, δ)`.

So adding columns to an interleaving never shrinks the list, and the whole arity ladder

  `Λ(C, δ) = Λ(C^{≡1}, δ) ≤ Λ(C^{≡2}, δ) ≤ Λ(C^{≡3}, δ) ≤ ⋯`

is monotone.  In particular, a list-size *lower* bound at the base code propagates verbatim to
**every** arity `m ≥ 1` (not just by the single diagonal embedding), so the convergent
`(1-√ρ, 1-ρ)` interior wall is inherited by the interleaved code at *all* arities uniformly.

## Proof

The engine is a general **column-reindexing** lemma.  Given a surjection `σ : Fin n → Fin m`
witnessed by a right inverse `τ` (`σ ∘ τ = id`), the map

  `pad : Matrix ι (Fin m) F → Matrix ι (Fin n) F`,  `pad V i j = V i (σ j)`

precomposes each row by `σ`.  It

* lands in the interleaved code at arity `n` (each column of `pad V` is a column of `V`, hence a
  base codeword);
* preserves the Hamming distance **exactly** — `(· ∘ σ)` is injective because `σ` is surjective,
  so `hammingDist_comp` gives `Δ₀(pad V, pad G) = Δ₀(V, G)`, hence the relative distance is
  preserved (same `|ι|`); and
* is injective (the first `m` columns, read off by `τ`, recover `V`).

Mapping the received word `G` for arity `m` to `pad G` for arity `n`, this injects each per-word
base list into the per-word interleaved list, giving the maximised bound.  Arity monotonicity then
specialises `σ` to the clamp `j ↦ min j (m-1)` (concretely the `if (j:ℕ) < m` truncation) with
`τ = Fin.castLE`.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

open ListDecodable Code InterleavedCode

namespace InterleavedCode.ListSize

variable {ι F : Type} [Fintype ι]

/-- **Column-reindexing bound for interleaved list sizes.**

Let `σ : Fin n → Fin m` be a surjection, witnessed by a right inverse `τ` (so `σ ∘ τ = id`).
Precomposing each row by `σ` injects each per-word base list of the `m`-interleaving into a
per-word base list of the `n`-interleaving, preserving relative Hamming distance exactly.  Hence

  `Λ(C^{≡m}, δ) ≤ Λ(C^{≡n}, δ)`.

This is the engine behind arity monotonicity (`Lambda_interleaved_arity_mono`): any surjection of
column-index sets witnesses a list-size inequality in the *opposite* direction. -/
theorem Lambda_interleaved_reindex_le [Fintype F] [DecidableEq F] [Nonempty ι] {m n : ℕ}
    (C : Set (ι → F)) (δ : ℝ)
    (σ : Fin n → Fin m) (τ : Fin m → Fin n) (hστ : Function.LeftInverse σ τ) :
    Lambda (interleavedCodeSet (κ := Fin m) C) δ
      ≤ Lambda (interleavedCodeSet (κ := Fin n) C) δ := by
  classical
  refine iSup_le fun G => ?_
  -- `pad`: precompose each row of a matrix by the column reindexing `σ`.
  set pad : Matrix ι (Fin m) F → Matrix ι (Fin n) F := fun V => fun i j => V i (σ j) with hpad
  set G' : Matrix ι (Fin n) F := pad G with hG'
  have hmaps : Set.MapsTo pad (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) G δ)
      (closeCodewordsRel (interleavedCodeSet (κ := Fin n) C) G' δ) := by
    intro V hV
    obtain ⟨hVC, hVball⟩ := hV
    refine ⟨?_, ?_⟩
    · -- every column of `pad V` is a column of `V`, hence a base codeword
      intro k
      have hcol : (pad V).transpose k = V.transpose (σ k) := by
        funext i; simp [hpad, Matrix.transpose_apply]
      rw [hcol]; exact hVC (σ k)
    · -- column precomposition by a surjection preserves Hamming distance exactly
      rw [relHammingBall, Set.mem_setOf_eq] at hVball ⊢
      -- `(· ∘ σ)` is injective because `σ` is surjective (the right inverse `τ` reads off rows).
      have hfinj : ∀ _ : ι, Function.Injective
          (fun (row : Fin m → F) (j : Fin n) => row (σ j)) := by
        intro _ h₁ h₂ heq
        funext k
        have := congrFun heq (τ k)
        simpa [hστ k] using this
      have hdist : (δᵣ(G', pad V) : ℝ) ≤ (δᵣ(G, V) : ℝ) := by
        unfold Code.relHammingDist
        have hHam : hammingDist G' (pad V) = hammingDist G V := by
          have := hammingDist_comp
            (β := fun _ : ι => Fin n → F) (γ := fun _ : ι => Fin m → F)
            (fun (_ : ι) (row : Fin m → F) (j : Fin n) => row (σ j))
            (x := G) (y := V) hfinj
          simpa [hpad, hG'] using this
        rw [hHam]
      -- transport the (instance-uniform) inequality through the `DecidableEq` instance gap
      have hVball' : (δᵣ(G, V) : ℝ) ≤ δ := by convert hVball using 3
      have key : (δᵣ(G', pad V) : ℝ) ≤ δ := le_trans hdist hVball'
      convert key using 3
  have hinj : Set.InjOn pad (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) G δ) := by
    intro a _ b _ hab
    funext i k
    have := congrFun (congrFun hab i) (τ k)
    simpa [hpad, hστ k] using this
  calc ((closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) G δ).ncard : ℕ∞)
      = (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) G δ).encard :=
        (Set.toFinite _).cast_ncard_eq
    _ ≤ (closeCodewordsRel (interleavedCodeSet (κ := Fin n) C) G' δ).encard :=
        Set.encard_le_encard_of_injOn hmaps hinj
    _ = ((closeCodewordsRel (interleavedCodeSet (κ := Fin n) C) G' δ).ncard : ℕ∞) :=
        ((Set.toFinite _).cast_ncard_eq).symm
    _ ≤ Lambda (interleavedCodeSet (κ := Fin n) C) δ :=
        le_iSup
          (fun f => ((closeCodewordsRel (interleavedCodeSet (κ := Fin n) C) f δ).ncard : ℕ∞)) G'

/-- **Interleaved list size is monotone in the arity.** For `1 ≤ m ≤ n`,

  `Λ(C^{≡m}, δ) ≤ Λ(C^{≡n}, δ)`.

Adding interleaving columns never shrinks the list.  The surjection witnessing
`Lambda_interleaved_reindex_le` is the clamp `j ↦ if (j:ℕ) < m then j else 0`, with right inverse
the canonical embedding `Fin.castLE : Fin m ↪ Fin n`. -/
theorem Lambda_interleaved_arity_mono [Fintype F] [DecidableEq F] [Nonempty ι] {m n : ℕ}
    [NeZero m] (hmn : m ≤ n) (C : Set (ι → F)) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) C) δ
      ≤ Lambda (interleavedCodeSet (κ := Fin n) C) δ := by
  classical
  refine Lambda_interleaved_reindex_le C δ
    (fun j => if h : (j : ℕ) < m then (⟨j, h⟩ : Fin m)
              else ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩)
    (Fin.castLE hmn) ?_
  intro k
  have hk : ((Fin.castLE hmn k : Fin n) : ℕ) < m := by simp [k.is_lt]
  simp only [hk, dif_pos]
  ext; simp

/-- **The arity ladder is monotone from the base code.** For every arity `n ≥ 1`,
`Λ(C, δ) ≤ Λ(C^{≡n}, δ)`, and this factors through *every* intermediate arity `m ≤ n` with `m ≥ 1`:

  `Λ(C, δ) ≤ Λ(C^{≡m}, δ) ≤ Λ(C^{≡n}, δ)`.

This strengthens `Lambda_interleaved_ge` (which only links the base code to a single arity) into a
fully monotone ladder, so a base-code list-size lower bound propagates to all arities through a
chain of inequalities rather than a single diagonal embedding. -/
theorem Lambda_base_le_interleaved_arity_chain [Fintype F] [DecidableEq F] [Nonempty ι] {m n : ℕ}
    [NeZero m] (hmn : m ≤ n) (C : Set (ι → F)) (δ : ℝ) :
    Lambda C δ ≤ Lambda (interleavedCodeSet (κ := Fin m) C) δ ∧
      Lambda (interleavedCodeSet (κ := Fin m) C) δ
        ≤ Lambda (interleavedCodeSet (κ := Fin n) C) δ :=
  ⟨Lambda_interleaved_ge C δ, Lambda_interleaved_arity_mono hmn C δ⟩

/-- **A base list-size lower bound propagates to every arity, monotonically.** If `L ≤ Λ(C, δ)`,
then for every `n ≥ 1`, `L ≤ Λ(C^{≡n}, δ)`, and for any intermediate `1 ≤ m ≤ n` the bound at
arity `m` is itself dominated by the bound at arity `n`.  This is the arity-uniform form of
`gap_present_in_interleaved`: the interior wall is present at *all* arities, and increasing the
arity can only enlarge the witnessed list. -/
theorem interior_lower_bound_arity_mono [Fintype F] [DecidableEq F] [Nonempty ι] {m n : ℕ}
    [NeZero m] (hmn : m ≤ n) (C : Set (ι → F)) (δ : ℝ) {L : ℕ∞} (hL : L ≤ Lambda C δ) :
    L ≤ Lambda (interleavedCodeSet (κ := Fin m) C) δ ∧
      Lambda (interleavedCodeSet (κ := Fin m) C) δ
        ≤ Lambda (interleavedCodeSet (κ := Fin n) C) δ :=
  ⟨le_trans hL (Lambda_interleaved_ge C δ), Lambda_interleaved_arity_mono hmn C δ⟩

/-! ## Axiom audit -/

#print axioms Lambda_interleaved_reindex_le
#print axioms Lambda_interleaved_arity_mono
#print axioms Lambda_base_le_interleaved_arity_chain
#print axioms interior_lower_bound_arity_mono

end InterleavedCode.ListSize
