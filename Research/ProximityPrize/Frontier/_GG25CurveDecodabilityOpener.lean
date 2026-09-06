/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodFromListSize

/-!
# B2 opener — the structural API of the [GG25] curve list-size (issue #334, class B2)

**Status / scope (honest).** The [GG25] (ePrint 2025/2054) Definition 3.1 *curve decodability*
`def` is **already landed** in-tree (`GG25CurveDecodability.lean` / `CurveDecodability.lean`,
both 0-`sorry`), and so is the forward reduction `curveDecodable_of_curveListSize`
(`GG25CurveDecodFromListSize.lean`):

  `CurveListSizeLe C ℓ δ m`  ∧  `m·b ≤ a`  ⟹  `CurveDecodable C ℓ δ a b`,

a lossless pigeonhole whose *only* open input is the **value** of the curve list-size `m` for
explicit plain Reed–Solomon above Johnson (= `RSCurveListSizeResidual` / BChKS Conj 1.12). The
paper [GG25] 2025/2054 itself is **not on this checkout** (see `/PAPERS_NEEDED.md`); the
definitions in-tree are reconstructed in the notation of [Jo26] Def 2.7 and are not what is
missing.

**What this file adds (the genuine gap).** The predicate `CurveListSizeLe`
(`GG25CurveDecodFromListSize.lean`) had **no structural API** — no monotonicity, and no proof
that an instance ever *exists*. Without an existence anchor the forward reduction is a
conditional with an unpinned antecedent. This file supplies the missing companion bricks:

* `CurveListSizeLe.mono` — weakening in the bound `m`;
* `curveListSizeLe_antitone_delta` — antitone in the radius `δ` (a smaller close set is easier
  to cover);
* `curveListSizeLe_card_le_card` — **the universal anchor**: *every* `F`-additive
  (submodule) code has curve list-size `≤ |F|`, proved by exhibiting the seed-by-seed
  **constant-curve assignment** `α ↦ (f α, 0, …, 0)` (whose curve `∑ⱼ αʲ • cⱼ = α⁰ • f α = f α`
  passes through `f α` at every seed). Its image over the close set has at most `|closeSet| ≤
  |F|` distinct curves, so the list-size hypothesis is *never vacuous* — it holds at `m = |F|`
  for free, and the open content is exactly *how far below `|F|`* one can push `m`.
* `curveDecodable_of_card_le_mul` — the corollary: feeding the universal `m = |F|` anchor into
  `curveDecodable_of_curveListSize` recovers `(ℓ, δ, a, b)`-curve-decodability whenever
  `|F|·b ≤ a` — the unconditional baseline a genuine list-size bound must improve on.

Together these pin the definitional shape of `CurveListSizeLe` (it is realizable, monotone, and
its trivial level is the field size), so the open problem is correctly *isolated as a number*
rather than left as an unrealizable predicate.

**Honesty.** Every result here is unconditional and axiom-clean. Nothing here advances the open
plain-RS list-size `m` — it only makes the engine's input a well-posed, anchored quantity.

## References
* [GG25] Z. Guo, V. Guruswami, ePrint 2025/2054 (ECCC TR25-166), Def 3.1, Thm 3.3.
* [Jo26] S. Jo, ePrint 2026/891, Def 2.7 (the in-tree restatement). Issue #334, class B2.
-/

open Finset Code
open scoped NNReal

namespace ProximityGap.B2Opener

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### Monotonicity of the curve list-size predicate -/

/-- **Weakening in the bound.** A curve list-size `≤ m` is also a curve list-size `≤ m'` for any
`m ≤ m'`: the same assignment covers the close set with `≤ m ≤ m'` distinct curves. -/
theorem CurveListSizeLe.mono {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {m m' : ℕ}
    (h : CurveListSizeLe (F := F) C ℓ δ m) (hm : m ≤ m') :
    CurveListSizeLe (F := F) C ℓ δ m' := by
  intro u f hf
  obtain ⟨asgn, hcard⟩ := h u f hf
  exact ⟨asgn, le_trans hcard hm⟩

/-! ### The universal anchor: every submodule code has curve list-size `≤ |F|` -/

/-- The **constant-curve assignment**: send every close seed `α` to the degree-`ℓ` stack
`(f α, 0, …, 0)`, i.e. the curve `α' ↦ f α` constant in the parameter. It is a valid
`CurveAssignment` for any submodule code: each row is a codeword (`f α ∈ C` in row `0`, `0 ∈ C`
elsewhere), and its curve `∑ⱼ α'ʲ • cⱼ = α'⁰ • f α = f α` passes through `f α` at *every*
seed `α'` — in particular at `α` itself. -/
noncomputable def constCurveAssignment (C : Submodule F (ι → A)) {ℓ : ℕ} {δ : ℝ≥0}
    (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A) (hf : ∀ α, f α ∈ (C : Set (ι → A))) :
    CurveAssignment (C : Set (ι → A)) ℓ δ u f where
  chooseCurve := fun α j => if (j : ℕ) = 0 then f α else 0
  mem_code := by
    intro α j
    by_cases hj : (j : ℕ) = 0
    · simp only [hj, if_true]; exact hf α
    · simp only [hj, if_false]; exact C.zero_mem
  passes_through := by
    intro α _hα
    funext i
    -- The constant curve evaluates to `f α` at the seed `α`: only the `j = 0` term survives.
    rw [Finset.sum_eq_single (0 : Fin (ℓ + 1))]
    · simp only [Fin.val_zero, if_true, pow_zero, one_smul]
    · intro j _ hj0
      have hj : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
      rw [if_neg hj, Pi.zero_apply, smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **The universal anchor (existence of a curve list-size bound).** Every `F`-additive
(submodule) code has curve list-size `≤ |F|` at *every* `(ℓ, δ)`: the constant-curve assignment
maps the close set into a set of at most `|closeSet| ≤ |F|` distinct curves. So the list-size
hypothesis of [GG25] is never vacuous — `m = |F|` always works, and the open question is purely
*how far below* `|F|` the bound `m` can be pushed for explicit plain RS above Johnson. -/
theorem curveListSizeLe_card_le_card (C : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) :
    CurveListSizeLe (F := F) (C : Set (ι → A)) ℓ δ (Fintype.card F) := by
  classical
  intro u f hf
  refine ⟨constCurveAssignment C u f hf, ?_⟩
  calc ((curveCloseSet δ u f).image (constCurveAssignment C u f hf).chooseCurve).card
      ≤ (curveCloseSet δ u f).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset F).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card F := Finset.card_univ

/-! ### The unconditional baseline from the universal anchor -/

/-- **The unconditional curve-decodability baseline.** Feeding the universal `m = |F|` anchor
(`curveListSizeLe_card_le_card`) into the forward reduction `curveDecodable_of_curveListSize`:
every submodule code is `(ℓ, δ, a, b)`-curve-decodable whenever `|F|·b ≤ a`. This is the
trivial floor a genuine [GG25] list-size bound must beat (a real `m ≪ |F|` weakens the
`|F|·b ≤ a` requirement to `m·b ≤ a`). -/
theorem curveDecodable_of_card_le_mul (C : Submodule F (ι → A)) (ℓ : ℕ) (δ : ℝ≥0)
    {a b : ℕ} (hF : 1 ≤ Fintype.card F) (hab : Fintype.card F * b ≤ a) :
    CurveDecodable (F := F) (C : Set (ι → A)) ℓ δ a b :=
  curveDecodable_of_curveListSize hF hab (curveListSizeLe_card_le_card C ℓ δ)

/-! ### Antitone in the radius -/

/-- **Antitone in the radius.** Shrinking `δ` only shrinks the close set (`curveCloseSet_mono`),
so any assignment that covers the larger close set with `≤ m` curves restricts to one covering
the smaller close set with `≤ m` curves. Hence a curve list-size bound at radius `δ'` transfers
to every smaller radius `δ ≤ δ'`. -/
theorem curveListSizeLe_antitone_delta (C : Submodule F (ι → A)) (ℓ : ℕ)
    {δ δ' : ℝ≥0} (hδ : δ ≤ δ') {m : ℕ}
    (h : CurveListSizeLe (F := F) (C : Set (ι → A)) ℓ δ' m) :
    CurveListSizeLe (F := F) (C : Set (ι → A)) ℓ δ m := by
  classical
  intro u f hf
  obtain ⟨asgn, hcard⟩ := h u f hf
  -- Restrict the (radius-`δ'`) assignment to the smaller (radius-`δ`) close set.
  refine ⟨{ chooseCurve := asgn.chooseCurve
            mem_code := asgn.mem_code
            passes_through := fun α hα =>
              asgn.passes_through α (curveCloseSet_mono hδ u f hα) }, ?_⟩
  refine le_trans (Finset.card_le_card ?_) hcard
  exact Finset.image_subset_image (curveCloseSet_mono hδ u f)

end ProximityGap.B2Opener

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.B2Opener.CurveListSizeLe.mono
#print axioms ProximityGap.B2Opener.curveListSizeLe_card_le_card
#print axioms ProximityGap.B2Opener.curveDecodable_of_card_le_mul
#print axioms ProximityGap.B2Opener.curveListSizeLe_antitone_delta
