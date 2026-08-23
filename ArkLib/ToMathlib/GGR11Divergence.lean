/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.GGR11Interleaved
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.JohnsonBound.Family

/-!
# GGR11 divergence lemma and the exact tree-structure ⟺ per-word-bound equivalence

Two contributions toward issue #73 (GGR11 interleaved list-size, ABF26 Lemma 2.10):

## 1. The divergence lemma (the formalized core of GGR11 Lemma 3.4)

`hammingDist_ge_minDist_of_mem_closeCodewordsRel_ne`: **distinct `δ`-close interleaved
codewords `V ≠ V'` have `hammingDist V V' ≥ minDist C`.**  This is the geometric heart of
the Erase-Decode argument: because the interleaved code `C^{≡m}` has the *same* minimum
distance as the base code `C` (`minDist_eq_minDist`), two distinct close codewords are at
least `minDist C` apart, so their agreement sets (with the received word `f`) can overlap in
at most `n − minDist C = (1 − δ_C)·n` coordinates (`agreement_inter_card_le`).  Concretely: on
the shared agreement they both equal `f`, and any column where they differ exhibits two
distinct base codewords agreeing there — which, by the base-code minimum distance, is
impossible on more than `n − minDist C` positions.

## 2. The tree-structure residual is *exactly* the per-word bound

`treeStructure_of_perWordBound`: the reverse of the existing `perWordBound_of_treeStructure`.
Supplying the **explicit** leaf-count function `t b' r' := (b'+r' choose r')·(Λ C δ)^{r'}`,
which satisfies the GGR11 Blue/Red budget recursion *with equality* (Pascal's rule +
the `L^{r'}` geometric factor), shows `GGR11PerWordBound → GGR11TreeStructure`.  Combined with
`perWordBound_of_treeStructure`, this gives `GGR11TreeStructure ⟺ GGR11PerWordBound`
(`treeStructure_iff_perWordBound`): the Erase-Decode *tree abstraction adds nothing* beyond
the closed-form per-word bound, so the genuine remaining obstruction is precisely
`(closeCodewordsRel (C^{≡m}) f δ).encard ≤ (b+r choose r)·(Λ C δ)^r` — there is no separate,
weaker "tree exists" target.

All declarations are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option maxHeartbeats 2000000

open ListDecodable Code InterleavedCode

namespace InterleavedCode.GGR11

variable {ι F : Type} [Fintype ι]

/-! ## 1. The divergence lemma -/

/-- **GGR11 Lemma 3.4 core (divergence).**  Distinct `δ`-close interleaved codewords are at
least `minDist C` apart in Hamming distance, because the interleaved code shares the base
code's minimum distance (`minDist_eq_minDist`). -/
theorem hammingDist_ge_minDist_of_mem_closeCodewordsRel_ne
    [Field F] [DecidableEq F] [Nonempty ι] {C : Set (ι → F)} {δ : ℝ} {m : ℕ} [NeZero m]
    {f : Matrix ι (Fin m) F}
    {V V' : Matrix ι (Fin m) F}
    (hV : V ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    (hV' : V' ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    (hne : V ≠ V') :
    Code.minDist C ≤ hammingDist V V' := by
  classical
  haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  -- both lie in the interleaved code
  have hVcode : V ∈ interleavedCodeSet (κ := Fin m) C := hV.1
  have hV'code : V' ∈ interleavedCodeSet (κ := Fin m) C := hV'.1
  -- the interleaved code has the same minimum distance as the base code (propositional bridge,
  -- avoiding the expensive `interleavedCodeSet`/`^⋈` defeq; the `DecidableEq (Fin m → F)`
  -- instance is left to canonical inference so both sides share `Fintype.decidablePiFintype`)
  have hmin : Code.minDist (interleavedCodeSet (κ := Fin m) C) = Code.minDist C := by
    -- `interleavedCodeSet C = C ^⋈ (Fin m)` is `rfl`; the only gap is the canonical
    -- `DecidableEq (Fin m → F)` instance on `Code.minDist` (the `#73` haveI used to unify it),
    -- which `convert` discharges as a subsingleton subgoal.
    convert minDist_eq_minDist (κ := Fin m) (F := F) C using 2
  -- distinct codewords are ≥ minDist apart
  have h := JohnsonBound.minDist_le_hammingDist_of_mem_ne
    (C := interleavedCodeSet (κ := Fin m) C) hVcode hV'code hne
  rwa [hmin] at h

/-- **Agreement-set overlap bound.**  Distinct `δ`-close interleaved codewords agree with each
other on at most `n − minDist C` coordinates; hence their agreement sets with the received
word `f` overlap in at most `n − minDist C = (1 − δ_C)·n` coordinates. -/
theorem agreement_inter_card_le
    [Field F] [DecidableEq F] [Nonempty ι] {C : Set (ι → F)} {δ : ℝ} {m : ℕ} [NeZero m]
    {f : Matrix ι (Fin m) F}
    {V V' : Matrix ι (Fin m) F}
    (hV : V ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    (hV' : V' ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    (hne : V ≠ V') :
    (Finset.univ.filter (fun i => V i = f i ∧ V' i = f i)).card
      ≤ Fintype.card ι - Code.minDist C := by
  classical
  -- the agreement intersection sits inside the V=V' set
  have hsub : (Finset.univ.filter (fun i => V i = f i ∧ V' i = f i))
      ⊆ Finset.univ.filter (fun i => V i = V' i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [hi.1, hi.2]
  -- |{i : V i = V' i}| = n − hammingDist V V'
  have hcompl : (Finset.univ.filter (fun i => V i = V' i)).card
      = Fintype.card ι - hammingDist V V' := by
    simpa [Code.agreementCols] using
      Code.agreementCols_card_eq_card_sub_hammingDist (u := V) (v := V')
  -- minDist ≤ hammingDist
  have hmin := hammingDist_ge_minDist_of_mem_closeCodewordsRel_ne hV hV' hne
  calc (Finset.univ.filter (fun i => V i = f i ∧ V' i = f i)).card
      ≤ (Finset.univ.filter (fun i => V i = V' i)).card := Finset.card_le_card hsub
    _ = Fintype.card ι - hammingDist V V' := hcompl
    _ ≤ Fintype.card ι - Code.minDist C := by omega

/-! ## 2. The tree-structure residual equals the per-word bound -/

/-- The explicit GGR11 closed-form leaf-count function `t b r := (b+r choose r)·L^r`
satisfies the Blue/Red budget recursion *with equality*: this is `ggr11_tree_count_le`'s
recursion run in reverse, witnessing that the closed form is itself a valid leaf-count. -/
private lemma closedForm_satisfies_recursion (L : ℕ∞) :
    (∀ b', (fun b r => ((b + r).choose r : ℕ∞) * L ^ r) b' 0 ≤ 1) ∧
    (∀ r', (fun b r => ((b + r).choose r : ℕ∞) * L ^ r) 0 (r' + 1)
        ≤ L * (fun b r => ((b + r).choose r : ℕ∞) * L ^ r) 0 r') ∧
    (∀ b' r', (fun b r => ((b + r).choose r : ℕ∞) * L ^ r) (b' + 1) (r' + 1)
        ≤ (fun b r => ((b + r).choose r : ℕ∞) * L ^ r) b' (r' + 1)
          + L * (fun b r => ((b + r).choose r : ℕ∞) * L ^ r) (b' + 1) r') := by
  refine ⟨?_, ?_, ?_⟩
  · intro b'
    simp
  · intro r'
    simp only [Nat.zero_add, Nat.choose_self, Nat.cast_one, one_mul]
    apply le_of_eq
    rw [pow_succ, mul_comm]
  · intro b' r'
    simp only
    have hpascal : ((b' + 1 + (r' + 1)).choose (r' + 1) : ℕ∞)
        = ((b' + (r' + 1)).choose (r' + 1) : ℕ∞) + ((b' + 1 + r').choose r' : ℕ∞) := by
      have e1 : b' + 1 + (r' + 1) = (b' + (r' + 1)) + 1 := by ring
      rw [e1, Nat.choose_succ_succ (b' + (r' + 1)) r']
      push_cast
      have e2 : b' + (r' + 1) = b' + 1 + r' := by ring
      rw [e2]
      ring
    have hterm : ((b' + 1 + r').choose r' : ℕ∞) * L ^ (r' + 1)
        = L * (((b' + 1 + r').choose r' : ℕ∞) * L ^ r') := by
      rw [pow_succ, ← mul_assoc, mul_comm]
    rw [hpascal, add_mul, hterm]

/-- **The Erase-Decode tree adds nothing: `GGR11PerWordBound → GGR11TreeStructure`.**

The reverse of `perWordBound_of_treeStructure`.  Given the closed-form per-word bound, the
explicit leaf-count function `t b' r' := (b'+r' choose r')·(Λ C δ)^{r'}` — which satisfies the
GGR11 budget recursion with equality (`closedForm_satisfies_recursion`) — witnesses
`GGR11TreeStructure`. -/
theorem treeStructure_of_perWordBound
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (h : GGR11PerWordBound C δ m b r) :
    GGR11TreeStructure C δ m b r := by
  intro f
  refine ⟨fun b' r' => ((b' + r').choose r' : ℕ∞) * (Lambda C δ) ^ r', ?_, ?_, ?_, ?_⟩
  · exact h f
  · exact (closedForm_satisfies_recursion (Lambda C δ)).1
  · exact (closedForm_satisfies_recursion (Lambda C δ)).2.1
  · exact (closedForm_satisfies_recursion (Lambda C δ)).2.2

/-- **The refined residual is exactly the per-word bound.**  `GGR11TreeStructure` and
`GGR11PerWordBound` are equivalent, so the Erase-Decode "tree existence" framing carries no
content beyond the closed-form bound `close.encard ≤ (b+r choose r)·(Λ C δ)^r`. -/
theorem treeStructure_iff_perWordBound
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ} :
    GGR11TreeStructure C δ m b r ↔ GGR11PerWordBound C δ m b r :=
  ⟨perWordBound_of_treeStructure, treeStructure_of_perWordBound⟩

#print axioms InterleavedCode.GGR11.hammingDist_ge_minDist_of_mem_closeCodewordsRel_ne
#print axioms InterleavedCode.GGR11.agreement_inter_card_le
#print axioms InterleavedCode.GGR11.treeStructure_of_perWordBound
#print axioms InterleavedCode.GGR11.treeStructure_iff_perWordBound

end InterleavedCode.GGR11
