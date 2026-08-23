/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.GGR11Interleaved

/-!
# GGR11 Algorithm 1: the Erase-Decode tree structure, constructed

This module **proves** the named external residual
`InterleavedCode.GGR11.GGR11TreeStructure` — and hence the full GGR11 §3
interleaved list-size bound — in the genuine finite-list regime (issue #73).

For a fixed received word `f : Matrix ι (Fin m) F`, instead of materialising the
Erase-Decode tree of GGR11 Algorithm 1 as data, we directly define the leaf-count
function it certifies:

* `eraseSet f W i` — the erasure set of the (uniquely determined) Algorithm-1
  path of a close interleaved codeword `W`: the rows where some column `k < i`
  of `W` already disagrees with `f`;
* `levelWt f W l` — the weight of the level-`l` edge on that path: the *new*
  disagreement rows contributed by column `l`;
* level colours `IsWhiteAt` / `IsRedAt` (Blue is "neither"), matching the GGR11
  thresholds: White means weight `< d(C) − δ·n`, Red means
  `d(C) ≤ 2·weight + |eraseSet|`;
* `leafBound C δ f b' r'` — the supremum, over all tree nodes (a level `i`
  together with a close codeword `V` fixing the first `i` columns), of the
  number of close codewords through that node whose remaining Blue/Red colour
  counts fit the budgets `(b', r')`.

The four `GGR11TreeStructure` inequalities are then the GGR11 §3 arguments,
made purely combinatorial:

* the **master inequality** (`minDist_le_mu_add_wt_add_wt`): two close
  codewords sharing their first `l` columns but differing at column `l`
  satisfy `d(C) ≤ μ + w + w'`, since the two column-codewords can disagree
  only on erased rows or on the two new-error sets;
* **GGR11 Lemma 3.3** (White uniqueness, `eq_col_of_isWhiteAt`): a White edge
  admits no sibling, because any sibling has weight `≤ δ·n − μ` while White
  means weight `< d(C) − δ·n`;
* **GGR11 Lemma 3.4** (`eq_col_of_not_isRedAt`, `blueAfter_le_budget`): two
  non-Red siblings contradict the master inequality, and each Blue edge
  contributes `≥ d(C) − δ·n` new erasures while erasures never exceed `δ·n`;
* **GGR11 Lemma 3.5** (`redAfter_le_budget` via `redDoubling_invariant`):
  along a path the deficit `d(C) − μ` halves at each Red edge, so once
  `d(C) ≤ 2^r·(d(C) − δ·n)` an `(r+1)`-st Red edge is impossible;
* **per-node branching ≤ Λ(C, δ)** (`col_mem_closeCodewordsRel`): each column
  choice at a node is a codeword within relative distance `δ` of the
  corresponding column of `f`.

## Main results

* `ggr11_treeStructure_of_budgets` — `GGR11TreeStructure C δ m b r` holds for
  any budgets with `δ·n ≤ b·(d(C) − δ·n)` and `d(C) ≤ 2^r·(d(C) − δ·n)`,
  assuming every base list `closeCodewordsRel C y δ` is finite.
* `ggr11_treeFrontier_of_budgets`, `ggr11_perWordBound_of_budgets`,
  `lambda_le_ggr11_of_budgets` — the residual chain instantiated.
* `lambda_le_ggr11_holds` — the public `InterleavedCode.lambda_le_ggr11`
  disposition Prop is **true** at its canonical budgets `b = ⌈δ/η⌉`,
  `r = ⌈log₂(δ₀/η)⌉` whenever the base lists are finite, in particular over
  any `Finite F` (`lambda_le_ggr11_holds_of_finite`).
-/

set_option linter.style.longFile 1700
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false
set_option maxHeartbeats 1000000

namespace InterleavedCode.GGR11

open ListDecodable Code InterleavedCode Finset

variable {ι F : Type} [Fintype ι]

/-! ## Path data of a close interleaved codeword -/

section PathData

variable [DecidableEq F] {m : ℕ}

open Classical in
/-- The erasure set accumulated before level `i` on the Algorithm-1 path of `W`
against the received word `f`: rows where some column `k < i` of `W` disagrees
with `f`. -/
noncomputable def eraseSet (f W : Matrix ι (Fin m) F) (i : ℕ) : Finset ι :=
  Finset.univ.filter fun j => ∃ k : Fin m, (k : ℕ) < i ∧ W j k ≠ f j k

open Classical in
/-- The weight of the level-`l` edge on the path of `W`: rows newly erased by
column `l`. -/
noncomputable def levelWt (f W : Matrix ι (Fin m) F) (l : Fin m) : ℕ :=
  (Finset.univ.filter fun j => j ∉ eraseSet f W (l : ℕ) ∧ W j l ≠ f j l).card

lemma mem_eraseSet {f W : Matrix ι (Fin m) F} {i : ℕ} {j : ι} :
    j ∈ eraseSet f W i ↔ ∃ k : Fin m, (k : ℕ) < i ∧ W j k ≠ f j k := by
  classical
  simp [eraseSet]

lemma eraseSet_zero (f W : Matrix ι (Fin m) F) : eraseSet f W 0 = ∅ := by
  ext j
  simp [mem_eraseSet]

lemma eraseSet_mono (f W : Matrix ι (Fin m) F) {i i' : ℕ} (h : i ≤ i') :
    eraseSet f W i ⊆ eraseSet f W i' := by
  intro j hj
  rw [mem_eraseSet] at hj ⊢
  obtain ⟨k, hk, hne⟩ := hj
  exact ⟨k, lt_of_lt_of_le hk h, hne⟩

/-- The erasure sets only depend on the columns below the level. -/
lemma eraseSet_congr {f W W' : Matrix ι (Fin m) F} {i : ℕ}
    (h : ∀ k : Fin m, (k : ℕ) < i → ∀ j, W j k = W' j k) :
    eraseSet f W i = eraseSet f W' i := by
  ext j
  rw [mem_eraseSet, mem_eraseSet]
  constructor
  · rintro ⟨k, hk, hne⟩
    exact ⟨k, hk, by rw [← h k hk j]; exact hne⟩
  · rintro ⟨k, hk, hne⟩
    exact ⟨k, hk, by rw [h k hk j]; exact hne⟩

/-- The level weight only depends on the columns up to and including the level. -/
lemma levelWt_congr {f W W' : Matrix ι (Fin m) F} {l : Fin m}
    (h : ∀ k : Fin m, (k : ℕ) < (l : ℕ) + 1 → ∀ j, W j k = W' j k) :
    levelWt f W l = levelWt f W' l := by
  classical
  have hS : eraseSet f W (l : ℕ) = eraseSet f W' (l : ℕ) :=
    eraseSet_congr (fun k hk j => h k (Nat.lt_succ_of_lt hk) j)
  unfold levelWt
  congr 1
  apply Finset.filter_congr
  intro j _
  rw [hS, h l (Nat.lt_succ_self _) j]

/-- One step of the erasure-set recursion: level `l` adds exactly its weight. -/
lemma card_eraseSet_succ (f W : Matrix ι (Fin m) F) (l : Fin m) :
    (eraseSet f W ((l : ℕ) + 1)).card = (eraseSet f W (l : ℕ)).card + levelWt f W l := by
  classical
  have hsplit : eraseSet f W ((l : ℕ) + 1) =
      eraseSet f W (l : ℕ) ∪
        Finset.univ.filter (fun j => j ∉ eraseSet f W (l : ℕ) ∧ W j l ≠ f j l) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_eraseSet]
    constructor
    · rintro ⟨k, hk, hne⟩
      rcases (Nat.lt_succ_iff.mp hk).lt_or_eq with hk' | hk'
      · exact Or.inl ⟨k, hk', hne⟩
      · by_cases hj : ∃ k' : Fin m, (k' : ℕ) < (l : ℕ) ∧ W j k' ≠ f j k'
        · exact Or.inl hj
        · refine Or.inr ⟨hj, ?_⟩
          have hkl : k = l := Fin.ext hk'
          rwa [hkl] at hne
    · rintro (⟨k, hk, hne⟩ | ⟨_, hne⟩)
      · exact ⟨k, Nat.lt_succ_of_lt hk, hne⟩
      · exact ⟨l, Nat.lt_succ_self _, hne⟩
  have hdisj : Disjoint (eraseSet f W (l : ℕ))
      (Finset.univ.filter (fun j => j ∉ eraseSet f W (l : ℕ) ∧ W j l ≠ f j l)) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [Finset.mem_filter] at hj'
    exact hj'.2.1 hj
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  rfl

/-- Erasure-set cardinalities telescope the level weights. -/
lemma card_eraseSet_eq_sum (f W : Matrix ι (Fin m) F) :
    ∀ i, i ≤ m → (eraseSet f W i).card
      = ∑ l ∈ Finset.univ.filter (fun l : Fin m => (l : ℕ) < i), levelWt f W l := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [eraseSet_zero]
    simp
  | succ i ih =>
    intro hi
    have him : i < m := hi
    have hfil : Finset.univ.filter (fun l : Fin m => (l : ℕ) < i + 1)
        = insert ⟨i, him⟩ (Finset.univ.filter (fun l : Fin m => (l : ℕ) < i)) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hl
        rcases (Nat.lt_succ_iff.mp hl).lt_or_eq with h | h
        · exact Or.inr h
        · exact Or.inl (Fin.ext h)
      · rintro (rfl | hl)
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt hl
    have hnotmem : (⟨i, him⟩ : Fin m) ∉
        Finset.univ.filter (fun l : Fin m => (l : ℕ) < i) := by
      simp
    have hstep : (eraseSet f W (i + 1)).card
        = (eraseSet f W i).card + levelWt f W ⟨i, him⟩ :=
      card_eraseSet_succ f W ⟨i, him⟩
    rw [hfil, Finset.sum_insert hnotmem, hstep, ih (le_of_lt him)]
    ring

/-- The final erasure set is exactly the interleaved disagreement set. -/
lemma card_eraseSet_top (f W : Matrix ι (Fin m) F) :
    (eraseSet f W m).card = hammingDist f W := by
  classical
  unfold hammingDist
  apply Finset.card_bij (fun j _ => j)
  · intro j hj
    rw [mem_eraseSet] at hj
    obtain ⟨k, _, hne⟩ := hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hEq
    exact hne (congrFun hEq k).symm
  · intro j₁ _ j₂ _ h
    exact h
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨j, ?_, rfl⟩
    rw [mem_eraseSet]
    have hne : ¬∀ k, f j k = W j k := fun h => hj (funext h)
    push_neg at hne
    obtain ⟨k, hk⟩ := hne
    exact ⟨k, k.isLt, fun h => hk h.symm⟩

end PathData

/-! ## Colours, budgets, and node classes -/

section Colours

variable [DecidableEq F] (C : Set (ι → F)) (δ : ℝ) {m : ℕ}

/-- The level-`l` edge is **White**: its weight is below `d(C) − δ·n`. -/
def IsWhiteAt (f W : Matrix ι (Fin m) F) (l : Fin m) : Prop :=
  (levelWt f W l : ℝ) < (Code.minDist C : ℝ) - δ * (Fintype.card ι)

/-- The level-`l` edge is **Red**: it is at or beyond the unique-decoding
radius of the punctured code, i.e. `d(C) ≤ 2·weight + |eraseSet|`. -/
def IsRedAt (f W : Matrix ι (Fin m) F) (l : Fin m) : Prop :=
  Code.minDist C ≤ 2 * levelWt f W l + (eraseSet f W (l : ℕ)).card

/-- The level-`l` edge is **Blue**: neither White nor Red. -/
def IsBlueAt (f W : Matrix ι (Fin m) F) (l : Fin m) : Prop :=
  ¬ IsWhiteAt C δ f W l ∧ ¬ IsRedAt C f W l

open Classical in
/-- Number of Blue levels at or after level `i` on the path of `W`. -/
noncomputable def blueAfter (f W : Matrix ι (Fin m) F) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun l : Fin m => i ≤ (l : ℕ) ∧ IsBlueAt C δ f W l).card

open Classical in
/-- Number of Red levels at or after level `i` on the path of `W`. -/
noncomputable def redAfter (f W : Matrix ι (Fin m) F) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun l : Fin m => i ≤ (l : ℕ) ∧ IsRedAt C f W l).card

/-- Whiteness only depends on the columns up to and including the level. -/
lemma isWhiteAt_congr {f W W' : Matrix ι (Fin m) F} {l : Fin m}
    (h : ∀ k : Fin m, (k : ℕ) < (l : ℕ) + 1 → ∀ j, W j k = W' j k) :
    IsWhiteAt C δ f W l ↔ IsWhiteAt C δ f W' l := by
  unfold IsWhiteAt
  rw [levelWt_congr h]

/-- Codewords agree on all columns below `i` with a reference codeword. -/
def prefixAgree (V W : Matrix ι (Fin m) F) (i : ℕ) : Prop :=
  ∀ l : Fin m, (l : ℕ) < i → ∀ j, W j l = V j l

/-- The set of close interleaved codewords passing through the tree node
`(i, V)` whose remaining colour counts fit the budgets `(b', r')`. -/
def nodeClass (f : Matrix ι (Fin m) F) (i : ℕ) (V : Matrix ι (Fin m) F)
    (b' r' : ℕ) : Set (Matrix ι (Fin m) F) :=
  {W | W ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ ∧
    prefixAgree V W i ∧ blueAfter C δ f W i ≤ b' ∧ redAfter C f W i ≤ r'}

/-- The Algorithm-1 leaf-count function certified by the construction: the
worst node class over all tree nodes. -/
noncomputable def leafBound (f : Matrix ι (Fin m) F) (b' r' : ℕ) : ℕ∞ :=
  ⨆ (i : ℕ) (V : Matrix ι (Fin m) F)
      (_ : V ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ),
    (nodeClass C δ f i V b' r').encard

lemma nodeClass_encard_le_leafBound (f : Matrix ι (Fin m) F) {i : ℕ}
    {V : Matrix ι (Fin m) F}
    (hV : V ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    (b' r' : ℕ) :
    (nodeClass C δ f i V b' r').encard ≤ leafBound C δ f b' r' := by
  unfold leafBound
  exact le_iSup_of_le i (le_iSup_of_le V (le_iSup_of_le hV le_rfl))

end Colours

/-! ## Basic facts about close codewords -/

section CloseFacts

variable [DecidableEq F] {C : Set (ι → F)} {δ : ℝ} {m : ℕ} {f : Matrix ι (Fin m) F}

/-- Columns of close interleaved codewords are codewords. -/
lemma col_mem_of_close {W : Matrix ι (Fin m) F}
    (hW : W ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    (l : Fin m) : (fun j => W j l) ∈ C := by
  have h : ∀ k : Fin m, W.transpose k ∈ C := hW.1
  have hcol : W.transpose l = fun j => W j l := by
    funext j
    rfl
  rw [← hcol]
  exact h l

/-- Closeness, in absolute terms: the final erasure count is at most `δ·n`. -/
lemma total_le_of_close [Nonempty ι] {W : Matrix ι (Fin m) F}
    (hW : W ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ) :
    ((eraseSet f W m).card : ℝ) ≤ δ * (Fintype.card ι) := by
  classical
  obtain ⟨_, hball⟩ := hW
  rw [relHammingBall, Set.mem_setOf_eq] at hball
  -- transport to the ambient `DecidableEq` instance (`Decidable` is a subsingleton)
  have hballI : ((Code.relHammingDist f W : ℚ≥0) : ℝ) ≤ δ := by
    convert hball using 3
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [card_eraseSet_top]
  have hdist : ((Code.relHammingDist f W : ℚ≥0) : ℝ)
      = (hammingDist f W : ℝ) / (Fintype.card ι : ℝ) := by
    unfold Code.relHammingDist
    push_cast
    try ring
  rw [hdist, div_le_iff₀ hcard] at hballI
  exact hballI

/-- Prefix-erasures plus the level weight stay within the total count. -/
lemma mu_add_wt_le_total {W : Matrix ι (Fin m) F} (l : Fin m) :
    (eraseSet f W (l : ℕ)).card + levelWt f W l ≤ (eraseSet f W m).card := by
  rw [← card_eraseSet_succ]
  exact Finset.card_le_card (eraseSet_mono f W l.isLt)

/-- **Master inequality** (heart of GGR11 Lemmas 3.3–3.5): if two close
codewords share all columns below `l` but differ at column `l`, then
`d(C) ≤ μ + w + w'` where `μ` is the shared erasure count at level `l` and
`w, w'` are the two level weights. -/
lemma minDist_le_mu_add_wt_add_wt {W W' : Matrix ι (Fin m) F}
    (hW : W ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    (hW' : W' ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    {l : Fin m}
    (hpre : ∀ k : Fin m, (k : ℕ) < (l : ℕ) → ∀ j, W j k = W' j k)
    (hdiff : ∃ j, W j l ≠ W' j l) :
    Code.minDist C
      ≤ (eraseSet f W (l : ℕ)).card + levelWt f W l + levelWt f W' l := by
  classical
  have hcC : (fun j => W j l) ∈ C := col_mem_of_close hW l
  have hc'C : (fun j => W' j l) ∈ C := col_mem_of_close hW' l
  have hne : (fun j => W j l) ≠ (fun j => W' j l) := by
    obtain ⟨j, hj⟩ := hdiff
    intro h
    exact hj (congrFun h j)
  -- the minimum distance lower-bounds the distance of the two columns
  have hmin : Code.minDist C ≤ hammingDist (fun j => W j l) (fun j => W' j l) := by
    unfold Code.minDist
    exact Nat.sInf_le ⟨_, hcC, _, hc'C, hne, rfl⟩
  -- the disagreement of the two columns is covered by the three sets
  have hcover : (Finset.univ.filter fun j => (fun j' => W j' l) j ≠ (fun j' => W' j' l) j)
      ⊆ (eraseSet f W (l : ℕ)
          ∪ Finset.univ.filter (fun j => j ∉ eraseSet f W (l : ℕ) ∧ W j l ≠ f j l))
        ∪ Finset.univ.filter (fun j => j ∉ eraseSet f W' (l : ℕ) ∧ W' j l ≠ f j l) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_cases hjS : j ∈ eraseSet f W (l : ℕ)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hjS)
    · have hjS' : j ∉ eraseSet f W' (l : ℕ) := by
        intro hmem
        rw [eraseSet_congr (f := f) (fun k hk j' => (hpre k hk j').symm)] at hmem
        exact hjS hmem
      by_cases hWf : W j l = f j l
      · -- then `W' j l ≠ f j l`, else the columns would agree at `j`
        have hW'f : W' j l ≠ f j l := by
          intro hW'f
          exact hj (show W j l = W' j l by rw [hWf, hW'f])
        refine Finset.mem_union_right _ ?_
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ j, hjS', hW'f⟩
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ j, hjS, hWf⟩
  have hdist : hammingDist (fun j => W j l) (fun j => W' j l)
      ≤ (eraseSet f W (l : ℕ)).card + levelWt f W l + levelWt f W' l := by
    unfold hammingDist levelWt
    refine le_trans (Finset.card_le_card hcover) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    exact add_le_add (Finset.card_union_le _ _) le_rfl
  exact le_trans hmin hdist

/-- **GGR11 Lemma 3.3** (White uniqueness): a White edge has no sibling. -/
lemma eq_col_of_isWhiteAt [Nonempty ι] {W W' : Matrix ι (Fin m) F}
    (hW : W ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    (hW' : W' ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    {l : Fin m}
    (hpre : ∀ k : Fin m, (k : ℕ) < (l : ℕ) → ∀ j, W j k = W' j k)
    (hwhite : IsWhiteAt C δ f W l) :
    ∀ j, W j l = W' j l := by
  by_contra hcon
  push_neg at hcon
  have hmaster := minDist_le_mu_add_wt_add_wt hW hW' hpre hcon
  -- `W'`'s level weight is bounded by its remaining budget `δ·n − μ`
  have hS : eraseSet f W' (l : ℕ) = eraseSet f W (l : ℕ) :=
    eraseSet_congr (fun k hk j => (hpre k hk j).symm)
  have hbudget' : ((eraseSet f W (l : ℕ)).card : ℝ) + levelWt f W' l
      ≤ δ * (Fintype.card ι) := by
    have h1 := mu_add_wt_le_total (f := f) (W := W') l
    rw [hS] at h1
    have h2 := total_le_of_close hW'
    have h3 : (((eraseSet f W (l : ℕ)).card + levelWt f W' l : ℕ) : ℝ)
        ≤ ((eraseSet f W' m).card : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  unfold IsWhiteAt at hwhite
  have hmaster' : (Code.minDist C : ℝ)
      ≤ ((eraseSet f W (l : ℕ)).card : ℝ) + levelWt f W l + levelWt f W' l := by
    exact_mod_cast hmaster
  linarith

/-- **GGR11 Lemma 3.4, sibling half**: two non-Red edges from the same node
agree — at most one codeword lies within the unique-decoding radius of the
punctured code. -/
lemma eq_col_of_not_isRedAt {W W' : Matrix ι (Fin m) F}
    (hW : W ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    (hW' : W' ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    {l : Fin m}
    (hpre : ∀ k : Fin m, (k : ℕ) < (l : ℕ) → ∀ j, W j k = W' j k)
    (hred : ¬ IsRedAt C f W l) (hred' : ¬ IsRedAt C f W' l) :
    ∀ j, W j l = W' j l := by
  by_contra hcon
  push_neg at hcon
  have hmaster := minDist_le_mu_add_wt_add_wt hW hW' hpre hcon
  have hS : eraseSet f W' (l : ℕ) = eraseSet f W (l : ℕ) :=
    eraseSet_congr (fun k hk j => (hpre k hk j).symm)
  unfold IsRedAt at hred hred'
  rw [hS] at hred'
  omega

/-- Each column of a close interleaved codeword is `δ`-close to the
corresponding column of the received word, so per-node branching is bounded by
the base list (in-tree: `ListSize.transpose_mem_closeCodewordsRel`). -/
lemma col_mem_closeCodewordsRel [Nonempty ι] {W : Matrix ι (Fin m) F}
    (hW : W ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    (l : Fin m) :
    (fun j => W j l) ∈ closeCodewordsRel C (fun j => f j l) δ :=
  ListSize.transpose_mem_closeCodewordsRel hW l

end CloseFacts

/-! ## Per-codeword budget lemmas (GGR11 Lemmas 3.4 and 3.5) -/

section Budgets

variable [DecidableEq F] {C : Set (ι → F)} {δ : ℝ} {m : ℕ} {f : Matrix ι (Fin m) F}

/-- **GGR11 Lemma 3.4, budget half**: the number of Blue levels is bounded by
any `b` with `δ·n ≤ b·(d(C) − δ·n)`. -/
lemma blueAfter_le_budget [Nonempty ι] {W : Matrix ι (Fin m) F}
    (hW : W ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    {b : ℕ}
    (hδD : δ * (Fintype.card ι) < (Code.minDist C : ℝ))
    (hb : δ * (Fintype.card ι)
      ≤ (b : ℝ) * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)))
    (i : ℕ) :
    blueAfter C δ f W i ≤ b := by
  classical
  set η : ℝ := (Code.minDist C : ℝ) - δ * (Fintype.card ι) with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  set B : Finset (Fin m) :=
    Finset.univ.filter (fun l : Fin m => i ≤ (l : ℕ) ∧ IsBlueAt C δ f W l) with hB
  -- each Blue level has weight at least η
  have hwt : ∀ l ∈ B, η ≤ (levelWt f W l : ℝ) := by
    intro l hl
    rw [hB, Finset.mem_filter] at hl
    have hwhite := hl.2.2.1
    unfold IsWhiteAt at hwhite
    rw [hη]
    linarith [not_lt.mp hwhite]
  -- the weights over Blue levels sum to at most the total `δ·n`
  have hsum : ∑ l ∈ B, (levelWt f W l : ℝ) ≤ δ * (Fintype.card ι) := by
    have h1 : ∑ l ∈ B, (levelWt f W l : ℝ) ≤ ∑ l : Fin m, (levelWt f W l : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      intro l _ _
      positivity
    have hfil : Finset.univ.filter (fun l : Fin m => (l : ℕ) < m) =
        (Finset.univ : Finset (Fin m)) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact l.isLt
    have h2 : ∑ l : Fin m, (levelWt f W l : ℝ) = ((eraseSet f W m).card : ℝ) := by
      have h3 := card_eraseSet_eq_sum f W m le_rfl
      rw [hfil] at h3
      rw [h3]
      push_cast
      try rfl
    rw [h2] at h1
    exact le_trans h1 (total_le_of_close hW)
  -- combine: `|B| · η ≤ δ·n ≤ b · η`
  have hcard : (B.card : ℝ) * η ≤ δ * (Fintype.card ι) := by
    have hns := Finset.card_nsmul_le_sum B (fun l => (levelWt f W l : ℝ)) η hwt
    rw [nsmul_eq_mul] at hns
    exact le_trans hns hsum
  have hfinal : (B.card : ℝ) ≤ (b : ℝ) :=
    le_of_mul_le_mul_right (le_trans hcard hb) hηpos
  have hcards : B.card ≤ b := by exact_mod_cast hfinal
  unfold blueAfter
  exact hcards

open Classical in
/-- The number of Red levels strictly below level `i`. -/
private noncomputable def redBefore (C : Set (ι → F)) (f W : Matrix ι (Fin m) F)
    (i : ℕ) : ℕ :=
  (Finset.univ.filter fun l : Fin m => (l : ℕ) < i ∧ IsRedAt C f W l).card

/-- **The Red doubling invariant** (GGR11 Lemma 3.5): along the path, each Red
level halves the deficit `d(C) − μ`. -/
private lemma redDoubling_invariant {W : Matrix ι (Fin m) F} :
    ∀ i, i ≤ m → (2 : ℝ) ^ (redBefore C f W i) *
        ((Code.minDist C : ℝ) - (eraseSet f W i).card)
      ≤ (Code.minDist C : ℝ) := by
  classical
  intro i
  induction i with
  | zero =>
    intro _
    simp [redBefore, eraseSet_zero]
  | succ i ih =>
    intro hi
    have him : i < m := hi
    have hih := ih (le_of_lt him)
    set l : Fin m := ⟨i, him⟩ with hl
    have hcard : (eraseSet f W (i + 1)).card
        = (eraseSet f W i).card + levelWt f W l :=
      card_eraseSet_succ f W l
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (redBefore C f W i) := by positivity
    by_cases hred : IsRedAt C f W l
    · -- Red step: the deficit halves, the exponent increments
      have hrb : redBefore C f W (i + 1) = redBefore C f W i + 1 := by
        unfold redBefore
        have hins : Finset.univ.filter
            (fun l' : Fin m => (l' : ℕ) < i + 1 ∧ IsRedAt C f W l')
            = insert l (Finset.univ.filter
                (fun l' : Fin m => (l' : ℕ) < i ∧ IsRedAt C f W l')) := by
          ext l'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hlt, hr⟩
            rcases (Nat.lt_succ_iff.mp hlt).lt_or_eq with h | h
            · exact Or.inr ⟨h, hr⟩
            · exact Or.inl (Fin.ext h)
          · rintro (rfl | ⟨hlt, hr⟩)
            · exact ⟨Nat.lt_succ_self _, hred⟩
            · exact ⟨Nat.lt_succ_of_lt hlt, hr⟩
        have hlnot : l ∉ Finset.univ.filter
            (fun l' : Fin m => (l' : ℕ) < i ∧ IsRedAt C f W l') := by
          intro hmem
          rw [Finset.mem_filter] at hmem
          have hlt : (l : ℕ) < i := hmem.2.1
          rw [hl] at hlt
          exact absurd hlt (lt_irrefl i)
        rw [hins, Finset.card_insert_of_notMem hlnot]
      have hwt : (Code.minDist C : ℝ)
          ≤ 2 * levelWt f W l + (eraseSet f W i).card := by
        unfold IsRedAt at hred
        exact_mod_cast hred
      have hhalf : 2 * ((Code.minDist C : ℝ) - (eraseSet f W (i + 1)).card)
          ≤ (Code.minDist C : ℝ) - (eraseSet f W i).card := by
        rw [hcard]
        push_cast
        linarith
      calc (2 : ℝ) ^ (redBefore C f W (i + 1)) *
            ((Code.minDist C : ℝ) - (eraseSet f W (i + 1)).card)
          = (2 : ℝ) ^ (redBefore C f W i) *
              (2 * ((Code.minDist C : ℝ) - (eraseSet f W (i + 1)).card)) := by
            rw [hrb]; ring
        _ ≤ (2 : ℝ) ^ (redBefore C f W i) *
              ((Code.minDist C : ℝ) - (eraseSet f W i).card) :=
            mul_le_mul_of_nonneg_left hhalf (le_of_lt hpow_pos)
        _ ≤ (Code.minDist C : ℝ) := hih
    · -- non-Red step: the deficit does not increase
      have hrb : redBefore C f W (i + 1) = redBefore C f W i := by
        unfold redBefore
        congr 1
        ext l'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hlt, hr⟩
          rcases (Nat.lt_succ_iff.mp hlt).lt_or_eq with h | h
          · exact ⟨h, hr⟩
          · exact absurd hr (by rw [show l' = l from Fin.ext h]; exact hred)
        · rintro ⟨hlt, hr⟩
          exact ⟨Nat.lt_succ_of_lt hlt, hr⟩
      have hmono : ((eraseSet f W i).card : ℝ)
          ≤ ((eraseSet f W (i + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (eraseSet_mono f W (Nat.le_succ i))
      calc (2 : ℝ) ^ (redBefore C f W (i + 1)) *
            ((Code.minDist C : ℝ) - (eraseSet f W (i + 1)).card)
          ≤ (2 : ℝ) ^ (redBefore C f W i) *
              ((Code.minDist C : ℝ) - (eraseSet f W i).card) := by
            rw [hrb]
            exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hpow_pos)
        _ ≤ (Code.minDist C : ℝ) := hih

/-- **GGR11 Lemma 3.5**: the number of Red levels is bounded by any `r` with
`d(C) ≤ 2^r·(d(C) − δ·n)`. -/
lemma redAfter_le_budget [Nonempty ι] {W : Matrix ι (Fin m) F}
    (hW : W ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    {r : ℕ}
    (hδD : δ * (Fintype.card ι) < (Code.minDist C : ℝ))
    (hr : (Code.minDist C : ℝ)
      ≤ 2 ^ r * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)))
    (i : ℕ) :
    redAfter C f W i ≤ r := by
  classical
  by_contra hcon
  push_neg at hcon
  -- pick the largest Red level: at least `r` Red levels precede it
  set R : Finset (Fin m) :=
    Finset.univ.filter (fun l : Fin m => i ≤ (l : ℕ) ∧ IsRedAt C f W l) with hR
  have hcard : r + 1 ≤ R.card := hcon
  have hne : R.Nonempty := Finset.card_pos.mp (by omega)
  set lmax : Fin m := R.max' hne with hlmax
  have hlmaxR : lmax ∈ R := R.max'_mem hne
  have hlmax_red : IsRedAt C f W lmax := by
    have hmem := hlmaxR
    rw [hR, Finset.mem_filter] at hmem
    exact hmem.2.2
  -- every other Red level is strictly below `lmax`
  have herase : R.erase lmax ⊆
      Finset.univ.filter
        (fun l : Fin m => (l : ℕ) < (lmax : ℕ) ∧ IsRedAt C f W l) := by
    intro l hl
    have hmem := Finset.mem_of_mem_erase hl
    have hne' := Finset.ne_of_mem_erase hl
    have hle := R.le_max' l hmem
    rw [hR, Finset.mem_filter] at hmem
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ l, lt_of_le_of_ne hle (fun h => hne' (Fin.ext h)), hmem.2.2⟩
  have hrb : r ≤ redBefore C f W (lmax : ℕ) := by
    unfold redBefore
    calc r = (r + 1) - 1 := by omega
      _ ≤ R.card - 1 := by omega
      _ = (R.erase lmax).card := (Finset.card_erase_of_mem hlmaxR).symm
      _ ≤ _ := Finset.card_le_card herase
  -- the invariant forces `μ ≥ δ·n` at `lmax`
  have hinv := redDoubling_invariant (C := C) (f := f) (W := W)
    (lmax : ℕ) (le_of_lt lmax.isLt)
  have hμtot : ((eraseSet f W (lmax : ℕ)).card : ℝ) ≤ δ * (Fintype.card ι) := by
    have h1 : ((eraseSet f W (lmax : ℕ)).card : ℝ) ≤ ((eraseSet f W m).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (eraseSet_mono f W (le_of_lt lmax.isLt))
    linarith [total_le_of_close hW]
  have hpow_mono : (2 : ℝ) ^ r ≤ (2 : ℝ) ^ (redBefore C f W (lmax : ℕ)) :=
    pow_le_pow_right₀ (by norm_num) hrb
  have hdef : (2 : ℝ) ^ r *
      ((Code.minDist C : ℝ) - (eraseSet f W (lmax : ℕ)).card)
      ≤ (Code.minDist C : ℝ) := by
    calc (2 : ℝ) ^ r * ((Code.minDist C : ℝ) - (eraseSet f W (lmax : ℕ)).card)
        ≤ (2 : ℝ) ^ (redBefore C f W (lmax : ℕ)) *
            ((Code.minDist C : ℝ) - (eraseSet f W (lmax : ℕ)).card) := by
          apply mul_le_mul_of_nonneg_right hpow_mono
          linarith
      _ ≤ (Code.minDist C : ℝ) := hinv
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  -- hence `δ·n ≤ μ` at `lmax`
  have hμδ : δ * (Fintype.card ι) ≤ ((eraseSet f W (lmax : ℕ)).card : ℝ) := by
    by_contra hμδ
    push_neg at hμδ
    have hlt : (2 : ℝ) ^ r * ((Code.minDist C : ℝ) - δ * (Fintype.card ι))
        < 2 ^ r * ((Code.minDist C : ℝ) - (eraseSet f W (lmax : ℕ)).card) := by
      apply mul_lt_mul_of_pos_left _ hpow_pos
      linarith
    linarith
  -- but Red at `lmax` forces `d(C) ≤ 2·w + μ` with `μ + w ≤ δ·n`
  have hbudget : ((eraseSet f W (lmax : ℕ)).card : ℝ) + levelWt f W lmax
      ≤ δ * (Fintype.card ι) := by
    have h1 := mu_add_wt_le_total (f := f) (W := W) lmax
    have h2 : (((eraseSet f W (lmax : ℕ)).card + levelWt f W lmax : ℕ) : ℝ)
        ≤ ((eraseSet f W m).card : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith [total_le_of_close hW]
  have hred' : (Code.minDist C : ℝ)
      ≤ 2 * levelWt f W lmax + (eraseSet f W (lmax : ℕ)).card := by
    unfold IsRedAt at hlmax_red
    exact_mod_cast hlmax_red
  linarith

end Budgets

/-! ## The Pascal recursion for `leafBound` -/

section Recursion

variable [DecidableEq F] {C : Set (ι → F)} {δ : ℝ} {m : ℕ} {f : Matrix ι (Fin m) F}

/-- Generic finite-fiber counting: if `g` maps `s` into a finset `t` and every
fiber has `encard ≤ T`, then `s.encard ≤ |t| · T`. -/
private lemma encard_le_card_mul_of_fibers {α β : Type*} {s : Set α} {g : α → β}
    {t : Finset β} {T : ℕ∞}
    (hmaps : ∀ a ∈ s, g a ∈ t)
    (hfib : ∀ b ∈ t, {a ∈ s | g a = b}.encard ≤ T) :
    s.encard ≤ (t.card : ℕ∞) * T := by
  classical
  induction t using Finset.induction generalizing s with
  | empty =>
    have hs : s = ∅ := by
      ext a
      simp only [Set.mem_empty_iff_false, iff_false]
      intro ha
      exact absurd (hmaps a ha) (Finset.notMem_empty _)
    simp [hs]
  | @insert b t hb ih =>
    have hsplit : s = {a ∈ s | g a = b} ∪ {a ∈ s | g a ≠ b} := by
      ext a
      simp only [Set.mem_union, Set.mem_setOf_eq]
      constructor
      · intro ha
        by_cases h : g a = b
        · exact Or.inl ⟨ha, h⟩
        · exact Or.inr ⟨ha, h⟩
      · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
    have h1 : {a ∈ s | g a = b}.encard ≤ T := hfib b (Finset.mem_insert_self b t)
    have h2 : {a ∈ s | g a ≠ b}.encard ≤ (t.card : ℕ∞) * T := by
      apply ih
      · intro a ha
        obtain ⟨has, hne⟩ := ha
        rcases Finset.mem_insert.mp (hmaps a has) with h | h
        · exact absurd h hne
        · exact h
      · intro c hc
        refine le_trans (Set.encard_mono ?_) (hfib c (Finset.mem_insert_of_mem hc))
        intro a ha
        exact ⟨ha.1.1, ha.2⟩
    calc s.encard ≤ {a ∈ s | g a = b}.encard + {a ∈ s | g a ≠ b}.encard :=
          le_trans (le_of_eq (congrArg Set.encard hsplit)) (Set.encard_union_le _ _)
      _ ≤ T + (t.card : ℕ∞) * T := add_le_add h1 h2
      _ = ((t.card + 1 : ℕ) : ℕ∞) * T := by
          push_cast
          ring
      _ = ((insert b t).card : ℕ∞) * T := by
          rw [Finset.card_insert_of_notMem hb]

/-- Whenever some close codeword exists, every leaf-count value is at least 1,
witnessed by the leaf node of that codeword. -/
private lemma one_le_leafBound
    (hne : (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).Nonempty)
    (b' r' : ℕ) : 1 ≤ leafBound C δ f b' r' := by
  classical
  obtain ⟨W₀, hW₀⟩ := hne
  have hblue : blueAfter C δ f W₀ m = 0 := by
    unfold blueAfter
    rw [Finset.card_eq_zero]
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_and]
    intro h
    exact absurd h (Nat.not_le.mpr l.isLt)
  have hred : redAfter C f W₀ m = 0 := by
    unfold redAfter
    rw [Finset.card_eq_zero]
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_and]
    intro h
    exact absurd h (Nat.not_le.mpr l.isLt)
  have hmem : W₀ ∈ nodeClass C δ f m W₀ b' r' := by
    refine ⟨hW₀, fun l _ j => rfl, ?_, ?_⟩
    · rw [hblue]; exact Nat.zero_le _
    · rw [hred]; exact Nat.zero_le _
  calc (1 : ℕ∞) ≤ (nodeClass C δ f m W₀ b' r').encard := by
        rw [Set.one_le_encard_iff_nonempty]
        exact ⟨W₀, hmem⟩
    _ ≤ leafBound C δ f b' r' := nodeClass_encard_le_leafBound C δ f hW₀ b' r'

/-- Budget counters shrink with the suffix. -/
private lemma blueAfter_mono (W : Matrix ι (Fin m) F) {i i' : ℕ} (h : i ≤ i') :
    blueAfter C δ f W i' ≤ blueAfter C δ f W i := by
  classical
  unfold blueAfter
  apply Finset.card_le_card
  intro l hl
  rw [Finset.mem_filter] at hl ⊢
  exact ⟨hl.1, le_trans h hl.2.1, hl.2.2⟩

private lemma redAfter_mono (W : Matrix ι (Fin m) F) {i i' : ℕ} (h : i ≤ i') :
    redAfter C f W i' ≤ redAfter C f W i := by
  classical
  unfold redAfter
  apply Finset.card_le_card
  intro l hl
  rw [Finset.mem_filter] at hl ⊢
  exact ⟨hl.1, le_trans h hl.2.1, hl.2.2⟩

/-- Consuming a Blue level decrements the Blue budget. -/
private lemma blueAfter_succ_add_one_le {W : Matrix ι (Fin m) F} {i : ℕ} {l : Fin m}
    (hil : i ≤ (l : ℕ)) (hblue : IsBlueAt C δ f W l) :
    blueAfter C δ f W ((l : ℕ) + 1) + 1 ≤ blueAfter C δ f W i := by
  classical
  unfold blueAfter
  have hnot : l ∉ Finset.univ.filter
      (fun l' : Fin m => (l : ℕ) + 1 ≤ (l' : ℕ) ∧ IsBlueAt C δ f W l') := by
    rw [Finset.mem_filter]
    push_neg
    intro _ h
    exact absurd h (by omega)
  have hsub : insert l (Finset.univ.filter
      (fun l' : Fin m => (l : ℕ) + 1 ≤ (l' : ℕ) ∧ IsBlueAt C δ f W l'))
      ⊆ Finset.univ.filter
        (fun l' : Fin m => i ≤ (l' : ℕ) ∧ IsBlueAt C δ f W l') := by
    intro l' hl'
    rcases Finset.mem_insert.mp hl' with rfl | hl'
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ l', hil, hblue⟩
    · rw [Finset.mem_filter] at hl' ⊢
      exact ⟨hl'.1, by omega, hl'.2.2⟩
  calc (Finset.univ.filter
        (fun l' : Fin m => (l : ℕ) + 1 ≤ (l' : ℕ) ∧ IsBlueAt C δ f W l')).card + 1
      = (insert l (Finset.univ.filter
          (fun l' : Fin m => (l : ℕ) + 1 ≤ (l' : ℕ) ∧ IsBlueAt C δ f W l'))).card :=
        (Finset.card_insert_of_notMem hnot).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Consuming a Red level decrements the Red budget. -/
private lemma redAfter_succ_add_one_le {W : Matrix ι (Fin m) F} {i : ℕ} {l : Fin m}
    (hil : i ≤ (l : ℕ)) (hred : IsRedAt C f W l) :
    redAfter C f W ((l : ℕ) + 1) + 1 ≤ redAfter C f W i := by
  classical
  unfold redAfter
  have hnot : l ∉ Finset.univ.filter
      (fun l' : Fin m => (l : ℕ) + 1 ≤ (l' : ℕ) ∧ IsRedAt C f W l') := by
    rw [Finset.mem_filter]
    push_neg
    intro _ h
    exact absurd h (by omega)
  have hsub : insert l (Finset.univ.filter
      (fun l' : Fin m => (l : ℕ) + 1 ≤ (l' : ℕ) ∧ IsRedAt C f W l'))
      ⊆ Finset.univ.filter
        (fun l' : Fin m => i ≤ (l' : ℕ) ∧ IsRedAt C f W l') := by
    intro l' hl'
    rcases Finset.mem_insert.mp hl' with rfl | hl'
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ l', hil, hred⟩
    · rw [Finset.mem_filter] at hl' ⊢
      exact ⟨hl'.1, by omega, hl'.2.2⟩
  calc (Finset.univ.filter
        (fun l' : Fin m => (l : ℕ) + 1 ≤ (l' : ℕ) ∧ IsRedAt C f W l')).card + 1
      = (insert l (Finset.univ.filter
          (fun l' : Fin m => (l : ℕ) + 1 ≤ (l' : ℕ) ∧ IsRedAt C f W l'))).card :=
        (Finset.card_insert_of_notMem hnot).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The first column on which two distinct matrices differ. -/
private lemma exists_first_diff {W W' : Matrix ι (Fin m) F} (hne : W ≠ W') :
    ∃ d : Fin m, (∃ j, W j d ≠ W' j d) ∧
      ∀ k : Fin m, (k : ℕ) < (d : ℕ) → ∀ j, W j k = W' j k := by
  classical
  set K : Finset (Fin m) := Finset.univ.filter (fun k => ∃ j, W j k ≠ W' j k) with hK
  have hKne : K.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hne
    funext j k
    by_contra hjk
    have hkK : k ∈ K := by
      rw [hK, Finset.mem_filter]
      exact ⟨Finset.mem_univ k, j, hjk⟩
    rw [h] at hkK
    exact absurd hkK (Finset.notMem_empty _)
  have hmemK : ∀ x ∈ K, ∃ j, W j x ≠ W' j x := by
    intro x hx
    rw [hK, Finset.mem_filter] at hx
    exact hx.2
  refine ⟨K.min' hKne, ?_, ?_⟩
  · exact hmemK _ (K.min'_mem hKne)
  · intro k hk j
    by_contra hjk
    have hkK : k ∈ K := by
      rw [hK, Finset.mem_filter]
      exact ⟨Finset.mem_univ k, j, hjk⟩
    have hle := K.min'_le k hkK
    have hle' : ((K.min' hKne : Fin m) : ℕ) ≤ (k : ℕ) := hle
    omega

/-- **`t(b', 0) ≤ 1`**: with no Red budget every node class is a chain of
forced choices, hence contains at most one codeword. -/
private lemma nodeClass_encard_le_one {i : ℕ} {V : Matrix ι (Fin m) F} {b' : ℕ} :
    (nodeClass C δ f i V b' 0).encard ≤ 1 := by
  classical
  rw [Set.encard_le_one_iff]
  intro W W' hW hW'
  by_contra hne
  obtain ⟨d, hdne, hdpre⟩ := exists_first_diff hne
  -- the first difference is at or above `i` (shared prefix with `V`)
  have hdi : i ≤ (d : ℕ) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨j, hj⟩ := hdne
    exact hj (by rw [hW.2.1 d hcon j, hW'.2.1 d hcon j])
  -- with Red budget 0, no level at or above `i` is Red for either codeword
  have hnored : ∀ {U : Matrix ι (Fin m) F}, U ∈ nodeClass C δ f i V b' 0 →
      ¬ IsRedAt C f U d := by
    intro U hU hred
    have hpos : 0 < redAfter C f U i := by
      unfold redAfter
      apply Finset.card_pos.mpr
      exact ⟨d, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ d, hdi, hred⟩⟩
    have hr0 : redAfter C f U i ≤ 0 := hU.2.2.2
    omega
  obtain ⟨j, hj⟩ := hdne
  exact hj (eq_col_of_not_isRedAt hW.1 hW'.1 hdpre
    (hnored hW) (hnored hW') j)

/-- **The common branching level.** In a node class where every member has a
non-White level in its suffix, all members share their columns below a common
level `l* ≥ i`, at which every member is non-White. -/
private lemma exists_common_branch [Nonempty ι]
    {i : ℕ} {V W₀ : Matrix ι (Fin m) F} {b' r' : ℕ}
    (hW₀ : W₀ ∈ nodeClass C δ f i V b' r')
    (hex : ∀ W ∈ nodeClass C δ f i V b' r',
      ∃ l : Fin m, i ≤ (l : ℕ) ∧ ¬ IsWhiteAt C δ f W l) :
    ∃ lstar : Fin m, i ≤ (lstar : ℕ) ∧
      (∀ W ∈ nodeClass C δ f i V b' r', ¬ IsWhiteAt C δ f W lstar) ∧
      (∀ W ∈ nodeClass C δ f i V b' r',
        ∀ k : Fin m, (k : ℕ) < (lstar : ℕ) → ∀ j, W j k = W₀ j k) := by
  classical
  -- the first non-White level of the reference codeword
  set L : Finset (Fin m) :=
    Finset.univ.filter (fun l => i ≤ (l : ℕ) ∧ ¬ IsWhiteAt C δ f W₀ l) with hL
  have hLne : L.Nonempty := by
    obtain ⟨l, hl1, hl2⟩ := hex W₀ hW₀
    refine ⟨l, ?_⟩
    rw [hL, Finset.mem_filter]
    exact ⟨Finset.mem_univ l, hl1, hl2⟩
  set lstar : Fin m := L.min' hLne with hlstar
  have hmem : lstar ∈ L := L.min'_mem hLne
  rw [hL, Finset.mem_filter] at hmem
  obtain ⟨_, hlstar_ge, hlstar_nw⟩ := hmem
  -- all levels in `[i, l*)` are White for `W₀`
  have hW₀white : ∀ l : Fin m, i ≤ (l : ℕ) → (l : ℕ) < (lstar : ℕ) →
      IsWhiteAt C δ f W₀ l := by
    intro l hl1 hl2
    by_contra hcon
    have hlL : l ∈ L := by
      rw [hL, Finset.mem_filter]
      exact ⟨Finset.mem_univ l, hl1, hcon⟩
    have hle' : (lstar : ℕ) ≤ (l : ℕ) := L.min'_le l hlL
    omega
  -- shared sub-arguments: the first difference with `W₀` is at or above `l*`
  have hkey : ∀ W ∈ nodeClass C δ f i V b' r', W ≠ W₀ →
      ∃ d : Fin m, (lstar : ℕ) ≤ (d : ℕ) ∧ (∃ j, W j d ≠ W₀ j d) ∧
        ∀ k : Fin m, (k : ℕ) < (d : ℕ) → ∀ j, W j k = W₀ j k := by
    intro W hW hne
    obtain ⟨d, hdne, hdpre⟩ := exists_first_diff hne
    have hdi : i ≤ (d : ℕ) := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨j, hj⟩ := hdne
      exact hj (by rw [hW.2.1 d hcon j, hW₀.2.1 d hcon j])
    have hdlstar : (lstar : ℕ) ≤ (d : ℕ) := by
      by_contra hcon
      push_neg at hcon
      have hwhite := hW₀white d hdi hcon
      obtain ⟨j, hj⟩ := hdne
      exact hj ((eq_col_of_isWhiteAt hW₀.1 hW.1
        (fun k hk j' => (hdpre k hk j').symm) hwhite j).symm)
    exact ⟨d, hdlstar, hdne, hdpre⟩
  refine ⟨lstar, hlstar_ge, ?_, ?_⟩
  · -- every member is non-White at `l*`
    intro W hW
    by_cases heq : W = W₀
    · rw [heq]; exact hlstar_nw
    · obtain ⟨d, hdlstar, hdne, hdpre⟩ := hkey W hW heq
      by_cases hd : (lstar : ℕ) = (d : ℕ)
      · -- the columns differ at `l*` itself: White is impossible for `W`
        intro hwhite
        obtain ⟨j, hj⟩ := hdne
        have hl_eq : lstar = d := Fin.ext hd
        rw [← hl_eq] at hdpre hj
        exact hj (eq_col_of_isWhiteAt hW.1 hW₀.1 hdpre hwhite j)
      · -- the columns agree at `l*`: Whiteness transfers from `W₀`
        have hlt : (lstar : ℕ) < (d : ℕ) := lt_of_le_of_ne hdlstar hd
        intro hwhite
        apply hlstar_nw
        rw [← isWhiteAt_congr (C := C) (δ := δ) (f := f)
          (fun k hk j => hdpre k (by omega) j)]
        exact hwhite
  · -- shared prefix below `l*`
    intro W hW k hk j
    by_cases heq : W = W₀
    · rw [heq]
    · obtain ⟨d, hdlstar, _, hdpre⟩ := hkey W hW heq
      exact hdpre k (by omega) j

/-- **The Red side of the Pascal step**: the members of a node class that are
Red at a common branching level `l*` number at most `Λ(C,δ)` column choices,
each of whose classes has a decremented Red budget. -/
private lemma redPart_encard_le [Nonempty ι]
    (hfin : ∀ y : ι → F, (closeCodewordsRel C y δ).Finite)
    {i : ℕ} {V W₀ : Matrix ι (Fin m) F} {β ρ : ℕ} {lstar : Fin m}
    (hlstar_ge : i ≤ (lstar : ℕ))
    (hlstar_pre : ∀ W ∈ nodeClass C δ f i V β (ρ + 1),
      ∀ k : Fin m, (k : ℕ) < (lstar : ℕ) → ∀ j, W j k = W₀ j k) :
    {W ∈ nodeClass C δ f i V β (ρ + 1) | IsRedAt C f W lstar}.encard
      ≤ Lambda C δ * leafBound C δ f β ρ := by
  classical
  set hfinL := hfin (fun j => f j lstar) with hfinLdef
  have hmaps : ∀ W ∈ {W ∈ nodeClass C δ f i V β (ρ + 1) | IsRedAt C f W lstar},
      (fun j => W j lstar) ∈ hfinL.toFinset := by
    intro W hW
    rw [Set.Finite.mem_toFinset]
    exact col_mem_closeCodewordsRel hW.1.1 lstar
  have hfib : ∀ c ∈ hfinL.toFinset,
      {W ∈ {W ∈ nodeClass C δ f i V β (ρ + 1) | IsRedAt C f W lstar} |
          (fun j => W j lstar) = c}.encard
        ≤ leafBound C δ f β ρ := by
    intro c _
    rcases Set.eq_empty_or_nonempty
      {W ∈ {W ∈ nodeClass C δ f i V β (ρ + 1) | IsRedAt C f W lstar} |
        (fun j => W j lstar) = c} with hFe | hFne
    · rw [hFe]
      simp
    obtain ⟨WR, hWR⟩ := hFne
    have hsubR : {W ∈ {W ∈ nodeClass C δ f i V β (ρ + 1) | IsRedAt C f W lstar} |
          (fun j => W j lstar) = c}
        ⊆ nodeClass C δ f ((lstar : ℕ) + 1) WR β ρ := by
      intro W hW
      have hcol : ∀ j, W j lstar = WR j lstar := by
        intro j
        have h1 : (fun j' => W j' lstar) = c := hW.2
        have h2 : (fun j' => WR j' lstar) = c := hWR.2
        rw [← h2] at h1
        exact congrFun h1 j
      refine ⟨hW.1.1.1, ?_, ?_, ?_⟩
      · intro k hk j
        rcases (Nat.lt_succ_iff.mp hk).lt_or_eq with hk' | hk'
        · rw [hlstar_pre W hW.1.1 k hk' j, hlstar_pre WR hWR.1.1 k hk' j]
        · have hkl : k = lstar := Fin.ext hk'
          rw [hkl]
          exact hcol j
      · have hmono := blueAfter_mono (C := C) (δ := δ) (f := f) W
          (show i ≤ (lstar : ℕ) + 1 by omega)
        have hbW : blueAfter C δ f W i ≤ β := hW.1.1.2.2.1
        omega
      · have hdec := redAfter_succ_add_one_le (C := C) (f := f)
          (W := W) hlstar_ge hW.1.2
        have hrW : redAfter C f W i ≤ ρ + 1 := hW.1.1.2.2.2
        omega
    calc {W ∈ {W ∈ nodeClass C δ f i V β (ρ + 1) | IsRedAt C f W lstar} |
          (fun j => W j lstar) = c}.encard
        ≤ (nodeClass C δ f ((lstar : ℕ) + 1) WR β ρ).encard :=
          Set.encard_mono hsubR
      _ ≤ leafBound C δ f β ρ :=
          nodeClass_encard_le_leafBound C δ f hWR.1.1.1 β ρ
  have hcount := encard_le_card_mul_of_fibers hmaps hfib
  have hΛ : (hfinL.toFinset.card : ℕ∞) ≤ Lambda C δ := by
    have hcard : (closeCodewordsRel C (fun j => f j lstar) δ).ncard
        = hfinL.toFinset.card :=
      Set.ncard_eq_toFinset_card _ hfinL
    rw [← hcard]
    exact le_iSup (fun y => ((closeCodewordsRel C y δ).ncard : ℕ∞))
      (fun j => f j lstar)
  calc {W ∈ nodeClass C δ f i V β (ρ + 1) | IsRedAt C f W lstar}.encard
      ≤ (hfinL.toFinset.card : ℕ∞) * leafBound C δ f β ρ := hcount
    _ ≤ Lambda C δ * leafBound C δ f β ρ := mul_le_mul_right' hΛ _

/-- An all-White member makes its node class a singleton. -/
private lemma encard_le_one_of_allWhite [Nonempty ι]
    {i : ℕ} {V Wa : Matrix ι (Fin m) F} {β ρ : ℕ}
    (hWa : Wa ∈ nodeClass C δ f i V β ρ)
    (hWawhite : ∀ l : Fin m, i ≤ (l : ℕ) → IsWhiteAt C δ f Wa l) :
    (nodeClass C δ f i V β ρ).encard ≤ 1 := by
  have hsub : nodeClass C δ f i V β ρ ⊆ {Wa} := by
    intro W hW
    rw [Set.mem_singleton_iff]
    by_contra hne
    obtain ⟨d, hdne, hdpre⟩ := exists_first_diff hne
    have hdi : i ≤ (d : ℕ) := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨j, hj⟩ := hdne
      exact hj (by rw [hW.2.1 d hcon j, hWa.2.1 d hcon j])
    obtain ⟨j, hj⟩ := hdne
    exact hj ((eq_col_of_isWhiteAt hWa.1 hW.1
      (fun k hk j' => (hdpre k hk j').symm) (hWawhite d hdi) j).symm)
  calc (nodeClass C δ f i V β ρ).encard
      ≤ ({Wa} : Set (Matrix ι (Fin m) F)).encard := Set.encard_mono hsub
    _ = 1 := Set.encard_singleton Wa

/-- **The Red-only column of the Pascal recursion**:
`t(0, ρ+1) ≤ Λ(C,δ) · t(0, ρ)`. -/
private lemma nodeClass_encard_step_zero [Nonempty ι]
    (hfin : ∀ y : ι → F, (closeCodewordsRel C y δ).Finite)
    (hΛ1 : 1 ≤ Lambda C δ)
    {i : ℕ} {V : Matrix ι (Fin m) F} (ρ : ℕ) :
    (nodeClass C δ f i V 0 (ρ + 1)).encard
      ≤ Lambda C δ * leafBound C δ f 0 ρ := by
  classical
  rcases (nodeClass C δ f i V 0 (ρ + 1)).eq_empty_or_nonempty with hAe | hAne
  · rw [hAe]
    simp
  obtain ⟨W₀, hW₀⟩ := hAne
  have hclose_ne : (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).Nonempty :=
    ⟨W₀, hW₀.1⟩
  have hone : (1 : ℕ∞) ≤ Lambda C δ * leafBound C δ f 0 ρ := by
    calc (1 : ℕ∞) = 1 * 1 := (one_mul 1).symm
      _ ≤ Lambda C δ * leafBound C δ f 0 ρ :=
        mul_le_mul' hΛ1 (one_le_leafBound hclose_ne 0 ρ)
  by_cases hallW : ∃ W ∈ nodeClass C δ f i V 0 (ρ + 1),
      ∀ l : Fin m, i ≤ (l : ℕ) → IsWhiteAt C δ f W l
  · obtain ⟨Wa, hWa, hWawhite⟩ := hallW
    exact le_trans (encard_le_one_of_allWhite hWa hWawhite) hone
  · push_neg at hallW
    obtain ⟨lstar, hlstar_ge, hlstar_nw, hlstar_pre⟩ :=
      exists_common_branch hW₀ (fun W hW => hallW W hW)
    -- with zero Blue budget, every member is Red at `l*`
    have hAred : nodeClass C δ f i V 0 (ρ + 1)
        ⊆ {W ∈ nodeClass C δ f i V 0 (ρ + 1) | IsRedAt C f W lstar} := by
      intro W hW
      refine ⟨hW, ?_⟩
      by_contra hnotred
      have hblue : IsBlueAt C δ f W lstar := ⟨hlstar_nw W hW, hnotred⟩
      have hdec := blueAfter_succ_add_one_le (C := C) (δ := δ) (f := f)
        (W := W) hlstar_ge hblue
      have hb0 : blueAfter C δ f W i ≤ 0 := hW.2.2.1
      omega
    calc (nodeClass C δ f i V 0 (ρ + 1)).encard
        ≤ {W ∈ nodeClass C δ f i V 0 (ρ + 1) | IsRedAt C f W lstar}.encard :=
          Set.encard_mono hAred
      _ ≤ Lambda C δ * leafBound C δ f 0 ρ :=
          redPart_encard_le hfin hlstar_ge hlstar_pre

/-- **The Pascal step of the recursion**:
`t(β+1, ρ+1) ≤ t(β, ρ+1) + Λ(C,δ) · t(β+1, ρ)`. -/
private lemma nodeClass_encard_step_succ [Nonempty ι]
    (hfin : ∀ y : ι → F, (closeCodewordsRel C y δ).Finite)
    (hΛ1 : 1 ≤ Lambda C δ)
    {i : ℕ} {V : Matrix ι (Fin m) F} (β ρ : ℕ) :
    (nodeClass C δ f i V (β + 1) (ρ + 1)).encard
      ≤ leafBound C δ f β (ρ + 1) + Lambda C δ * leafBound C δ f (β + 1) ρ := by
  classical
  rcases (nodeClass C δ f i V (β + 1) (ρ + 1)).eq_empty_or_nonempty with hAe | hAne
  · rw [hAe]
    simp
  obtain ⟨W₀, hW₀⟩ := hAne
  have hclose_ne : (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).Nonempty :=
    ⟨W₀, hW₀.1⟩
  have hone : (1 : ℕ∞) ≤ Lambda C δ * leafBound C δ f (β + 1) ρ := by
    calc (1 : ℕ∞) = 1 * 1 := (one_mul 1).symm
      _ ≤ Lambda C δ * leafBound C δ f (β + 1) ρ :=
        mul_le_mul' hΛ1 (one_le_leafBound hclose_ne (β + 1) ρ)
  by_cases hallW : ∃ W ∈ nodeClass C δ f i V (β + 1) (ρ + 1),
      ∀ l : Fin m, i ≤ (l : ℕ) → IsWhiteAt C δ f W l
  · obtain ⟨Wa, hWa, hWawhite⟩ := hallW
    calc (nodeClass C δ f i V (β + 1) (ρ + 1)).encard
        ≤ 1 := encard_le_one_of_allWhite hWa hWawhite
      _ ≤ Lambda C δ * leafBound C δ f (β + 1) ρ := hone
      _ ≤ _ := self_le_add_left _ _
  · push_neg at hallW
    obtain ⟨lstar, hlstar_ge, hlstar_nw, hlstar_pre⟩ :=
      exists_common_branch hW₀ (fun W hW => hallW W hW)
    -- split into the Blue child and the Red children
    have hsplit : nodeClass C δ f i V (β + 1) (ρ + 1)
        = {W ∈ nodeClass C δ f i V (β + 1) (ρ + 1) | ¬ IsRedAt C f W lstar}
          ∪ {W ∈ nodeClass C δ f i V (β + 1) (ρ + 1) | IsRedAt C f W lstar} := by
      ext W
      simp only [Set.mem_union, Set.mem_setOf_eq]
      constructor
      · intro hW
        by_cases h : IsRedAt C f W lstar
        · exact Or.inr ⟨hW, h⟩
        · exact Or.inl ⟨hW, h⟩
      · rintro (⟨hW, _⟩ | ⟨hW, _⟩) <;> exact hW
    have hBlue : {W ∈ nodeClass C δ f i V (β + 1) (ρ + 1) |
          ¬ IsRedAt C f W lstar}.encard
        ≤ leafBound C δ f β (ρ + 1) := by
      rcases Set.eq_empty_or_nonempty
        {W ∈ nodeClass C δ f i V (β + 1) (ρ + 1) | ¬ IsRedAt C f W lstar}
        with hBe | hBne
      · rw [hBe]
        simp
      obtain ⟨WB, hWB⟩ := hBne
      -- all Blue children share the column at `l*`; descend into that class
      have hsubB : {W ∈ nodeClass C δ f i V (β + 1) (ρ + 1) | ¬ IsRedAt C f W lstar}
          ⊆ nodeClass C δ f ((lstar : ℕ) + 1) WB β (ρ + 1) := by
        intro W hW
        have hcol : ∀ j, W j lstar = WB j lstar := by
          apply eq_col_of_not_isRedAt hW.1.1 hWB.1.1
          · intro k hk j
            rw [hlstar_pre W hW.1 k hk j, hlstar_pre WB hWB.1 k hk j]
          · exact hW.2
          · exact hWB.2
        refine ⟨hW.1.1, ?_, ?_, ?_⟩
        · -- shared prefix at `l* + 1`
          intro k hk j
          rcases (Nat.lt_succ_iff.mp hk).lt_or_eq with hk' | hk'
          · rw [hlstar_pre W hW.1 k hk' j, hlstar_pre WB hWB.1 k hk' j]
          · have hkl : k = lstar := Fin.ext hk'
            rw [hkl]
            exact hcol j
        · -- the Blue level at `l*` decrements the Blue budget
          have hblue : IsBlueAt C δ f W lstar := ⟨hlstar_nw W hW.1, hW.2⟩
          have hdec := blueAfter_succ_add_one_le (C := C) (δ := δ) (f := f)
            (W := W) hlstar_ge hblue
          have hbW : blueAfter C δ f W i ≤ β + 1 := hW.1.2.2.1
          omega
        · -- the Red budget only shrinks
          have hmono := redAfter_mono (C := C) (f := f) W
            (show i ≤ (lstar : ℕ) + 1 by omega)
          have hrW : redAfter C f W i ≤ ρ + 1 := hW.1.2.2.2
          omega
      calc {W ∈ nodeClass C δ f i V (β + 1) (ρ + 1) | ¬ IsRedAt C f W lstar}.encard
          ≤ (nodeClass C δ f ((lstar : ℕ) + 1) WB β (ρ + 1)).encard :=
            Set.encard_mono hsubB
        _ ≤ leafBound C δ f β (ρ + 1) :=
            nodeClass_encard_le_leafBound C δ f hWB.1.1 β (ρ + 1)
    have hRed := redPart_encard_le (β := β + 1) hfin hlstar_ge hlstar_pre
    calc (nodeClass C δ f i V (β + 1) (ρ + 1)).encard
        ≤ {W ∈ nodeClass C δ f i V (β + 1) (ρ + 1) | ¬ IsRedAt C f W lstar}.encard
          + {W ∈ nodeClass C δ f i V (β + 1) (ρ + 1) | IsRedAt C f W lstar}.encard :=
          le_trans (le_of_eq (congrArg Set.encard hsplit)) (Set.encard_union_le _ _)
      _ ≤ _ := add_le_add hBlue hRed

end Recursion

/-! ## Assembly: the GGR11 tree structure, proven -/

section Assembly

variable [DecidableEq F] {C : Set (ι → F)} {δ : ℝ}

/-- A code with a positive minimum distance is nonempty. -/
private lemma code_nonempty_of_minDist_pos (hD : 0 < Code.minDist C) : C.Nonempty := by
  by_contra hC
  rw [Set.not_nonempty_iff_eq_empty] at hC
  have hempty : {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro d ⟨u, hu, _⟩
    rw [hC] at hu
    exact absurd hu (Set.notMem_empty u)
  have hD0 : Code.minDist C = 0 := by
    unfold Code.minDist
    rw [hempty]
    exact Nat.sInf_empty
  omega

/-- With a nonempty code, a nonnegative radius, and finite lists, the
maximised list size is at least one. -/
private lemma one_le_Lambda_of_nonempty
    (hfin : ∀ y : ι → F, (closeCodewordsRel C y δ).Finite)
    (hC : C.Nonempty) (hδ0 : 0 ≤ δ) : 1 ≤ Lambda C δ := by
  classical
  obtain ⟨c, hc⟩ := hC
  have hmem : c ∈ closeCodewordsRel C c δ := by
    refine ⟨hc, ?_⟩
    rw [relHammingBall, Set.mem_setOf_eq]
    have h0 : ((Code.relHammingDist c c : ℚ≥0) : ℝ) ≤ δ := by
      have hself : Code.relHammingDist c c = 0 := by
        unfold Code.relHammingDist
        simp [hammingDist_self]
      rw [hself]
      simpa using hδ0
    convert h0 using 3
  have hpos : 0 < (closeCodewordsRel C c δ).ncard :=
    Set.ncard_pos (hfin c) |>.mpr ⟨c, hmem⟩
  calc (1 : ℕ∞) ≤ ((closeCodewordsRel C c δ).ncard : ℕ∞) := by
        exact_mod_cast hpos
    _ ≤ Lambda C δ :=
        le_iSup (fun y => ((closeCodewordsRel C y δ).ncard : ℕ∞)) c

/-- **The GGR11 Erase-Decode tree structure, constructed** (issue #73).

For any code `C` with all base lists finite, any radius `0 ≤ δ` strictly below
the relative distance (in the absolute form `δ·n < d(C)`), and any budgets
`b, r` satisfying the GGR11 inequalities `δ·n ≤ b·(d(C) − δ·n)` and
`d(C) ≤ 2^r·(d(C) − δ·n)`, the refined residual `GGR11TreeStructure C δ m b r`
**holds for every interleaving order `m`**.  The witnessing leaf-count function
is `leafBound C δ f`. -/
theorem ggr11_treeStructure_of_budgets [Nonempty ι]
    (hfin : ∀ y : ι → F, (closeCodewordsRel C y δ).Finite)
    (hδ0 : 0 ≤ δ)
    (hδD : δ * (Fintype.card ι) < (Code.minDist C : ℝ))
    {b r : ℕ}
    (hb : δ * (Fintype.card ι)
      ≤ (b : ℝ) * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)))
    (hr : (Code.minDist C : ℝ)
      ≤ 2 ^ r * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)))
    (m : ℕ) :
    GGR11TreeStructure C δ m b r := by
  classical
  -- the code is nonempty, so `Λ(C, δ) ≥ 1`
  have hD : 0 < Code.minDist C := by
    by_contra hD
    push_neg at hD
    have : ((Code.minDist C : ℕ) : ℝ) ≤ 0 := by exact_mod_cast hD
    have hn : (0 : ℝ) ≤ δ * (Fintype.card ι) :=
      mul_nonneg hδ0 (by positivity)
    linarith
  have hΛ1 : 1 ≤ Lambda C δ :=
    one_le_Lambda_of_nonempty hfin (code_nonempty_of_minDist_pos hD) hδ0
  intro f
  refine ⟨leafBound C δ f, ?_, ?_, ?_, ?_⟩
  · -- domination: the root node class is the whole close set
    rcases (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).eq_empty_or_nonempty
      with he | ⟨V, hV⟩
    · rw [he]
      simp
    · have hsub : closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ
          ⊆ nodeClass C δ f 0 V b r := by
        intro W hW
        refine ⟨hW, ?_, ?_, ?_⟩
        · intro l hl
          exact absurd hl (Nat.not_lt_zero _)
        · exact blueAfter_le_budget hW hδD hb 0
        · exact redAfter_le_budget hW hδD hr 0
      calc (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard
          ≤ (nodeClass C δ f 0 V b r).encard := Set.encard_mono hsub
        _ ≤ leafBound C δ f b r := nodeClass_encard_le_leafBound C δ f hV b r
  · -- base: `t(b', 0) ≤ 1`
    intro b'
    refine iSup_le fun i => iSup_le fun V => iSup_le fun _ => ?_
    exact nodeClass_encard_le_one
  · -- the Red-only column: `t(0, r'+1) ≤ Λ · t(0, r')`
    intro r'
    refine iSup_le fun i => iSup_le fun V => iSup_le fun _ => ?_
    exact nodeClass_encard_step_zero hfin hΛ1 (i := i) (V := V) r'
  · -- the Pascal step: `t(b'+1, r'+1) ≤ t(b', r'+1) + Λ · t(b'+1, r')`
    intro b' r'
    refine iSup_le fun i => iSup_le fun V => iSup_le fun _ => ?_
    exact nodeClass_encard_step_succ hfin hΛ1 (i := i) (V := V) b' r'

/-- The granular per-word frontier, from the construction. -/
theorem ggr11_treeFrontier_of_budgets [Nonempty ι]
    (hfin : ∀ y : ι → F, (closeCodewordsRel C y δ).Finite)
    (hδ0 : 0 ≤ δ)
    (hδD : δ * (Fintype.card ι) < (Code.minDist C : ℝ))
    {b r : ℕ}
    (hb : δ * (Fintype.card ι)
      ≤ (b : ℝ) * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)))
    (hr : (Code.minDist C : ℝ)
      ≤ 2 ^ r * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)))
    (m : ℕ) :
    GGR11TreeFrontier C δ m b r :=
  frontier_of_treeStructure (ggr11_treeStructure_of_budgets hfin hδ0 hδD hb hr m)

/-- The per-word GGR11 list-size bound, from the construction. -/
theorem ggr11_perWordBound_of_budgets [Nonempty ι]
    (hfin : ∀ y : ι → F, (closeCodewordsRel C y δ).Finite)
    (hδ0 : 0 ≤ δ)
    (hδD : δ * (Fintype.card ι) < (Code.minDist C : ℝ))
    {b r : ℕ}
    (hb : δ * (Fintype.card ι)
      ≤ (b : ℝ) * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)))
    (hr : (Code.minDist C : ℝ)
      ≤ 2 ^ r * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)))
    (m : ℕ) :
    GGR11PerWordBound C δ m b r :=
  perWordBound_of_treeStructure (ggr11_treeStructure_of_budgets hfin hδ0 hδD hb hr m)

/-- **The GGR11 interleaved list-size bound, end to end** (ABF26 Lemma 2.10 /
GGR11 Theorem 3.6): `|Λ(C^{≡m}, δ)| ≤ (b+r choose r)·|Λ(C,δ)|^r`, with no
external hypotheses beyond finiteness of the base lists. -/
theorem lambda_le_ggr11_of_budgets [Nonempty ι]
    (hfin : ∀ y : ι → F, (closeCodewordsRel C y δ).Finite)
    (hδ0 : 0 ≤ δ)
    (hδD : δ * (Fintype.card ι) < (Code.minDist C : ℝ))
    {b r : ℕ}
    (hb : δ * (Fintype.card ι)
      ≤ (b : ℝ) * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)))
    (hr : (Code.minDist C : ℝ)
      ≤ 2 ^ r * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)))
    (m : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin m) C) δ
      ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r :=
  lambda_le_ggr11_of_treeStructure (ggr11_treeStructure_of_budgets hfin hδ0 hδD hb hr m)

end Assembly

/-! ## The canonical budgets `b = ⌈δ/η⌉`, `r = ⌈log₂(δ₀/η)⌉` -/

section Canonical

variable [DecidableEq F] {C : Set (ι → F)} {δ : ℝ}

/-- The canonical Blue budget satisfies its GGR11 inequality. -/
private lemma canonical_hb [Nonempty ι]
    (hδ0 : 0 ≤ δ)
    (hδub : δ < (Code.minDist C : ℝ) / (Fintype.card ι)) :
    δ * (Fintype.card ι)
      ≤ ((⌈δ / ((Code.minDist C : ℝ) / (Fintype.card ι) - δ)⌉₊ : ℕ) : ℝ)
        * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)) := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  set δ₀ : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι) with hδ₀
  have hη : 0 < δ₀ - δ := by linarith
  have hceil : δ / (δ₀ - δ) ≤ ((⌈δ / (δ₀ - δ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hmul : δ ≤ ((⌈δ / (δ₀ - δ)⌉₊ : ℕ) : ℝ) * (δ₀ - δ) := by
    have h := mul_le_mul_of_nonneg_right hceil (le_of_lt hη)
    rwa [div_mul_cancel₀ _ (ne_of_gt hη)] at h
  have hηn : (δ₀ - δ) * (Fintype.card ι) = (Code.minDist C : ℝ) - δ * (Fintype.card ι) := by
    rw [hδ₀, sub_mul, div_mul_cancel₀ _ (ne_of_gt hn)]
  calc δ * (Fintype.card ι)
      ≤ (((⌈δ / (δ₀ - δ)⌉₊ : ℕ) : ℝ) * (δ₀ - δ)) * (Fintype.card ι) :=
        mul_le_mul_of_nonneg_right hmul (le_of_lt hn)
    _ = ((⌈δ / (δ₀ - δ)⌉₊ : ℕ) : ℝ) * ((δ₀ - δ) * (Fintype.card ι)) := by ring
    _ = ((⌈δ / (δ₀ - δ)⌉₊ : ℕ) : ℝ) * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)) := by
        rw [hηn]

/-- The canonical Red budget satisfies its GGR11 inequality. -/
private lemma canonical_hr [Nonempty ι]
    (hδ0 : 0 ≤ δ)
    (hδub : δ < (Code.minDist C : ℝ) / (Fintype.card ι)) :
    (Code.minDist C : ℝ)
      ≤ 2 ^ (⌈Real.log ((Code.minDist C : ℝ) / (Fintype.card ι)
              / ((Code.minDist C : ℝ) / (Fintype.card ι) - δ)) / Real.log 2⌉₊ : ℕ)
        * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)) := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  set δ₀ : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι) with hδ₀
  have hη : 0 < δ₀ - δ := by linarith
  have hδ₀pos : 0 < δ₀ := lt_of_le_of_lt hδ0 hδub
  set r : ℕ := ⌈Real.log (δ₀ / (δ₀ - δ)) / Real.log 2⌉₊ with hrdef
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hquot_pos : (0 : ℝ) < δ₀ / (δ₀ - δ) := div_pos hδ₀pos hη
  -- `δ₀/η ≤ 2^r` via logs
  have hceil : Real.log (δ₀ / (δ₀ - δ)) / Real.log 2 ≤ (r : ℝ) := Nat.le_ceil _
  have hlog_le : Real.log (δ₀ / (δ₀ - δ)) ≤ (r : ℝ) * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right hceil (le_of_lt hlog2)
    rwa [div_mul_cancel₀ _ (ne_of_gt hlog2)] at h
  have hpow : δ₀ / (δ₀ - δ) ≤ (2 : ℝ) ^ r := by
    have h2r : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
    have hexp : δ₀ / (δ₀ - δ) = Real.exp (Real.log (δ₀ / (δ₀ - δ))) :=
      (Real.exp_log hquot_pos).symm
    have hexp2 : ((2 : ℝ) ^ r) = Real.exp ((r : ℝ) * Real.log 2) := by
      rw [← Real.log_pow, Real.exp_log h2r]
    rw [hexp, hexp2]
    exact Real.exp_le_exp.mpr hlog_le
  -- clear denominators: `δ₀ ≤ 2^r · η`, then multiply by `n`
  have hquot : δ₀ ≤ (2 : ℝ) ^ r * (δ₀ - δ) := by
    have h := mul_le_mul_of_nonneg_right hpow (le_of_lt hη)
    rwa [div_mul_cancel₀ _ (ne_of_gt hη)] at h
  have hD_eq : (Code.minDist C : ℝ) = δ₀ * (Fintype.card ι) := by
    rw [hδ₀, div_mul_cancel₀ _ (ne_of_gt hn)]
  have hηn : (δ₀ - δ) * (Fintype.card ι) = (Code.minDist C : ℝ) - δ * (Fintype.card ι) := by
    rw [hδ₀, sub_mul, div_mul_cancel₀ _ (ne_of_gt hn)]
  calc (Code.minDist C : ℝ) = δ₀ * (Fintype.card ι) := hD_eq
    _ ≤ ((2 : ℝ) ^ r * (δ₀ - δ)) * (Fintype.card ι) :=
        mul_le_mul_of_nonneg_right hquot (le_of_lt hn)
    _ = (2 : ℝ) ^ r * ((δ₀ - δ) * (Fintype.card ι)) := by ring
    _ = (2 : ℝ) ^ r * ((Code.minDist C : ℝ) - δ * (Fintype.card ι)) := by rw [hηn]

/-- `GGR11TreeStructure` at the canonical GGR11 budgets. -/
theorem ggr11_treeStructure_canonical [Nonempty ι]
    (hfin : ∀ y : ι → F, (closeCodewordsRel C y δ).Finite)
    (hδ0 : 0 ≤ δ)
    (hδub : δ < (Code.minDist C : ℝ) / (Fintype.card ι))
    (m : ℕ) :
    GGR11TreeStructure C δ m
      ⌈δ / ((Code.minDist C : ℝ) / (Fintype.card ι) - δ)⌉₊
      ⌈Real.log ((Code.minDist C : ℝ) / (Fintype.card ι)
          / ((Code.minDist C : ℝ) / (Fintype.card ι) - δ)) / Real.log 2⌉₊ := by
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hδD : δ * (Fintype.card ι) < (Code.minDist C : ℝ) := by
    have h := mul_lt_mul_of_pos_right hδub hn
    rwa [div_mul_cancel₀ _ (ne_of_gt hn)] at h
  exact ggr11_treeStructure_of_budgets hfin hδ0 hδD
    (canonical_hb hδ0 hδub) (canonical_hr hδ0 hδub) m

/-- **The public disposition `InterleavedCode.lambda_le_ggr11` holds** in the
finite-list regime: the formerly external GGR11 Erase-Decode wall is now an
in-tree theorem. -/
theorem lambda_le_ggr11_holds {ι F : Type} [Fintype ι] [Field F] [DecidableEq F]
    (C : Set (ι → F)) (δ : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hδ_lb : 0 ≤ δ)
    (hδ_ub : δ < (Code.minDist C : ℝ) / (Fintype.card ι))
    (hfin : ∀ y : ι → F, (closeCodewordsRel C y δ).Finite) :
    lambda_le_ggr11 C δ m hm hδ_lb hδ_ub := by
  have hι : Nonempty ι := by
    by_contra hι
    have hcard : Fintype.card ι = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun i => absurd ⟨i⟩ hι⟩
    rw [hcard] at hδ_ub
    simp at hδ_ub
    linarith
  exact lambda_le_ggr11_of_treeStructure
    (ggr11_treeStructure_canonical hfin hδ_lb hδ_ub m)

/-- `lambda_le_ggr11_holds`, with the finiteness hypothesis discharged by a
finite alphabet. -/
theorem lambda_le_ggr11_holds_of_finite {ι F : Type} [Fintype ι] [Field F]
    [DecidableEq F] [Finite F]
    (C : Set (ι → F)) (δ : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hδ_lb : 0 ≤ δ)
    (hδ_ub : δ < (Code.minDist C : ℝ) / (Fintype.card ι)) :
    lambda_le_ggr11 C δ m hm hδ_lb hδ_ub :=
  lambda_le_ggr11_holds C δ m hm hδ_lb hδ_ub (fun _ => Set.toFinite _)

end Canonical

-- Axiom audit: the construction is sorry/axiom-clean.
#print axioms ggr11_treeStructure_of_budgets
#print axioms ggr11_treeFrontier_of_budgets
#print axioms ggr11_perWordBound_of_budgets
#print axioms lambda_le_ggr11_of_budgets
#print axioms ggr11_treeStructure_canonical
#print axioms lambda_le_ggr11_holds
#print axioms lambda_le_ggr11_holds_of_finite

end InterleavedCode.GGR11
