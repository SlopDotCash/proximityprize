/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
Round 14, Angle E — the DERANDOMIZATION frontier of the proximity-prize list-size problem
(ABF26 / ArkLib #232), formalized HONESTLY over a general finite alphabet.

Context. The known capacity results for Reed–Solomon list decoding (GZ23: randomly punctured
RS codes achieve list-decoding capacity; GG25: random RS codes have mutual correlated
agreement up to capacity) hold for RANDOM evaluation sets.  The prize statement fixes an
EXPLICIT smooth multiplicative-subgroup evaluation domain.  The gap between
"some evaluation set of size n works" and "the explicit subgroup domain works" is the
derandomization core.  This file:

(a) defines `ListDecodableTo` (relative-radius list decodability) and its absolute-agreement
    form `ListDecodableAbs`, with a PROVED exact bridge (`listDecodableTo_iff_abs`);
(b) states the derandomization question as named Props (`ExistsGoodDomain`,
    `AllSubgroupDomainsGood`, `DerandomizationCore`) — the core is stated and deliberately
    NOT asserted anywhere;
(c) PROVES the genuinely-true structural fragments about puncturing one evaluation point:
    (i)   `listDecodableAbs_punctureCode` — at the SAME absolute agreement threshold t,
          list decodability survives puncturing (relative to the smaller domain this is a
          margin gain, which is exactly why it is true);
    (ii)  `naive_margin_fails_concrete` — the naive guess
          "absolute threshold t implies threshold t-1 on the punctured domain with the same
          list size" is REFUTED by an explicit counterexample (so the q-factor below is
          genuinely needed);
    (iii) `listDecodableAbs_punctureCode_pigeonhole` — the CORRECT margin version: threshold
          t+1 with list L implies threshold t on the punctured domain with list |F|·L
          (pigeonhole over the deleted coordinate), and `pigeonhole_tight_concrete` shows
          the factor |F| is tight on the same counterexample;
    (iv)  `listDecodableAbs_of_punctureCode` — the transfer direction used in
          derandomization: a good punctured (smaller, possibly explicit) domain pulls back
          to the original domain with threshold t+1, given injectivity of puncturing;
    (v)   trivial endpoint facts and concrete non-degenerate instances for everything.

What is NOT proven here: `DerandomizationCore` itself (whether existence of a good size-n
evaluation set implies the smooth subgroup domains are good).  That is the open research
content; it is stated as a `def ... : Prop` only and never claimed.
-/
import ArkLib.Data.CodingTheory.CodeGeometry
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace R14Derand

open Finset

/-! ## Part 0: agreement, distance, and the two forms of list decodability -/

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [DecidableEq F]

/-- Absolute agreement: the number of coordinates where two words coincide. -/
def agreement (w c : ι → F) : ℕ :=
  (Finset.univ.filter fun i => w i = c i).card

/-- Hamming distance: the number of coordinates where two words differ. -/
def hammingDistance (w c : ι → F) : ℕ :=
  (Finset.univ.filter fun i => ¬ w i = c i).card

/-- The derandomization frontier's local agreement count is the Johnson-geometry agreement
count. This connects the absolute-threshold language here to the Gram/Johnson layer. -/
lemma agreement_eq_codeGeometry_agree (w c : ι → F) :
    agreement w c = CodeGeometry.agree w c := rfl

/-- The local Hamming-distance spelling is Mathlib's `hammingDist`. -/
lemma hammingDistance_eq_hammingDist (w c : ι → F) :
    hammingDistance w c = hammingDist w c := rfl

lemma agreement_add_hammingDistance (w c : ι → F) :
    agreement w c + hammingDistance w c = Fintype.card ι := by
  simpa [agreement_eq_codeGeometry_agree, hammingDistance_eq_hammingDist] using
    CodeGeometry.agree_add_hammingDist w c

lemma agreement_le_card (w c : ι → F) : agreement w c ≤ Fintype.card ι := by
  unfold agreement
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- Absolute-agreement list decodability: for every received word `w`, at most `L`
codewords of `C` agree with `w` on at least `t` coordinates. -/
def ListDecodableAbs (C : Finset (ι → F)) (t L : ℕ) : Prop :=
  ∀ w : ι → F, (C.filter fun c => t ≤ agreement w c).card ≤ L

/-- Relative-radius list decodability: every Hamming ball of relative radius `δ`
contains at most `L` codewords of `C`. -/
def ListDecodableTo (C : Finset (ι → F)) (δ : ℚ) (L : ℕ) : Prop :=
  ∀ w : ι → F,
    (C.filter fun c => (hammingDistance w c : ℚ) ≤ δ * (Fintype.card ι : ℚ)).card ≤ L

/-- Exact bridge between the relative and the absolute form.  This is the precise reason
naive puncturing monotonicity fails for the RELATIVE form: the absolute threshold
`n - ⌊δ n⌋` moves when `n` shrinks. -/
theorem listDecodableTo_iff_abs (C : Finset (ι → F)) {δ : ℚ} (hδ : 0 ≤ δ) (L : ℕ) :
    ListDecodableTo C δ L ↔
      ListDecodableAbs C (Fintype.card ι - ⌊δ * (Fintype.card ι : ℚ)⌋₊) L := by
  have key : ∀ w c : ι → F,
      ((hammingDistance w c : ℚ) ≤ δ * (Fintype.card ι : ℚ) ↔
        Fintype.card ι - ⌊δ * (Fintype.card ι : ℚ)⌋₊ ≤ agreement w c) := by
    intro w c
    have hsum := agreement_add_hammingDistance w c
    have hpos : (0 : ℚ) ≤ δ * (Fintype.card ι : ℚ) :=
      mul_nonneg hδ (Nat.cast_nonneg _)
    rw [show ((hammingDistance w c : ℚ) ≤ δ * (Fintype.card ι : ℚ)) ↔
        hammingDistance w c ≤ ⌊δ * (Fintype.card ι : ℚ)⌋₊ from (Nat.le_floor_iff hpos).symm]
    omega
  have hfe : ∀ w : ι → F,
      C.filter (fun c => (hammingDistance w c : ℚ) ≤ δ * (Fintype.card ι : ℚ)) =
        C.filter (fun c => Fintype.card ι - ⌊δ * (Fintype.card ι : ℚ)⌋₊ ≤ agreement w c) :=
    fun w => Finset.filter_congr (fun c _ => key w c)
  constructor
  · intro h w
    rw [← hfe w]
    exact h w
  · intro h w
    rw [hfe w]
    exact h w

/-! ### Endpoint facts -/

/-- Every code is trivially list decodable with list size its own cardinality. -/
theorem listDecodableAbs_card (C : Finset (ι → F)) (t : ℕ) :
    ListDecodableAbs C t C.card :=
  fun _ => Finset.card_le_card (Finset.filter_subset _ _)

/-- If the threshold exceeds the number of coordinates, the list is empty. -/
theorem listDecodableAbs_zero_of_gt {C : Finset (ι → F)} {t : ℕ}
    (ht : Fintype.card ι < t) : ListDecodableAbs C t 0 := by
  intro w
  have hempty : C.filter (fun c => t ≤ agreement w c) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 ?_
    intro c _
    have hle := agreement_le_card w c
    omega
  simp [hempty]

/-- Monotone in the list size. -/
theorem ListDecodableAbs.mono_L {C : Finset (ι → F)} {t L L' : ℕ}
    (h : ListDecodableAbs C t L) (hL : L ≤ L') : ListDecodableAbs C t L' :=
  fun w => (h w).trans hL

/-- Antitone in the agreement threshold. -/
theorem ListDecodableAbs.anti_t {C : Finset (ι → F)} {t t' L : ℕ}
    (htt : t ≤ t') (h : ListDecodableAbs C t L) : ListDecodableAbs C t' L := by
  intro w
  refine le_trans (Finset.card_le_card ?_) (h w)
  intro c hc
  rcases Finset.mem_filter.1 hc with ⟨h1, h2⟩
  exact Finset.mem_filter.2 ⟨h1, le_trans htt h2⟩

/-! ## Part 1: puncturing one evaluation point -/

/-- Restriction of a word to the domain with the coordinate `x` deleted. -/
def punctureWord (x : ι) (c : ι → F) : {i : ι // i ≠ x} → F :=
  fun i => c i.1

/-- The punctured code: the image of the code under deleting coordinate `x`. -/
def punctureCode (x : ι) (C : Finset (ι → F)) : Finset ({i : ι // i ≠ x} → F) :=
  C.image (punctureWord x)

/-- Extension of a punctured word back to the full domain, with value `a` at `x`. -/
def extendWord (x : ι) (a : F) (w' : {i : ι // i ≠ x} → F) : ι → F :=
  fun i => if h : i = x then a else w' ⟨i, h⟩

@[simp] lemma punctureWord_extendWord (x : ι) (a : F) (w' : {i : ι // i ≠ x} → F) :
    punctureWord x (extendWord x a w') = w' := by
  funext i
  simp [punctureWord, extendWord, i.2]

@[simp] lemma extendWord_self (x : ι) (a : F) (w' : {i : ι // i ≠ x} → F) :
    extendWord x a w' x = a := by
  simp [extendWord]

/-- Agreement only drops when a coordinate is deleted. -/
lemma agreement_punctureWord_le (x : ι) (w c : ι → F) :
    agreement (punctureWord x w) (punctureWord x c) ≤ agreement w c := by
  unfold agreement
  refine Finset.card_le_card_of_injOn (fun i => i.1) ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      punctureWord] at hi ⊢
    exact hi
  · intro a _ b _ h
    exact Subtype.ext h

/-- Deleting one coordinate loses at most one unit of agreement. -/
lemma agreement_le_punctureWord_succ (x : ι) (w c : ι → F) :
    agreement w c ≤ agreement (punctureWord x w) (punctureWord x c) + 1 := by
  unfold agreement
  have hsub : (Finset.univ.filter fun i => w i = c i) ⊆
      insert x ((Finset.univ.filter fun i : {i : ι // i ≠ x} =>
        punctureWord x w i = punctureWord x c i).image (fun i => i.1)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_cases hx : i = x
    · subst hx
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨i, hx⟩, ?_, rfl⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, punctureWord]
      exact hi
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_insert_le _ _).trans ?_
  exact Nat.add_le_add_right Finset.card_image_le 1

/-- If the two words also agree at the deleted coordinate, the full agreement is at least
the punctured agreement plus one. -/
lemma agreement_punctureWord_succ_le (x : ι) (w c : ι → F) (hx : w x = c x) :
    agreement (punctureWord x w) (punctureWord x c) + 1 ≤ agreement w c := by
  unfold agreement
  have hnot : x ∉ (Finset.univ.filter fun i : {i : ι // i ≠ x} =>
      punctureWord x w i = punctureWord x c i).image (fun i => i.1) := by
    simp only [Finset.mem_image]
    rintro ⟨j, -, hj⟩
    exact j.2 hj
  have hcard : ((Finset.univ.filter fun i : {i : ι // i ≠ x} =>
      punctureWord x w i = punctureWord x c i).image (fun i => i.1)).card =
      (Finset.univ.filter fun i : {i : ι // i ≠ x} =>
        punctureWord x w i = punctureWord x c i).card :=
    Finset.card_image_of_injective _ (fun a b h => Subtype.ext h)
  have hsub : insert x ((Finset.univ.filter fun i : {i : ι // i ≠ x} =>
      punctureWord x w i = punctureWord x c i).image (fun i => i.1)) ⊆
      Finset.univ.filter fun i => w i = c i := by
    intro i hi
    rcases Finset.mem_insert.1 hi with h | h
    · subst h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx
    · rcases Finset.mem_image.1 h with ⟨j, hj, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, punctureWord] at hj ⊢
      exact hj
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, hcard] at h1
  exact h1

/-! ### (i) Same-threshold monotonicity under puncturing (TRUE, proved)

In ABSOLUTE agreement form, keeping the SAME threshold `t` on the smaller domain is the
correct margin: relative to `n - 1` coordinates, demanding `t` agreements is a strictly
stronger relative requirement, and list decodability survives. -/

theorem listDecodableAbs_punctureCode [Nonempty F] {C : Finset (ι → F)} {t L : ℕ}
    (h : ListDecodableAbs C t L) (x : ι) :
    ListDecodableAbs (punctureCode x C) t L := by
  intro w'
  obtain ⟨a⟩ := ‹Nonempty F›
  have hw : punctureWord x (extendWord x a w') = w' := punctureWord_extendWord x a w'
  have hsub : (punctureCode x C).filter (fun c' => t ≤ agreement w' c') ⊆
      (C.filter fun c => t ≤ agreement (extendWord x a w') c).image (punctureWord x) := by
    intro c' hc'
    rcases Finset.mem_filter.1 hc' with ⟨hmem, ht⟩
    simp only [punctureCode] at hmem
    rcases Finset.mem_image.1 hmem with ⟨c, hcC, rfl⟩
    refine Finset.mem_image.2 ⟨c, Finset.mem_filter.2 ⟨hcC, ?_⟩, rfl⟩
    have h1 : agreement (punctureWord x (extendWord x a w')) (punctureWord x c) ≤
        agreement (extendWord x a w') c := agreement_punctureWord_le x _ c
    rw [hw] at h1
    exact ht.trans h1
  exact ((Finset.card_le_card hsub).trans Finset.card_image_le).trans (h _)

/-! ### (iii) The correct threshold-drop version: pigeonhole over the deleted value
(TRUE, proved; the |F| factor is unavoidable, see the tightness witness below). -/

theorem listDecodableAbs_punctureCode_pigeonhole [Fintype F] {C : Finset (ι → F)}
    {t L : ℕ} (h : ListDecodableAbs C (t + 1) L) (x : ι) :
    ListDecodableAbs (punctureCode x C) t (Fintype.card F * L) := by
  intro w'
  have h1 : ((punctureCode x C).filter fun c' => t ≤ agreement w' c').card ≤
      (C.filter fun c => t ≤ agreement w' (punctureWord x c)).card := by
    have hsub : (punctureCode x C).filter (fun c' => t ≤ agreement w' c') ⊆
        (C.filter fun c => t ≤ agreement w' (punctureWord x c)).image (punctureWord x) := by
      intro c' hc'
      rcases Finset.mem_filter.1 hc' with ⟨hmem, ht⟩
      simp only [punctureCode] at hmem
      rcases Finset.mem_image.1 hmem with ⟨c, hcC, rfl⟩
      exact Finset.mem_image.2 ⟨c, Finset.mem_filter.2 ⟨hcC, ht⟩, rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have h2 : (C.filter fun c => t ≤ agreement w' (punctureWord x c)).card =
      ∑ a ∈ (Finset.univ : Finset F),
        ((C.filter fun c => t ≤ agreement w' (punctureWord x c)).filter
          fun c => c x = a).card :=
    Finset.card_eq_sum_card_fiberwise (fun c _ => Finset.mem_univ (c x))
  have h3 : ∀ a : F,
      ((C.filter fun c => t ≤ agreement w' (punctureWord x c)).filter
        fun c => c x = a).card ≤ L := by
    intro a
    have hsub : ((C.filter fun c => t ≤ agreement w' (punctureWord x c)).filter
        fun c => c x = a) ⊆ C.filter fun c => t + 1 ≤ agreement (extendWord x a w') c := by
      intro c hc
      rcases Finset.mem_filter.1 hc with ⟨hc1, hcx⟩
      rcases Finset.mem_filter.1 hc1 with ⟨hcC, ht⟩
      refine Finset.mem_filter.2 ⟨hcC, ?_⟩
      have hagree : extendWord x a w' x = c x := by
        rw [extendWord_self, hcx]
      have hstep := agreement_punctureWord_succ_le x (extendWord x a w') c hagree
      rw [punctureWord_extendWord] at hstep
      omega
    exact (Finset.card_le_card hsub).trans (h _)
  calc ((punctureCode x C).filter fun c' => t ≤ agreement w' c').card
      ≤ (C.filter fun c => t ≤ agreement w' (punctureWord x c)).card := h1
    _ = ∑ a ∈ (Finset.univ : Finset F),
        ((C.filter fun c => t ≤ agreement w' (punctureWord x c)).filter
          fun c => c x = a).card := h2
    _ ≤ ∑ _a ∈ (Finset.univ : Finset F), L := Finset.sum_le_sum fun a _ => h3 a
    _ = Fintype.card F * L := by simp [mul_comm]

/-! ### (iv) Transfer back from the punctured domain (the derandomization-relevant
direction): a good smaller domain certifies the larger one at threshold `t+1`, provided
puncturing is injective on the code (true for RS codes when `|S| - 1 ≥ k`). -/

theorem listDecodableAbs_of_punctureCode {C : Finset (ι → F)} {t L : ℕ} (x : ι)
    (hinj : ∀ a ∈ C, ∀ b ∈ C, punctureWord x a = punctureWord x b → a = b)
    (h : ListDecodableAbs (punctureCode x C) t L) :
    ListDecodableAbs C (t + 1) L := by
  intro w
  have hb : (C.filter fun c => t + 1 ≤ agreement w c).card ≤
      ((punctureCode x C).filter fun c' =>
        t ≤ agreement (punctureWord x w) c').card := by
    refine Finset.card_le_card_of_injOn (punctureWord x) ?_ ?_
    · intro c hc
      rw [Finset.mem_coe] at hc
      rcases Finset.mem_filter.1 hc with ⟨hcC, ht⟩
      rw [Finset.mem_coe]
      refine Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hcC, ?_⟩
      have hstep := agreement_le_punctureWord_succ x w c
      omega
    · intro a ha b hb' hab
      exact hinj a (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).1
        b (Finset.mem_filter.1 (Finset.mem_coe.1 hb')).1 hab
  exact hb.trans (h _)

end General

/-! ## Part 2: the naive guess is FALSE — explicit counterexample, and tightness of the
pigeonhole factor.

Code `C₀ = {000, 111} ⊆ Bool^3`.  It is list decodable at absolute threshold 2 with list
size 1 (the two codewords are at distance 3, and any word agrees with both on a total of
exactly 3 coordinates, so never twice with each).  Puncture the last coordinate: the word
`01` agrees on exactly 1 coordinate with BOTH punctured codewords `00` and `11`, so at
threshold `2 - 1 = 1` the punctured list has size 2.  Hence
"`ListDecodableAbs C t L` implies `ListDecodableAbs (puncture C) (t-1) L`" is FALSE,
while the proved `|F| · L = 2` bound is attained exactly. -/

/-- The two-codeword repetition code in `Bool^3`. -/
def C₀ : Finset (Fin 3 → Bool) := {fun _ => false, fun _ => true}

theorem C0_listDecodableAbs_two_one : ListDecodableAbs C₀ 2 1 := by
  unfold ListDecodableAbs
  decide

/-- The naive threshold-drop guess fails on `C₀`: the punctured code is NOT list decodable
at threshold 1 with list size 1. -/
theorem naive_margin_fails_concrete :
    ¬ ListDecodableAbs (punctureCode (2 : Fin 3) C₀) 1 1 := by
  unfold ListDecodableAbs punctureCode C₀
  decide

/-- Non-degenerate instance of the same-threshold puncturing theorem (i). -/
theorem punctured_same_threshold :
    ListDecodableAbs (punctureCode (2 : Fin 3) C₀) 2 1 :=
  listDecodableAbs_punctureCode C0_listDecodableAbs_two_one 2

/-- The conclusion of `punctured_same_threshold` is not empty-handed: the threshold-2 list
of the punctured code is actually attained (size exactly 1 for some received word), and
the punctured code genuinely has 2 codewords. -/
theorem punctured_same_threshold_attained :
    (punctureCode (2 : Fin 3) C₀).card = 2 ∧
      ∃ w' : {i : Fin 3 // i ≠ 2} → Bool,
        ((punctureCode (2 : Fin 3) C₀).filter fun c' => 2 ≤ agreement w' c').card = 1 := by
  constructor
  · decide
  · decide

/-- Non-degenerate instance of the pigeonhole theorem (iii): threshold drops 2 → 1,
list size pays the factor `|Bool| = 2`. -/
theorem punctured_pred_threshold :
    ListDecodableAbs (punctureCode (2 : Fin 3) C₀) 1 2 := by
  have h := listDecodableAbs_punctureCode_pigeonhole (t := 1)
    C0_listDecodableAbs_two_one (2 : Fin 3)
  simpa using h

/-- TIGHTNESS: on `C₀` the pigeonhole factor `|F|` cannot be improved — list size 2 holds
and list size 1 fails at the dropped threshold. -/
theorem pigeonhole_tight_concrete :
    ListDecodableAbs (punctureCode (2 : Fin 3) C₀) 1 2 ∧
      ¬ ListDecodableAbs (punctureCode (2 : Fin 3) C₀) 1 1 :=
  ⟨punctured_pred_threshold, naive_margin_fails_concrete⟩

/-- Non-degenerate instance of the transfer theorem (iv): the punctured bound pulls back. -/
theorem transfer_back_concrete : ListDecodableAbs C₀ 2 2 :=
  listDecodableAbs_of_punctureCode (2 : Fin 3) (by decide) punctured_pred_threshold

/-- Non-degenerate instance of the relative↔absolute bridge: relative radius 1/3 on
`Bool^3` is absolute threshold 2. -/
theorem C0_relative_third : ListDecodableTo C₀ (1/3 : ℚ) 1 := by
  rw [listDecodableTo_iff_abs C₀ (by norm_num) 1]
  have hfl : Fintype.card (Fin 3) - ⌊(1/3 : ℚ) * (Fintype.card (Fin 3) : ℚ)⌋₊ = 2 := by
    norm_num
  rw [hfl]
  exact C0_listDecodableAbs_two_one

/-! ## Part 3: Reed–Solomon codes, smooth (subgroup) domains, and the OPEN core -/

section RS

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- The Reed–Solomon code of message length `k` on the evaluation set `S ⊆ F`:
all words on `S` that are evaluations of a polynomial of degree `< k`
(`natDegree < k`; for `k = 0` the code is empty by convention). -/
noncomputable def RSCode (k : ℕ) (S : Finset F) : Finset (↥S → F) :=
  Finset.univ.filter
    (fun w => ∃ p : Polynomial F, p.natDegree < k ∧ ∀ s : ↥S, w s = p.eval (s : F))

lemma mem_RSCode {k : ℕ} {S : Finset F} {w : ↥S → F} :
    w ∈ RSCode k S ↔
      ∃ p : Polynomial F, p.natDegree < k ∧ ∀ s : ↥S, w s = p.eval (s : F) := by
  unfold RSCode
  simp

theorem const_mem_RSCode {k : ℕ} (hk : 0 < k) (S : Finset F) (a : F) :
    (fun _ => a) ∈ RSCode k S := by
  rw [mem_RSCode]
  exact ⟨Polynomial.C a, by simpa using hk, fun s => by simp⟩

theorem rsCode_nonempty {k : ℕ} (hk : 0 < k) (S : Finset F) :
    (RSCode k S).Nonempty :=
  ⟨_, const_mem_RSCode hk S (0 : F)⟩

/-- Trivial endpoint instance for RS codes. -/
theorem rsCode_listDecodable_card (k t : ℕ) (S : Finset F) :
    ListDecodableAbs (RSCode k S) t (RSCode k S).card :=
  listDecodableAbs_card _ _

/-- `S` is a (smooth-type) subgroup domain: the value set of a multiplicative subgroup
of `Fˣ`.  The prize's smooth domain (a power-of-two-order subgroup) is an instance. -/
def IsSubgroupDomain (S : Finset F) : Prop :=
  ∃ H : Subgroup Fˣ, (S : Set F) = Units.val '' (H : Set Fˣ)

/-- The singleton `{1}` is a subgroup domain (the trivial subgroup), so the explicit-domain
side of the question is inhabited. -/
theorem isSubgroupDomain_singleton_one : IsSubgroupDomain ({1} : Finset F) := by
  refine ⟨⊥, ?_⟩
  ext a
  simp only [Finset.coe_singleton, Set.mem_singleton_iff, Set.mem_image, SetLike.mem_coe,
    Subgroup.mem_bot]
  constructor
  · rintro rfl
    exact ⟨1, rfl, rfl⟩
  · rintro ⟨u, rfl, rfl⟩
    rfl

theorem exists_subgroupDomain : ∃ S : Finset F, S.card = 1 ∧ IsSubgroupDomain S :=
  ⟨{1}, Finset.card_singleton 1, isSubgroupDomain_singleton_one⟩

/-- "Some evaluation set of size `n` gives a `(t, L)` list-decodable RS code." -/
def ExistsGoodDomain (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n k t L : ℕ) : Prop :=
  ∃ S : Finset F, S.card = n ∧ ListDecodableAbs (RSCode k S) t L

/-- "EVERY size-`n` subgroup (smooth-type) evaluation set gives a `(t, L)` list-decodable
RS code." -/
def AllSubgroupDomainsGood (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n k t L : ℕ) : Prop :=
  ∀ S : Finset F, S.card = n → IsSubgroupDomain S → ListDecodableAbs (RSCode k S) t L

/-- THE OPEN DERANDOMIZATION CORE — stated only, deliberately NOT asserted or proved
anywhere in this file.  The random-puncturing capacity results (GZ23, GG25) certify
`ExistsGoodDomain` in the capacity regime (`t` slightly above `k`, `L` constant); the
proximity prize needs `AllSubgroupDomainsGood` for explicit smooth domains.  Whether the
implication holds — i.e. whether the existential certificate can be derandomized to the
explicit subgroup domain — is the open research content beyond the Johnson radius. -/
def DerandomizationCore (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n k t L : ℕ) : Prop :=
  ExistsGoodDomain F n k t L → AllSubgroupDomainsGood F n k t L

/-- Non-degenerate instance: `ExistsGoodDomain` holds (with the trivial list bound) for
every evaluation set, so the hypothesis side of the open core is inhabited. -/
theorem existsGoodDomain_card (k t : ℕ) (S : Finset F) :
    ExistsGoodDomain F S.card k t (RSCode k S).card :=
  ⟨S, rfl, listDecodableAbs_card _ _⟩

/-- Trivial regime of the conclusion side: when the threshold exceeds `n`, every domain
(subgroup or not) is good, with any list size. -/
theorem allSubgroupDomainsGood_of_lt {n k t L : ℕ} (ht : n < t) :
    AllSubgroupDomainsGood F n k t L := by
  intro S hS _
  have hcard : Fintype.card ↥S = n := by rw [Fintype.card_coe, hS]
  intro w
  refine le_trans (listDecodableAbs_zero_of_gt (C := RSCode k S) ?_ w) (Nat.zero_le L)
  omega

/-- The open core holds trivially in the above-`n` threshold regime — this shows the
Props compose as intended; the contentful regime (`k ≤ t ≤ n`, beyond Johnson) is open. -/
theorem derandomizationCore_of_lt {n k t L : ℕ} (ht : n < t) :
    DerandomizationCore F n k t L :=
  fun _ => allSubgroupDomainsGood_of_lt ht

end RS

end R14Derand

#print axioms R14Derand.listDecodableTo_iff_abs
#print axioms R14Derand.listDecodableAbs_punctureCode
#print axioms R14Derand.listDecodableAbs_punctureCode_pigeonhole
#print axioms R14Derand.listDecodableAbs_of_punctureCode
#print axioms R14Derand.naive_margin_fails_concrete
#print axioms R14Derand.pigeonhole_tight_concrete
#print axioms R14Derand.transfer_back_concrete
#print axioms R14Derand.C0_relative_third
#print axioms R14Derand.punctured_same_threshold_attained
#print axioms R14Derand.existsGoodDomain_card
#print axioms R14Derand.derandomizationCore_of_lt
#print axioms R14Derand.exists_subgroupDomain
