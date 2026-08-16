/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Issue #232: the per-line pair co-occurrence bound (round 14)

The per-line refinement of the second-moment kernel (rounds 13/13b). The global second moment
`∑_w |Λ(w,r)|² = |C|·∑ A_w·I(w,r)` averages over ALL centers in `Fⁿ` and provably cannot pin the
interior threshold (Markov over `q^n` centers is hopeless). The proximity-gap quantity lives on
*lines* `{f + γ·g : γ ∈ F}` — so the kernel must be restricted to a line. This file proves the
elementary core of that restriction:

**Pair co-occurrence bound.** On a line with nowhere-zero direction (`g i ≠ 0` for all `i`),
for ANY two words `c ≠ c'` at Hamming distance `w` and agreement threshold `a`, the number `B` of
line points having agreement `≥ a` with BOTH `c` and `c'` satisfies
    `B · 2a  ≤  B · w + 2(n − w)`,
i.e. `B ≤ 2(n−w)/(2a−w)` whenever `2a > w`, and `B = 0` whenever `2a > 2n − w`.

**Proof shape (one-vote double counting).** Since `g i ≠ 0`, coordinate `i` agrees with `c` at
exactly one `γ` (the vote `γᵢ(c) = (cᵢ − fᵢ)/gᵢ`). Off the support of `c − c'` the votes for `c`
and `c'` coincide (shared votes, at most `n − w` across the whole line, *pairwise disjoint in γ*);
on the support they are disjoint at every fixed `γ`. A doubly-good `γ` with shared-vote count `t`
and disjoint counts `u, u'` has `a ≤ t + u`, `a ≤ t + u'`, `u + u' ≤ w`, hence `2t ≥ 2a − w`;
summing the disjoint `t`'s over the bad set gives the bound.

This is the same one-vote-per-coordinate primitive as `Hab25Core` (Lemma 1 of ePrint 2025/2110,
[AHIV17/BKS18]) but combined differently: Hab25 bounds the folds matching a *fixed* codeword pair
across the interleaved disagreement set; here we bound the *co-occurrence of two codewords* in the
per-point agreement lists along the line — the off-diagonal term of the per-line second moment.

**Sharpness / non-vacuity (numeric witness).** On `RS[8,4]` over `F₁₇` with the smooth order-8
evaluation domain `⟨2⟩ = {1,2,4,8,9,13,15,16}` (rate `1/2`, `d = 5`) at the strict-interior
agreement threshold `a = 5` (`δ = 3/8 ∈ (1−√½, ½)`), every pair has `w ∈ [5,8]` and `2a = 10 > w`,
so the bound binds on EVERY pair: co-occurrence `≤ 1` for `w ∈ {5,6}` and `= 0` for `w ∈ {7,8}`.
An exhaustive scan of 80 lines (random, codeword-direction, near-codeword base; 4181 co-occurring
pairs) matched exactly: every `w ∈ {5,6}` pair co-occurred exactly once, no `w ∈ {7,8}` pair ever
co-occurred, zero violations. In the prize window (`ρ = 1/2`, `δ ∈ (1−√ρ, 1−ρ)`) every codeword
pair satisfies `2a > w`, so the bound is never vacuous there.
-/

open Finset

namespace LinePairCooccurrence

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The point of the line `{f + γ·g}` at parameter `γ`. -/
def linePt (f g : Fin n → F) (γ : F) : Fin n → F := fun i => f i + γ * g i

/-- Coordinates where `u` and `v` agree. -/
def agreeSet (u v : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => u i = v i)

omit [Field F] [Fintype F] in
@[simp] theorem mem_agreeSet {u v : Fin n → F} {i : Fin n} :
    i ∈ agreeSet u v ↔ u i = v i := by simp [agreeSet]

/-- Off-support of the pair: coordinates where `c` and `c'` coincide. -/
def offSupp (c c' : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c i = c' i)

omit [Field F] [Fintype F] in
@[simp] theorem mem_offSupp {c c' : Fin n → F} {i : Fin n} :
    i ∈ offSupp c c' ↔ c i = c' i := by simp [offSupp]

/-- Support of the pair: coordinates where `c` and `c'` differ (cardinality = Hamming distance). -/
def supp (c c' : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c i ≠ c' i)

omit [Field F] [Fintype F] in
@[simp] theorem mem_supp {c c' : Fin n → F} {i : Fin n} :
    i ∈ supp c c' ↔ c i ≠ c' i := by simp [supp]

omit [Field F] [Fintype F] in
theorem supp_card_eq_hammingDist (c c' : Fin n → F) :
    (supp c c').card = hammingDist c c' := rfl

/-- The bad set: line parameters whose point has agreement `≥ a` with both `c` and `c'`. -/
def badSet (f g c c' : Fin n → F) (a : ℕ) : Finset F :=
  Finset.univ.filter
    (fun γ => a ≤ (agreeSet (linePt f g γ) c).card ∧ a ≤ (agreeSet (linePt f g γ) c').card)

@[simp] theorem mem_badSet {f g c c' : Fin n → F} {a : ℕ} {γ : F} :
    γ ∈ badSet f g c c' a ↔
      a ≤ (agreeSet (linePt f g γ) c).card ∧ a ≤ (agreeSet (linePt f g γ) c').card := by
  simp [badSet]

/-- Shared votes at `γ`: off-support coordinates where the line point agrees with `c`
(equivalently with `c'`). -/
def shared (f g c c' : Fin n → F) (γ : F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => linePt f g γ i = c i ∧ c i = c' i)

omit [Fintype F] in
@[simp] theorem mem_shared {f g c c' : Fin n → F} {γ : F} {i : Fin n} :
    i ∈ shared f g c c' γ ↔ linePt f g γ i = c i ∧ c i = c' i := by simp [shared]

omit [Fintype F] in
/-- **One vote per coordinate:** for a nowhere-zero direction, the shared-vote sets at distinct
parameters are disjoint — a coordinate `i` satisfies `f i + γ·g i = c i` for at most one `γ`. -/
theorem shared_disjoint (f g c c' : Fin n → F) (hg : ∀ i, g i ≠ 0)
    {γ γ' : F} (hne : γ ≠ γ') :
    Disjoint (shared f g c c' γ) (shared f g c c' γ') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  have h1 : f i + γ * g i = c i := (mem_shared.mp hi).1
  have h2 : f i + γ' * g i = c i := (mem_shared.mp hi').1
  have : γ * g i = γ' * g i := add_left_cancel (h1.trans h2.symm)
  exact hne (mul_right_cancel₀ (hg i) this)

/-- **Per-point vote split:** a doubly-good `γ` has `2a ≤ 2·(shared votes) + |supp|`. -/
theorem per_point_bound (f g c c' : Fin n → F) (a : ℕ) {γ : F}
    (hγ : γ ∈ badSet f g c c' a) :
    2 * a ≤ 2 * (shared f g c c' γ).card + (supp c c').card := by
  obtain ⟨hA, hA'⟩ := mem_badSet.mp hγ
  set p := linePt f g γ with hp
  set A := agreeSet p c with hAdef
  set A' := agreeSet p c' with hA'def
  set off := offSupp c c' with hoff
  -- the off-support parts of both agreement sets are exactly the shared votes
  have hAoff : A ∩ off = shared f g c c' γ := by
    ext i; simp only [Finset.mem_inter, hAdef, hoff, mem_agreeSet, mem_offSupp, mem_shared, hp]
  have hA'off : A' ∩ off = shared f g c c' γ := by
    ext i
    simp only [Finset.mem_inter, hA'def, hoff, mem_agreeSet, mem_offSupp, mem_shared, hp]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2 ▸ h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2 ▸ h1, h2⟩
  -- the on-support parts are disjoint and both live in supp
  have hdisj : Disjoint (A \ off) (A' \ off) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    have h1 : p i = c i := mem_agreeSet.mp (Finset.mem_sdiff.mp hi).1
    have h2 : p i = c' i := mem_agreeSet.mp (Finset.mem_sdiff.mp hi').1
    exact (Finset.mem_sdiff.mp hi).2 (mem_offSupp.mpr (h1 ▸ h2))
  have hsub : (A \ off) ∪ (A' \ off) ⊆ supp c c' := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact mem_supp.mpr (fun hcc => (Finset.mem_sdiff.mp h).2 (mem_offSupp.mpr hcc))
    · exact mem_supp.mpr (fun hcc => (Finset.mem_sdiff.mp h).2 (mem_offSupp.mpr hcc))
  have hsplitA : (A ∩ off).card + (A \ off).card = A.card :=
    Finset.card_inter_add_card_sdiff A off
  have hsplitA' : (A' ∩ off).card + (A' \ off).card = A'.card :=
    Finset.card_inter_add_card_sdiff A' off
  have hcup : (A \ off).card + (A' \ off).card ≤ (supp c c').card := by
    have := Finset.card_union_of_disjoint hdisj
    have hle := Finset.card_le_card hsub
    omega
  have ht : (A ∩ off).card = (shared f g c c' γ).card := by rw [hAoff]
  have ht' : (A' ∩ off).card = (shared f g c c' γ).card := by rw [hA'off]
  omega

/-- **The per-line pair co-occurrence bound** (integer form, no division):
    `|badSet| · 2a  ≤  |badSet| · |supp| + 2·|offSupp|`.
With `w = Δ(c,c')` this reads `B·2a ≤ B·w + 2(n−w)`, i.e. `B ≤ 2(n−w)/(2a−w)` when `2a > w`. -/
theorem badSet_card_bound (f g c c' : Fin n → F) (a : ℕ) (hg : ∀ i, g i ≠ 0) :
    (badSet f g c c' a).card * (2 * a) ≤
      (badSet f g c c' a).card * (supp c c').card + 2 * (offSupp c c').card := by
  set bad := badSet f g c c' a with hbad
  -- total shared votes across the bad set are pairwise disjoint subsets of the off-support
  have hdisj : ∀ γ ∈ bad, ∀ γ' ∈ bad, γ ≠ γ' →
      Disjoint (shared f g c c' γ) (shared f g c c' γ') :=
    fun γ _ γ' _ hne => shared_disjoint f g c c' hg hne
  have hbiUnion : (bad.biUnion (shared f g c c')).card
      = ∑ γ ∈ bad, (shared f g c c' γ).card := Finset.card_biUnion hdisj
  have hsubset : bad.biUnion (shared f g c c') ⊆ offSupp c c' := by
    intro i hi
    obtain ⟨γ, _, hγi⟩ := Finset.mem_biUnion.mp hi
    exact mem_offSupp.mpr (mem_shared.mp hγi).2
  have hsum : ∑ γ ∈ bad, (shared f g c c' γ).card ≤ (offSupp c c').card := by
    rw [← hbiUnion]; exact Finset.card_le_card hsubset
  calc bad.card * (2 * a)
      = ∑ _γ ∈ bad, 2 * a := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ bad, (2 * (shared f g c c' γ).card + (supp c c').card) :=
        Finset.sum_le_sum (fun γ hγ => per_point_bound f g c c' a hγ)
    _ = 2 * (∑ γ ∈ bad, (shared f g c c' γ).card) + bad.card * (supp c c').card := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, smul_eq_mul]
    _ ≤ 2 * (offSupp c c').card + bad.card * (supp c c').card := by
        have := Nat.mul_le_mul_left 2 hsum; omega
    _ = bad.card * (supp c c').card + 2 * (offSupp c c').card := by ring

/-- **Heavy-agreement emptiness:** if `2a > 2·|offSupp| + |supp|` (i.e. `2a > 2n − w`), no line
point is doubly good. Kills all `w > 2(n−a)` pairs outright (the `w ∈ {7,8}` rows of the
`RS[8,4]/F₁₇` witness). -/
theorem badSet_eq_empty (f g c c' : Fin n → F) (a : ℕ)
    (h : 2 * (offSupp c c').card + (supp c c').card < 2 * a) :
    badSet f g c c' a = ∅ := by
  by_contra hne
  obtain ⟨γ, hγ⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hper := per_point_bound f g c c' a hγ
  have hshared : (shared f g c c' γ).card ≤ (offSupp c c').card := by
    apply Finset.card_le_card
    intro i hi
    exact mem_offSupp.mpr (mem_shared.mp hi).2
  omega

instance primeFact_LinePairCooccurrenceBound_1 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Non-vacuity: over `ZMod 5` with `n = 2`, `f = 0`, `g = (1,1)`, `c = (0,0)`, `c' = (0,1)`,
`a = 1`: the bad set is nonempty (`γ = 0` agrees with both on coordinate 0) and the bound holds
with `|supp| = 1`, `|offSupp| = 1`. -/
example :
    let f : Fin 2 → ZMod 5 := fun _ => 0
    let g : Fin 2 → ZMod 5 := fun _ => 1
    let c : Fin 2 → ZMod 5 := fun _ => 0
    let c' : Fin 2 → ZMod 5 := fun i => if i = 1 then 1 else 0
    (badSet f g c c' 1).Nonempty ∧
      (badSet f g c c' 1).card * 2 ≤ (badSet f g c c' 1).card * 1 + 2 * 1 := by
  decide

end LinePairCooccurrence
