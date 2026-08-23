/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority), Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Block Relative Distance for smooth Reed-Solomon Codes

This file formalizes the notion of mutual correlated agreement for proximity generators,
introduced in Section 4 [ACFY24].

## Implementation notes

Block relative distance is defined for smooth rather than constrained Reed Solomon codes,
as is done in the reference paper, as they are more general.
The definition of `block' is also stated in a more general form than the reference paper.

We define distances for smooth ReedSolomon codes with respect to power and fiber domains,
as per Section 4.3.1, [ACFY24].
We have generalized the definitions for a generic i to present (i,k)-wise distance measures.
This modification is necessary to support following lemmas from Section  4.3.2.
The definitions from Section 4.3.1 correspond to i = 0.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]

-/

namespace BlockRelDistance

open ListDecodable NNReal ReedSolomon

variable {F : Type*} [Field F]
         {ι : Type*} [Fintype ι] [Pow ι ℕ]

/-- The `2^k`-th power images over an embedding `φ : ι ↪ F` and a finite set
  of elements `S : Finset ι`.

  In particular, it returns the set of field elements `y ∈ F` for which there exists `x ∈ S`
  such that `y = (φ x)^(2ᵏ)`. It models the image of the map `x ↦ (φ x)^(2ᵏ)` restricted to `S`.
  Semantically: `indexPowT S φ k = { (φ x)^(2ᵏ) | x ∈ S } ⊆ F`.
-/
def indexPowT (S : Finset ι) (φ : ι ↪ F) (k : ℕ) := { y : F // ∃ x ∈ S, y = (φ x) ^ (2^k) }

/-- For i ≤ k, the generic `2^(k-i)`-th power fiber over `y ∈ indexPowT S φ k`.
  For `φ' : ι^(2ⁱ) → F`, this defines the preimage of `y` under the map
  `x^(2ⁱ) ↦ x^(2ᵏ)` restricted to `x^(2ⁱ) ∈ S'`.

  It returns the subset `S'` of elements of type `ι^(2ⁱ)`
    such that `(x^(2ⁱ))^(2^(k-i)) = x^(2^k) = y`.
  Example i = 0 : powFiberT 0 k S' φ' y = { x ∈ S' | (x)^(2^k) = y }.
  Example i = 1 : powFiberT 1 k S' φ' y = { x^2 ∈ S' | (x^2)^(2^(k-1)) = y }.
-/
def powFiberT (i : ℕ) {k : ℕ} {S : Finset ι} {φ : ι ↪ F} (S' : Finset (indexPowT S φ i))
    (φ' : (indexPowT S φ i) ↪ F) (y : indexPowT S φ k) :=
  { x : (indexPowT S φ i) // x ∈ S' ∧ (φ' x) ^ (2^(k-i)) = y.val }

/-- Definition 4.16
  For `ι` be a smooth evaluation domain, `k` be a folding parameter, `z ∈ (ι^(2ᵏ))`,
  Block is the set of elements `{ y ∈ S', y ^ 2^(k-i) = z }`, for `S' : Finset ι^(2ⁱ)`. -/
def block (i : ℕ) {k : ℕ} {S : Finset ι} {φ : ι ↪ F}
    (S' : Finset (indexPowT S φ i))
  (φ' : (indexPowT S φ i) ↪ F) (z : indexPowT S φ k)
  [DecidableEq F] [DecidableEq ι] [Smooth φ] :=
    powFiberT i S' φ' z

/-- The class DecidableBlockDisagreement provides a decidability instance for testing
  pointwise inequality of two functions `f, g : ι^(2ⁱ) → F` on elements of `block i k S' φ' z`,
  for all `z ∈ LpowT S' φ' k`.

  This class abstracts the decidability condition required to determine whether two
  functions disagree on any point in the preimage of `z` under the map `x^(2ⁱ) ↦ x^(2ᵏ)` over the
  evaluation domain `φ' : ι^(2ⁱ) ↪ F`. This is useful in defining sets of such `z`.
-/
class DecidableBlockDisagreement
  (i k : ℕ) {S : Finset ι} {φ : ι ↪ F}
  [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  (φ' : (indexPowT S φ i) ↪ F) where
  dec_inst :
    ∀ z : indexPowT S φ k, ∀ g : (indexPowT S φ i) → F,
      Decidable (∃ y : block i S' φ' z, f y.val ≠ g y.val)

/-- Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then
  the (i,k)-wise block relative distance is defined as
    Δᵣ(i, k, f, S', φ', g) = |{z ∈ ι ^ 2^k : ∃ y ∈ Block(i,k,S',φ',z) f(y) ≠ g(y)}| / |ι^(2^k)|.

  Below, we define a disagreementSet(i,k,f,S',φ') as a map (g → Finset (indexPow S φ k))
  using the class DecidableBlockDisagreement, to filter a finite subset of the Finset
  (indexPow S φ k), as per {z ∈ ι ^ 2^k : ∃ y ∈ Block(i,k,S',φ',z) f(y) ≠ g(y)} for a given g.

  *Block-wise* variant of the canonical `Code.disagreementCols` (in
  `ArkLib/Data/CodingTheory/Basic/Distance.lean`): rather than reporting
  disagreement at each *coordinate*, this collects the *blocks* `z` for
  which at least one fiber-point `y ∈ Block z` disagrees. The
  base-case relationship: at `k = 0`, every block is a singleton and
  the two coincide. -/
noncomputable def disagreementSet
  (i k : ℕ) {S : Finset ι} {φ : ι ↪ F}
  [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  (φ' : (indexPowT S φ i) ↪ F) [∀ i : ℕ, Fintype (indexPowT S φ i)]
  [h : DecidableBlockDisagreement i k f S' φ'] :
  (g : (indexPowT S φ i) → F) → Finset (indexPowT S φ k) :=
  fun g =>
    Finset.univ.filter (fun z => @decide _ (h.dec_inst z g))

/-- Definition 4.17
  Given the disagreementSet from above, we obtain the block relative distance as
  |disagreementSet|/ |ι ^ (2^k)|
-/
noncomputable def blockRelDistance
  (i k : ℕ) {S : Finset ι} {φ : ι ↪ F}
  [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  (φ' : (indexPowT S φ i) ↪ F) [∀ i : ℕ, Fintype (indexPowT S φ i)]
  [h : DecidableBlockDisagreement i k f S' φ'] :
  (g : (indexPowT S φ i) → F) → ℝ≥0 :=
  fun g =>
    (disagreementSet i k f S' φ' g).card / (Fintype.card (indexPowT S φ k) : ℝ≥0)

/-- notation `Δᵣ(i, k, f, S', φ', g)` is the (i,k)-wise block relative distance. -/
scoped notation "Δᵣ( "i", "k", "f", "S'", "φ'", "g" )"  => blockRelDistance i k f S' φ' g

omit [Pow ι ℕ] in
/-- The block relative distance simplifies to the standard relative Hamming distance when `k=i`:
each block over `z` is then the singleton `{z}` itself, so block disagreement is pointwise
disagreement.

`hφ'` pins the evaluation embedding to the canonical subtype inclusion (as in the paper, where
the power domain sits inside `F` directly); for an arbitrary embedding the blocks are unrelated
to the points and the claim fails. -/
lemma blockRelDistance_eq_relHammingDist_of_k_eq_i -- Renamed for clarity
    (i : ℕ) {S : Finset ι} {φ : ι ↪ F}
  [DecidableEq F] [DecidableEq ι] [Smooth φ]
  -- The Fintype instance is now declared before it is needed by `hS'`.
  [h_fintype : ∀ i : ℕ, Fintype (indexPowT S φ i)]
  (f g : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  (hS' : S' = Finset.univ) -- This now works.
  (φ' : (indexPowT S φ i) ↪ F)
  (hφ' : ∀ x : indexPowT S φ i, φ' x = x.val)
  [h_dec : DecidableBlockDisagreement i i f S' φ'] :
  Δᵣ(i, i, f, S', φ', g) = δᵣ(f, g) := by
  classical
  have hset : disagreementSet i i f S' φ' g
      = Finset.univ.filter (fun z => f z ≠ g z) := by
    unfold disagreementSet
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨x, hxS', hxz⟩, hfg⟩
      rw [Nat.sub_self, pow_zero, pow_one, hφ'] at hxz
      have hxz' : x = z := Subtype.ext hxz
      subst hxz'
      exact hfg
    · intro hfg
      refine ⟨⟨z, ?_, ?_⟩, hfg⟩
      · rw [hS']; exact Finset.mem_univ z
      · rw [Nat.sub_self, pow_zero, pow_one, hφ']
  unfold blockRelDistance
  rw [hset]
  unfold Code.relHammingDist
  rw [NNRat.cast_div]
  congr 1

/-- For the set S ⊆ F^ι, we define the minimum block relative distance wrt set S. -/
noncomputable def minBlockRelDistance
  (i k : ℕ) {S : Finset ι} {φ : ι ↪ F}
  [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  (φ' : (indexPowT S φ i) ↪ F) (Set : Set ((indexPowT S φ i) → F))
  [∀ i : ℕ, Fintype (indexPowT S φ i)]
  [h : DecidableBlockDisagreement i k f S' φ'] : ℝ≥0 :=
    sInf { d : ℝ≥0 | ∃ g ∈ Set, Δᵣ(i, k, f, S', φ', g) = d}

/-- notation `Δₛ(i, k, f, S', φ', Set)` denotes the minimum block relative distance wrt `Set`. -/
scoped notation "Δₛ( "i", "k", "f", "S'", "φ'", "Set" )"  => minBlockRelDistance i k f S' φ' Set

/-- Definition 4.18
  For a smooth ReedSolomon code C = RS[F, ι^(2ⁱ), φ', m], proximity parameter δ ∈ [0,1]
  function f : ι^(2ⁱ) → F, we define the following as the list of codewords of C δ-close to f,
  i.e., u ∈ C such that Δᵣ(i, k, f, S', φ', u) ≤ δ. -/
noncomputable def listBlockRelDistance
  (i k : ℕ) {S : Finset ι} {φ : ι ↪ F} {φ' : (indexPowT S φ i) ↪ F}
  {m : ℕ} [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [DecidableEq (indexPowT S φ i)] [Smooth φ']
  (C : Set ((indexPowT S φ i) → F)) (_hcode : C = smoothCode φ' m) (δ : ℝ≥0)
  [h : DecidableBlockDisagreement i k f S' φ'] : (Set ((indexPowT S φ i) → F)) :=
    { u ∈ C | Δᵣ(i, k, f, S', φ', u) ≤ δ }

/-- `Λᵣ(i, k, f, S', C, hcode, δ)` denotes the list of codewords of C δ-close to f,
  wrt to the block relative distance. -/
scoped notation "Λᵣ( "i", "k", "f", "S'", "C", "hcode", "δ")" =>
  listBlockRelDistance i k f S' C hcode δ

omit [Pow ι ℕ] in
/-- Claim 4.19, Part 1
  For a smooth Reed-Solomon code, the standard relative Hamming distance `δᵣ(f,g)`
  is a lower bound for the (i, k)-wise block relative distance `Δᵣ(i, k, f, S', φ', g)`.

  ## Statement repair (paper-faithful hypotheses)

  As literally stated over the file's loose `indexPowT`/instance setup the claim is not provable
  for an arbitrary evaluation embedding `φ'`, an arbitrary `S'`, or arbitrary subtype `Fintype`
  instances; the paper's smooth-domain setting silently supplies extra structure. We make that
  structure explicit, exactly mirroring the repair documented on
  `blockRelDistance_eq_relHammingDist_of_k_eq_i` (the `k = i` case proven above):

  * `hφ' : ∀ x, φ' x = x.val` pins the power-domain embedding to the canonical subtype inclusion
    (as in the paper, where `ι^(2ⁱ)` sits inside `F` directly). For an arbitrary `φ'` the blocks
    are unrelated to the evaluation points and the inequality fails.
  * `hS' : S' = Finset.univ` is the paper's full evaluation domain.
  * `hik : i ≤ k` is implicit in the paper (folding only ever increases the exponent).
  * `hcard : Fintype.card (indexPowT S φ i) = 2 ^ (k - i) * Fintype.card (indexPowT S φ k)` is the
    2-adic cardinality relation that holds for genuine smooth domains (the `x ↦ x^(2^(k-i))` map
    is `2^(k-i)`-to-`1`). It is **not** derivable from the file's `indexPowT` definition together
    with `[Smooth φ]` alone, because that data does not pin the subtype `Fintype` instances, so we
    take it as a documented hypothesis.

  Both this lemma and its only consumer in this file (`listBlock_subset_listHamming`, Claim 4.19
  Part 2, which cites Part 1 verbatim) are otherwise-unused leaf lemmas — `git grep` confirms no
  external references — so the hypotheses are threaded through both consistently.

  ## Proof idea

  Each Hamming-disagreement point `x` (i.e. `f x ≠ g x`) maps to `z(x) ∈ indexPowT S φ k` with
  `z(x).val = x.val ^ (2^(k-i))`; with `hφ'`/`hS'` it witnesses `z(x) ∈ disagreementSet`. The fiber
  of `z ↦ z(x)` over any `b` has size `≤ 2^(k-i)`, since distinct `x` have distinct `val`s
  (injectivity of `Subtype.val`) and these are all roots of `X^(2^(k-i)) - C b.val` over the field
  `F` (`Polynomial.nthRoots`). Hence `Δ₀(f,g) ≤ 2^(k-i) * #disagreementSet`, and dividing through
  by `card_i = 2^(k-i) * card_k` gives `δᵣ(f,g) ≤ Δᵣ`.
-/
lemma relHammingDist_le_blockRelDistance
    (i k : ℕ) {S : Finset ι} {φ : ι ↪ F} {φ' : (indexPowT S φ i) ↪ F}
  [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f g : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  [h_fintype : ∀ i : ℕ, Fintype (indexPowT S φ i)]
  (hS' : S' = Finset.univ)
  (hφ' : ∀ x : indexPowT S φ i, φ' x = x.val)
  (hik : i ≤ k)
  (hcard : Fintype.card (indexPowT S φ i)
    = 2 ^ (k - i) * Fintype.card (indexPowT S φ k))
  [Smooth φ']
  [h_dec : DecidableBlockDisagreement i k f S' φ'] :
  δᵣ(f, g) ≤ Δᵣ(i, k, f, S', φ', g) := by
  classical
  -- Abbreviation for the power `p = 2^(k-i)`, which is strictly positive.
  set p : ℕ := 2 ^ (k - i) with hp_def
  have hp_pos : 0 < p := pow_pos (by norm_num) _
  -- The map sending a point `x : indexPowT S φ i` to its `p`-th power `x.val^p`, packaged back
  -- into `indexPowT S φ k`.  Well-definedness uses `2^i * 2^(k-i) = 2^k` (needs `i ≤ k`).
  have hz_val : ∀ x : indexPowT S φ i, ∃ x₀ ∈ S, (x.val) ^ p = (φ x₀) ^ (2 ^ k) := by
    rintro x
    obtain ⟨x₀, hx₀S, hx₀⟩ := x.property
    refine ⟨x₀, hx₀S, ?_⟩
    rw [hx₀, ← pow_mul, hp_def, ← pow_add]
    congr 1
    rw [← Nat.add_sub_assoc hik, Nat.add_sub_cancel_left]
  let z : indexPowT S φ i → indexPowT S φ k :=
    fun x => ⟨(x.val) ^ p, by obtain ⟨x₀, hx₀S, h⟩ := hz_val x; exact ⟨x₀, hx₀S, h⟩⟩
  have hz_val_eq : ∀ x : indexPowT S φ i, (z x).val = (x.val) ^ p := fun _ => rfl
  -- The Hamming-disagreement Finset.
  set D : Finset (indexPowT S φ i) := Finset.univ.filter (fun x => f x ≠ g x) with hD_def
  -- Each disagreement point lands in `disagreementSet` under `z`.
  have h_maps : ∀ x ∈ D, z x ∈ disagreementSet i k f S' φ' g := by
    intro x hx
    rw [hD_def, Finset.mem_filter] at hx
    have hfg : f x ≠ g x := hx.2
    unfold disagreementSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    refine ⟨⟨x, ?_, ?_⟩, hfg⟩
    · -- `x ∈ block i S' φ' (z x)` : membership in `S'` and the fiber equation.
      rw [hS']; exact Finset.mem_univ x
    · rw [hφ', hz_val_eq]
  -- Each fiber of `z` over a point `b` has size at most `p`, via roots of `X^p - C b.val`.
  have h_fiber : ∀ b ∈ disagreementSet i k f S' φ' g,
      (Finset.filter (fun x => z x = b) D).card ≤ p := by
    intro b _
    -- Inject the fiber into `F` via `Subtype.val`; the image lands in the `p`-th roots of `b.val`.
    set fib : Finset (indexPowT S φ i) := Finset.filter (fun x => z x = b) D with hfib_def
    have h_inj : Set.InjOn (fun x : indexPowT S φ i => x.val) fib :=
      fun a _ b _ h => Subtype.ext h
    have h_image_sub :
        fib.image (fun x : indexPowT S φ i => x.val) ⊆ (Polynomial.nthRoots p b.val).toFinset := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hxfib, hxy⟩ := hy
      rw [hfib_def, Finset.mem_filter] at hxfib
      have hzxb : z x = b := hxfib.2
      have hroot : (x.val) ^ p = b.val := by rw [← hz_val_eq x, hzxb]
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hp_pos, ← hxy]
      exact hroot
    calc fib.card = (fib.image (fun x : indexPowT S φ i => x.val)).card :=
            (Finset.card_image_of_injOn h_inj).symm
      _ ≤ (Polynomial.nthRoots p b.val).toFinset.card := Finset.card_le_card h_image_sub
      _ ≤ Multiset.card (Polynomial.nthRoots p b.val) := Multiset.toFinset_card_le _
      _ ≤ p := Polynomial.card_nthRoots p b.val
  -- Fiberwise counting: `#D ≤ p * #disagreementSet`.
  have hcount : Δ₀(f, g) ≤ p * (disagreementSet i k f S' φ' g).card := by
    have hHam : Δ₀(f, g) = D.card := rfl
    rw [hHam]
    exact Finset.card_le_mul_card_image_of_maps_to h_maps p h_fiber
  -- Endgame: divide the integer inequality by the cardinalities, in `ℝ≥0`.
  unfold Code.relHammingDist blockRelDistance
  rw [NNRat.cast_div]
  push_cast
  rw [hcard, Nat.cast_mul]
  -- Goal: `↑Δ₀(f,g) / (↑p * ↑card_k) ≤ ↑#disSet / ↑card_k` in `ℝ≥0`.
  set hh : ℝ≥0 := (Δ₀(f, g) : ℝ≥0) with hhdef
  set dd : ℝ≥0 := ((disagreementSet i k f S' φ' g).card : ℝ≥0) with hddef
  set cc : ℝ≥0 := (Fintype.card (indexPowT S φ k) : ℝ≥0) with hccdef
  set pp : ℝ≥0 := (p : ℝ≥0) with hppdef
  have hpp_pos : 0 < pp := by rw [hppdef]; exact_mod_cast hp_pos
  have hcount' : hh ≤ pp * dd := by
    rw [hhdef, hppdef, hddef]; exact_mod_cast hcount
  -- `hh / (pp * cc) = (hh / pp) / cc ≤ dd / cc`.
  rw [← div_div]
  rcases eq_or_lt_of_le (zero_le cc) with hcc | hcc
  · -- `cc = 0`: both sides are `_ / 0 = 0`.
    simp [← hcc]
  · rw [div_le_div_iff_of_pos_right hcc]
    exact div_le_of_le_mul₀ (zero_le pp) (zero_le dd) (by rwa [mul_comm] at hcount')

omit [Pow ι ℕ] in
/-- Claim 4.19, Part 2
  As a consequence of `relHammingDist_le_blockRelDistance`, the list of codewords
  within a certain block relative distance `δ` is a subset of the list of codewords
  within the same relative Hamming distance `δ`.

  This cites Claim 4.19 Part 1 (`relHammingDist_le_blockRelDistance`) verbatim, so it inherits the
  same paper-faithful hypotheses (`hS'`, `hφ'`, `hik`, `hcard`); see that lemma's docstring for the
  full justification. Both are otherwise-unused leaf lemmas in this file. -/
lemma listBlock_subset_listHamming
    (i k : ℕ) {S : Finset ι} {φ : ι ↪ F} {φ' : (indexPowT S φ i) ↪ F}
  {m : ℕ} [DecidableEq F] [DecidableEq ι] [Smooth φ]
  (f : (indexPowT S φ i) → F) (S' : Finset (indexPowT S φ i))
  [h_fintype : ∀ i : ℕ, Fintype (indexPowT S φ i)] [DecidableEq (indexPowT S φ i)] [Smooth φ']
  (hS' : S' = Finset.univ)
  (hφ' : ∀ x : indexPowT S φ i, φ' x = x.val)
  (hik : i ≤ k)
  (hcard : Fintype.card (indexPowT S φ i)
    = 2 ^ (k - i) * Fintype.card (indexPowT S φ k))
  (C : Set ((indexPowT S φ i) → F)) (hcode : C = smoothCode φ' m)
  [h_dec : DecidableBlockDisagreement i k f S' φ']
  (δ : ℝ≥0) :
  Λᵣ(i, k, f, S', C, hcode, δ) ⊆ closeCodewordsRel C f δ := by
  intro u hu
  simp only [listBlockRelDistance, Set.mem_sep_iff] at hu
  refine ⟨hu.1, ?_⟩
  have h1 := relHammingDist_le_blockRelDistance (φ' := φ') i k f u S' hS' hφ' hik hcard
  have h3 := le_trans h1 hu.2
  change (↑(@Code.relHammingDist _ (h_fintype i) F
    (fun a b => Classical.propDecidable (a = b)) f u) : ℝ) ≤ ↑δ
  rw [show (fun (a b : F) => Classical.propDecidable (a = b)) =
    ‹DecidableEq F› from Subsingleton.elim _ _]
  exact_mod_cast h3


end BlockRelDistance
