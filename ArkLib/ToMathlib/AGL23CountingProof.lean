/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.AGL23Barrier

/-!
# AGL23 counting-extraction sub-bricks

Self-contained, verified building blocks toward the AGL23/BDG24 large-alphabet barrier
counting inequality (`AGL23CountingExtraction`, ABF26 §T3.10). The full extraction theorem
requires the unformalized AGL23 §4 (Lemma 4.1 subcode-with-distance, Lemma 4.2 large set
family, §3.3 pigeonhole) together with a `q`-ary Plotkin upper bound that is absent from
mathlib; that part remains genuinely external. This file isolates the *pure combinatorial
core* of the §3.3 pigeonhole step:

> **Bounded-fiber restriction counting.** For a finite codeword set `S : Finset (ι → F)` and a
> coordinate window `I₀ : Finset ι`, if the `I₀`-restriction map has every fiber of size at
> most `m` (no more than `m` words of `S` share a given restriction), then
> `|S| ≤ m · |image|`, equivalently the restriction image is large: `|image| ≥ |S| / m`.

This is exactly the step that converts a per-window collision bound (the consequence of
list-decodability: at most `ℓ` codewords agree on a near-complementary coordinate set) into the
*large family* `Fam` consumed by `AGL23.alphabet_barrier_reduction`. We then package a
`Fam`-existence corollary in the precise shape the reduction consumes, and an explicit
`2^(c·n)`-lower-bound bridge.
-/

open Real
open ListDecodable

namespace AGL23

variable {ι : Type*} {F : Type*}

/-- The `I₀`-restriction of a word, as a function `I₀ → F`. -/
def restrict (I₀ : Finset ι) (w : ι → F) : I₀ → F := fun i => w i

/-- **Bounded-fiber restriction counting (pigeonhole engine).** If the `I₀`-restriction map on a
finite codeword set `S` has every fiber of size at most `m`, then `|S| ≤ m · |image|`. This is
the combinatorial heart of the AGL23 §3.3 pigeonhole step: a uniform per-fiber collision bound
forces the restriction image to be large. -/
theorem card_le_mul_image_card_of_fiber_card_le [DecidableEq F]
    (S : Finset (ι → F)) (I₀ : Finset ι) (m : ℕ)
    (hfib : ∀ y : I₀ → F,
      (S.filter (fun w => restrict I₀ w = y)).card ≤ m) :
    S.card ≤ m * (S.image (restrict I₀)).card := by
  classical
  -- Partition `S` over the fibers of the restriction map indexed by its image.
  have hpart :
      S.card = ∑ y ∈ S.image (restrict I₀),
        (S.filter (fun w => restrict I₀ w = y)).card :=
    Finset.card_eq_sum_card_fiberwise (fun w hw => Finset.mem_image_of_mem _ hw)
  calc S.card
      = ∑ y ∈ S.image (restrict I₀),
          (S.filter (fun w => restrict I₀ w = y)).card := hpart
    _ ≤ ∑ _y ∈ S.image (restrict I₀), m :=
          Finset.sum_le_sum (fun y _ => hfib y)
    _ = (S.image (restrict I₀)).card * m := by rw [Finset.sum_const, smul_eq_mul]
    _ = m * (S.image (restrict I₀)).card := by rw [Nat.mul_comm]

/-- **Image-size lower bound.** Reformulation of the fiber bound as a *lower* bound on the
restriction image: `|image| ≥ |S| / m` (with `m ≥ 1`). This is the form directly feeding the
`Fam`-lower-bound used by `alphabet_barrier_reduction`. -/
theorem image_card_ge_of_fiber_card_le [DecidableEq F]
    (S : Finset (ι → F)) (I₀ : Finset ι) (m : ℕ) (_hm : 1 ≤ m)
    (hfib : ∀ y : I₀ → F,
      (S.filter (fun w => restrict I₀ w = y)).card ≤ m) :
    S.card / m ≤ (S.image (restrict I₀)).card := by
  have hkey := card_le_mul_image_card_of_fiber_card_le S I₀ m hfib
  exact Nat.div_le_of_le_mul hkey

/-- **Real-valued image-size lower bound.** The `ℝ`-cast form `|S| / m ≤ |image|`, the precise
shape consumed when chaining into the `2^(c·n)` family lower bound of
`alphabet_barrier_reduction` (avoids the floor in the `ℕ`-division form). -/
theorem image_card_ge_real_of_fiber_card_le [DecidableEq F]
    (S : Finset (ι → F)) (I₀ : Finset ι) (m : ℕ) (hm : 1 ≤ m)
    (hfib : ∀ y : I₀ → F,
      (S.filter (fun w => restrict I₀ w = y)).card ≤ m) :
    (S.card : ℝ) / m ≤ ((S.image (restrict I₀)).card : ℝ) := by
  have hkey := card_le_mul_image_card_of_fiber_card_le S I₀ m hfib
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hmR]
  have : (S.card : ℝ) ≤ ((m * (S.image (restrict I₀)).card : ℕ) : ℝ) := by exact_mod_cast hkey
  rw [Nat.cast_mul] at this
  linarith [this, (by ring : ((m : ℝ) * (S.image (restrict I₀)).card)
    = ((S.image (restrict I₀)).card : ℝ) * m)]

/-- **`Fam`-existence corollary in `alphabet_barrier_reduction` shape.** Given a finite codeword
set `S`, a window `I₀`, a per-fiber collision bound `m`, and a lower bound `2^(c·n) ≤ |S| / m`,
the `I₀`-restriction image is a family `Fam` realized as `I₀`-restrictions of `S` and of size at
least `2^(c·n)`. This is exactly the `(Fam, hFam_lower, hrealize)` triple that
`alphabet_barrier_reduction` consumes — produced from the pigeonhole engine above. -/
theorem exists_fam_of_fiber_bound [Fintype F] [DecidableEq F]
    (S : Finset (ι → F)) (I₀ : Finset ι) (m : ℕ) (hm : 1 ≤ m)
    (n c : ℝ)
    (hfib : ∀ y : I₀ → F,
      (S.filter (fun w => restrict I₀ w = y)).card ≤ m)
    (hS_lower : (2 : ℝ) ^ (c * n) ≤ (S.card : ℝ) / m) :
    ∃ Fam : Finset (I₀ → F),
      (2 : ℝ) ^ (c * n) ≤ (Fam.card : ℝ) ∧
      Fam ⊆ S.image (fun w => fun i : I₀ => w i) := by
  classical
  refine ⟨S.image (restrict I₀), ?_, ?_⟩
  · exact le_trans hS_lower (image_card_ge_real_of_fiber_card_le S I₀ m hm hfib)
  · -- `restrict I₀` is definitionally the restriction used by the reduction
    intro x hx; exact hx

/-- **End-to-end bridge: pigeonhole engine ⟹ alphabet lower bound.** Combines
`exists_fam_of_fiber_bound` with `alphabet_barrier_reduction`: from a window `I₀` of size
`≤ 4·ε·n`, a per-fiber collision bound `m`, and the source-set lower bound
`2^(c·n) ≤ |S| / m`, conclude the AGL23 alphabet bound `q ≥ 2^((c/4)/ε)` directly. This shows
the bounded-fiber brick really discharges the combinatorial input of the reduction. -/
theorem alphabet_barrier_of_fiber_bound [Fintype F] [DecidableEq F]
    (S : Finset (ι → F)) (I₀ : Finset ι) (m : ℕ) (hm : 1 ≤ m)
    (n ε c : ℝ) (hn : 0 < n) (hε : 0 < ε)
    (hI₀ : (I₀.card : ℝ) ≤ 4 * ε * n)
    (hq1 : (1 : ℝ) ≤ Fintype.card F)
    (hfib : ∀ y : I₀ → F,
      (S.filter (fun w => restrict I₀ w = y)).card ≤ m)
    (hS_lower : (2 : ℝ) ^ (c * n) ≤ (S.card : ℝ) / m) :
    (2 : ℝ) ^ ((c / 4) / ε) ≤ (Fintype.card F : ℝ) := by
  obtain ⟨Fam, hFam_lower, hrealize⟩ :=
    exists_fam_of_fiber_bound S I₀ m hm n c hfib hS_lower
  exact alphabet_barrier_reduction S I₀ Fam n ε c hn hε hI₀ hq1 hFam_lower hrealize

end AGL23

#print axioms AGL23.card_le_mul_image_card_of_fiber_card_le
#print axioms AGL23.image_card_ge_of_fiber_card_le
#print axioms AGL23.image_card_ge_real_of_fiber_card_le
#print axioms AGL23.exists_fam_of_fiber_bound
#print axioms AGL23.alphabet_barrier_of_fiber_bound
