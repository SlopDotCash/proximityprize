/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SmoothFiberCount
import Mathlib.Algebra.Polynomial.Expand

/-!
# Single-class weight rigidity — the census C3 claim, formal, at every radix (issue #232)

The branch census (DISPROOF_LOG O69, `probe_branch_census.py`) observed C3: a word whose
fold tree keeps a single alive branch at depth `ℓ` has weight `w` with `2^ℓ ∣ n − w`
(0/95,623 violations). In slice language (O63/O70) a single alive branch means a single
coefficient residue class: `f = X^r · g(X^m)`. This file proves the exact statement, for
ANY radix `m` with `m ∣ n` (nothing 2-adic is needed):

* `single_class_weight` — on a full `n`-th-root domain (`|H| = n = s·m`, `0 ∉ H`),
  `weight(X^r·g(X^m)) = n − m·#{y ∈ H^m : g(y) = 0}`: the zero set is a union of FULL
  `m`-power fibers (via `SmoothFiberCount.preimage_card_eq`) — single-class words are
  fiber-aligned;
* `dvd_sub_weight_of_single_class` — hence `m ∣ n − w`, the census rigidity as a theorem.

Contrapositive reading: any weight with `m ∤ n − w` forces ≥ 2 alive coefficient classes
mod `m` — narrowness in the 2-adic (or any-adic) coefficient tree is only available at
coset-compatible weights, the O46/O47 structure boundary.
-/

namespace ArkLib.ProximityGap.SingleClassWeight

open Polynomial ArkLib.ProximityGap.SmoothFiberCount

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Evaluation of a single-residue-class polynomial `X^r · g(X^m)`. -/
theorem eval_single_class (g : F[X]) (r m : ℕ) (x : F) :
    (X ^ r * Polynomial.expand F m g).eval x = x ^ r * g.eval (x ^ m) := by
  rw [eval_mul, eval_pow, eval_X, expand_eval]

omit [DecidableEq F] in
/-- On a domain avoiding zero, a single-class polynomial vanishes at `x` iff its slice
`g` vanishes at `x^m`. -/
theorem single_class_eval_eq_zero_iff {H : Finset F} (h0 : (0 : F) ∉ H)
    (g : F[X]) (r m : ℕ) {x : F} (hx : x ∈ H) :
    (X ^ r * Polynomial.expand F m g).eval x = 0 ↔ g.eval (x ^ m) = 0 := by
  have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
  rw [eval_single_class]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (pow_ne_zero r hx0)
    · exact h
  · intro h
    rw [h, mul_zero]

/-- **Exact weight of a single-class polynomial on a full root-of-unity domain**:
`weight = n − m·#(slice zeros in the image domain)`. The zero set is a union of full
`m`-power fibers — single-class words are fiber-aligned. -/
theorem single_class_weight (H : Finset F) {n s m : ℕ}
    (hroots : ∀ x ∈ H, x ^ n = 1) (hcard : H.card = n)
    (hnsm : n = s * m) (hs : 1 ≤ s) (hm : 1 ≤ m) (h0 : (0 : F) ∉ H)
    (g : F[X]) (r : ℕ) :
    (H.filter (fun x => (X ^ r * Polynomial.expand F m g).eval x ≠ 0)).card
      = n - m * ((H.image (· ^ m)).filter (fun y => g.eval y = 0)).card := by
  set Z : Finset F := (H.image (· ^ m)).filter (fun y => g.eval y = 0) with hZ
  have hZsub : Z ⊆ H.image (· ^ m) := Finset.filter_subset _ _
  have hzeros : H.filter (fun x => (X ^ r * Polynomial.expand F m g).eval x = 0)
      = H.filter (fun x => x ^ m ∈ Z) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hxH, hzero⟩
      refine ⟨hxH, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hxH, rfl⟩, ?_⟩⟩
      exact (single_class_eval_eq_zero_iff h0 g r m hxH).mp hzero
    · rintro ⟨hxH, hxZ⟩
      exact ⟨hxH, (single_class_eval_eq_zero_iff h0 g r m hxH).mpr
        (Finset.mem_filter.mp hxZ).2⟩
  have hcount : (H.filter (fun x => (X ^ r * Polynomial.expand F m g).eval x = 0)).card
      = m * Z.card := by
    rw [hzeros]
    exact preimage_card_eq H hroots hcard hnsm hs hm Z hZsub
  have hsplit : (H.filter (fun x => (X ^ r * Polynomial.expand F m g).eval x = 0)).card
      + (H.filter (fun x => ¬ (X ^ r * Polynomial.expand F m g).eval x = 0)).card
      = H.card := Finset.card_filter_add_card_filter_not
        (s := H) (p := fun x => (X ^ r * Polynomial.expand F m g).eval x = 0)
  simp only [ne_eq]
  omega

/-- **The census C3 rigidity, formal (every radix):** a single-class word's weight `w`
satisfies `m ∣ n − w` — staying in one coefficient class mod `m` forces fiber-aligned
(coset-compatible) weight. -/
theorem dvd_sub_weight_of_single_class (H : Finset F) {n s m : ℕ}
    (hroots : ∀ x ∈ H, x ^ n = 1) (hcard : H.card = n)
    (hnsm : n = s * m) (hs : 1 ≤ s) (hm : 1 ≤ m) (h0 : (0 : F) ∉ H)
    (g : F[X]) (r : ℕ) :
    m ∣ n - (H.filter (fun x => (X ^ r * Polynomial.expand F m g).eval x ≠ 0)).card := by
  rw [single_class_weight H hroots hcard hnsm hs hm h0 g r]
  have hle : m * ((H.image (· ^ m)).filter (fun y => g.eval y = 0)).card ≤ n := by
    have := preimage_card_eq H hroots hcard hnsm hs hm
      ((H.image (· ^ m)).filter (fun y => g.eval y = 0)) (Finset.filter_subset _ _)
    calc m * ((H.image (· ^ m)).filter (fun y => g.eval y = 0)).card
        = (H.filter (fun x => x ^ m ∈ (H.image (· ^ m)).filter (fun y => g.eval y = 0))).card :=
          this.symm
      _ ≤ H.card := Finset.card_filter_le _ _
      _ = n := hcard
  rw [Nat.sub_sub_self hle]
  exact dvd_mul_right m _

end ArkLib.ProximityGap.SingleClassWeight

