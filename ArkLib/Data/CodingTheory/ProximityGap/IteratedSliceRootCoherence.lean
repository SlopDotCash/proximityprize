/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FoldPolynomialSlices
import ArkLib.ToMathlib.IteratedFoldConservation

/-!
# Iterated slice root-coherence (issue #232, O69's "Conjecture D in elementary form")

DISPROOF_LOG O69 left as the named open core the **iterated** weight/dead-locus
tradeoff: at every depth `ℓ` of the 2-adic fold tree, a low-evaluation-weight error
forces all `2^ℓ` branch values (equivalently, for polynomial errors, all `2^ℓ` iterated
coefficient slices) to vanish *simultaneously* on a large common locus — the alive
slices must share root structure. Depth 1 was stated in O69 (`weight_ge_live_image`,
which commit `2dcc9cfd9` announced but did not actually land in-tree); the iterated form
was probed (3000 trials) but unproven.

This file **proves the iterated form at every depth**, in two layers:

* `branchVal_eq_zero_of_fiber_vanish` — **branch locality**: the depth-`ℓ` branch value
  at `y` reads the error only on the iterated fiber `{x ∈ S : x^(2^ℓ) = y}`. This is
  the one new ingredient the induction needs (the "weight transport" brick).
* `live_card_le_weight` / `dead_card_ge` — **iterated weight transport, hypothesis-free**
  (any `S`, any valued error `v`, no characteristic or closure assumptions): the set of
  depth-`ℓ` points where *some* branch value survives has size at most the evaluation
  weight `w` of `v`; dually, on at least `|iterSq S ℓ| − w` points of the depth-`ℓ`
  domain ALL `2^ℓ` branch values vanish at once.
* `branchSlice` / `branchVal_polyeval` — the **iterated slice law**: on a tower that
  stays negation-closed for the first `ℓ` levels (`0 ∉ D`, `2 ≠ 0`), the depth-`ℓ`
  branch values of a polynomial error `f.eval` are evaluations of the iterated
  coefficient slices `branchSlice f b` (even fold ↦ `evenSlice`, odd fold ↦
  `X · oddSlice`, exponent code `e ↦ ⌈e/2⌉` per O63).
* `iterated_slice_root_coherence` (+ `_div` with `|iterSq D ℓ| = |D|/2^ℓ` made explicit
  via `iterSq_card_mul`) — **the theorem**: for a polynomial error of evaluation weight
  `w` on such a tower, the common root locus shared by ALL `2^ℓ` iterated slices inside
  the depth-`ℓ` domain has size at least `|D|/2^ℓ − w`.

Adversarial probe (`scripts/probes/probe_sliceroots_iterated.py`): 1572 per-depth cases
over `μ_n ⊂ F_p`, `(p,n)` up to `(769, 256)`, depths 1–3, including minimal-weight
vanishing-set words, fiber-aligned supports (the `alive(ℓ) = 1` boundary `2^ℓ ∣ n − w`),
multiplicative-coset supports and single-residue sparse coefficients: 0 violations of
`live ≤ w` and 0 slice-law mismatches before formalization.
-/

namespace ArkLib.IteratedSliceCoherence

open Polynomial Finset ArkLib.IteratedFold
open LamLeungTwoPow (evenSlice oddSlice eval_evenSlice eval_oddSlice fiber_eq_pair)

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Branch locality and the iterated weight transport (hypothesis-free) -/

/-- **Branch locality**: the depth-`|b|` branch value at `y` depends only on the error
restricted to the iterated fiber `{x ∈ S : x^(2^|b|) = y}`. In particular it vanishes
whenever the error vanishes on that fiber. -/
theorem branchVal_eq_zero_of_fiber_vanish {S : Finset F} {v : F → F} (b : List Bool) :
    ∀ y : F, y ∈ iterSq S b.length →
      (∀ x ∈ S, x ^ 2 ^ b.length = y → v x = 0) → branchVal S v b y = 0 := by
  induction b with
  | nil =>
    intro y hy hfib
    exact hfib y hy (pow_one y)
  | cons c bs ih =>
    intro y _ hfib
    have hsum : ∀ z ∈ (iterSq S bs.length).filter (fun z => z ^ 2 = y),
        branchVal S v bs z = 0 := by
      intro z hz
      obtain ⟨hzS, hz2⟩ := Finset.mem_filter.mp hz
      refine ih z hzS ?_
      intro x hx hxz
      refine hfib x hx ?_
      rw [List.length_cons, pow_succ, pow_mul, hxz, hz2]
    cases c with
    | false =>
      rw [branchVal_false, foldVal]
      exact Finset.sum_eq_zero hsum
    | true =>
      rw [branchVal_true, foldValOdd]
      exact Finset.sum_eq_zero fun z hz => by rw [hsum z hz, zero_mul]

open Classical in
/-- **Iterated weight transport**: at every depth `ℓ`, the set of points of the
depth-`ℓ` domain where *some* branch value survives has size at most the evaluation
weight of the error. No hypotheses: any support set, any valued error, any field. -/
theorem live_card_le_weight (S : Finset F) (v : F → F) (ℓ : ℕ) :
    ((iterSq S ℓ).filter
        (fun y => ∃ b : List Bool, b.length = ℓ ∧ branchVal S v b y ≠ 0)).card
      ≤ (S.filter (fun x => v x ≠ 0)).card := by
  have hsub : (iterSq S ℓ).filter
        (fun y => ∃ b : List Bool, b.length = ℓ ∧ branchVal S v b y ≠ 0)
      ⊆ (S.filter (fun x => v x ≠ 0)).image (· ^ 2 ^ ℓ) := by
    intro y hy
    obtain ⟨hyS, b, hb, hbne⟩ := Finset.mem_filter.mp hy
    by_contra hyim
    refine hbne (branchVal_eq_zero_of_fiber_vanish b y (by rw [hb]; exact hyS) ?_)
    intro x hx hxy
    by_contra hvx
    exact hyim (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hvx⟩, hb ▸ hxy⟩)
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

open Classical in
/-- **Dead-locus lower bound** (dual form): at depth `ℓ`, ALL `2^ℓ` branch values vanish
simultaneously on at least `|iterSq S ℓ| − w` points of the depth-`ℓ` domain, where `w`
is the evaluation weight. Hypothesis-free. -/
theorem dead_card_ge (S : Finset F) (v : F → F) (ℓ : ℕ) :
    (iterSq S ℓ).card - (S.filter (fun x => v x ≠ 0)).card
      ≤ ((iterSq S ℓ).filter
          (fun y => ∀ b : List Bool, b.length = ℓ → branchVal S v b y = 0)).card := by
  have hdead_eq : (iterSq S ℓ).filter
        (fun y => ∀ b : List Bool, b.length = ℓ → branchVal S v b y = 0)
      = iterSq S ℓ \ (iterSq S ℓ).filter
          (fun y => ∃ b : List Bool, b.length = ℓ ∧ branchVal S v b y ≠ 0) := by
    rw [← Finset.filter_not]
    refine Finset.filter_congr fun y _ => ?_
    constructor
    · rintro h ⟨b, hb, hne⟩
      exact hne (h b hb)
    · intro h b hb
      by_contra hne
      exact h ⟨b, hb, hne⟩
  rw [hdead_eq, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]
  exact Nat.sub_le_sub_left (live_card_le_weight S v ℓ) _

/-! ## The iterated slice law for polynomial errors -/

omit [DecidableEq F] in
/-- Self-negation is impossible on a support avoiding `0` in characteristic `≠ 2`. -/
theorem ne_neg_of_mem {S : Finset F} (h0 : (0 : F) ∉ S) (h2 : (2 : F) ≠ 0) {z : F}
    (hz : z ∈ S) : z ≠ -z := by
  intro hcontra
  apply h0
  have h2z : (2 : F) * z = 0 := by linear_combination hcontra
  rcases mul_eq_zero.mp h2z with h | h
  · exact absurd h h2
  · rwa [← h]

theorem foldVal_congr {S : Finset F} {v w : F → F} (h : ∀ x ∈ S, v x = w x) (y : F) :
    foldVal S v y = foldVal S w y := by
  simp only [foldVal]
  exact Finset.sum_congr rfl fun x hx => h x (Finset.mem_filter.mp hx).1

theorem foldValOdd_congr {S : Finset F} {v w : F → F} (h : ∀ x ∈ S, v x = w x) (y : F) :
    foldValOdd S v y = foldValOdd S w y := by
  simp only [foldValOdd]
  exact Finset.sum_congr rfl fun x hx => by rw [h x (Finset.mem_filter.mp hx).1]

/-- The even fold of a polynomial error is the even coefficient slice (the
`FoldPolynomialSlices` law, restated for the iterated-fold `foldVal`). -/
theorem foldVal_polyeval {S : Finset F} (hneg : ∀ x ∈ S, -x ∈ S) (h0 : (0 : F) ∉ S)
    (h2 : (2 : F) ≠ 0) (g : F[X]) {z : F} (hz : z ∈ S) :
    foldVal S (fun x => g.eval x) (z ^ 2) = (evenSlice g).eval (z ^ 2) := by
  have hne : z ≠ -z := ne_neg_of_mem h0 h2 hz
  rw [foldVal, fiber_eq_pair hneg hz, Finset.sum_pair hne, eval_evenSlice]

/-- The odd fold of a polynomial error is `X ·` the odd coefficient slice. -/
theorem foldValOdd_polyeval {S : Finset F} (hneg : ∀ x ∈ S, -x ∈ S) (h0 : (0 : F) ∉ S)
    (h2 : (2 : F) ≠ 0) (g : F[X]) {z : F} (hz : z ∈ S) :
    foldValOdd S (fun x => g.eval x) (z ^ 2) = (X * oddSlice g).eval (z ^ 2) := by
  have hne : z ≠ -z := ne_neg_of_mem h0 h2 hz
  rw [foldValOdd, fiber_eq_pair hneg hz, Finset.sum_pair hne, eval_mul, eval_X]
  have hodd := eval_oddSlice g z
  calc g.eval z * z + g.eval (-z) * -z
      = z * (g.eval z - g.eval (-z)) := by ring
    _ = z * (z * (oddSlice g).eval (z ^ 2)) := by rw [hodd]
    _ = z ^ 2 * (oddSlice g).eval (z ^ 2) := by ring

/-- The iterated coefficient slice along a branch word: the even fold takes the even
slice, the odd fold takes `X ·` the odd slice (the unit twist of the fold), matching
the exponent code `e ↦ ⌈e/2⌉` of O63. -/
noncomputable def branchSlice (f : F[X]) : List Bool → F[X]
  | [] => f
  | false :: bs => evenSlice (branchSlice f bs)
  | true :: bs => X * oddSlice (branchSlice f bs)

/-- **The iterated slice law**: on a tower that stays negation-closed for the first
`|b|` levels, the depth-`|b|` branch values of a polynomial error are evaluations of
the iterated coefficient slices. -/
theorem branchVal_polyeval {D : Finset F} (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ D)
    (f : F[X]) :
    ∀ b : List Bool,
      (∀ m < b.length, ∀ x ∈ iterSq D m, -x ∈ iterSq D m) →
      ∀ y ∈ iterSq D b.length,
        branchVal D (fun x => f.eval x) b y = (branchSlice f b).eval y := by
  intro b
  induction b with
  | nil =>
    intro _ y _
    rfl
  | cons c bs ih =>
    intro hneg y hy
    have hm : bs.length < (c :: bs).length := by
      rw [List.length_cons]
      exact Nat.lt_succ_self _
    have hnegm : ∀ x ∈ iterSq D bs.length, -x ∈ iterSq D bs.length := hneg bs.length hm
    have h0m : (0 : F) ∉ iterSq D bs.length := zero_not_mem_iterSq h0 bs.length
    have hih : ∀ x ∈ iterSq D bs.length,
        branchVal D (fun x => f.eval x) bs x = (branchSlice f bs).eval x :=
      ih (fun m hmlt => hneg m (lt_trans hmlt hm))
    have hy' : y ∈ (iterSq D bs.length).image (· ^ 2) := hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy'
    cases c with
    | false =>
      rw [branchVal_false, foldVal_congr hih (z ^ 2), foldVal_polyeval hnegm h0m h2 _ hz]
      rfl
    | true =>
      rw [branchVal_true, foldValOdd_congr hih (z ^ 2),
        foldValOdd_polyeval hnegm h0m h2 _ hz]
      rfl

/-! ## The iterated root-coherence theorem -/

open Classical in
/-- **Iterated slice root-coherence** (O69's open core, abstract-cardinality form): for
a polynomial error of evaluation weight `w` on a tower negation-closed through depth
`ℓ`, ALL `2^ℓ` iterated coefficient slices vanish simultaneously on at least
`|iterSq D ℓ| − w` common points of the depth-`ℓ` domain — low weight forces the alive
slices to share that root locus. -/
theorem iterated_slice_root_coherence {D : Finset F} (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ D) (f : F[X]) (ℓ : ℕ)
    (hneg : ∀ m < ℓ, ∀ x ∈ iterSq D m, -x ∈ iterSq D m) :
    (iterSq D ℓ).card - (D.filter (fun x => f.eval x ≠ 0)).card
      ≤ ((iterSq D ℓ).filter
          (fun y => ∀ b : List Bool, b.length = ℓ → (branchSlice f b).eval y = 0)).card := by
  have htrans : (iterSq D ℓ).filter
        (fun y => ∀ b : List Bool, b.length = ℓ → (branchSlice f b).eval y = 0)
      = (iterSq D ℓ).filter
          (fun y => ∀ b : List Bool, b.length = ℓ →
            branchVal D (fun x => f.eval x) b y = 0) := by
    refine Finset.filter_congr fun y hy => ?_
    constructor
    · intro h b hb
      subst hb
      rw [branchVal_polyeval h2 h0 f b hneg y hy]
      exact h b rfl
    · intro h b hb
      subst hb
      rw [← branchVal_polyeval h2 h0 f b hneg y hy]
      exact h b rfl
  rw [htrans]
  exact dead_card_ge D (fun x => f.eval x) ℓ

/-! ## The exact tower cardinality, and the `|D|/2^ℓ − w` form -/

/-- Squaring exactly halves a negation-closed support avoiding `0` (char `≠ 2`). -/
theorem card_image_sq_mul_two {S : Finset F} (hneg : ∀ x ∈ S, -x ∈ S)
    (h0 : (0 : F) ∉ S) (h2 : (2 : F) ≠ 0) :
    (S.image (· ^ 2)).card * 2 = S.card := by
  have hmaps : ∀ x ∈ S, x ^ 2 ∈ S.image (· ^ 2) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  have hfib : ∀ y ∈ S.image (· ^ 2), (S.filter fun x => x ^ 2 = y).card = 2 := by
    intro y hy
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hy
    rw [fiber_eq_pair hneg hx₀]
    exact Finset.card_pair (ne_neg_of_mem h0 h2 hx₀)
  calc (S.image (· ^ 2)).card * 2
      = ∑ _y ∈ S.image (· ^ 2), 2 := by rw [Finset.sum_const, smul_eq_mul]
    _ = ∑ y ∈ S.image (· ^ 2), (S.filter fun x => x ^ 2 = y).card :=
        Finset.sum_congr rfl fun y hy => (hfib y hy).symm
    _ = S.card := (Finset.card_eq_sum_card_fiberwise hmaps).symm

/-- The depth-`ℓ` domain of a tower negation-closed through depth `ℓ` has exactly
`|D|/2^ℓ` points: `|iterSq D ℓ| · 2^ℓ = |D|`. -/
theorem iterSq_card_mul {D : Finset F} (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ D) :
    ∀ ℓ : ℕ, (∀ m < ℓ, ∀ x ∈ iterSq D m, -x ∈ iterSq D m) →
      (iterSq D ℓ).card * 2 ^ ℓ = D.card := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro _
    simp [iterSq]
  | succ n ih =>
    intro hneg
    have hstep : ((iterSq D n).image (· ^ 2)).card * 2 = (iterSq D n).card :=
      card_image_sq_mul_two (hneg n (Nat.lt_succ_self n)) (zero_not_mem_iterSq h0 n) h2
    calc (iterSq D (n + 1)).card * 2 ^ (n + 1)
        = ((iterSq D n).image (· ^ 2)).card * 2 * 2 ^ n := by
          rw [show iterSq D (n + 1) = (iterSq D n).image (· ^ 2) from rfl, pow_succ]
          ring
      _ = (iterSq D n).card * 2 ^ n := by rw [hstep]
      _ = D.card := ih (fun m hm => hneg m (Nat.lt_succ_of_lt hm))

open Classical in
/-- **Iterated slice root-coherence, `|D|/2^ℓ − w` form**: the common root locus shared
by all `2^ℓ` iterated coefficient slices of a weight-`w` polynomial error has size at
least `|D|/2^ℓ − w` inside the depth-`ℓ` domain. -/
theorem iterated_slice_root_coherence_div {D : Finset F} (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ D) (f : F[X]) (ℓ : ℕ)
    (hneg : ∀ m < ℓ, ∀ x ∈ iterSq D m, -x ∈ iterSq D m) :
    D.card / 2 ^ ℓ - (D.filter (fun x => f.eval x ≠ 0)).card
      ≤ ((iterSq D ℓ).filter
          (fun y => ∀ b : List Bool, b.length = ℓ → (branchSlice f b).eval y = 0)).card := by
  have hpos : 0 < 2 ^ ℓ := pow_pos (by norm_num) ℓ
  have hcard : D.card / 2 ^ ℓ = (iterSq D ℓ).card := by
    rw [← iterSq_card_mul h2 h0 ℓ hneg, Nat.mul_div_assoc _ dvd_rfl,
      Nat.div_self hpos, mul_one]
  rw [hcard]
  exact iterated_slice_root_coherence h2 h0 f ℓ hneg

end ArkLib.IteratedSliceCoherence
