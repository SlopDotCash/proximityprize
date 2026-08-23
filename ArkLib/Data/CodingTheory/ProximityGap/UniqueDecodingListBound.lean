/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Card

/-!
# Unique-decoding list bound and Reed–Solomon agreement bound (verified, self-contained)

This file proves, from first principles with mathlib only, two foundational facts that sit at the
*bottom* row of the ABF26 proximity state-of-the-art table (Issue #232 §3, the `δ < δ_min/2` regime
"below unique decoding"):

* `listBall_card_le_one` — **unique decoding.** For any code `C` with minimum Hamming distance `≥ d`
  and any received word `r`, if `2 * e < d` then the list of codewords within Hamming distance `e` of
  `r` has **at most one** element (pure triangle-inequality packing). This is *why* `ε_mca` is trivial
  in this regime: the list is a singleton.
* `agreement_card_le` — **Reed–Solomon agreement bound (Singleton-sharp).** Two distinct polynomials
  of degree `< k`, evaluated on an injective domain `D : ι ↪ F`, agree in at most `k - 1` coordinates
  (the agreement set injects into the roots of `p - q ≠ 0`). Hence their RS codewords are at Hamming
  distance `≥ n - (k - 1)`: RS has minimum distance `≥ n - k + 1`.

Both are `sorry`-free and self-contained (no dependency on the ProximityGap research cone). They are
genuine classical coding-theory bricks — not the open prize, but the honestly-proven base case the
whole `δ`-axis is measured from.
-/

namespace ArkLib.CodingTheory.UniqueDecoding

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [DecidableEq F]

/-- A code `C` has **minimum distance at least `d`** if any two distinct codewords differ in at least
`d` coordinates. -/
def MinDistGe (C : Set (ι → F)) (d : ℕ) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≠ y → d ≤ hammingDist x y

/-- **Unique decoding, pointwise form.** If `C` has minimum distance `≥ d` and two codewords `x, y`
both lie within Hamming distance `e` of a received word `r` with `2 * e < d`, then `x = y`.

Proof: `hammingDist x y ≤ hammingDist x r + hammingDist r y ≤ e + e = 2e < d`; were `x ≠ y`, the
minimum-distance hypothesis would force `d ≤ hammingDist x y`, contradicting `hammingDist x y < d`. -/
theorem eq_of_close {C : Set (ι → F)} {d e : ℕ} (hC : MinDistGe C d) (h2e : 2 * e < d)
    {r x y : ι → F} (hx : x ∈ C) (hy : y ∈ C)
    (hrx : hammingDist x r ≤ e) (hry : hammingDist y r ≤ e) : x = y := by
  by_contra hne
  have hxy : d ≤ hammingDist x y := hC hx hy hne
  have htri : hammingDist x y ≤ hammingDist x r + hammingDist r y := hammingDist_triangle x r y
  rw [hammingDist_comm y r] at hry
  omega

/-- The **decoding list**: codewords of `C` (given as a `Finset`) within Hamming distance `e` of `r`. -/
def listBall (C : Finset (ι → F)) (r : ι → F) (e : ℕ) : Finset (ι → F) :=
  C.filter (fun c => hammingDist c r ≤ e)

/-- **Unique-decoding list bound.** Below half the minimum distance (`2 * e < d`), the decoding list
has at most one element. This is the `δ < δ_min/2` "below unique decoding" regime of the ABF26 table:
the list is a singleton, so list-decoding collapses to unique decoding. -/
theorem listBall_card_le_one {C : Finset (ι → F)} {d e : ℕ}
    (hC : MinDistGe (C : Set (ι → F)) d) (h2e : 2 * e < d) (r : ι → F) :
    (listBall C r e).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [listBall, Finset.mem_filter] at hx hy
  exact eq_of_close hC h2e (Finset.mem_coe.mpr hx.1) (Finset.mem_coe.mpr hy.1) hx.2 hy.2

/-! ### Reed–Solomon agreement / minimum distance via root counting -/

open Polynomial

variable [Field F]

/-- The Reed–Solomon codeword of a polynomial `p` over an evaluation domain `D`. -/
def rsCodeword (D : ι → F) (p : F[X]) : ι → F := fun i => p.eval (D i)

/-- **Agreement bound.** Two distinct polynomials of degree `< k` evaluated on an injective domain
agree in at most `k - 1` coordinates. The agreement coordinates inject (via the injective `D`) into
`(p - q).roots`, of which there are at most `natDegree (p - q) ≤ k - 1`. -/
theorem agreement_card_le {D : ι ↪ F} {k : ℕ} {p q : F[X]}
    (hp : p.natDegree < k) (hq : q.natDegree < k) (hpq : p ≠ q) :
    (Finset.univ.filter (fun i => p.eval (D i) = q.eval (D i))).card ≤ k - 1 := by
  have hd : p - q ≠ 0 := sub_ne_zero.mpr hpq
  set s := Finset.univ.filter (fun i => p.eval (D i) = q.eval (D i)) with hs
  -- `i ↦ D i` injects `s` into the root finset of `p - q`.
  have hmap : ∀ i ∈ s, D i ∈ (p - q).roots.toFinset := by
    intro i hi
    rw [hs, Finset.mem_filter] at hi
    rw [Multiset.mem_toFinset, mem_roots hd, IsRoot.def, eval_sub, sub_eq_zero]
    exact hi.2
  have hcard : s.card ≤ (p - q).roots.toFinset.card :=
    Finset.card_le_card_of_injOn (fun i => D i) hmap (fun a _ b _ h => D.injective h)
  have hroots : (p - q).roots.toFinset.card ≤ (p - q).natDegree :=
    le_trans (Multiset.toFinset_card_le _) (card_roots' (p - q))
  have hdeg : (p - q).natDegree < k :=
    lt_of_le_of_lt (natDegree_sub_le p q) (by omega)
  omega

/-! ### Sharpness: the unique-decoding threshold `2·e < d` is tight -/

/-- **Sharpness, center existence.** If `x ≠ y` differ in `d = hammingDist x y` coordinates, there is
a center `r` within Hamming distance `⌈d/2⌉ = (d+1)/2` of *both* `x` and `y`. Construction: flip `x`
to `y`'s value on `⌊d/2⌋` of the `d` disagreement coordinates (`Finset.piecewise`). -/
theorem exists_center_within_half {x y : ι → F} (hxy : x ≠ y) :
    ∃ r : ι → F, hammingDist x r ≤ (hammingDist x y + 1) / 2 ∧
                 hammingDist y r ≤ (hammingDist x y + 1) / 2 := by
  classical
  set S : Finset ι := Finset.univ.filter (fun i => x i ≠ y i) with hSdef
  have hScard : S.card = hammingDist x y := by rw [hammingDist, hSdef]
  obtain ⟨T, hTS, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := S) (n := hammingDist x y / 2)
      (by rw [hScard]; exact Nat.div_le_self _ _)
  refine ⟨T.piecewise y x, ?_, ?_⟩
  · have hx : hammingDist x (T.piecewise y x) = T.card := by
      rw [hammingDist]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hne
        by_cases hiT : i ∈ T
        · exact hiT
        · rw [Finset.piecewise_eq_of_notMem _ _ _ hiT] at hne; exact absurd rfl hne
      · intro hiT
        rw [Finset.piecewise_eq_of_mem _ _ _ hiT]
        have hiS : i ∈ S := hTS hiT
        rw [hSdef, Finset.mem_filter] at hiS
        exact hiS.2
    rw [hx, hTcard]; omega
  · have hy : hammingDist y (T.piecewise y x) = (S \ T).card := by
      rw [hammingDist]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · intro hne
        by_cases hiT : i ∈ T
        · rw [Finset.piecewise_eq_of_mem _ _ _ hiT] at hne; exact absurd rfl hne
        · rw [Finset.piecewise_eq_of_notMem _ _ _ hiT] at hne
          refine ⟨?_, hiT⟩
          rw [hSdef, Finset.mem_filter]
          exact ⟨Finset.mem_univ i, Ne.symm hne⟩
      · rintro ⟨hiS, hiT⟩
        rw [Finset.piecewise_eq_of_notMem _ _ _ hiT]
        rw [hSdef, Finset.mem_filter] at hiS
        exact Ne.symm hiS.2
    rw [hy, Finset.card_sdiff, Finset.inter_eq_left.mpr hTS, hScard, hTcard]; omega

/-- **Sharpness of `listBall_card_le_one`.** Two distinct codewords `x ≠ y` (a code with minimum
distance `d = hammingDist x y`) yield a decoding list of size `≥ 2` at radius `e = ⌈d/2⌉`, where
`2 * e ≥ d`. So the hypothesis `2 * e < d` cannot be weakened: at `2 * e = d` the list already
exceeds one. -/
theorem listBall_two_at_half {x y : ι → F} (hxy : x ≠ y) :
    ∃ (r : ι → F) (e : ℕ), hammingDist x y ≤ 2 * e ∧ 2 ≤ (listBall {x, y} r e).card := by
  obtain ⟨r, hxr, hyr⟩ := exists_center_within_half hxy
  refine ⟨r, (hammingDist x y + 1) / 2, by omega, ?_⟩
  have hxmem : x ∈ listBall {x, y} r ((hammingDist x y + 1) / 2) := by
    have hx : x ∈ ({x, y} : Finset (ι → F)) := Finset.mem_insert_self x {y}
    simpa only [listBall, Finset.mem_filter] using ⟨hx, hxr⟩
  have hymem : y ∈ listBall {x, y} r ((hammingDist x y + 1) / 2) := by
    have hy : y ∈ ({x, y} : Finset (ι → F)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
    simpa only [listBall, Finset.mem_filter] using ⟨hy, hyr⟩
  exact Finset.one_lt_card.mpr ⟨x, hxmem, y, hymem, hxy⟩

end ArkLib.CodingTheory.UniqueDecoding
