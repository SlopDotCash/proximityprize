/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusTowerDescent
import ArkLib.Data.CodingTheory.ProximityGap.HaloFreeThreshold

/-!
# The finite-field tower: above the threshold, the full dyadic classification holds in `F_p`

`CensusTowerDescent.lean` proved the 2-adic tower in characteristic zero;
`HaloFreeThreshold.lean` proved the depth-1 finite-field classification above an explicit
prime bound. This file completes layer 2 of the census architecture at **all dyadic
depths**: the tower induction is refactored over a *depth-1 oracle* (any field with
`2 ≠ 0`), so that

* `tower_closed_of_oracle` — the generic induction: if every level of the 2-adic filtration
  satisfies "vanishing sum ⟹ antipodal-closed", then `j` vanishing dyadic power sums force
  closure under the order-`2^j` root;
* `roots_pow_eq` — the generic bridge: in any field, the `2^m`-th roots of unity are exactly
  the powers of a primitive root (card argument);
* `depth1_finite` — the set form of the halo-free threshold: for `p` above the level-`m`
  bound, a set of `2^m`-th roots of `F_p` with vanishing sum is antipodal-closed;
* `tower_closed_finite` — **the finite-field tower**: for `p > (2^{m−1})^{2^{m−1}}`, a set
  of `2^m`-th roots of unity in `F_p` whose first `j` dyadic power sums vanish is a union
  of `x ↦ x^{2^j}` fibers. The level-`m'` thresholds decrease down the tower, so the single
  top-level hypothesis covers every level.

With this, layer 2 (threshold-protected finite-field = char-0 core) is proven at all
depths; the below-threshold residue is exactly the priced O149 halo.

## References
* Issue #357 (surfaces (i)-classification and (ii)); DISPROOF_LOG O145–O150.
-/

set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.KKH26

open Finset

variable {L : Type*} [Field L] [DecidableEq L]

/-! ## The generic transfer (any field with `2 ≠ 0`) -/

/-- `antipodal_fiber_sum`, generalized from `CharZero` to any field with `2 ≠ 0`. -/
theorem antipodal_fiber_sum' (h2 : (2 : L) ≠ 0) (g : L → L) (T : Finset L)
    (hanti : ∀ x ∈ T, -x ∈ T) (h0 : (0 : L) ∉ T) :
    ∑ x ∈ T, g (x ^ 2) = 2 * ∑ y ∈ T.image (fun x => x ^ 2), g y := by
  classical
  have hmaps : ∀ x ∈ T, (fun x => x ^ 2) x ∈ T.image (fun x => x ^ 2) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => g (x ^ 2))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro y hy
  obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hy
  have hxne : x ≠ 0 := fun h => h0 (h ▸ hxT)
  have hxnneg : x ≠ -x := by
    intro h
    have h2x : (2 : L) * x = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2x with hc | hx
    · exact h2 hc
    · exact hxne hx
  have hfilter : T.filter (fun z => z ^ 2 = x ^ 2) = {x, -x} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzT, hz⟩
      have hzz : (z - x) * (z + x) = 0 := by linear_combination hz
      rcases mul_eq_zero.mp hzz with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    · rintro (rfl | rfl)
      · exact ⟨hxT, rfl⟩
      · exact ⟨hanti x hxT, by ring⟩
  rw [hfilter]
  rw [Finset.sum_insert (by simpa using hxnneg), Finset.sum_singleton]
  have hnegsq : (-x) ^ 2 = x ^ 2 := by ring
  rw [hnegsq]
  ring

/-! ## The generic tower induction over a depth-1 oracle -/

/-- **The tower induction, generic over a depth-1 oracle.** If, at every level
`m' ∈ (m − j, m]` of the 2-adic filtration, vanishing sums of `2^{m'}`-th roots force
antipodal closure, then `j` vanishing dyadic power sums force closure under the
order-`2^j` root. Both the characteristic-zero tower and the finite-field
above-threshold tower are instances. -/
theorem tower_closed_of_oracle (h2 : (2 : L) ≠ 0) :
    ∀ (j m : ℕ), j ≤ m →
    (∀ m', m - j < m' → m' ≤ m → ∀ {η : L}, IsPrimitiveRoot η (2 ^ m') →
      ∀ (S : Finset L), (∀ x ∈ S, x ^ (2 ^ m') = 1) → (∑ x ∈ S, x = 0) →
        ∀ x ∈ S, -x ∈ S) →
    ∀ {ζ : L}, IsPrimitiveRoot ζ (2 ^ m) → ∀ (T : Finset L),
      (∀ x ∈ T, x ^ (2 ^ m) = 1) →
      (∀ i, i < j → ∑ x ∈ T, x ^ (2 ^ i) = 0) →
      ∀ x ∈ T, ζ ^ (2 ^ (m - j)) * x ∈ T := by
  intro j
  induction j with
  | zero =>
    intro m _ _ ζ hζ T hT _ x hx
    have h1 : ζ ^ (2 ^ (m - 0)) = 1 := by
      simpa using hζ.pow_eq_one
    rw [h1, one_mul]
    exact hx
  | succ j ih =>
    intro m hjm horacle ζ hζ T hT hsums x hxT
    have hm1 : 1 ≤ m := by omega
    have h0 : (0 : L) ∉ T := by
      intro h
      have := hT 0 h
      rw [zero_pow (by positivity : 2 ^ m ≠ 0)] at this
      exact zero_ne_one this
    -- antipodal at the top level, via the oracle
    have hanti : ∀ y ∈ T, -y ∈ T := by
      refine horacle m (by omega) le_rfl hζ T hT ?_
      have := hsums 0 (by omega)
      simpa using this
    -- descend to the squares
    set T' : Finset L := T.image (fun x => x ^ 2) with hT'def
    have hζ2 : IsPrimitiveRoot (ζ ^ 2) (2 ^ (m - 1)) := by
      have h := hζ.pow (n := 2 ^ m) (by positivity) (show 2 ^ m = 2 * 2 ^ (m - 1) by
        rw [← pow_succ']
        congr 1
        omega)
      simpa using h
    have hT'roots : ∀ y ∈ T', y ^ (2 ^ (m - 1)) = 1 := by
      intro y hy
      obtain ⟨z, hzT, rfl⟩ := Finset.mem_image.mp hy
      rw [← pow_mul, show 2 * 2 ^ (m - 1) = 2 ^ m by rw [← pow_succ']; congr 1; omega]
      exact hT z hzT
    have hsums' : ∀ i, i < j → ∑ y ∈ T', y ^ (2 ^ i) = 0 := by
      intro i hi
      have htr := antipodal_fiber_sum' h2 (fun y => y ^ (2 ^ i)) T hanti h0
      have hpow : ∀ z : L, (z ^ 2) ^ (2 ^ i) = z ^ (2 ^ (i + 1)) := by
        intro z
        rw [← pow_mul]
        congr 1
        rw [pow_succ']
      simp only [hpow] at htr
      rw [hsums (i + 1) (by omega)] at htr
      rcases mul_eq_zero.mp htr.symm with hc | hOK
      · exact absurd hc h2
      · exact hOK
    have horacle' : ∀ m', (m - 1) - j < m' → m' ≤ m - 1 →
        ∀ {η : L}, IsPrimitiveRoot η (2 ^ m') →
        ∀ (S : Finset L), (∀ y ∈ S, y ^ (2 ^ m') = 1) → (∑ y ∈ S, y = 0) →
          ∀ y ∈ S, -y ∈ S := by
      intro m' h1' h2'
      exact horacle m' (by omega) (by omega)
    have hIH := ih (m - 1) (by omega) horacle' hζ2 T' hT'roots hsums'
    -- pullback
    have hx2 : x ^ 2 ∈ T' := Finset.mem_image_of_mem _ hxT
    have hclosed := hIH (x ^ 2) hx2
    have hexp : ((ζ ^ 2) ^ (2 ^ (m - 1 - j))) * x ^ 2
        = (ζ ^ (2 ^ (m - (j + 1))) * x) ^ 2 := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      congr 2
      have : m - 1 - j = m - (j + 1) := by omega
      rw [this]
      ring
    rw [hexp] at hclosed
    obtain ⟨w, hwT, hw2⟩ := Finset.mem_image.mp hclosed
    have hfac : (w - ζ ^ (2 ^ (m - (j + 1))) * x) * (w + ζ ^ (2 ^ (m - (j + 1))) * x) = 0 := by
      linear_combination hw2
    rcases mul_eq_zero.mp hfac with h | h
    · rw [← sub_eq_zero.mp h]
      exact hwT
    · have : ζ ^ (2 ^ (m - (j + 1))) * x = -w := by linear_combination h
      rw [this]
      exact hanti w hwT

/-! ## The finite-field instantiation -/

/-- **The generic root-coverage bridge:** in any field, the `2^m`-th roots of unity are
exactly the powers of a primitive `2^m`-th root (the `2^m` distinct powers exhaust the
≤ `2^m` roots of `X^{2^m} − 1`). -/
theorem exists_pow_eq_of_pow_eq_one {η : L} {n : ℕ} (hn : 0 < n)
    (hη : IsPrimitiveRoot η n) {x : L} (hx : x ^ n = 1) :
    ∃ i, i < n ∧ η ^ i = x := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨i, hilt, hieq⟩ := hη.eq_pow_of_pow_eq_one hx
  exact ⟨i, hilt, hieq⟩

/-- **Depth 1 in set form (finite field, above threshold):** for `p` above the level-`m`
bound, a set of `2^m`-th roots of unity in `F_p` with vanishing sum is antipodal-closed. -/
theorem depth1_finite {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {η : ZMod p} (hη : IsPrimitiveRoot η (2 ^ m))
    (hp : ((2 : ℕ) ^ (m - 1)) ^ 2 ^ (m - 1) < p)
    (S : Finset (ZMod p)) (hS : ∀ x ∈ S, x ^ (2 ^ m) = 1)
    (hsum : ∑ x ∈ S, x = 0) :
    ∀ x ∈ S, -x ∈ S := by
  classical
  set N : ℕ := 2 ^ (m - 1) with hN
  have hηN : η ^ N = -1 := by
    have := R12.pow_half_eq_neg_one hm hη
    simpa [hN] using this
  -- exponent set of `S`
  set E : Finset ℕ := (range (2 ^ m)).filter (fun e => η ^ e ∈ S) with hE
  have hEsub : E ⊆ range (2 ^ m) := Finset.filter_subset _ _
  -- `S` is the image of `E` under `η ^ ·`, injectively
  have hinj : ∀ a ∈ range (2 ^ m), ∀ b ∈ range (2 ^ m), η ^ a = η ^ b → a = b := by
    intro a ha b hb hab
    exact hη.pow_inj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab
  have hSimg : S = E.image (fun e => η ^ e) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hilt, hieq⟩ := exists_pow_eq_of_pow_eq_one (by positivity) hη (hS x hx)
      exact Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hilt, hieq ▸ hx⟩, hieq⟩
    · intro hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp he).2
  have hsumE : ∑ e ∈ E, η ^ e = 0 := by
    rw [hSimg, Finset.sum_image (fun a ha b hb h => hinj a (hEsub ha) b (hEsub hb) h)] at hsum
    exact hsum
  -- apply the halo-free threshold
  have hclosed : AntipodalClosed N E := by
    rw [← sum_pow_eq_zero_iff_antipodalClosed hm hη hEsub (by simpa [hN] using hp)]
    exact hsumE
  -- transfer back to `S`
  intro x hx
  obtain ⟨i, hilt, hieq⟩ := exists_pow_eq_of_pow_eq_one (by positivity) hη (hS x hx)
  have hiE : i ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hilt, hieq ▸ hx⟩
  have h2N : 2 * N = 2 ^ m := by
    rw [hN, ← pow_succ']
    congr 1
    omega
  rcases Nat.lt_or_ge i N with hiN | hiN
  · -- antipodal partner is `i + N`
    have hmem : i + N ∈ E := (hclosed i hiN).mp hiE
    have : η ^ (i + N) ∈ S := (Finset.mem_filter.mp hmem).2
    have heq : η ^ (i + N) = -x := by
      rw [pow_add, hηN, hieq]
      ring
    rwa [heq] at this
  · -- antipodal partner is `i − N`
    have hiN' : i - N < N := by
      have := Finset.mem_range.mp (hEsub hiE)
      omega
    have hmem : i - N ∈ E := by
      have := (hclosed (i - N) hiN').mpr
      rw [Nat.sub_add_cancel hiN] at this
      exact this hiE
    have : η ^ (i - N) ∈ S := (Finset.mem_filter.mp hmem).2
    have heq : η ^ (i - N) = -x := by
      have hsplit : η ^ i = η ^ (i - N) * η ^ N := by
        rw [← pow_add]
        congr 1
        omega
      rw [hηN] at hsplit
      have : η ^ (i - N) = -η ^ i := by
        rw [hsplit]
        ring
      rw [this, hieq]
    rwa [heq] at this

/-- **THE FINITE-FIELD TOWER (above threshold).** For a prime `p` above the level-`m`
bound and a primitive `2^m`-th root `ζ ∈ F_p`: a set of `2^m`-th roots of unity whose
first `j` dyadic power sums vanish is closed under multiplication by `ζ^{2^{m−j}}` —
a union of `x ↦ x^{2^j}` fibers. The single top-level threshold covers every level of
the descent (lower levels have strictly smaller bounds). Layer 2 of the census
architecture, at all dyadic depths. -/
theorem tower_closed_finite {p : ℕ} [Fact p.Prime] {m j : ℕ} (hm : 1 ≤ m) (hjm : j ≤ m)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ (2 ^ m))
    (hp : ((2 : ℕ) ^ (m - 1)) ^ 2 ^ (m - 1) < p)
    (T : Finset (ZMod p)) (hT : ∀ x ∈ T, x ^ (2 ^ m) = 1)
    (hsums : ∀ i, i < j → ∑ x ∈ T, x ^ (2 ^ i) = 0) :
    ∀ x ∈ T, ζ ^ (2 ^ (m - j)) * x ∈ T := by
  classical
  -- `p` is odd: a primitive `2^m`-th root (`m ≥ 1`) gives `−1 ≠ 1` in `F_p`.
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hζN := R12.pow_half_eq_neg_one hm hζ
    intro h
    have hneg : (-1 : ZMod p) = 1 := by
      have h21 : (2 : ZMod p) = 1 + 1 := by ring
      have : (1 : ZMod p) + 1 = 0 := by rw [← h21]; exact h
      linear_combination -this
    have hone : ζ ^ (2 ^ (m - 1)) = 1 := by rw [hζN, hneg]
    have hdvd := hζ.pow_eq_one_iff_dvd (2 ^ (m - 1)) |>.mp hone
    have hlt : (2 : ℕ) ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hpos : 0 < (2 : ℕ) ^ (m - 1) := by positivity
    have := Nat.le_of_dvd hpos hdvd
    omega
  refine tower_closed_of_oracle h2 j m hjm ?_ hζ T hT hsums
  intro m' hm'lo hm'hi η hη S hS hsum
  have hm'1 : 1 ≤ m' := by
    -- `m' > m − j ≥ 0`; if `m' = 0` then `m − j < 0`, impossible.
    omega
  refine depth1_finite hm'1 hη ?_ S hS hsum
  -- level-`m'` threshold is dominated by the level-`m` threshold
  calc ((2 : ℕ) ^ (m' - 1)) ^ 2 ^ (m' - 1)
      ≤ ((2 : ℕ) ^ (m - 1)) ^ 2 ^ (m - 1) := by
        have h1 : (2 : ℕ) ^ (m' - 1) ≤ 2 ^ (m - 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2' : (2 : ℕ) ^ (m' - 1) ≤ 2 ^ (m - 1) := h1
        calc ((2 : ℕ) ^ (m' - 1)) ^ 2 ^ (m' - 1)
            ≤ ((2 : ℕ) ^ (m - 1)) ^ 2 ^ (m' - 1) := Nat.pow_le_pow_left h1 _
          _ ≤ ((2 : ℕ) ^ (m - 1)) ^ 2 ^ (m - 1) :=
              Nat.pow_le_pow_right (by positivity) (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ < p := hp

/-! ## Source audit -/

#print axioms tower_closed_of_oracle
#print axioms depth1_finite
#print axioms tower_closed_finite

end ArkLib.ProximityGap.KKH26
