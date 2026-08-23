/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FoldedSumThreshold

/-!
# The slanted-stratum mod-p transfer threshold (#357, item 3)

Item 3 of the 26-thread review: the mod-`p` transfer for the slanted stratum's
12-term determinant, as an instantiation of the generic folded-sum engine
(`FoldedSumThreshold.lean`).  The slanted collinearity determinant of three
pair-points `(s_t, p_t) = (ζ^{a_t} + ζ^{b_t}, ζ^{a_t + b_t})`,

  `det = (s₂ − s₁)(p₃ − p₁) − (s₃ − s₁)(p₂ − p₁)`,

expands into exactly twelve `±ζ^e` monomials (`ℓ¹` weight `12`).  Hence:

* `slanted_sum_eq_det` — the weighted-sum form of the determinant;
* `slanted_transfer` — **the two-layer law for the slanted stratum**: for every
  prime above the explicit threshold `(2^{m−1}·12)^{2^{m−1}}`, the determinant
  vanishes mod `p` **iff** its folded polynomial vanishes in characteristic zero.

Combined with the probe-complete char-0 classification
(`probe_slanted_stratum_census.py`: every disjoint slanted collinear triple is an
affine-Galois image of chord/shape-I/shape-II), this pins the large-`p` slanted
census to the three families at every scale above threshold.
-/

open Finset

namespace ArkLib.ProximityGap.SlantedTransfer

open ArkLib.ProximityGap.WindowTwoLayer

/-- The twelve exponents of the slanted determinant
`(s₂−s₁)(p₃−p₁) − (s₃−s₁)(p₂−p₁)` in the order
`+s₂p₃, −s₂p₁, −s₁p₃, −s₃p₂, +s₃p₁, +s₁p₂` (two monomials each). -/
def slantedExp (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) : Fin 12 → ℕ :=
  ![a₂ + (a₃ + b₃), b₂ + (a₃ + b₃),
    a₂ + (a₁ + b₁), b₂ + (a₁ + b₁),
    a₁ + (a₃ + b₃), b₁ + (a₃ + b₃),
    a₃ + (a₂ + b₂), b₃ + (a₂ + b₂),
    a₃ + (a₁ + b₁), b₃ + (a₁ + b₁),
    a₁ + (a₂ + b₂), b₁ + (a₂ + b₂)]

/-- The matching signs. -/
def slantedWt : Fin 12 → ℤ :=
  ![1, 1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1]

theorem l1Weight_slanted : l1Weight Finset.univ slantedWt = 12 := by decide

/-- The twelve-term weighted sum IS the slanted collinearity determinant. -/
theorem slanted_sum_eq_det {p : ℕ} [Fact p.Prime] (g : ZMod p)
    (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) :
    ∑ x : Fin 12, ((slantedWt x : ZMod p)) * g ^ (slantedExp a₁ b₁ a₂ b₂ a₃ b₃ x)
      = ((g ^ a₂ + g ^ b₂) - (g ^ a₁ + g ^ b₁)) * (g ^ (a₃ + b₃) - g ^ (a₁ + b₁))
        - ((g ^ a₃ + g ^ b₃) - (g ^ a₁ + g ^ b₁)) * (g ^ (a₂ + b₂) - g ^ (a₁ + b₁)) := by
  simp only [Fin.sum_univ_succ, Finset.sum_empty, Fin.sum_univ_zero, slantedExp,
    slantedWt, Matrix.cons_val_zero, Matrix.cons_val_succ, Int.cast_one, Int.cast_neg,
    pow_add]
  ring

/-- **The slanted-stratum two-layer transfer** (item 3): above the explicit threshold
`(2^{m−1}·12)^{2^{m−1}}`, three pair-points are slanted-collinear mod `p` iff their
folded determinant vanishes in characteristic zero — the slanted census at large `p`
is exactly the characteristic-zero census (= the three families, by the
probe-complete classification). -/
theorem slanted_transfer {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ)
    (hp : (2 ^ (m - 1) * 12) ^ 2 ^ (m - 1) < p) :
    (((g ^ a₂ + g ^ b₂) - (g ^ a₁ + g ^ b₁)) * (g ^ (a₃ + b₃) - g ^ (a₁ + b₁))
        - ((g ^ a₃ + g ^ b₃) - (g ^ a₁ + g ^ b₁)) * (g ^ (a₂ + b₂) - g ^ (a₁ + b₁)) = 0)
      ↔ foldedSum m Finset.univ (slantedExp a₁ b₁ a₂ b₂ a₃ b₃) slantedWt = 0 := by
  rw [← slanted_sum_eq_det]
  refine foldedSum_vanishing_iff_char0 hm hg Finset.univ _ slantedWt ?_
  rw [l1Weight_slanted]
  exact hp

/-! ## The vertical-stratum transfer (the 4-term surface)

The vertical stratum (equal pair-sums) is gated by the 4-term vanishing sum
`ζ^i + ζ^j − ζ^{i'} − ζ^{j'} = 0`; its char-0 closure is
`MCAVerticalStratumCharZero.pair_sum_rigidity`.  The same engine instantiation
transfers it mod `p`. -/

/-- The four exponents of the vertical (equal pair-sum) surface. -/
def verticalExp (i j i' j' : ℕ) : Fin 4 → ℕ := ![i, j, i', j']

/-- The matching signs. -/
def verticalWt : Fin 4 → ℤ := ![1, 1, -1, -1]

theorem l1Weight_vertical : l1Weight Finset.univ verticalWt = 4 := by decide

/-- The four-term weighted sum IS the vertical pair-sum difference. -/
theorem vertical_sum_eq {p : ℕ} [Fact p.Prime] (g : ZMod p) (i j i' j' : ℕ) :
    ∑ x : Fin 4, ((verticalWt x : ZMod p)) * g ^ (verticalExp i j i' j' x)
      = (g ^ i + g ^ j) - (g ^ i' + g ^ j') := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, verticalExp, verticalWt,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Int.cast_one, Int.cast_neg]
  ring

/-- **The vertical-stratum two-layer transfer** (item 3, second surface): above
`(2^{m−1}·4)^{2^{m−1}}`, two pair-sums agree mod `p` iff they agree in
characteristic zero — where `pair_sum_rigidity` forces the pairs equal.  The
large-`p` vertical census is exactly `C(n/2, 3)`. -/
theorem vertical_transfer {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) (i j i' j' : ℕ)
    (hp : (2 ^ (m - 1) * 4) ^ 2 ^ (m - 1) < p) :
    (g ^ i + g ^ j = g ^ i' + g ^ j')
      ↔ foldedSum m Finset.univ (verticalExp i j i' j') verticalWt = 0 := by
  rw [← sub_eq_zero, ← vertical_sum_eq g i j i' j']
  refine foldedSum_vanishing_iff_char0 hm hg Finset.univ _ verticalWt ?_
  rw [l1Weight_vertical]
  exact hp

end ArkLib.ProximityGap.SlantedTransfer

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.SlantedTransfer.slanted_sum_eq_det
#print axioms ArkLib.ProximityGap.SlantedTransfer.slanted_transfer
#print axioms ArkLib.ProximityGap.SlantedTransfer.vertical_sum_eq
#print axioms ArkLib.ProximityGap.SlantedTransfer.vertical_transfer
