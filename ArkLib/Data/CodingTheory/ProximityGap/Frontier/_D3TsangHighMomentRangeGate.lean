/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# D3 Tsang/Soundararajan high-moment range gate

Issue #464 flagged arXiv:2606.10242 as a possible cheap high-moment input.  The theorem is a
Tsang-range moment estimate: it supplies moments only inside a prescribed admissible range.  In
the plain Reed-Solomon prize regime, the analogous diagonal-dominant range has the schematic form

```text
n^(2r) <= q.
```

For a polynomial field size `q = n^beta`, this range forces `2r <= beta`.  Thus it reaches only
constant depth at fixed exponent `beta`, while the Paley/prize transfer needs depth growing like
`log q`.  The missing ingredient is not another diagonal-range mean-value bound; it is uniform
wraparound control beyond that range.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.D3TsangHighMomentRangeGate

/-- The schematic diagonal-dominant range for a `2r`-th moment theorem. -/
def DiagonalRange (n q r : ℕ) : Prop :=
  n ^ (2 * r) ≤ q

/-- **Polynomial field sizes exit the diagonal range past constant depth.**  If `q = n^beta` and
`beta < 2r`, then the diagonal condition `n^(2r) <= q` is false. -/
theorem not_diagonalRange_at_poly_field_of_beta_lt_twice_depth
    {n beta r : ℕ} (hn : 2 ≤ n) (hbeta : beta < 2 * r) :
    ¬ DiagonalRange n (n ^ beta) r := by
  intro hdiag
  have hbase : 1 < n := by omega
  have hlt : n ^ beta < n ^ (2 * r) := Nat.pow_lt_pow_right hbase hbeta
  exact not_lt_of_ge hdiag hlt

/-- Therefore any diagonal-range theorem at `q = n^beta` can only apply at depths satisfying
`2r <= beta`. -/
theorem twice_depth_le_beta_of_diagonalRange_at_poly_field
    {n beta r : ℕ} (hn : 2 ≤ n) (hdiag : DiagonalRange n (n ^ beta) r) :
    2 * r ≤ beta := by
  by_contra hle
  have hbeta : beta < 2 * r := Nat.lt_of_not_ge hle
  exact not_diagonalRange_at_poly_field_of_beta_lt_twice_depth hn hbeta hdiag

/-- A prize-like depth beyond the fixed polynomial exponent is outside the diagonal range. -/
theorem diagonalRange_fails_at_depth_beta_plus
    {n beta c : ℕ} (hn : 2 ≤ n) (hc : 0 < c) :
    ¬ DiagonalRange n (n ^ beta) (beta + c) := by
  apply not_diagonalRange_at_poly_field_of_beta_lt_twice_depth hn
  omega

/-- **Range countermodel.**  A bound known only up to depth `R` is compatible with an arbitrary
failure at depth `R + 1`.  Range-restricted high moments therefore do not control the
wraparound/log-depth moment needed by the prize unless a separate beyond-range input is supplied. -/
theorem range_bound_does_not_control_next_depth (B : ℝ) (R : ℕ) :
    ∃ stat : ℕ → ℝ, (∀ r, r ≤ R → stat r ≤ B) ∧ B < stat (R + 1) := by
  refine ⟨fun r => if r ≤ R then B - 1 else B + 1, ?_, ?_⟩
  · intro r hr
    simp [hr]
  · have hnot : ¬ R + 1 ≤ R := by omega
    simp [hnot]

/-! ## Axiom audit. -/
#print axioms not_diagonalRange_at_poly_field_of_beta_lt_twice_depth
#print axioms twice_depth_le_beta_of_diagonalRange_at_poly_field
#print axioms diagonalRange_fails_at_depth_beta_plus
#print axioms range_bound_does_not_control_next_depth

end ArkLib.ProximityGap.Frontier.D3TsangHighMomentRangeGate
