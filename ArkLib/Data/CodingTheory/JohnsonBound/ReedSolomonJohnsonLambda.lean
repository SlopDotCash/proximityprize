/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.JohnsonBound.Family

/-!
# Reed–Solomon Johnson list-size at the `Lambda` level (#371 / #389 floor lane)

The δ* prize **floor** asks for `δ* ≥ 1 − √ρ − η` over the full Johnson range,
"conditional on one named object with a numeric budget". The smooth-domain MCA
floor path (`SmoothDomainMCAWitness.le_mcaThreshold_ofListSizeGCXK25`) consumes
two inputs: a list-size bound `hΛ : Lambda C (1 − √ρ − η) ≤ L` and the
first-moment per-stack bad-scalar count `hBadCount`.

This file discharges the **first** input for Reed–Solomon codes, instantiating
the proven MDS Johnson list-size bound `CodingTheory.mds_johnson_lambda_le`
(ABF26 Corollary 3.3, `|Λ(C, 1−√ρ−η)| ≤ 1/(2ηρ)`) at an RS code — which is MDS
(`ReedSolomon.isMDS_code`, Singleton-tight `d = n − k + 1`). With `hΛ` now
in-tree, the conditional RS Johnson floor is reduced to the *single* named
residual `hBadCount` — exactly the prize's "one named object" form.

* `rs_johnson_lambda_le` — the RS list-size bound at the Johnson-minus-η radius,
  fully axiom-clean (it is a pure instantiation of the proven MDS bound).
-/

open CodingTheory ListDecodable

namespace ArkLib.JohnsonBound

/-- **Reed–Solomon Johnson list-size at the `Lambda` level.** For the
Reed–Solomon code `ReedSolomon.code α k` of rate `ρ = k / n` (`n = |ι|`), the
list size at the Johnson-minus-`η` radius is bounded by `1 / (2ηρ)`:

  `|Λ(RS[α,k], 1 − √ρ − η)| ≤ 1 / (2 · η · ρ)`.

This is the RS instance of the proven MDS bound `mds_johnson_lambda_le`
(ABF26 Corollary 3.3), available because RS codes are MDS
(`ReedSolomon.isMDS_code`). It supplies the list-size hypothesis `hΛ` of the
smooth-domain MCA floor path. -/
theorem rs_johnson_lambda_le {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k : ℕ} [NeZero k] {α : ι ↪ F}
    (η : ℝ) (hη_pos : 0 < η) (hk : k ≤ Fintype.card ι) :
    (Lambda ((ReedSolomon.code α k : Set (ι → F)))
        (1 - Real.sqrt ((k : ℝ) / Fintype.card ι) - η) : ENNReal) ≤
      ENNReal.ofReal (1 / (2 * η * ((k : ℝ) / Fintype.card ι))) := by
  have hfin : Module.finrank F (ReedSolomon.code α k) = k :=
    ReedSolomon.dim_eq_deg_of_le' hk
  have hmds := CodingTheory.mds_johnson_lambda_le
    (ReedSolomon.code α k) η hη_pos (ReedSolomon.isMDS_code hk)
  simpa only [hfin] using hmds

/-- **`ℕ`-valued RS Johnson list-size, ready for the GCXK25 floor consumer.** The same bound
with the list size packaged as the natural number `L = ⌈1/(2ηρ)⌉₊`, in the `ℕ∞` order that
`SmoothDomainMCAWitness.le_mcaThreshold_ofListSizeGCXK25` consumes as its `hΛ` hypothesis:

  `Λ(RS[α,k], 1 − √ρ − η) ≤ ⌈1/(2ηρ)⌉₊`.

This is the directly-pluggable list-size atom: supplying it to the smooth-domain MCA floor path
leaves `hBadCount` (the GCXK25 first-moment per-stack bad-scalar count) as the *sole* residual for
the conditional RS Johnson δ* floor. -/
theorem rs_johnson_lambda_nat_le {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k : ℕ} [NeZero k] {α : ι ↪ F}
    (η : ℝ) (hη_pos : 0 < η) (hk : k ≤ Fintype.card ι) :
    Lambda ((ReedSolomon.code α k : Set (ι → F)))
        (1 - Real.sqrt ((k : ℝ) / Fintype.card ι) - η)
      ≤ (⌈1 / (2 * η * ((k : ℝ) / Fintype.card ι))⌉₊ : ℕ∞) := by
  rw [← ENat.toENNReal_le, ENat.toENNReal_coe]
  refine le_trans (rs_johnson_lambda_le η hη_pos hk) ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)

end ArkLib.JohnsonBound
