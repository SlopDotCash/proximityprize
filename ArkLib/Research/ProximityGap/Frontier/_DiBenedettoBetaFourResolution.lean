/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Resolving the di Benedetto bound at β = 4 (#444)

The campaign carried a long-standing DISPUTE about the di Benedetto et al. subgroup exponential-sum
bound at the prize point β = 4. The ground truth (di Benedetto–Garaev–García–González-Sánchez–
Shparlinski–Trujillo, *New estimates for exponential sums over multiplicative subgroups and intervals
in prime fields*, arXiv:2003.06165) is:

> For a multiplicative subgroup `H ⊆ F_p^×` of order `H` with **`H > p^{1/4}`**,
> `max_{(a,p)=1} |Σ_{x∈H} e_p(ax)| ≤ H^{1 − 31/2880 + o(1)}`.

This file FORMALIZES the exact exponent arithmetic and the validity geometry, RESOLVING the dispute.
It does NOT re-prove the (deep) di Benedetto theorem; it pins down precisely (a) that the saving is a
genuine sub-trivial power of `H` with **no `p^{1/72}` prefactor** (correcting the retracted `n^{73/72}`
claim), and (b) that the validity hypothesis `H > p^{1/4}` is **exactly `β < 4`**, so the prize point
β = 4 is the EXCLUDED boundary `H = p^{1/4}`.

Conventions: `H = n` (our `μ_n`, `n = 2^a`), `p = n^β`, so `H = n`, `p^{1/4} = n^{β/4}`, and the
di Benedetto exponent is `dbExp = 1 − 31/2880 = 2849/2880`.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.DiBenedettoBetaFour

open Real

/-- The di Benedetto exponent `1 − 31/2880`. -/
noncomputable def dbExp : ℝ := 1 - 31/2880

/-- **(1) The exponent is `2849/2880`, a genuine SUB-TRIVIAL saving.** `1 − 31/2880 = 2849/2880 < 1`.
There is no `p`-prefactor in the stated theorem: the bound is a clean power `H^{dbExp}`. -/
theorem dbExp_eq : dbExp = 2849/2880 := by unfold dbExp; norm_num

theorem dbExp_lt_one : dbExp < 1 := by unfold dbExp; norm_num

theorem dbExp_pos : 0 < dbExp := by unfold dbExp; norm_num

/-- **(2) Validity geometry: `H > p^{1/4} ⟺ β < 4`.** With `H = n` and `p = n^β` (`n > 1`),
`n > (n^β)^{1/4} ↔ β < 4`. So the di Benedetto hypothesis is satisfied EXACTLY in the range `β < 4`. -/
theorem validity_iff_beta_lt_four (n β : ℝ) (hn : 1 < n) :
    n > (n ^ β) ^ ((1 : ℝ) / 4) ↔ β < 4 := by
  have hn0 : (0 : ℝ) ≤ n := le_of_lt (lt_trans one_pos hn)
  have hmul : (n ^ β) ^ ((1 : ℝ) / 4) = n ^ (β / 4) := by
    rw [← Real.rpow_mul hn0]; congr 1; ring
  rw [gt_iff_lt, hmul]
  have key : n ^ (β / 4) < n ↔ β / 4 < 1 := by
    nth_rewrite 2 [← Real.rpow_one n]
    exact Real.rpow_lt_rpow_left_iff hn
  rw [key]; constructor <;> intro h <;> linarith

/-- **(3) β = 4 is the EXCLUDED boundary.** At `β = 4`, `p^{1/4} = (n^4)^{1/4} = n = H` exactly, so the
STRICT hypothesis `H > p^{1/4}` FAILS (it is equality). The prize point is the closed endpoint that
the di Benedetto theorem does not cover. -/
theorem boundary_at_four (n : ℝ) (hn : 0 ≤ n) :
    (n ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) = n := by
  rw [← Real.rpow_mul hn, show (4 : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one]

/-- The strict hypothesis fails at β = 4: `¬ (n > (n^4)^{1/4})` since they are equal. -/
theorem hypothesis_fails_at_four (n : ℝ) (hn : 0 ≤ n) :
    ¬ (n > (n ^ (4 : ℝ)) ^ ((1 : ℝ) / 4)) := by
  rw [boundary_at_four n hn]; exact lt_irrefl n

/-- **(4) Where it applies (`β < 4`), the realized bound is SUB-TRIVIAL: `n^{dbExp} < n`** (for
`n > 1`). I.e. the di Benedetto bound is genuinely below the trivial `M ≤ n` — NOT `n^{73/72} > n`.
This corrects the retracted prefactor claim. -/
theorem realized_subtrivial (n : ℝ) (hn : 1 < n) : n ^ dbExp < n := by
  have h1 : n ^ dbExp < n ^ (1 : ℝ) := by
    apply Real.rpow_lt_rpow_left_iff hn |>.mpr dbExp_lt_one
  rwa [Real.rpow_one] at h1

/-- **(5) Capstone — the resolution.** For `n > 1`:
* the di Benedetto exponent is `2849/2880 < 1` (a genuine saving, no `p`-prefactor);
* the hypothesis `H > p^{1/4}` holds EXACTLY for `β < 4`, where the bound `n^{2849/2880} < n` is
  sub-trivial;
* at `β = 4` the hypothesis FAILS (`H = p^{1/4}`), so the prize point is the excluded boundary.
Hence: di Benedetto gives `M ≤ n^{0.989...}` throughout `β < 4` (a real but tiny saving, far above
the prize `√n`), and is SILENT at the prize point `β = 4` — for the *boundary* reason, not because
the bound exceeds `n`. -/
theorem di_benedetto_beta_four_resolution (n : ℝ) (hn : 1 < n) :
    dbExp = 2849/2880 ∧ dbExp < 1 ∧
    (∀ β : ℝ, n > (n ^ β) ^ ((1:ℝ)/4) ↔ β < 4) ∧
    ¬ (n > (n ^ (4:ℝ)) ^ ((1:ℝ)/4)) ∧
    n ^ dbExp < n := by
  refine ⟨dbExp_eq, dbExp_lt_one, ?_, ?_, realized_subtrivial n hn⟩
  · intro β; exact validity_iff_beta_lt_four n β hn
  · exact hypothesis_fails_at_four n (le_of_lt (lt_trans one_pos hn))

end ArkLib.ProximityGap.DiBenedettoBetaFour

-- axiom audit
#print axioms ArkLib.ProximityGap.DiBenedettoBetaFour.dbExp_lt_one
#print axioms ArkLib.ProximityGap.DiBenedettoBetaFour.validity_iff_beta_lt_four
#print axioms ArkLib.ProximityGap.DiBenedettoBetaFour.boundary_at_four
#print axioms ArkLib.ProximityGap.DiBenedettoBetaFour.realized_subtrivial
#print axioms ArkLib.ProximityGap.DiBenedettoBetaFour.di_benedetto_beta_four_resolution
