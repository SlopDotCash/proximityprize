/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceAgreementReality
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceTowerFloor

/-!
# The resonance off-diagonal is nonnegative and phase-gauge invariant (door-(iv), Lane 3)

`_ResonanceAgreementReality` proved the agreement off-diagonal `resonanceOffDiag u r` is **real** and,
for unit-modulus phases, `resonanceMoment u r = (m-1)^r + (resonanceOffDiag u r).re`.  This file pins
two further structural facts about that real off-diagonal — both honesty-grade Lane-3 locks, neither a
bound *toward* the prize:

1. **Floor lock (nonnegativity).**  Combining the reality decomposition with the in-tree Wick tower
   floor `(m-1)^r ≤ resonanceMoment u r` (`resonanceMoment_ge_pow`), the off-diagonal real part is
   **nonnegative** for every unit-modulus phase:

   > `0 ≤ (resonanceOffDiag u r).re`                          (`resonanceOffDiag_re_nonneg`)

   So the agreement off-diagonal never interferes *destructively* below the Wick floor `(m-1)^r` — the
   `√`-cancellation question is entirely a question about *how large* a **nonnegative** real off-diagonal
   can grow, never about a sign cancellation underneath the floor.  (Probe
   `probe_dooriv_agreement_offdiag_real.py`/`probe_offdiag_sign_gauge.py`: `min O(r) = 0` over thousands
   of random unit phases, `m=3..7`, `r=1..3`.)

2. **Phase-gauge invariance.**  The agreement double sum (hence `T(r)`, hence the off-diagonal) is
   invariant under the global rotation `u ↦ c·u` for unit-modulus `c`: every summand carries `r`
   conjugated and `r` un-conjugated phase factors, so the `c`-factors cancel `‖c‖^{2r}=1`.  Formally the
   resonance moment only depends on `u` through its *relative* phases:

   > `‖c‖ = 1 → resonanceMoment (fun a => c * u a) r = resonanceMoment u r`
   >                                                       (`resonanceMoment_const_smul_eq`)

   This is the formal companion of the phase-mass/phase-distribution dichotomy: the prize cannot be
   resolved by the absolute phase, only by the phase *distribution* of `{b·x^m}`.

No CORE / cancellation / completion / moment / anti-concentration / capacity claim — both results are
constraints that *localize* the open object, not bounds on it.  The off-diagonal stays OPEN.
Self-contained leaf over `_ResonanceAgreementReality` + `_ResonanceTowerFloor`.  Axiom-clean
(`{propext, Classical.choice, Quot.sound}`).  Issue #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- `((m - 1 : ℕ) : ℝ) ^ r = ((m : ℝ) - 1) ^ r` for `1 ≤ m` (nat-sub then cast = real-sub). -/
private theorem nat_pred_cast_pow_eq (r : ℕ) :
    ((m - 1 : ℕ) : ℝ) ^ r = ((m : ℝ) - 1) ^ r := by
  have hm : (1 : ℕ) ≤ m := NeZero.one_le
  rw [Nat.cast_sub hm, Nat.cast_one]

/-- **The off-diagonal real part is nonnegative.** For unit-modulus phases, the agreement off-diagonal
sits at or above `0`: `resonanceMoment u r = (m-1)^r + (resonanceOffDiag u r).re` and the in-tree Wick
floor gives `(m-1)^r ≤ resonanceMoment u r`, so `0 ≤ (resonanceOffDiag u r).re`. The off-diagonal never
interferes destructively below the Wick floor. -/
theorem resonanceOffDiag_re_nonneg (u : ZMod m → ℂ) (r : ℕ)
    (hu : ∀ a : ZMod m, ‖u a‖ = 1) :
    0 ≤ (resonanceOffDiag u r).re := by
  have hdecomp := resonanceMoment_eq_wick_add_offDiag_re u r (fun a _ => hu a)
  have hfloor : ((m : ℝ) - 1) ^ r ≤ resonanceMoment u r := resonanceMoment_ge_pow u hu r
  rw [hdecomp, nat_pred_cast_pow_eq r] at hfloor
  linarith

/-- **Phase-gauge invariance of the resonance moment.** Rotating every phase by a fixed unit-modulus
`c` (`u ↦ c·u`) leaves `phaseSum` scaled by `c^r`, hence each `‖phaseSum‖²` unchanged (`‖c^r‖²=1`), so
`resonanceMoment` is invariant.  The moment depends on `u` only through its *relative* phases. -/
theorem resonanceMoment_const_smul_eq (u : ZMod m → ℂ) (r : ℕ) {c : ℂ} (hc : ‖c‖ = 1) :
    resonanceMoment (fun a => c * u a) r = resonanceMoment u r := by
  classical
  unfold resonanceMoment
  refine Finset.sum_congr rfl (fun d _ => ?_)
  -- phaseSum (c • u) r d = c^r * phaseSum u r d
  have hps : phaseSum (fun a => c * u a) r d = c ^ r * phaseSum u r d := by
    unfold phaseSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun X hX => ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hps, norm_mul, norm_pow, hc, one_pow, one_mul]

end ArkLib.ProximityGap.GaussPhaseResonance

#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag_re_nonneg
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_const_smul_eq
