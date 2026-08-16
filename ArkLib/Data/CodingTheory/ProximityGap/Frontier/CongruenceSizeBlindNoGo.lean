/- Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# Residue-only congruence certificates cannot imply size bounds (#444 guardrail)

The prize wall is a bound on the DC-subtracted char-p surplus. In the notation of
`DCSubtractedMoment.sum_nonzero_moment` and `DCEnergyCorrection.DCEnergyBound`, the live target is
the reduced moment inequality
`q·E_r(G) − |G|^(2r) ≤ q·(2r−1)‼·|G|^r`, equivalently `A_r ≤ Wick`. Some swarm attempts produce only a
*congruence* certificate for a natural-valued excess/count abstraction, such as `M ∣ W` or
`W ≡ c (mod M)`, from a finite symmetry. A residue-only certificate can bound size only by a separate
wraparound argument such as `M ∣ W ∧ W < M ⟹ W = 0`, which requires independent size information.

**This file proves the generic arithmetic guardrail:** for any modulus `M ≥ 1` and any budget `slack`,
the class `{W : M ∣ W}` (and every residue class mod `M`) contains witnesses exceeding `slack`. Thus
divisibility or a fixed residue class, by itself, cannot imply `W ≤ slack`. This does **not** rule out a
real finite-symmetry argument that also supplies analytic/counting structure about the actual #444
residual; it only rules out treating the congruence alone as a size certificate.

Together with the in-tree no-gos this records the residue-only member of the "size bound cannot come
from method X alone" catalogue:
algebraic invariants of `Ψ` are **house-blind** (`disc(Ψ)=p^{m-1}f²`, SVP lower bound);
LP / Delsarte duals are **degree-1-blind** (`DelsarteLPNoGo.parseval_lp_extremal`); residue-only
congruence certificates are **size-blind** (here). The remaining lever is the archimedean, nonlinear,
depth-`ln q` energy bound = the BGK/Paley wall.

-/

namespace ArkLib.ProximityGap.CongruenceSizeBlindNoGo

/-- **A divisibility certificate cannot bound size.** For any modulus `M ≥ 1` and any budget `slack`,
there is a multiple of `M` strictly exceeding `slack`. Hence `M ∣ W` is consistent with `W > slack`:
knowing only `M ∣ W` never proves `W ≤ slack`. -/
theorem dvd_cannot_bound_size (M slack : ℕ) (hM : 0 < M) :
    ∃ W, M ∣ W ∧ slack < W := by
  refine ⟨M * (slack + 1), Dvd.intro _ rfl, ?_⟩
  calc slack < slack + 1 := Nat.lt_succ_self slack
    _ = 1 * (slack + 1) := (one_mul _).symm
    _ ≤ M * (slack + 1) := Nat.mul_le_mul_right _ hM

/-- **Divisibility alone does not imply any fixed upper bound.** This is the direct logical form of
`dvd_cannot_bound_size`: the residue-only certificate `M ∣ W` cannot prove `W ≤ slack`. -/
theorem not_forall_dvd_bound (M slack : ℕ) (hM : 0 < M) :
    ¬ ∀ W, M ∣ W → W ≤ slack := by
  rintro h
  rcases dvd_cannot_bound_size M slack hM with ⟨W, hdiv, hlt⟩
  exact not_lt_of_ge (h W hdiv) hlt

/-- **Residue-class form.** Every residue class `c (mod M)` (`M ≥ 1`) contains elements exceeding any
budget `slack`. So a symmetry/Galois/parity pin `W ≡ c (mod M)` is size-blind. -/
theorem residue_class_unbounded (M c slack : ℕ) (hM : 0 < M) :
    ∃ W, W % M = c % M ∧ slack < W := by
  refine ⟨c % M + M * (slack + 1), ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  · have h : slack + 1 ≤ M * (slack + 1) := by
      calc slack + 1 = 1 * (slack + 1) := (one_mul _).symm
        _ ≤ M * (slack + 1) := Nat.mul_le_mul_right _ hM
    omega

/-- **A fixed residue class alone does not imply any fixed upper bound.** -/
theorem not_forall_residue_bound (M c slack : ℕ) (hM : 0 < M) :
    ¬ ∀ W, W % M = c % M → W ≤ slack := by
  rintro h
  rcases residue_class_unbounded M c slack hM with ⟨W, hres, hlt⟩
  exact not_lt_of_ge (h W hres) hlt

end ArkLib.ProximityGap.CongruenceSizeBlindNoGo

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CongruenceSizeBlindNoGo.dvd_cannot_bound_size
#print axioms ArkLib.ProximityGap.CongruenceSizeBlindNoGo.not_forall_dvd_bound
#print axioms ArkLib.ProximityGap.CongruenceSizeBlindNoGo.residue_class_unbounded
#print axioms ArkLib.ProximityGap.CongruenceSizeBlindNoGo.not_forall_residue_bound
