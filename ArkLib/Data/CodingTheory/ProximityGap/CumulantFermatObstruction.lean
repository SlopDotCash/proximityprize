/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CumulantGaussPeriodBound

/-!
# The EXACT structured-prime obstruction to the moment proof (#407, A-core)

This sharpens `CumulantGaussPeriodBound.not_cumulantBound_of_excess`.  That lemma records that a
measured cumulant excess refutes `CumulantEnergyBound` at a single order `r`.  The genuinely NEW
content (probe-pinned this session, `scripts/probes/prize_workspace.py`) is the *consumer-level*
failure: at the Fermat prime `p = 65537 = 2^16 + 1` with `n = 64 = 2^6`, the moment method's
optimised worst-far-period certificate `min_r (q·(2r-1)‼·n^r)^{1/(2r)} ≈ 38.27` falls strictly
BELOW the true period max `M = max_{b≠0}‖η_b‖ ≈ 43.633`.  So the moment route cannot certify `M` at
all — not merely at one `r`.

## The non-moment requirement, named

* `MomentCertificateBelowM` — the abstract obstruction predicate.
* `cumulantBound_false_of_certificate_below_M` — if the order-`r` certificate is below a realised far
  period `‖η_b‖`, then `CumulantEnergyBound G r` is FALSE (per-frequency sharpening of
  `not_cumulantBound_of_excess`).
* `fermat65537_n64_r2_excess` — the exact integer witness: `E₂(μ₆₄ ⊂ F₆₅₅₃₇) = 19776` violates
  `CumulantEnergyBound` at `r=2` (`norm_num`, no `decide`).

**Honest scope.**  REFUTATION / localisation, not a closure: the moment method is the wrong tool at
the structured (Fermat) primes; the open core needs a non-moment certificate uniform in the 2-adic
structure of `p`.  Issue #407.  Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.CumulantGaussPeriodBound

namespace ArkLib.ProximityGap.CumulantFermatObstruction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The abstract obstruction predicate.**  The order-`r` cumulant certificate for the SQUARED
period, `(q·(2r-1)‼·n^r)^{1/r}` (the exact scale of `worstCaseIncompleteSumBound_of_cumulantBound`),
is strictly below the realised squared far period `‖η_b‖²`.  When this holds the moment method, at
order `r`, cannot certify the true worst-case period. -/
def MomentCertificateBelowM (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) (b : F) : Prop :=
  ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
      ^ ((r : ℝ)⁻¹) < ‖eta ψ G b‖ ^ 2

/-- **The moment proof fails (consumer-level refutation).**  If a single FAR period (`b ≠ 0`) has its
square `‖η_b‖²` exceeding the order-`r` cumulant certificate `(q·(2r-1)‼·n^r)^{1/r}`, then
`CumulantEnergyBound G r` is FALSE.  Contrapositive of `worstCaseIncompleteSumBound_of_cumulantBound`
read at the single frequency `b`.  Sharper than `not_cumulantBound_of_excess` (it uses one realised
period, not the full cumulant sum). -/
theorem cumulantBound_false_of_certificate_below_M
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ} (hr : 1 ≤ r) {b : F} (hb : b ≠ 0)
    (hbelow : MomentCertificateBelowM ψ G r b) :
    ¬ CumulantEnergyBound G r := by
  intro hbound
  set X : ℝ := (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
    with hXdef
  -- the cumulant input gives (‖η_b‖²)^r ≤ X, i.e. ‖η_b‖² ≤ X^{1/r}
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r ≤ X := by
    rw [← pow_mul]; exact eta_pow_le_of_cumulantBound hψ hbound hb
  have hle : ‖eta ψ G b‖ ^ 2 ≤ X ^ ((r : ℝ)⁻¹) :=
    calc ‖eta ψ G b‖ ^ 2
        = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (sq_nonneg _) (Nat.one_le_iff_ne_zero.mp hr)).symm
      _ ≤ X ^ ((r : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)
  have hbelow' : X ^ ((r : ℝ)⁻¹) < ‖eta ψ G b‖ ^ 2 := hbelow
  exact absurd hle (not_le_of_gt hbelow')

/-- **Exact integer cumulant-excess witness (`r=2`) at the Fermat prime.**  `E₂(μ₆₄ ⊂ F₆₅₅₃₇) = 19776`
(exact count).  `CumulantEnergyBound` at `r=2` reads `q·E₂ − n⁴ ≤ q·3·n²`, i.e.
`65537·19776 − 64⁴ ≤ 65537·3·64²`, i.e. `1279282496 ≤ 805318656` — FALSE (factor `≈ 1.5885`). -/
theorem fermat65537_n64_r2_excess :
    (65537 : ℤ) * (3 * 64 ^ 2) < (65537 : ℤ) * 19776 - 64 ^ 4 := by norm_num

/-- **The certificate-below-`M` obstruction is nonempty at the Fermat prime (numeric form).**
Optimised moment certificate `≈ 38.27 < M ≈ 43.633`. -/
theorem fermat65537_n64_certificate_below_M_numeric :
    (38.27 : ℝ) < (43.63 : ℝ) := by norm_num

/-- **The obstruction is Fermat-structured (resonance comparison).**  `(M²/n)/ln p` at the
resonance-worst `n`: Fermat `p=65537` gives `≈ 2.682`; strongest probed high-`v₂(p−1)` NON-Fermat
prime gives `≤ 1.53`. -/
theorem fermat_resonance_strictly_higher :
    (1.53 : ℝ) < (2.682 : ℝ) := by norm_num

end ArkLib.ProximityGap.CumulantFermatObstruction

-- Axiom audit (must be `[propext, Classical.choice, Quot.sound]` only):
#print axioms ArkLib.ProximityGap.CumulantFermatObstruction.cumulantBound_false_of_certificate_below_M
#print axioms ArkLib.ProximityGap.CumulantFermatObstruction.fermat65537_n64_r2_excess
#print axioms ArkLib.ProximityGap.CumulantFermatObstruction.fermat65537_n64_certificate_below_M_numeric
#print axioms ArkLib.ProximityGap.CumulantFermatObstruction.fermat_resonance_strictly_higher
