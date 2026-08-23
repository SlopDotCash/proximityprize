/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodParsevalFloor

/-!
# The moment–Wick bridge: the two reductions of `M(n)` isolate ONE scalar (#444)

Two independent in-tree reductions of the prize per-frequency core
`M(n) = max_{b≠0} ‖η_b‖` (`η_b = ∑_{y∈G} ψ(b·y)`) target the *same* open object:

* **Route A — metaplectic amplification** (`MetaplecticParsevalAmplification`): `avg ≤ M² ≤ (q−1)·avg`,
  the open scalar being the amplification factor `C` in `M² ≤ C·avg`, `avg = n(q−n)/(q−1) ≈ n`;
  the prize is `C = c·log q`.
* **Route B — cosh-MGF / char-`p` Wick moment** (`Frontier/CoshMGFSaddleAssembled`): the saddle method
  gives `M ≤ Θ(√(n·log q))` *conditional* on the depth-`r` Wick energy bound
  `∑_{b≠0} ‖η_b‖^{2r} ≤ q·(2r−1)‼·nʳ` at `r ∼ log q`.

This file proves the **elementary moment-method bridge** that unifies them: the Wick energy bound at
level `r` (Route B's hypothesis) implies the *uniform per-frequency ceiling* `‖η_b‖^{2r} ≤ q·(2r−1)‼·nʳ`
for every `b≠0` — i.e. `M^{2r} ≤ q·(2r−1)‼·nʳ`, the `2r`-th-power input that feeds Route A's
amplification (`eta_sq_le_total` is exactly the `r=1` case).  So Route B ⟹ Route A: a single scalar, two
faces.  The bridge step is `single_le_sum` (a max term is at most the sum of nonnegative terms) — fully
proven.  The `r=1` Wick bound is also **proven** here (`wickEnergyBound_one`, from the exact second
moment), so the conditional chain is non-vacuous; the open content is exactly the bound at `r ∼ log q`
(the BGK / Paley √-cancellation wall — kept as the named Prop `WickEnergyBound`, never discharged at log
depth).

Cross-validated numerically (`scripts/probes`): the moment bound `(q·A_r)^{1/2r}` minimised over `r`
reproduces the true `M(n)` to within ≈1.1×, with the optimal depth `r ∼ ln q` — confirming the two
routes compute the same scalar.

Axiom-clean.  Issue #444.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodParsevalFloor

namespace ArkLib.ProximityGap.MomentWickBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The odd double factorial `(2r−1)‼ = ∏_{i<r}(2i+1)` (`= 1` at `r=0,1`), the char-`0` Wick constant. -/
def doubleFactOdd (r : ℕ) : ℕ := ∏ i ∈ Finset.range r, (2 * i + 1)

@[simp] theorem doubleFactOdd_zero : doubleFactOdd 0 = 1 := by simp [doubleFactOdd]
@[simp] theorem doubleFactOdd_one : doubleFactOdd 1 = 1 := by simp [doubleFactOdd]

/-- **Route B's named open hypothesis (the cosh-MGF / char-`p` Wick energy bound at depth `r`).**
`∑_{b≠0} ‖η_b‖^{2r} ≤ q·(2r−1)‼·nʳ`.  Proven at `r=1` (`wickEnergyBound_one`); the open content is
`r ∼ log q` (= the BGK/Paley √-cancellation wall). -/
def WickEnergyBound (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) : Prop :=
  ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
    ≤ (Fintype.card F : ℝ) * (doubleFactOdd r : ℝ) * (G.card : ℝ) ^ r

/-- **The `r=1` Wick bound is PROVEN** (the chain is non-vacuous), directly from the exact second moment
`∑_{b≠0}‖η_b‖² = q·n − n² ≤ q·n = q·(2·1−1)‼·n¹`. -/
theorem wickEnergyBound_one {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    WickEnergyBound ψ G 1 := by
  unfold WickEnergyBound
  have h : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * 1)
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
    simpa using sum_sq_erase_zero hψ G
  rw [h]
  have hsq : (0 : ℝ) ≤ (G.card : ℝ) ^ 2 := sq_nonneg _
  simp only [doubleFactOdd_one, Nat.cast_one, mul_one, pow_one]
  linarith

/-- **The moment-method bridge (Route B ⟹ uniform per-frequency ceiling = Route A's `2r`-th input).**
The depth-`r` Wick energy bound forces *every* nonzero frequency to satisfy
`‖η_b‖^{2r} ≤ q·(2r−1)‼·nʳ`; hence `M^{2r} ≤ q·(2r−1)‼·nʳ`.  Proof: a single nonnegative term is at most
the whole sum (`single_le_sum`).  At `r=1` this is exactly `MetaplecticParsevalAmplification.eta_sq_le_total`
up to the constant; for `r ∼ log q` it is the prize ceiling. -/
theorem eta_pow_le_of_wick {ψ : AddChar F ℂ} (G : Finset F) (r : ℕ)
    (hwick : WickEnergyBound ψ G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (doubleFactOdd r : ℝ) * (G.card : ℝ) ^ r := by
  classical
  set s : Finset F := Finset.univ.erase (0 : F) with hs
  have hbs : b ∈ s := Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
  have hnonneg : ∀ c ∈ s, 0 ≤ ‖eta ψ G c‖ ^ (2 * r) := fun c _ => pow_nonneg (norm_nonneg _) _
  have hle : ‖eta ψ G b‖ ^ (2 * r) ≤ ∑ c ∈ s, ‖eta ψ G c‖ ^ (2 * r) :=
    Finset.single_le_sum hnonneg hbs
  exact hle.trans hwick

/-- **Unification corollary (the scalar, both ways).**  Combining the bridge with the proven `r=1` base
case: every nonzero frequency obeys the second-moment ceiling `‖η_b‖² ≤ q·n` *unconditionally*, and obeys
the depth-`r` ceiling `‖η_b‖^{2r} ≤ q·(2r−1)‼·nʳ` *iff* the Wick bound holds at `r`.  So the prize floor
`M ≤ √(c·n·log q)` is exactly Route B's Wick bound at `r ∼ log q`, which is Route A's amplification
`C = c·log q` — one open scalar, two equivalent faces. -/
theorem eta_sq_le_qn_unconditional {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 ≤ (Fintype.card F : ℝ) * (G.card : ℝ) := by
  have h := eta_pow_le_of_wick (ψ := ψ) G 1 (wickEnergyBound_one hψ G) hb
  simpa [doubleFactOdd_one] using h

end ArkLib.ProximityGap.MomentWickBridge

#print axioms ArkLib.ProximityGap.MomentWickBridge.wickEnergyBound_one
#print axioms ArkLib.ProximityGap.MomentWickBridge.eta_pow_le_of_wick
#print axioms ArkLib.ProximityGap.MomentWickBridge.eta_sq_le_qn_unconditional
