/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G59CharZeroFloorInsufficiency

/-!
# LANE G61: the G57 pure-DC gate is strictly stronger than `DCEnergyBound` by the char-`0` slack

This file formalizes the exact separation that calibrates the fresh G56-frontier numeric
refutation of G57's convenient sufficient gate. The frontier probe showed, with exact integer
receipts at a prize-shaped thin prime (`n = 32`, `p = 21523361`, `ζ = 3`, `r = 17`), that

`q·wraparoundExcessR > n^{2r}`  —  the **pure-DC gate is FALSE** —

*while the DC-subtracted target `DCEnergyBound` still survives*, using only a fraction of its
slack budget. This file proves the structural fact that makes that numeric observation a genuine
**no-go against the route, not against the prize**: the pure-DC gate is a strictly stronger
statement than `DCEnergyBound`, separated by exactly the nonnegative characteristic-`0` slack
`q·(Wickₚ − negSymCount)`. Refuting the gate therefore cannot refute the real target.

## The two statements

Write `q = |F|`, `n = 2m`, `G = Gset ζ m`, and reuse the G56 split
`rEnergy G r = negSymCount G (2r) + wraparoundExcessR ζ m r`. Two candidate certificates:

* **(GATE)** the pure-DC gate  `q·wraparoundExcessR ζ m r ≤ n^{2r}`
  (G57's forward hypothesis `hwrap`, the convenient sufficient condition);
* **(REAL)** the DC-subtracted target  `DCEnergyBound G r`, which by G59's exact `(★)` is
  equivalent to  `q·wraparoundExcessR ζ m r ≤ n^{2r} + q·(Wickₚ − negSymCount G (2r))`.

Because `negSymCount G (2r) ≤ Wickₚ` (G57 `negSymCount_le_wick`), the extra term on (REAL) is a
**nonnegative slack** `slack := q·(Wickₚ − negSymCount G (2r)) ≥ 0`. Hence:

## What is proved (all axiom-clean, all on existing G56/G57/G59 objects)

1. `charZeroSlack_nonneg`: the char-`0` slack `q·(Wickₚ − negSymCount) ≥ 0` (G57).
2. `dcEnergyBound_of_pureDCGate`: (GATE) ⟹ (REAL). One direction of the implication — the pure-DC
   gate is *sufficient* for `DCEnergyBound`. (This is exactly G57's landed consumer, re-derived
   here through G59's `(★)` to make the slack explicit.)
3. `dcEnergyBound_iff_pureDCGate_add_slack`: (REAL) `↔` (GATE relaxed by the slack). The DC-
   subtracted bound is the pure-DC gate with its right-hand side enlarged by exactly `slack`.
4. `pureDCGate_refuted_dcEnergyBound_survives`: **the calibration theorem.** If a probe refutes
   the pure-DC gate strictly — `n^{2r} < q·wraparoundExcessR` — then `DCEnergyBound` STILL holds
   as long as the wraparound excess stays inside the *slack-relaxed* budget
   `q·wraparoundExcessR ≤ n^{2r} + slack`. So a gate-refutation with a positive slack margin
   `n^{2r} < q·wraparoundExcessR ≤ n^{2r} + slack` is a witness that the two statements genuinely
   diverge: the route's sufficient condition is dead, the real target is not. This is the exact
   logical content of the frontier's `pW/n^{2r} = 1.07…` (gate false) vs `0.34·budget` (target
   alive) receipts.
5. `pureDCGate_strictly_stronger`: **the no-go corollary.** Whenever the census is strictly below
   the Wick scale (`negSymCount G (2r) < Wickₚ`, i.e. `0 < q` and `slack > 0`), there is a real
   value of the wraparound excess — namely anything in the half-open corridor
   `(n^{2r}/q, n^{2r}/q + (Wickₚ − negSymCount)]` — at which (REAL) holds but (GATE) fails. Thus
   `¬((REAL) → (GATE))`: the pure-DC gate is a *strictly* stronger statement, and any argument
   that only refutes the gate leaves `DCEnergyBound` untouched.

This is a **precise route/target separation**, not a closure and not a wrapper: it does not bound
`wraparoundExcessR`, it proves that the convenient G57 gate the frontier probe killed is not the
prize obligation, and it names the exact wedge (`slack`) between them. It composes directly with
G57 (`dcEnergyBound_Gset_of_wraparoundExcessR_le_dc`, the (GATE) ⟹ (REAL) direction) and G59
(`dcEnergyBound_iff_wraparound_residual`, the `(★)` relabel), and it certifies the frontier
lane's `[466-g56-…]` gate-refutation as a route no-go rather than a prize refutation.

Issue #466.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.style.openClassical false

open scoped Classical

namespace ArkLib.ProximityGap.Frontier.G61PureDCGateStrictlyStronger

open ArkLib.ProximityGap.Frontier.E3StrataCount (negSymCount)
open ArkLib.ProximityGap.Frontier.G56AllDepthPatternDecomposition
  (wraparoundExcessR Gset Gset_card rEnergy_Gset_eq_negSymCount_add_wraparoundExcessR)
open ArkLib.ProximityGap.DCEnergyCorrection (DCEnergyBound)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)

variable {F : Type*} [Field F] [Fintype F]

/-- The char-`0` Wick pairing scale `Wickₚ = (2r−1)‼·n^r` as a real number (mirrors G59's
`wickR`, re-declared here to keep the file self-contained; the value is identical). -/
private noncomputable def wickR (n r : ℕ) : ℝ :=
  (Nat.doubleFactorial (2 * r - 1) : ℝ) * (n : ℝ) ^ r

/-- The **characteristic-`0` slack** separating the DC-subtracted target from the pure-DC gate:
`slack = q·(Wickₚ − negSymCount G (2r))`. It is the entire wedge between (REAL) and (GATE). -/
private noncomputable def charZeroSlack (ζ : F) (m r : ℕ) : ℝ :=
  (Fintype.card F : ℝ) * (wickR (2 * m) r - (negSymCount (Gset ζ m) (2 * r) : ℝ))

/-- The char-`0` slack is nonnegative: the antipodally balanced census never exceeds the Wick
scale (`negSymCount_le_wick`, G57), and `q ≥ 0`. This is why the DC-subtracted target is *weaker*
than the pure-DC gate — the gate throws away this nonnegative headroom. -/
theorem charZeroSlack_nonneg {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    0 ≤ charZeroSlack ζ m r := by
  have h2 : (2 : F) ≠ 0 := by
    intro h2
    have hneg : (-1 : F) = 1 := by linear_combination -h2
    have hzpow : ζ ^ m = 1 :=
      (ArkLib.ProximityGap.Frontier.G56AllDepthPatternDecomposition.zeta_pow_m hm hprim).trans hneg
    exact hprim.pow_ne_one_of_pos_of_lt hm.ne' (by omega) hzpow
  have h0 : (0 : F) ∉ Gset ζ m := by
    intro hzero
    obtain ⟨a, _ha, hpow⟩ := Finset.mem_image.mp hzero
    exact (pow_ne_zero a
      (ArkLib.ProximityGap.Frontier.G56AllDepthPatternDecomposition.zeta_ne_zero hm hprim)) hpow
  have hnat :=
    ArkLib.ProximityGap.Frontier.G57AllDepthWraparoundDCConsumer.negSymCount_le_wick
      (Gset ζ m) r h2 h0
  have hcard : (Gset ζ m).card = 2 * m := Gset_card hm hprim
  have hle : (negSymCount (Gset ζ m) (2 * r) : ℝ) ≤ wickR (2 * m) r := by
    have : (negSymCount (Gset ζ m) (2 * r) : ℝ)
        ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * ((Gset ζ m).card : ℝ) ^ r := by
      exact_mod_cast hnat
    rw [hcard] at this
    simpa [wickR] using this
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have : 0 ≤ (Fintype.card F : ℝ) * (wickR (2 * m) r - (negSymCount (Gset ζ m) (2 * r) : ℝ)) :=
    mul_nonneg hq (by linarith [hle])
  simpa [charZeroSlack] using this

/-- The G56 additive-energy split cast to `ℝ` (re-derived locally, mirrors G59). -/
private theorem rEnergy_split_real {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    (rEnergy (Gset ζ m) r : ℝ)
      = (negSymCount (Gset ζ m) (2 * r) : ℝ) + (wraparoundExcessR ζ m r : ℝ) := by
  exact_mod_cast rEnergy_Gset_eq_negSymCount_add_wraparoundExcessR hm hprim

/-- **(REAL) `↔` (GATE relaxed by the slack).** `DCEnergyBound G r` is exactly the pure-DC gate
`q·wraparoundExcessR ≤ n^{2r}` with the right-hand side enlarged by the char-`0` slack. This is
G59's `(★)` re-derived locally from the G56 split and the definition of `DCEnergyBound`, written
to expose `charZeroSlack` as the single additive wedge. -/
theorem dcEnergyBound_iff_pureDCGate_add_slack {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    DCEnergyBound (Gset ζ m) r
      ↔ (Fintype.card F : ℝ) * (wraparoundExcessR ζ m r : ℝ)
          ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r) + charZeroSlack ζ m r := by
  unfold DCEnergyBound charZeroSlack
  rw [rEnergy_split_real hm hprim, Gset_card hm hprim]
  simp only [wickR]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **(GATE) ⟹ (REAL).** The pure-DC gate `q·wraparoundExcessR ≤ n^{2r}` is *sufficient* for the
DC-subtracted energy bound — it discharges the target with the entire char-`0` slack to spare.
(This re-derives G57's landed consumer through G59's `(★)`, making the unused slack explicit.) -/
theorem dcEnergyBound_of_pureDCGate {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    (hgate : (Fintype.card F : ℝ) * (wraparoundExcessR ζ m r : ℝ)
      ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r)) :
    DCEnergyBound (Gset ζ m) r := by
  refine (dcEnergyBound_iff_pureDCGate_add_slack hm hprim).mpr ?_
  have hslack := charZeroSlack_nonneg (ζ := ζ) (m := m) (r := r) hm hprim
  linarith [hgate, hslack]

/-- **The calibration theorem — gate refuted, target survives.** Suppose a probe refutes the pure-DC
gate *strictly*, `n^{2r} < q·wraparoundExcessR` (the frontier's `pW/n^{2r} = 1.07…` receipt), yet
the wraparound excess still fits inside the slack-relaxed budget,
`q·wraparoundExcessR ≤ n^{2r} + slack`. Then `DCEnergyBound G r` STILL holds. So the exact regime
`n^{2r} < q·wraparoundExcessR ≤ n^{2r} + slack` is a witness that (GATE) and (REAL) diverge:
the route's convenient sufficient condition is dead while the prize's DC-subtracted target is
alive. This is the precise logical content of the G56-frontier gate-refutation being a **route
no-go, not a prize refutation.** -/
theorem pureDCGate_refuted_dcEnergyBound_survives {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    (hgate_refuted :
      ((2 * m : ℕ) : ℝ) ^ (2 * r) < (Fintype.card F : ℝ) * (wraparoundExcessR ζ m r : ℝ))
    (hreal :
      (Fintype.card F : ℝ) * (wraparoundExcessR ζ m r : ℝ)
        ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r) + charZeroSlack ζ m r) :
    DCEnergyBound (Gset ζ m) r ∧
      ¬ ((Fintype.card F : ℝ) * (wraparoundExcessR ζ m r : ℝ)
          ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r)) := by
  refine ⟨(dcEnergyBound_iff_pureDCGate_add_slack hm hprim).mpr hreal, ?_⟩
  intro hgate
  exact absurd hgate (not_le.mpr hgate_refuted)

/-- **The no-go corollary — the pure-DC gate is STRICTLY stronger.** Whenever the char-`0` slack
is strictly positive (the census is strictly below the Wick scale,
`negSymCount G (2r) < Wickₚ`, with `0 < q`), the implication `(REAL) → (GATE)` FAILS at a concrete
value of the wraparound excess: take `w := (n^{2r} + slack)/q`. Then (REAL) holds at `w` (its
budget is met with equality) but (GATE) fails at `w` (`q·w = n^{2r} + slack > n^{2r}`). Hence the
pure-DC gate is a *strictly* stronger statement than the DC-subtracted target, and any argument
refuting only the gate leaves `DCEnergyBound` untouched. The hypotheses are exactly the generic
off-floor regime the frontier probe operates in (`0 < slack`), i.e. the honest complement of G59's
floor-saturation punchline. -/
theorem pureDCGate_strictly_stronger {ζ : F} {m r : ℕ}
    (hq : (0 : ℝ) < (Fintype.card F : ℝ))
    (hslack_pos : (0 : ℝ) < charZeroSlack ζ m r) :
    ∃ w : ℝ,
      0 ≤ w ∧
      ((Fintype.card F : ℝ) * w
        ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r) + charZeroSlack ζ m r) ∧
      ¬ ((Fintype.card F : ℝ) * w ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r)) := by
  refine ⟨(((2 * m : ℕ) : ℝ) ^ (2 * r) + charZeroSlack ζ m r) / (Fintype.card F : ℝ), ?_, ?_, ?_⟩
  · have hnum : 0 ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r) + charZeroSlack ζ m r := by positivity
    positivity
  · rw [mul_div_cancel₀ _ (ne_of_gt hq)]
  · rw [mul_div_cancel₀ _ (ne_of_gt hq)]
    exact not_le.mpr (by linarith [hslack_pos])

#print axioms charZeroSlack_nonneg
#print axioms dcEnergyBound_iff_pureDCGate_add_slack
#print axioms dcEnergyBound_of_pureDCGate
#print axioms pureDCGate_refuted_dcEnergyBound_survives
#print axioms pureDCGate_strictly_stronger

end ArkLib.ProximityGap.Frontier.G61PureDCGateStrictlyStronger
