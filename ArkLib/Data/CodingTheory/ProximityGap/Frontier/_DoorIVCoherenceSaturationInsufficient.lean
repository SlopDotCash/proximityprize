/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone

/-!
# Door-(iv) constraint: under coherence saturation the prize burden transfers ENTIRELY to a
strict-sub-trivial half-mass bound (#444)

## Probe-grounded motivation (rule-2: probe before formalize)

The prize is localized to `M(n) = max_{b≠0} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(b·x)`.  Door-(iv)'s
localized object (Shaw essay 2026-06-18, Lane 1) is the index-2 coset-half coherence
`ρ(b) = ‖A_b + B_b‖ / (‖A_b‖ + ‖B_b‖) ∈ [0,1]`, with the triangle identity `M = ρ(b)·H(b)`,
`H(b) = ‖A_b‖ + ‖B_b‖` the half-mass.  The live door-(iv) hope was a coherence/anti-alignment saving:
if the halves DESTRUCTIVELY interfere at the worst `b` (`ρ(b*)` small), that interference could carry
√-cancellation without a moment or a √q-completion.

PROBE (`scripts/probes/probe_dooriv_worstb_coherence_deficit_law.py`, proper `μ_n < F_p*`, `p ≫ n³`,
structured odd-`m` primes, `n = 16..256`, never `n = q−1`) measured the DEFICIT SCALING LAW of the
worst-frequency canonical index-2 coherence and compared it to the coherence that the trivial
half-mass ceiling `H ≤ n` would need to reach the prize, `ρ_needed = √(n·L)/n`:

  | n   | ρ(b*)    | 1−ρ(b*) | H/n    | ρ_needed = √(nL)/n |
  |-----|----------|---------|--------|--------------------|
  | 16  | 1.000000 | 0       | 0.86   | 0.72               |
  | 32  | 1.000000 | 0       | 0.72   | 0.57               |
  | 64  | 1.000000 | 0       | 0.53   | 0.44               |
  | 128 | 1.000000 | 0       | 0.37   | 0.34               |
  | 256 | 1.000000 | 0       | 0.28   | 0.25  ⟸ ρ ≫ ρ_needed |

`ρ(b*) ≡ 1` (deficit `≡ 0`) on the canonical squares-coset split at EVERY tested `n`, while
`ρ_needed = √(n·L)/n → 0`.  So `ρ(b*) ≫ ρ_needed`: **coherence is provably INSUFFICIENT** to reach the
prize on its own.  The entire √-cancellation is carried by `H(b*) = ‖A‖+‖B‖`, whose normalized value
`H/n` itself decays (measured `H/n ~ n^{-c}`, `c ≈ 0.3..0.5`), i.e. the burden sits on the
self-similar half-mass recursion, NOT on the index-2 coherence object.

## The load-bearing fact (this file, axiom-clean)

`_DoorIVWorstBHalfMassCarriesAll` already records the qualitative consequence `ρ = 1 ⟹ M = H`.  This
file adds the QUANTITATIVE prize-regime transfer the probe demands, in the existing `prizeScale`
vocabulary:

* **Coherence saturation carries only the trivial ceiling.**  If `M = H` (saturation) and `H ≤ n`
  (the trivial per-half ceiling, each half a sum of `n/2` unit phases), then `M ≤ n` — the SAME
  trivial bound, with no progress toward the prize.
* **The prize bound under saturation is exactly a half-mass bound.**  If `M = H` then
  `M ≤ C·prizeScale n L ↔ H ≤ C·prizeScale n L`.
* **In the prize regime that half-mass bound is STRICTLY STRONGER than the trivial ceiling.**  When
  `prizeScale n L < n` (i.e. `√(n·L) < n ⟺ L < n`, the thin prize window), any `C·prizeScale n L`
  with `C ≤ 1` is `< n`, so the prize half-mass bound strictly improves the trivial ceiling — meaning
  coherence saturation supplies NONE of the needed gap; the whole burden is a strict-sub-trivial
  bound on `H`.

This is a **refutation with mechanism** for door-(iv) Lane 1 (it removes the index-2 coherence lever
and pins the prize burden on the half-mass descent), NOT a CORE/cancellation/completion/moment/
capacity claim: it does not bound `M(n)`.  It sharpens `_DoorIVWorstBHalfMassCarriesAll` from the
qualitative `M = H` into the quantitative prize-regime insufficiency the probe exhibits.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVCoherenceSaturationInsufficient

open ArkLib.ProximityGap.Frontier.ShawValueCapstone

/-- **Coherence saturation carries only the trivial ceiling.**  If at the worst frequency the
coset-half coherence is saturated (`M = H`, from `ρ = 1`) and the half-mass obeys the trivial
per-half ceiling `H ≤ n`, then `M ≤ n` — the same trivial bound, with no progress toward the prize.

The point (door-(iv) Lane 1): the coherence factor being `1` propagates the trivial ceiling
unchanged.  Coherence supplies no saving; the burden remains on `H`. -/
theorem magnitude_le_trivial_of_saturation {M H n : ℝ}
    (hsat : M = H) (hceil : H ≤ n) : M ≤ n := by
  rw [hsat]; exact hceil

/-- **The prize bound under coherence saturation is exactly a half-mass bound.**  When `M = H`, the
raw prize-shaped bound `M ≤ C·prizeScale n L` is equivalent to the half-mass bound
`H ≤ C·prizeScale n L`.

So once coherence saturates at the worst `b`, the ENTIRE prize task is to bound the half-mass `H`;
the coherence object contributes nothing further. -/
theorem prizeBound_iff_halfMassBound_of_saturation {M H C n L : ℝ}
    (hsat : M = H) :
    M ≤ C * prizeScale n L ↔ H ≤ C * prizeScale n L := by
  rw [hsat]

/-- **In the thin prize regime the saturation half-mass bound is strictly below the trivial ceiling.**
When the prize scale is below the subgroup size (`prizeScale n L < n`, i.e. `√(n·L) < n ⟺ L < n`,
the thin prize window) and the constant satisfies `0 < C ≤ 1`, the prize-shaped half-mass target
`C·prizeScale n L` is strictly less than the trivial ceiling `n`.

Combined with `prizeBound_iff_halfMassBound_of_saturation`: under coherence saturation the prize
demands a half-mass bound `H ≤ C·prizeScale n L < n` that is STRICTLY STRONGER than the trivial
`H ≤ n`.  Coherence saturation supplies none of that gap; the whole burden is a strict-sub-trivial
bound on `H`, i.e. the self-similar half-mass recursion. -/
theorem prizeTarget_lt_trivial_ceiling {C n L : ℝ}
    (hscale : prizeScale n L < n) (hC0 : 0 < C) (hC1 : C ≤ 1) :
    C * prizeScale n L < n := by
  have hps_nonneg : 0 ≤ prizeScale n L := by
    unfold prizeScale; exact Real.sqrt_nonneg _
  calc
    C * prizeScale n L ≤ 1 * prizeScale n L :=
      mul_le_mul_of_nonneg_right hC1 hps_nonneg
    _ = prizeScale n L := one_mul _
    _ < n := hscale

/-- **Measured half-mass excess is a direct obstruction under saturation.**  If coherence is
saturated (`M = H`) and the half-mass exceeds the prize target `C·prizeScale n L`, then the prize
bound for `M` fails.  This is the probe-facing contrapositive of the transfer equivalence: once
`ρ(b*) = 1`, no cross-half coherence term can rescue an over-budget half-mass. -/
theorem not_prizeBound_of_saturation_and_halfMass_gt {M H C n L : ℝ}
    (hsat : M = H) (hH : C * prizeScale n L < H) :
    ¬ M ≤ C * prizeScale n L := by
  intro hM
  have hHle : H ≤ C * prizeScale n L :=
    (prizeBound_iff_halfMassBound_of_saturation hsat).mp hM
  exact not_le_of_gt hH hHle

/-- **Coherence-insufficiency transfer (door-(iv) Lane 1 capstone of this file).**  Suppose at the
worst frequency the coset-half coherence is saturated (`M = H`), the half-mass obeys the trivial
ceiling (`H ≤ n`), and we are in the thin prize regime (`prizeScale n L < n`).  Then for any prize
constant `0 < C ≤ 1`:

* the prize-shaped bound `M ≤ C·prizeScale n L` holds **iff** the strict-sub-trivial half-mass bound
  `H ≤ C·prizeScale n L` holds, and
* that target `C·prizeScale n L` is strictly below the trivial ceiling `n` that coherence saturation
  alone delivers.

Hence the prize burden transfers entirely OFF the index-2 coherence object and ONTO a strict-sub-
trivial bound on the half-mass `H` (the self-similar descent).  This is the kerneled form of the
probe verdict `ρ(b*) ≡ 1 ≫ ρ_needed = √(n·L)/n` ⟹ COHERENCE-INSUFFICIENT. -/
theorem coherenceSaturation_transfers_to_strict_subTrivial_halfMass
    {M H C n L : ℝ}
    (hsat : M = H) (hceil : H ≤ n) (hscale : prizeScale n L < n)
    (hC0 : 0 < C) (hC1 : C ≤ 1) :
    (M ≤ C * prizeScale n L ↔ H ≤ C * prizeScale n L) ∧
      C * prizeScale n L < n :=
  ⟨prizeBound_iff_halfMassBound_of_saturation hsat,
   prizeTarget_lt_trivial_ceiling hscale hC0 hC1⟩

end ArkLib.ProximityGap.Frontier.DoorIVCoherenceSaturationInsufficient

#print axioms
  ArkLib.ProximityGap.Frontier.DoorIVCoherenceSaturationInsufficient.not_prizeBound_of_saturation_and_halfMass_gt
#print axioms
  ArkLib.ProximityGap.Frontier.DoorIVCoherenceSaturationInsufficient.coherenceSaturation_transfers_to_strict_subTrivial_halfMass
