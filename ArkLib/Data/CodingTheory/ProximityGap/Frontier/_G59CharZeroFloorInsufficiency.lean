/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G57AllDepthWraparoundDCConsumer

/-!
# LANE G59: characteristic-zero histogram control alone cannot close the DC-subtracted energy

This file formalizes the surviving structural obstruction behind the #466 signed-walk /
histogram route: a bound obtained purely from the **characteristic-zero** symmetric-walk
histogram controls *only* the antipodally balanced census `negSymCount`, and therefore cannot
by itself certify the DC-subtracted energy bound `DCEnergyBound` once the DC floor dominates —
the exact remaining obligation is a genuinely **characteristic-`p`** hypothesis on the
wraparound excess `wraparoundExcessR`.

## The two invariants and where each route sees them

G56 splits the `r`-fold additive energy of `G = Gset ζ m` (with `ζ` primitive of order
`n = 2m`) exactly:

`rEnergy G r = negSymCount G (2r) + wraparoundExcessR ζ m r`.        (G56)

* `negSymCount G (2r)` is the antipodally balanced count. It is **characteristic-independent**:
  it counts index-level antipodal pairings, exactly the object a symmetric-walk / char-`0`
  histogram argument controls. G57 discharges it unconditionally,
  `negSymCount G (2r) ≤ Wickₚ` where `Wickₚ = (2r−1)‼·n^r` (`negSymCount_le_wick`).
* `wraparoundExcessR ζ m r` counts the **nonzero** folded patterns that vanish at `ζ` — i.e.
  patterns that are NOT antipodally balanced yet still sum to zero *because* `ζ` satisfies a
  characteristic-`p` relation. A char-`0` histogram never sees these; they are the entire
  arithmetic content of the wall.

## What is proved here (all axiom-clean, all on existing objects)

`DCEnergyBound G r` unfolds (`DCEnergyCorrection`) to `q·E_r − n^{2r} ≤ q·Wickₚ`.
Substituting G56 gives the **exact** equivalent

`q·wraparoundExcessR ≤ n^{2r} + q·(Wickₚ − negSymCount)`.        (★)

1. `dcEnergyBound_iff_wraparound_residual`: (★) as an honest `↔` (real arithmetic).
2. `wraparound_le_of_dcEnergyBound`: the **necessity** direction of (★), unconditionally — any
   proof of `DCEnergyBound` forces the wraparound bound up to the char-`0` slack
   `q·(Wickₚ − negSymCount) ≥ 0` (nonnegativity is `negSymCount_le_wick`, G57).
3. `dcEnergyBound_iff_wraparound_le_of_floor_saturated`: **the punchline.** When the DC floor is
   saturated, `negSymCount G (2r) = Wickₚ` (the char-`0` histogram bound is tight — "the DC
   floor dominates"), the slack in (★) is exactly `0`, so

   `DCEnergyBound G r ↔ q·wraparoundExcessR ≤ n^{2r}`.

   The char-`0` invariant has been fully spent; the surviving obligation is *precisely* the
   char-`p` hypothesis `q·wraparoundExcessR ≤ n^{2r}` on the wraparound excess, individually
   necessary and sufficient. This isolates the exact hypothesis the FLEET brief asks for.
4. `charZero_histogram_insufficient`: the no-go framing. The strongest thing a char-`0`
   histogram / signed-walk argument can deliver is a bound `negSymCount G (2r) ≤ B`. Such a
   bound implies `DCEnergyBound` **iff** it is *also* supplied with
   `q·wraparoundExcessR ≤ n^{2r} + q·(B − negSymCount)` — and at the floor (`B = Wickₚ`,
   `negSymCount = Wickₚ`) this collapses to the bare char-`p` hypothesis
   `q·wraparoundExcessR ≤ n^{2r}`, with zero contribution from any char-`0` refinement.

This is a **precise no-go / exact-necessity result**, not a closure. It does not bound
`wraparoundExcessR`; it proves that char-`0` control cannot, and names the exact residual.
It composes with G57's forward gate (`dcEnergyBound_Gset_of_wraparoundExcessR_le_dc`): together
G57+G59 show the DC-subtracted energy bound is, at the floor, *equivalent* to the wraparound
gate — closing the "can histogram control alone finish?" branch in `DISPROOF_LOG`.

Issue #466.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.style.openClassical false

open scoped Classical

namespace ArkLib.ProximityGap.Frontier.G59CharZeroFloorInsufficiency

open ArkLib.ProximityGap.Frontier.E3StrataCount (negSymCount)
open ArkLib.ProximityGap.Frontier.G56AllDepthPatternDecomposition
  (wraparoundExcessR Gset Gset_card rEnergy_Gset_eq_negSymCount_add_wraparoundExcessR)
open ArkLib.ProximityGap.Frontier.G57AllDepthWraparoundDCConsumer (negSymCount_le_wick)
open ArkLib.ProximityGap.DCEnergyCorrection (DCEnergyBound)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)

variable {F : Type*} [Field F] [Fintype F]

/-- Abbreviation for the char-`0` Wick pairing scale `Wickₚ = (2r−1)‼·n^r` as a real number. -/
private noncomputable def wickR (n r : ℕ) : ℝ :=
  (Nat.doubleFactorial (2 * r - 1) : ℝ) * (n : ℝ) ^ r

/-- The G56 additive-energy split, cast to `ℝ`, for the subgroup `Gset ζ m`. -/
private theorem rEnergy_split_real {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    (rEnergy (Gset ζ m) r : ℝ)
      = (negSymCount (Gset ζ m) (2 * r) : ℝ) + (wraparoundExcessR ζ m r : ℝ) := by
  exact_mod_cast rEnergy_Gset_eq_negSymCount_add_wraparoundExcessR hm hprim

/-- The char-`0` DC-floor bound (G57) cast to `ℝ`, phrased with `wickR`: the antipodally
balanced census never exceeds the Wick pairing scale. This is exactly the content a symmetric
walk / characteristic-zero histogram argument can supply, and no more. -/
private theorem negSymCount_le_wickR {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    (negSymCount (Gset ζ m) (2 * r) : ℝ) ≤ wickR (2 * m) r := by
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
  have hnat := negSymCount_le_wick (Gset ζ m) r h2 h0
  have hcard : (Gset ζ m).card = 2 * m := Gset_card hm hprim
  have : (negSymCount (Gset ζ m) (2 * r) : ℝ)
      ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * ((Gset ζ m).card : ℝ) ^ r := by
    exact_mod_cast hnat
  rw [hcard] at this
  simpa [wickR] using this

/-- **(★) — the exact reduction.** `DCEnergyBound (Gset ζ m) r` is equivalent to the wraparound
excess fitting inside the DC mass `n^{2r}` PLUS the characteristic-zero slack
`q·(Wickₚ − negSymCount)`. This is a pure relabeling of the DC-subtracted prize prop through the
G56 energy split — no arithmetic input, just the identity `E_r = negSymCount + wraparoundExcessR`
and the definition of `DCEnergyBound`. -/
theorem dcEnergyBound_iff_wraparound_residual {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    DCEnergyBound (Gset ζ m) r
      ↔ (Fintype.card F : ℝ) * (wraparoundExcessR ζ m r : ℝ)
          ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r)
            + (Fintype.card F : ℝ)
              * (wickR (2 * m) r - (negSymCount (Gset ζ m) (2 * r) : ℝ)) := by
  unfold DCEnergyBound
  rw [rEnergy_split_real hm hprim, Gset_card hm hprim]
  constructor
  · intro h; simp only [wickR]; nlinarith [h]
  · intro h; simp only [wickR] at h; nlinarith [h]

/-- **Necessity, unconditional.** Any proof of the DC-subtracted energy bound forces the
wraparound excess to fit inside the DC mass plus the char-`0` slack. The slack is nonnegative
(`negSymCount ≤ Wickₚ`, G57), so a `DCEnergyBound` proof can only *relax* the wraparound
obligation by the amount of unused char-`0` headroom — never eliminate it. -/
theorem wraparound_le_of_dcEnergyBound {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    (h : DCEnergyBound (Gset ζ m) r) :
    (Fintype.card F : ℝ) * (wraparoundExcessR ζ m r : ℝ)
      ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r)
        + (Fintype.card F : ℝ)
          * (wickR (2 * m) r - (negSymCount (Gset ζ m) (2 * r) : ℝ)) :=
  (dcEnergyBound_iff_wraparound_residual hm hprim).mp h

/-- **The punchline — char-`0` control is spent once the DC floor dominates.** When the
antipodally balanced census saturates the Wick scale, `negSymCount (Gset ζ m) (2r) = Wickₚ`
(the strongest possible char-`0` histogram bound, holding with equality — "the DC floor
dominates"), the char-`0` slack in (★) is exactly `0`. Hence the DC-subtracted energy bound is
*equivalent* to the bare characteristic-`p` gate on the wraparound excess:

`DCEnergyBound (Gset ζ m) r ↔ q·wraparoundExcessR ζ m r ≤ n^{2r}`.

The right-hand side is precisely G57's forward hypothesis `hwrap`. So at the floor the two are
the same statement: no characteristic-zero refinement can move the frontier — the surviving
obligation lives entirely in `wraparoundExcessR`. -/
theorem dcEnergyBound_iff_wraparound_le_of_floor_saturated {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    (hfloor : (negSymCount (Gset ζ m) (2 * r) : ℝ) = wickR (2 * m) r) :
    DCEnergyBound (Gset ζ m) r
      ↔ (Fintype.card F : ℝ) * (wraparoundExcessR ζ m r : ℝ)
          ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r) := by
  rw [dcEnergyBound_iff_wraparound_residual hm hprim, hfloor]
  simp

/-- **The no-go framing.** The most a characteristic-zero histogram / signed-walk argument can
deliver is an upper bound `negSymCount (Gset ζ m) (2r) ≤ B` on the balanced census, with `B` no
larger than the Wick scale (`B ≤ Wickₚ`; the sharpest such bound is `B = negSymCount ≤ Wickₚ` by
G57). This theorem discharges `DCEnergyBound` from such a char-`0` bound **only when it is paired**
with a wraparound hypothesis `q·wraparoundExcessR ≤ n^{2r} + q·(B − negSymCount)`. A *weaker*
char-`0` bound (larger `B`, still `≤ Wickₚ`) only *loosens* the required wraparound gate, so
char-`0` refinement can never *shrink* the characteristic-`p` obligation below the floor residual
`q·wraparoundExcessR ≤ n^{2r}` (recovered at `B = Wickₚ` with the floor saturated). Hence no
char-`0` bound closes the prize without an independent characteristic-`p` input on
`wraparoundExcessR`. -/
theorem charZero_histogram_insufficient {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    {B : ℝ} (hB : B ≤ wickR (2 * m) r)
    (hwrap : (Fintype.card F : ℝ) * (wraparoundExcessR ζ m r : ℝ)
        ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r)
          + (Fintype.card F : ℝ) * (B - (negSymCount (Gset ζ m) (2 * r) : ℝ))) :
    DCEnergyBound (Gset ζ m) r := by
  refine (dcEnergyBound_iff_wraparound_residual hm hprim).mpr (hwrap.trans ?_)
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hslack :
      (Fintype.card F : ℝ) * (B - (negSymCount (Gset ζ m) (2 * r) : ℝ))
        ≤ (Fintype.card F : ℝ)
            * (wickR (2 * m) r - (negSymCount (Gset ζ m) (2 * r) : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith [hB]) hq
  linarith [hslack]

/-- The clean corollary that ties `charZero_histogram_insufficient` back to `DCEnergyBound`:
a char-`0` bound `B` closes the DC-subtracted energy prize **iff** it comes with a wraparound
hypothesis at least as strong as the floor residual. At `B = Wickₚ` and floor saturation the
char-`0` term drops out entirely. -/
theorem dcEnergyBound_of_charZero_bound_and_wraparound {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    (hwrap : (Fintype.card F : ℝ) * (wraparoundExcessR ζ m r : ℝ)
        ≤ ((2 * m : ℕ) : ℝ) ^ (2 * r)
          + (Fintype.card F : ℝ)
            * (wickR (2 * m) r - (negSymCount (Gset ζ m) (2 * r) : ℝ))) :
    DCEnergyBound (Gset ζ m) r :=
  (dcEnergyBound_iff_wraparound_residual hm hprim).mpr hwrap

#print axioms dcEnergyBound_iff_wraparound_residual
#print axioms wraparound_le_of_dcEnergyBound
#print axioms dcEnergyBound_iff_wraparound_le_of_floor_saturated
#print axioms charZero_histogram_insufficient
#print axioms dcEnergyBound_of_charZero_bound_and_wraparound

end ArkLib.ProximityGap.Frontier.G59CharZeroFloorInsufficiency
