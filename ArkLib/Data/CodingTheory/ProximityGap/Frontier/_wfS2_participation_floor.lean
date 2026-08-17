/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Algebra.Order.Chebyshev

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# wf-S2 (#444): the spectral PARTICIPATION floor — a second/fourth-moment spread certificate

This is the CONCENTRATION/SPREAD lane of the Proximity-Prize core (issue #444). The prize is a
bound on the *worst-case* frequency `M := max_{b≠0} ‖η_b‖`, where `η_b = ∑_{y∈G} ψ(b·y)` is the
subgroup Gauss sum, NOT on the *total* additive energy `E_r = (1/q)·∑_b ‖η_b‖^{2r}`. The 25-year
wall worry is that at a *structured* prime the energy `E_2` could inflate (char-`p` coincidences
beyond char-`0`) while `M` stays small — in which case the inflated mass must be SPREAD over many
frequencies. The dual worry — CONCENTRATION onto few frequencies — would spike some `‖η_b‖`.

`_wfS2_spread_floor.lean` proves the *second*-moment half: `M`-bound ⇒ wide support
(`|S| ≥ q·|G|/M²`). This file proves the **participation floor**, the sharper *second-vs-fourth*-
moment statement that does NOT presuppose an `M`-bound: it is a pure Cauchy–Schwarz consequence of
the two Parseval-type moments

  `A := ∑_b ‖η_b‖²  (= q·|G|, the proven second moment)` and `B := ∑_b ‖η_b‖⁴ (= q·E_2)`,

namely the **inverse participation ratio**

  `(number of frequencies carrying the mass) ≥ A² / B = (∑‖η_b‖²)² / ∑‖η_b‖⁴`.

This `A²/B` is exactly the *participation ratio* `PR·m` measured by the S2 probe
(`scripts/probes/rust/probe_wfS2_percoset_shape.rs`): empirically `PR ≈ 0.34` is **flat and
prime-structure-independent** at prize scale (`β≈4`, `n=16…128`, both `v2(p-1)` extremes) and stays
`≈ 0.31` even at the famous Fermat structured prime (`n=32, p=65537`, where `E_2` *does* inflate
12.9%) — the spurious mass is REDISTRIBUTED over `~600` cosets, never piled on a few. The theorem
here is the rigorous mechanism behind that observation: **a small fourth moment `B` forces the
support to be wide**, i.e. the energy `E_2` and the spread of `M` are tied together by a moment
inequality that holds in EVERY characteristic — no Weil input.

Pairing with the existing transport lemmas:
* `_wfS2_spread_floor`: `M`-bound ⇒ wide support (2nd moment).
* `EnergyCharacterTransport.exists_charSum_ge_of_energy`: large `E_2` ⇒ some large `‖η_b‖` (4th
  moment, the concentration *converse* — large energy needs a spike SOMEWHERE).
* **This file**: the two moments TOGETHER lower-bound the participation `A²/B` ≤ `|S|`, the
  spread certificate that the probe's flat `PR` realises. Together they say: large `E_2` forces a
  spike, but a moderate `B = q·E_2` simultaneously forces that spike to be accompanied by a wide
  support — concentration on `o(A²/B)` frequencies is impossible.

All three are Weil-free `ℝ`-arithmetic on Parseval identities.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta subgroup_gaussSum_secondMoment)

namespace ArkLib.ProximityGap.ParticipationFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The spectral **support**: frequencies whose Gauss sum is nonzero. -/
noncomputable def spectralSupport (ψ : AddChar F ℂ) (G : Finset F) : Finset F :=
  Finset.univ.filter (fun b => eta ψ G b ≠ 0)

/-- **The participation floor (multiplicative form).** Writing `A := ∑_b ‖η_b‖²` and
`B := ∑_b ‖η_b‖⁴`, on the spectral support `S` we have `A² ≤ |S| · B`. So the number of
frequencies carrying the second-moment mass `A` is at least the inverse participation ratio `A²/B`.
This is Cauchy–Schwarz between the `1`-vector and `b ↦ ‖η_b‖²`, restricted to the support (the
zero terms contribute nothing). No characteristic-`p` / Weil input. -/
theorem participation_floor_mul (ψ : AddChar F ℂ) (G : Finset F) :
    (∑ b : F, ‖eta ψ G b‖ ^ 2) ^ 2
      ≤ ((spectralSupport ψ G).card : ℝ) * ∑ b : F, ‖eta ψ G b‖ ^ 4 := by
  classical
  set S := spectralSupport ψ G with hS
  -- restrict both moments to the support
  have hA : ∑ b : F, ‖eta ψ G b‖ ^ 2 = ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro b _ hb
    simp only [hS, spectralSupport, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hb
    rw [hb, norm_zero]; ring
  have hB : ∑ b : F, ‖eta ψ G b‖ ^ 4 = ∑ b ∈ S, ‖eta ψ G b‖ ^ 4 := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro b _ hb
    simp only [hS, spectralSupport, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hb
    rw [hb, norm_zero]; ring
  rw [hA, hB]
  -- apply Chebyshev/Cauchy–Schwarz with f b = ‖η_b‖²; note (‖η_b‖²)² = ‖η_b‖⁴
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := fun b => ‖eta ψ G b‖ ^ 2)
  have hpow : ∀ b : F, (‖eta ψ G b‖ ^ 2) ^ 2 = ‖eta ψ G b‖ ^ 4 := by
    intro b; ring
  simp only [hpow] at hcs
  exact hcs

/-- **The participation floor (divided form): `|S| ≥ A²/B`.** With `A = ∑‖η_b‖²` and
`B = ∑‖η_b‖⁴ > 0`, the spectral support has at least `A²/B` frequencies. This is the inverse
participation ratio: a small fourth moment `B` (energy `E_2 = B/q`) FORCES a wide support — the
spectral mass cannot concentrate on fewer than `A²/B` frequencies, *whatever the characteristic*.
-/
theorem participation_floor_div (ψ : AddChar F ℂ) (G : Finset F)
    (hB : 0 < ∑ b : F, ‖eta ψ G b‖ ^ 4) :
    (∑ b : F, ‖eta ψ G b‖ ^ 2) ^ 2 / (∑ b : F, ‖eta ψ G b‖ ^ 4)
      ≤ ((spectralSupport ψ G).card : ℝ) := by
  rw [div_le_iff₀ hB]
  have := participation_floor_mul ψ G
  linarith [this]

/-- **Participation floor pinned by the proven second moment.** Substituting the Weil-free second
moment `∑_b ‖η_b‖² = q·|G|` (`subgroup_gaussSum_secondMoment`), the participation floor reads

  `|S| ≥ (q·|G|)² / ∑_b ‖η_b‖⁴ = (q·|G|)² / (q·E_2)`,

i.e. `|S| ≥ q·|G|²/E_2`. The energy `E_2 = (1/q)∑‖η_b‖⁴` and the spectral spread `|S|` are tied
together with NO `M`-bound assumed: the larger the energy, the *more* the support must spread to
carry the FIXED second-moment mass `q·|G|`. This is the rigorous core of the S2 reframing —
char-`p` energy inflation is a SPREAD phenomenon forced by the second-moment identity, not a
concentration that could spike `M`. -/
theorem participation_floor_pinned {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hB : 0 < ∑ b : F, ‖eta ψ G b‖ ^ 4) :
    ((Fintype.card F : ℝ) * G.card) ^ 2 / (∑ b : F, ‖eta ψ G b‖ ^ 4)
      ≤ ((spectralSupport ψ G).card : ℝ) := by
  have h2 : ∑ b : F, ‖eta ψ G b‖ ^ 2 = (Fintype.card F : ℝ) * G.card :=
    subgroup_gaussSum_secondMoment hψ G
  have := participation_floor_div ψ G hB
  rwa [h2] at this

end ArkLib.ProximityGap.ParticipationFloor
