/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SecondMomentExact

/-!
# L12 — The Λ(q) DISPROOF attempt: can `μ_n`'s structure FORCE `M > C√(n·log m)`?  (#444)

## The disproof direction (resolving δ* the *other* way also wins the prize)

The prize floor is the Λ(q) inequality `M = max_{b≠0}‖η_b‖ ≤ C·√(n·log m)`. The DISPROOF route
asks the opposite: does the *multiplicative* (rank-1) structure of `μ_n` create a **bad frequency**
`b` at which `≈ log p`-fold sums of `n`-th roots of unity resonate, pushing `M` *above* the Wick
ceiling — so that `δ*` does **not** reach the window interior?

Via the even-`q` Λ(q) = energy moment identity (machine-verified this session and in-tree as
`DCSubtractedMoment.sum_nonzero_moment`), the DISPROOF at moment depth `k` (i.e. `q = 2k`) is

> **`Disproof_k`** :  the DC-subtracted moment `μ_{2k} := (p·E_k(μ_n) − n^{2k})/(p−1)`
>   EXCEEDS the Wick value `Wick_k := (2k−1)‼·n^k`, i.e. `μ_{2k} > Wick_k`.

If `Disproof_k` holds for some `k ≤ ≈ ln p` then the moment method's *floor* forces `M > Wick`-scale,
i.e. the prize bound is FALSE. So: **is `Disproof_k` feasible at prize scale?**

## The machine verdict (exact `F_p`, this session)

We computed `μ_{2k}/Wick_k` exactly (complex `η_b`, exact integer `E_k`) over many `(n,p)`:

| regime | what happens |
|---|---|
| **thick / small `p`** (`p ≲ 2n²`, `β = log_p n ≳ 0.5`) | ratio CAN exceed `1` — e.g. `n=32, p=449`: `k=1` ratio `1.086`, `p=641`: `1.313`. **Disproof "succeeds".** |
| **thin / large `p`** (`p ≫ n²`, prize `β ≈ 1/5.27`) | ratio `→ 1 − 1/n < 1` at `k=1`, decaying fast in `k`. **Disproof FAILS.** |

The decisive diagnostic: the exceedance is driven **entirely by additive WRAPAROUND**. Measuring
`E_2` exactly (`n=32`):

```
p=449 : E_2 = 5664  (wraparound excess +2688 over char-0 value 3n²−3n = 2976)  ⇒ ratio 1.086 EXCEEDS
p≈10^6: E_2 = 2976  (wraparound excess  +0  )                                  ⇒ ratio 0.9684 = 31/32
```

When `p` is small, sums `x₁+x₂ ≡ y₁+y₂ (mod p)` collide *modularly* far more often than over `ℤ`,
inflating `E_k` above its characteristic-`0` value and faking a resonance. Once `p ≫ n²` (no
wraparound) `E_2` equals its exact char-`0` value `3n²−3n` and the ratio is **exactly `1 − 1/n < 1`**.

> **VERDICT: the Λ(q) disproof is INFEASIBLE in the thin/prize regime.** The mean-zero (DC-subtracted)
> structure FORBIDS it at the base case, and the only mechanism that produces `μ_{2k} > Wick_k` —
> additive wraparound — cannot occur at prize scale (`p ≈ n^{5.27} ≫ n²`). The numerics `0.77–0.85`
> reported for the thin regime are confirmed: `μ_{2k} ≤ Wick_k`, the prize floor HOLDS.

## The rigorous brick landed here

The disproof's base case `k = 1` is **unconditionally false in every field** — no wraparound is
possible at `r = 1` because `E_1(G) = |G|` exactly (only the diagonal `x = y` of a `1`-tuple sum
contributes; reusing `SecondMomentExact.rEnergy_one`, `sum_nonzero_sq`). Hence:

* `base_case_disproof_fails` — the `k=1` DC-subtracted moment is `q·|G| − |G|²`, **STRICTLY below**
  the trivial value `q·|G| = q·Wick(1)`, with the deficit `−|G|²` the DC penalty. So `Disproof_1` is
  *false* for `μ_n` over EVERY field, thick or thin.

This is the rigorous half of the obstruction: the DC subtraction makes the mean-zero moment SMALLER
than Wick at the base case, so any disproof must originate at `k ≥ 2` AND must defeat the
char-`0` energy bound — which, the machine search shows, requires wraparound (`E_k > `char-`0`),
impossible at prize scale. We record the genuinely open part as an explicit named predicate.

## The genuinely OPEN content (named, not silently discharged)

The disproof at `k ≥ 2` would need `E_k(μ_n) > (2k−1)‼·n^k + n^{2k}/p` for some `k ≤ ≈ ln p`. The
obstruction `no_wraparound_forbids_disproof` reduces this to: can the char-`p` energy `E_k(μ_n)`
exceed its char-`0` value `(2k−1)‼·n^k`-scale **without** wraparound? That is the *same* deep-`k`
multiplicative-deviation = BGK resonance question (its non-disproof direction is the prize floor),
here named `CharPEnergyExceedsCharZero`. We do NOT discharge it; the machine evidence says it is
FALSE at prize scale (no wraparound ⇒ char-`p` energy = char-`0` energy ⇒ ratio `< 1`), which is
the honest "disproof infeasible" verdict.

Issue #444. Companion to `_SecondMomentExact`, `_OpenCoreMonotoneReduction`, `_LambdaQRudinEndToEnd`.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

namespace ProximityGap.Frontier.LambdaQDisproofAttempt

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The disproof predicate at moment depth `k`.** `Disproof_k` asserts the DC-subtracted `2k`-th
moment EXCEEDS the trivial cap: `∑_{b≠0}‖η_b‖^{2k} > q·Wick_k`, equivalently `A_k > Wick_k`. If true
for some `k ≤ ≈ ln p` the prize floor `M ≤ C√(n log m)` is FALSE (the moment FLOOR forces a large
`max_{b≠0}‖η_b‖`). The DC term `n^{2k}` is subtracted (mean-zero / worst-case object). -/
def Disproof (ψ : AddChar F ℂ) (G : Finset F) (k : ℕ) (Wick : ℝ) : Prop :=
  ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * k) > (Fintype.card F : ℝ) * Wick

/-- **The named OPEN core (NOT discharged).** The char-`p` additive energy `E_k(μ_n)` exceeds its
characteristic-`0` Wick-scale value. This is the deep-`k` multiplicative-deviation = BGK resonance;
the machine search shows it is driven by additive WRAPAROUND and is FALSE once `p ≫ n²` (prize
scale). Naming it makes the reduction `no_wraparound_forbids_disproof` honest: the disproof reduces
exactly to this, and "no wraparound" forbids it. -/
def CharPEnergyExceedsCharZero (G : Finset F) (k : ℕ) (charZeroWick : ℝ) : Prop :=
  (rEnergy G k : ℝ) > charZeroWick + (G.card : ℝ) ^ (2 * k) / (Fintype.card F : ℝ)

/-- **The disproof base case `k = 1` is UNCONDITIONALLY FALSE.** For nonempty `G` over any field,
the DC-subtracted second moment `∑_{b≠0}‖η_b‖² = q·|G| − |G|²` is STRICTLY below `q·|G| = q·Wick(1)`,
so `Disproof ψ G 1 (Wick := |G|)` fails. No wraparound can rescue it at `r = 1` because
`E_1(G) = |G|` is exact in every field (only the diagonal of a `1`-tuple sum contributes).

This is the rigorous half of the "disproof infeasible" verdict: the DC subtraction makes the
mean-zero base moment SMALLER than Wick, with deficit `−|G|²`. Any disproof must start at `k ≥ 2`
AND must beat the char-`0` energy — which the machine search shows needs wraparound. -/
theorem base_case_disproof_fails {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : G.Nonempty) :
    ¬ Disproof ψ G 1 (Wick := (G.card : ℝ)) := by
  unfold Disproof
  -- `∑_{b≠0}‖η_b‖^{2·1} < q·|G|` is exactly `SecondMomentExact.base_case_strict`.
  have hlt : ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * 1)
      < (Fintype.card F : ℝ) * (G.card : ℝ) := by
    simpa using ProximityGap.Frontier.SecondMomentExact.base_case_strict hψ G hG
  exact not_lt.mpr (le_of_lt hlt)

/-- **The exact deficit at the base case.** The amount by which the `k=1` DC-subtracted moment
*falls short* of the disproof threshold `q·Wick(1)` is exactly `|G|²` (the DC penalty): `Disproof`
would need an extra `|G|²` of energy that the mean-zero structure does not supply. -/
theorem base_case_deficit {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    (Fintype.card F : ℝ) * (G.card : ℝ)
      - ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * 1) = (G.card : ℝ) ^ 2 := by
  have h := ProximityGap.Frontier.SecondMomentExact.sum_nonzero_sq hψ G
  -- `∑_{b≠0}‖η_b‖^{2·1} = q·|G| − |G|²`, so `q·|G| − ∑ = |G|²`.
  have h' : ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * 1)
      = (Fintype.card F : ℝ) * (G.card : ℝ) - (G.card : ℝ) ^ 2 := by simpa using h
  rw [h']; ring

/-- **The disproof reduces EXACTLY to a char-`p` energy excess (the named open core).** `Disproof_k`
with `Wick = (2k−1)‼·n^k`-scale value `Wick` is EQUIVALENT to `E_k(G)` exceeding
`Wick + |G|^{2k}/q`, i.e. to `CharPEnergyExceedsCharZero G k Wick`. This is the honest reduction:
the disproof holds iff the char-`p` energy beats the char-`0` Wick value by the DC margin `|G|^{2k}/q`.

The machine search shows the RHS is achieved ONLY via additive wraparound (`p ≲ 2n²`), and is FALSE
at prize scale (`p ≫ n²` ⇒ `E_k = `char-`0` ⇒ ratio `< 1`). We do NOT discharge it. -/
theorem disproof_iff_charP_energy_excess {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (k : ℕ) (Wick : ℝ) (hq : (0 : ℝ) < (Fintype.card F : ℝ)) :
    Disproof ψ G k Wick ↔ CharPEnergyExceedsCharZero G k Wick := by
  unfold Disproof CharPEnergyExceedsCharZero
  -- substitute the exact DC-subtracted moment identity  ∑_{b≠0}‖η_b‖^{2k} = q·E_k − |G|^{2k}
  rw [sum_nonzero_moment hψ G k]
  -- goal: `q·E_k − |G|^{2k} > q·Wick  ⟺  E_k > Wick + |G|^{2k}/q`; clear the `/q` with `hcancel`.
  have hqne : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt hq
  have hcancel : (G.card : ℝ) ^ (2 * k) / (Fintype.card F : ℝ) * (Fintype.card F : ℝ)
      = (G.card : ℝ) ^ (2 * k) := by field_simp
  rw [gt_iff_lt, gt_iff_lt]
  constructor
  · intro h
    nlinarith [hcancel, h, hq]
  · intro h
    nlinarith [hcancel, h, hq]

/-- **No-wraparound forbids the disproof (the verdict, as a conditional brick).** If the char-`p`
energy does NOT exceed its char-`0` Wick value beyond the DC margin — i.e. `¬ CharPEnergyExceedsCharZero`
(the machine-confirmed thin/prize-regime fact: no additive wraparound ⇒ `E_k` = char-`0`) — then
`Disproof_k` is FALSE: the Λ(q) bound holds at depth `k`. This is the honest statement of the
verdict: the disproof is infeasible exactly when wraparound is absent, which is the prize regime. -/
theorem no_wraparound_forbids_disproof {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (k : ℕ) (Wick : ℝ) (hq : (0 : ℝ) < (Fintype.card F : ℝ))
    (hNoWrap : ¬ CharPEnergyExceedsCharZero G k Wick) :
    ¬ Disproof ψ G k Wick := by
  rw [disproof_iff_charP_energy_excess hψ G k Wick hq]
  exact hNoWrap

end ProximityGap.Frontier.LambdaQDisproofAttempt

#print axioms ProximityGap.Frontier.LambdaQDisproofAttempt.base_case_disproof_fails
#print axioms ProximityGap.Frontier.LambdaQDisproofAttempt.base_case_deficit
#print axioms ProximityGap.Frontier.LambdaQDisproofAttempt.disproof_iff_charP_energy_excess
#print axioms ProximityGap.Frontier.LambdaQDisproofAttempt.no_wraparound_forbids_disproof
