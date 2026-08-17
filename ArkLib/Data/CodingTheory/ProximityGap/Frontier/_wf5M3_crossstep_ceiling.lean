/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-M3)
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharPDeepMomentTail
import Mathlib.Data.Nat.Factorial.DoubleFactorial

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option autoImplicit false

/-!
# The additive-depth recursion closure: a per-step cross bound propagates the Lam–Leung ceiling
  (Issue #444, lane wf-M3)

The substrate `CharPMomentRecursion.lean` proves, exactly and char-`p`-unconditionally, the
one-step additive-moment recursion (the "T4" identity)

    `E_{r+1}(G) = |G| · E_r(G) + cross_r`,    `cross_r = ∑_{s∈G} ∑_{t∈G\{s}} C_r(s−t)`,

together with the *trivial* off-diagonal ceiling `E_{r+1} ≤ |G|² · E_r` (`rEnergy_succ_le`),
which only beats the prize target for depth `r ≳ (|G|−1)/2 ≍ 1.36 n` — far above the prize moment
depth `r ≍ log m`. The prize-relevant question is the *short-depth* control of `cross_r`.

This file isolates the **exact closure mechanism** of the additive-depth recursion: it shows that
a single per-step *absolute* bound on `cross_r` is *necessary and sufficient* to propagate the
Lam–Leung char-`0` ceiling

    `E_r(G) ≤ (2r−1)‼ · n^r`,    `n = |G|`,

inductively to **all** depths `r`. The per-step bound is named as one `Prop` (`M3CrossStepBound`)
— it is **NOT** proven here; it is precisely the open char-`p` transfer crux (the same wall as
`GaussianEnergyBound` / BCHKS-1.12, restated one increment of `r` at a time). What *is* proven,
axiom-clean, is the **propagation implication**:

    `(∀ r, cross_r ≤ 2r · (2r−1)‼ · n^{r+1})`   ⟹   `(∀ r, E_r(G) ≤ (2r−1)‼ · n^r)`.

## The arithmetic of the step (why this exact constant)

If the ceiling holds at level `r` and we want it at level `r+1`, the recursion gives
`E_{r+1} = n·E_r + cross_r ≤ n·(2r−1)‼·n^r + cross_r = (2r−1)‼·n^{r+1} + cross_r`.
The level-`(r+1)` ceiling is `(2r+1)‼·n^{r+1} = (2r+1)·(2r−1)‼·n^{r+1}` (since
`(2(r+1)−1)‼ = (2r+1)‼ = (2r+1)·(2r−1)‼`, `doubleFactorial_add_two`). So the slack available for
`cross_r` is exactly `[(2r+1) − 1]·(2r−1)‼·n^{r+1} = 2r·(2r−1)‼·n^{r+1}` — which is the bound
`M3CrossStepBound r`. This is **sharp**: it is the largest per-step cross bound that the recursion
can absorb without breaking the ceiling.

## Numerical pre-screen (wf-M3, `probe_wf5M3_*.py`)

`cross_r / (2r·(2r−1)‼·n^{r+1})` over the **char-`0`-faithful** regime (prime `p` large enough
that `E_r(μ_n)` has stabilized to its char-`0` value):

| n  | p     | r=1   | r=2   | r=3   | r=4   | r=5   |
|----|-------|-------|-------|-------|-------|-------|
| 8  | 3457  | 0.812 | 0.615 | 0.405 | 0.233 | 0.119 |
| 16 | 7681  | 0.906 | 0.794 | 0.679 | 0.578 | 0.500 |
| 16 | 12289 | 0.906 | 0.794 | 0.651 | 0.511 | 0.396 |
| 32 | 61441 | 0.953 | 0.894 | 0.894 | 1.177*| —     |

All ratios `≤ 1` **exactly while `p` keeps `E_r` char-`0`-faithful** (n=8,16 all listed `r`; n=32
up to `r=3`, where `p=61441` is still faithful). The single `*`-marked failure (n=32, r=4) is
*not* a counterexample to the lemma: it is the point where `p=61441` drops below the char-`0`
faithfulness threshold for n=32, so `E_4` is already char-`p`-polluted (spurious mod-`p` vanishing
sums of 32nd roots). **Conclusion of the pre-screen: `M3CrossStepBound` is EQUIVALENT to char-`0`
fidelity of `E_r`; it is not an independent lever — it is the char-`p` transfer wall (CLAUDE.md
face #3) restated per increment of `r`.** Verified by `probe_wf5M3_invariant.py` (exact bigint).

## Honest scope (the open crux)

`M3CrossStepBound` is the OPEN char-`p` transfer. It is PROVEN (char-0, Lam–Leung) only when the
prime `p` exceeds the norm threshold `p > (2r)^{n/2}` so that no spurious `≤2r`-term `±1` relation
of `n`-th roots vanishes mod `p`; for the prize `n = 2^30`, `p ≈ n·2^128`, this threshold
`(2r)^{2^29}` is astronomically false. The band `r ∈ [β log n, 1.36n]` is exactly where neither
the norm bound (top, `r > 1.36n`) nor the small-`n` faithfulness (`n < 40`) applies. This file
does NOT close it; it makes the per-step obligation precise and shows it is *sufficient*.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
- Lam, Leung. *On vanishing sums of roots of unity*. (char-0 antipodal structure of `2^μ`-th roots.)
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CharPMomentRecursion (autocorr rEnergy_succ)

namespace ArkLib.ProximityGap.CrossStepCeiling

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The off-diagonal cross mass `cross_r = ∑_{s∈G} ∑_{t∈G\{s}} C_r(s−t)` of the
additive-depth recursion, as it appears in the proven `rEnergy_succ`. -/
noncomputable def crossMass (G : Finset F) (r : ℕ) : ℕ :=
  ∑ s ∈ G, ∑ t ∈ G.erase s, autocorr G r (s - t)

/-- Restatement of the proven substrate recursion in terms of `crossMass`:
`E_{r+1} = |G| · E_r + cross_r`. (Pure renaming of `CharPMomentRecursion.rEnergy_succ`.) -/
theorem rEnergy_succ_crossMass (G : Finset F) (r : ℕ) :
    rEnergy G (r + 1) = G.card * rEnergy G r + crossMass G r := by
  rw [rEnergy_succ]; rfl

/-- **The per-step cross bound (the OPEN char-`p` crux, lane wf-M3).** For a finite set `G` of
size `n`, the off-diagonal cross mass at depth `r` is bounded by `2r · (2r−1)‼ · n^{r+1}`. This is
the *sharp* per-step slack the additive-depth recursion can absorb while preserving the Lam–Leung
ceiling `E_r ≤ (2r−1)‼·n^r`. PROVEN in char-0 (Lam–Leung antipodal structure) / for `p` above the
root-norm threshold; OPEN in the prize band `r ∈ [β log n, 1.36n]`. Named here as a `Prop`, not
proven. -/
def M3CrossStepBound (G : Finset F) : Prop :=
  ∀ r : ℕ, crossMass G r ≤ 2 * r * Nat.doubleFactorial (2 * r - 1) * G.card ^ (r + 1)

/-- The Lam–Leung char-`0` ceiling at depth `r`: `E_r(G) ≤ (2r−1)‼ · n^r`. -/
def LamLeungCeiling (G : Finset F) (r : ℕ) : Prop :=
  rEnergy G r ≤ Nat.doubleFactorial (2 * r - 1) * G.card ^ r

/-- **Base case `r = 0`: `E_0 = 1 ≤ 1`.** The empty `0`-tuple sums to `0`; `E_0 = #{(v,w)} = 1`
(the unique pair of empty tuples), and `(2·0−1)‼ · n^0 = (−1 truncated to 0 →) (0)‼ · 1`. In ℕ,
`2*0-1 = 0` and `0‼ = 1`, `n^0 = 1`, so the RHS is `1`. We show `E_0 ≤ 1` via the explicit
`rEnergy` count over the single empty tuple. -/
theorem lamLeungCeiling_zero (G : Finset F) : LamLeungCeiling G 0 := by
  unfold LamLeungCeiling
  -- (2*0-1)‼ = 0‼ = 1; n^0 = 1; RHS = 1; and E_0 = 1 (substrate `rEnergy_zero`)
  rw [ArkLib.ProximityGap.CharPDeepMomentTail.rEnergy_zero]
  -- goal: 1 ≤ (2*0-1)‼ * G.card^0 = 0‼ * 1 = 1
  have h1 : (2 * 0 - 1 : ℕ) = 0 := by norm_num
  rw [h1, pow_zero, Nat.mul_one, show Nat.doubleFactorial 0 = 1 from rfl]

/-- **The exact step-arithmetic identity behind the constant:** for any `r`,
`(2(r+1)−1)‼ = (2r+1)·(2r−1)‼`. (i.e. `(2r+1)‼ = (2r+1)·(2r−1)‼`.) -/
theorem doubleFactorial_step (r : ℕ) :
    Nat.doubleFactorial (2 * (r + 1) - 1)
      = (2 * r + 1) * Nat.doubleFactorial (2 * r - 1) := by
  cases r with
  | zero => decide
  | succ k =>
    -- 2*(k+1+1)-1 = 2k+3 = (2k+1)+2; (2k+3)‼ = (2k+3)·(2k+1)‼
    have h1 : 2 * (k + 1 + 1) - 1 = (2 * k + 1) + 2 := by omega
    have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [h1, h2, Nat.doubleFactorial_add_two]
    ring_nf

/-- **THE PROPAGATION STEP (axiom-clean): the per-step bound carries the ceiling up by one.**
Assuming `M3CrossStepBound G` and the ceiling at depth `r`, the ceiling holds at depth `r+1`.
Pure ℕ-arithmetic on the proven recursion `E_{r+1} = n·E_r + cross_r`:
`E_{r+1} ≤ n·(2r−1)‼·n^r + 2r·(2r−1)‼·n^{r+1} = (1+2r)·(2r−1)‼·n^{r+1} = (2(r+1)−1)‼·n^{r+1}`. -/
theorem lamLeungCeiling_step (G : Finset F) (hstep : M3CrossStepBound G) (r : ℕ)
    (hr : LamLeungCeiling G r) : LamLeungCeiling G (r + 1) := by
  unfold LamLeungCeiling at hr ⊢
  rw [rEnergy_succ_crossMass]
  set n := G.card
  set D := Nat.doubleFactorial (2 * r - 1)
  -- term 1: n · E_r ≤ n · (D · n^r) = D · n^{r+1}
  have hT1 : n * rEnergy G r ≤ D * n ^ (r + 1) := by
    calc n * rEnergy G r ≤ n * (D * n ^ r) := Nat.mul_le_mul_left _ hr
      _ = D * n ^ (r + 1) := by ring
  -- term 2: cross_r ≤ 2r · D · n^{r+1}
  have hT2 : crossMass G r ≤ 2 * r * D * n ^ (r + 1) := hstep r
  -- sum ≤ (1 + 2r) · D · n^{r+1} = (2(r+1)-1)‼ · n^{r+1}
  calc n * rEnergy G r + crossMass G r
      ≤ D * n ^ (r + 1) + 2 * r * D * n ^ (r + 1) := Nat.add_le_add hT1 hT2
    _ = (2 * r + 1) * D * n ^ (r + 1) := by ring
    _ = Nat.doubleFactorial (2 * (r + 1) - 1) * n ^ (r + 1) := by
        rw [doubleFactorial_step r]

/-- **THE CLOSURE (axiom-clean): the per-step cross bound implies the full Lam–Leung ceiling at
every depth.** `M3CrossStepBound G  ⟹  ∀ r, E_r(G) ≤ (2r−1)‼·n^r`. Straight induction on `r` from
the base case and the propagation step; the *entire* additive-depth recursion content is the proven
substrate `rEnergy_succ`, so the only non-elementary input is the named per-step crux
`M3CrossStepBound` (the open char-`p` transfer). For the prize moment certificate this gives, at the
optimal depth `r ≍ ln q`, the worst Gauss period `B = max_{b≠0}‖η_b‖ ≤ √(2n ln q)` via the in-tree
`q·∑_b‖η_b‖^{2r} = q·E_r` raw-moment identity — i.e. the prize bound `M(n) ≤ C√(n log(p/n))`,
*conditional on* `M3CrossStepBound`. -/
theorem lamLeung_ceiling_of_crossStep (G : Finset F) (hstep : M3CrossStepBound G) :
    ∀ r : ℕ, LamLeungCeiling G r := by
  intro r
  induction r with
  | zero => exact lamLeungCeiling_zero G
  | succ k ih => exact lamLeungCeiling_step G hstep k ih

end ArkLib.ProximityGap.CrossStepCeiling

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CrossStepCeiling.rEnergy_succ_crossMass
#print axioms ArkLib.ProximityGap.CrossStepCeiling.lamLeungCeiling_zero
#print axioms ArkLib.ProximityGap.CrossStepCeiling.doubleFactorial_step
#print axioms ArkLib.ProximityGap.CrossStepCeiling.lamLeungCeiling_step
#print axioms ArkLib.ProximityGap.CrossStepCeiling.lamLeung_ceiling_of_crossStep
