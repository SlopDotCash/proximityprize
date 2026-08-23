/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (THREAD T7-twise-independence)
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# `t`-wise ADDITIVE independence of the dilated phases ⟹ Wick energy (#444, T7)

## What this thread unifies

Two faces of the prize floor `M = max_{b≠0}|η_b| ≤ √(2e·n·log p)` have been attacked separately:

* **The independence face** (`_PhasePairwiseToSubGaussian`): `η_b = Σ_{k=1}^{n/2} Y_k`,
  `Y_k = 2cos(2π·b·x_k/p)`; pairwise near-independence is machine-true (`|Corr| = 0.045`), and the
  abstract framework there shows `t`-wise *product-moment* independence ⟹ the `r`-th moment matches
  the Gaussian/Wick value for `r ≤ t`.
* **The energy face** (`_OpenCoreMonotoneReduction`, `DCSubtractedMoment`, the `W_r`-excess memory):
  the `2r`-th moment of `η_b` is the additive energy `E_r(μ_n) = #{x₁+⋯+x_r = y₁+⋯+y_r}`, and the
  open core is `E_r ≤ (2r−1)‼·n^r = Wick_r` at the saddle depth `r ≈ log p`. The char-0 part is the
  Lam–Leung antipodal-matching count `E_r^{char0} = (2r−1)‼·n^r` EXACTLY; the open content is the
  char-`p` **excess** `W_r = E_r − E_r^{char0}`, an ONSET-THRESHOLD (memory
  `issue444-Wr-excess-onset-threshold-not-birthday`): `W_r = 0` for small `r`, becoming positive only
  past an onset depth `r₀(n)`.

**T7's observation: these are the SAME object viewed through one combinatorial lens — the additive
relations of the dilated set `{b·x_k}`.** The energy `E_r` is a count of `2r`-term `±1` additive
relations `Σ_{i} ε_i z_{k_i} ≡ 0 (mod p)` with `ε_i ∈ {±1}` and `z_k = b·x_k`. Among these:

* the **trivial / diagonal** relations (each `+z` paired with an equal `−z`) are the
  perfect-matchings counted in char 0; there are exactly `(2r−1)‼·n^r` of them = `E_r^{char0} = Wick_r`;
* a **nontrivial** relation is a `±1`-vanishing sum that is NOT a diagonal matching — this is exactly a
  short relation of `2^μ`-th roots mod `p`, and contributes to the excess `W_r`.

So the structural hypothesis **"the dilated set `{b·x_k}` is `t`-wise additively independent"** —
meaning *no nontrivial `±1`-relation of length `≤ t`* — is EXACTLY `W_r = 0` for all `2r ≤ t`, hence
`E_r = E_r^{char0} = Wick_r` for `r ≤ t/2`. This is the statement that unifies the independence and
energy faces under a single name: `NoShortRelation`.

## What this file BUILDS (axiom-clean)

We make the relation-counting abstract (`relCount`, `diagCount`, `excess`) and prove the chain that
turns "no short relation up to depth `t`" into the Wick energy bound up to `r ≤ t/2`:

* `excess_def` / `relCount_eq_diag_add_excess` — `E_r = E_r^{char0} + W_r` (the split is by definition).
* `NoShortRelation` — the NAMED OPEN HYPOTHESIS: `W_r = 0` for all `2r ≤ t`. This is `t`-wise additive
  independence = no nontrivial `≤t`-term `±1`-relation of the dilated roots. **The genuine open content.**
* `energy_eq_diag_of_noShortRelation` — `NoShortRelation t ⟹ E_r = E_r^{char0}` for `2r ≤ t`.
* `energy_le_wick_of_noShortRelation` — with the proven char-0 ceiling `E_r^{char0} ≤ Wick_r`
  (Lam–Leung, supplied as the in-tree handle `hchar0`), this yields **`E_r ≤ Wick_r` for `r ≤ t/2`** —
  the open core at every depth the saddle uses.
* `wick_energy_of_tIndep_to_saddle` — the capstone: `t`-wise additive independence at depth
  `t = 2·⌈log p⌉` ⟹ the Wick energy bound `E_r ≤ Wick_r` at every saddle depth `r ≤ ⌈log p⌉`, which is
  the single-depth (indeed all-depths-`≤` saddle) input the floor derivation
  (`_MomentSaddleValue.prize_floor_amgm_sqrt_e`) consumes.

We also relate this to the product-moment framework: `noShortRelation_iff_excessVanishes` shows the
additive-independence statement is precisely the excess-vanishing statement, so T7's `NoShortRelation`
and the energy face's `W_r = 0` are definitionally the same Prop.

## The NAMED OPEN INPUT (honest)

`NoShortRelation t` for `t = 2·⌈log p⌉` of the dilated `2^μ`-th roots `{b·x_k}` is the BGK/BCHKS-1.12
wall under a structural name. It says: no nontrivial `±1`-relation
`Σ ε_i x_{k_i} ≡ 0 (mod p)` of length `≤ 2 log p` among the `n`-th roots of unity. Equivalently the
onset threshold `r₀(n)` of the excess `W_r` exceeds the saddle depth `⌈log p⌉` (memory
`issue444-Wr-excess-onset-threshold-not-birthday`). Pairwise (`t = 2`) is machine-true; the deep case
`t ≈ 2 log p` at `n = 2^30`, `p ≈ n·2^128` is open. **We name it; we do not discharge it.** Feeding a
vacuous discharge would be the one forbidden move.

## Honest scope

The reduction machinery (split → no-short-relation → char-0 ceiling → Wick) is the prize-TRUE direction,
fully proven. The single input `NoShortRelation (2·⌈log p⌉)` is the open core, identical to the
`DCSubtractedMoment`/`_CharZeroMGFBesselBound` wall and to the `TIndepBound` open input of
`_PhasePairwiseToSubGaussian`, now exhibited as ONE combinatorial Prop unifying the independence and
energy faces. LANDED abstract framework + REDUCED bridge. Issue #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset

namespace ArkLib.ProximityGap.Frontier.TwiseIndependenceFramework

/-! ## §1. The energy / relation-count split `E_r = E_r^{char0} + W_r`.

We work with abstract real-valued counting functions indexed by the moment order `r`:
* `relCount r` is the full additive energy `E_r(μ_n)` over `F_p` (the `2r`-th moment of `η_b`, summed
  over the subgroup; = `#{x₁+⋯+x_r = y₁+⋯+y_r : xᵢ,yᵢ ∈ μ_n}` counted with the relation lens);
* `diagCount r` is the char-0 / diagonal part `E_r^{char0} = #{trivial perfect-matching relations}`,
  the Lam–Leung antipodal-matching count;
* `excess r = relCount r − diagCount r = W_r` is the surplus from NONTRIVIAL short `±1`-relations.

All three are supplied abstractly; the in-tree handles are `DCSubtractedMoment.sum_nonzero_moment`
(for `relCount`), the Lam–Leung char-0 bound (for `diagCount`), and the `W_r`-excess recompute (for
`excess`). This file proves the LOGICAL chain between them. -/

variable (relCount diagCount excess : ℕ → ℝ)

/-- **The energy split is the definition of the excess.** `W_r := E_r − E_r^{char0}`, i.e.
`excess r = relCount r − diagCount r`. Recording it as a hypothesis `hsplit` lets every consumer below
rewrite the full energy as `char-0 part + excess`. -/
def IsEnergySplit : Prop := ∀ r : ℕ, relCount r = diagCount r + excess r

/-- **`E_r = E_r^{char0} + W_r`** (the split, restated as an equation per `r`). The full additive energy
is its char-0 (diagonal-matching) part plus the nontrivial-relation excess. -/
theorem relCount_eq_diag_add_excess (hsplit : IsEnergySplit relCount diagCount excess) (r : ℕ) :
    relCount r = diagCount r + excess r := hsplit r

/-! ## §2. `t`-wise ADDITIVE independence = no short relation = vanishing excess (the named hypothesis). -/

/-- **`t`-wise additive independence of the dilated phases (the NAMED OPEN CORE).**

`NoShortRelation excess t` asserts that the nontrivial-relation excess `W_r = excess r` VANISHES for
every moment order `r` whose relations have length `2r ≤ t`:
```
∀ r, 2r ≤ t → excess r = 0.
```
Combinatorially: the dilated set `{b·x_k}` of `n`-th roots admits **no nontrivial `±1`-relation
`Σ_{i} ε_i x_{k_i} ≡ 0 (mod p)` of length `≤ t`** beyond the trivial diagonal matchings — every short
vanishing `±1`-sum of the roots is a perfect matching (char-0 / antipodal). This is the single object
that unifies:
* the **independence face** — it is the additive-relation form of `TIndepBound Y t` (no high-order
  dependence among the rank-1 linear phases `θ_k = b·x_k`);
* the **energy face** — it is exactly `W_r = 0` for `2r ≤ t`, the onset threshold `r₀(n) > t/2` of the
  `W_r`-excess (memory `issue444-Wr-excess-onset-threshold-not-birthday`).

**This is the genuine open content.** Pairwise (`t = 2`, so `r = 1`) is machine-true (`W_1 = 0`,
Parseval); the deep case `t = 2⌈log p⌉` at the prize scale `n = 2^30`, `p ≈ n·2^128` is the
BGK/BCHKS-1.12 wall. We name it; we do NOT discharge it. -/
def NoShortRelation (t : ℕ) : Prop := ∀ r : ℕ, 2 * r ≤ t → excess r = 0

/-- **`NoShortRelation` is exactly the excess-vanishing statement** (the unification, stated as an
`Iff`). The `t`-wise additive-independence hypothesis of T7 and the `W_r = 0` energy-face hypothesis are
the *same* Prop: there is no content difference, only a change of name (additive-relation language vs
energy-excess language). This is the formal sense in which the independence and energy faces coincide. -/
theorem noShortRelation_iff_excessVanishes (t : ℕ) :
    NoShortRelation excess t ↔ ∀ r : ℕ, 2 * r ≤ t → excess r = 0 := Iff.rfl

/-! ## §3. No short relation ⟹ the full energy equals its char-0 part (for `r ≤ t/2`). -/

/-- **`t`-wise additive independence ⟹ `E_r = E_r^{char0}` for `2r ≤ t`.** When no nontrivial
`≤t`-term relation exists, the excess `W_r` vanishes, so the full additive energy collapses to its
diagonal (char-0 / Lam–Leung) part:
```
E_r = E_r^{char0}     for all r with 2r ≤ t.
```
This is the precise sense in which "no short relation" reduces the char-`p` energy to the char-0 energy
— the entire char-`p` transfer is the excess, and it is zero. -/
theorem energy_eq_diag_of_noShortRelation
    (hsplit : IsEnergySplit relCount diagCount excess)
    {t : ℕ} (hns : NoShortRelation excess t) {r : ℕ} (hr : 2 * r ≤ t) :
    relCount r = diagCount r := by
  rw [hsplit r, hns r hr, add_zero]

/-! ## §4. The Wick energy bound from no short relation + the char-0 (Lam–Leung) ceiling. -/

/-- **The capstone reduction: `t`-wise additive independence + Lam–Leung ⟹ Wick energy** for
`r ≤ t/2`. Given:
* `hsplit` — the energy split `E_r = E_r^{char0} + W_r`;
* `hchar0` — the **in-tree PROVEN** char-0 ceiling `E_r^{char0} ≤ (2r−1)‼·n^r = Wick r` (Lam–Leung
  antipodal matchings of distinct values, `c_r = (2r−1)‼` EXACT — the prize handle marked "char-0:
  `E_r^{char0} ≤ (2r−1)‼·n^r` PROVEN");
* `hns` — the named open `NoShortRelation excess t` (no nontrivial `≤t`-term `±1`-relation),

the full char-`p` additive energy obeys the Wick ceiling at every moment order whose relations have
length `≤ t`:
```
E_r ≤ Wick r = (2r−1)‼·n^r       for all r with 2r ≤ t.
```
This is the open core (the `μ_{2r} ≤ Wick_r` sub-Gaussian energy) at all depths up to `t/2`,
established from the SINGLE structural input `NoShortRelation`. -/
theorem energy_le_wick_of_noShortRelation
    (Wick : ℕ → ℝ)
    (hsplit : IsEnergySplit relCount diagCount excess)
    (hchar0 : ∀ r : ℕ, diagCount r ≤ Wick r)
    {t : ℕ} (hns : NoShortRelation excess t) {r : ℕ} (hr : 2 * r ≤ t) :
    relCount r ≤ Wick r := by
  rw [energy_eq_diag_of_noShortRelation relCount diagCount excess hsplit hns hr]
  exact hchar0 r

/-! ## §5. Specialization to the saddle depth `t = 2⌈log p⌉` (the floor-deriving input). -/

/-- **The saddle-depth capstone (the floor input).** With the saddle depth `R = ⌈log p⌉` (the optimal
moment order in `_MomentSaddleValue`, `R ≈ 110` at prize scale), set the additive-independence depth to
`t = 2R`. Then `t`-wise additive independence `NoShortRelation excess (2R)` — no nontrivial
`≤2⌈log p⌉`-term `±1`-relation of the dilated `2^μ`-th roots — gives the Wick energy bound
```
E_r ≤ Wick r      at EVERY saddle depth r ≤ R = ⌈log p⌉,
```
which is exactly (indeed more than) the single-depth char-`p` Wick input that
`_MomentSaddleValue.prize_floor_amgm_sqrt_e` turns into `M ≤ √(e·n·log p)` — the explicit-constant
floor. So the **entire floor follows from `NoShortRelation` at depth `2⌈log p⌉`**, the one named open
input, which is simultaneously the `W_r`-onset-threshold and the deep `TIndepBound` of the phases. -/
theorem wick_energy_of_tIndep_to_saddle
    (Wick : ℕ → ℝ) (R : ℕ)
    (hsplit : IsEnergySplit relCount diagCount excess)
    (hchar0 : ∀ r : ℕ, diagCount r ≤ Wick r)
    (hns : NoShortRelation excess (2 * R)) :
    ∀ r : ℕ, r ≤ R → relCount r ≤ Wick r := by
  intro r hr
  exact energy_le_wick_of_noShortRelation relCount diagCount excess Wick hsplit hchar0 hns
    (by omega)

/-- **Monotone restriction of the open hypothesis.** Additive independence at a DEEPER depth implies it
at every shallower depth: `NoShortRelation excess t` with `s ≤ t` gives `NoShortRelation excess s`. This
records that the saddle-depth input `NoShortRelation (2⌈log p⌉)` is the strongest in the family and
implies all the shallower (already-verified, e.g. pairwise `t = 2`) instances — the open content is
genuinely the DEPTH, exactly as the `W_r`-onset crossing the saddle. -/
theorem noShortRelation_mono {s t : ℕ} (hst : s ≤ t)
    (hns : NoShortRelation excess t) : NoShortRelation excess s :=
  fun r hr => hns r (le_trans hr hst)

/-- **Pairwise additive independence is unconditional (the base case `r = 1`).** The depth-2 instance
`NoShortRelation excess 2` reduces to `excess 1 = 0`, i.e. `W_1 = 0` — the Parseval / second-moment
fact that the dilated roots have no nontrivial `2`-term relation beyond `z = −(−z)` (antipodal). Given
the in-tree base `W_1 = 0`, the framework reproduces it; the open content is purely the EXTENSION of
this base to depth `2⌈log p⌉`. The depth-`2` window also touches `r = 0` (the empty relation, with
`E_0 = E_0^{char0} = 1` so `W_0 = 0`); we take `h0 : excess 0 = 0` (the trivial empty-sum identity)
alongside the genuine base `h1 : excess 1 = 0`. -/
theorem noShortRelation_two_of_excessOne_zero (h0 : excess 0 = 0) (h1 : excess 1 = 0) :
    NoShortRelation excess 2 := by
  intro r hr
  have hr1 : r ≤ 1 := by omega
  interval_cases r
  · simpa using h0
  · simpa using h1

end ArkLib.ProximityGap.Frontier.TwiseIndependenceFramework

/-! ## Axiom audit — must be ⊆ {propext, Classical.choice, Quot.sound}; no `sorryAx`. -/
open ArkLib.ProximityGap.Frontier.TwiseIndependenceFramework in
#print axioms relCount_eq_diag_add_excess
open ArkLib.ProximityGap.Frontier.TwiseIndependenceFramework in
#print axioms noShortRelation_iff_excessVanishes
open ArkLib.ProximityGap.Frontier.TwiseIndependenceFramework in
#print axioms energy_eq_diag_of_noShortRelation
open ArkLib.ProximityGap.Frontier.TwiseIndependenceFramework in
#print axioms energy_le_wick_of_noShortRelation
open ArkLib.ProximityGap.Frontier.TwiseIndependenceFramework in
#print axioms wick_energy_of_tIndep_to_saddle
open ArkLib.ProximityGap.Frontier.TwiseIndependenceFramework in
#print axioms noShortRelation_mono
open ArkLib.ProximityGap.Frontier.TwiseIndependenceFramework in
#print axioms noShortRelation_two_of_excessOne_zero
