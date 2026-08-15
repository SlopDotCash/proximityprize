/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ60Dictionary
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ43AutoInstantiation

/-!
# SYZ66 — the BadCountCeiling bridge: composing G87's syndrome dichotomy with the strip radius

SYZ60 collapsed the entire per-stack counting dictionary to a single scalar residual
`BadCountCeiling : ∀ u, mcaBadCount (evalCode g 2³⁰ (2²⁹−1)) (predecessorRadius 2³⁰ stripNumerator)
(u 0)(u 1) ≤ 2³⁰` — at the **strip** predecessor radius `357913940/2³⁰ < 1/3`.  SYZ60's docstring
named the supply chain (G87 `mcaEvent`→syndrome bridge, SYZ18 distinct supports, G86 rank-collapse
dichotomy, SYZ29 pencil accounting) but did not compose it.  This file composes it **as far as it
honestly goes**, and isolates the one link that does not close.

## The strip threshold (recomputed for `stripNumerator = 357913941`)

At `δ = predecessorRadius 2³⁰ 357913941 = 357913940/2³⁰`, the `mcaEvent` witness set has
`t = (1−δ)·2³⁰ = 715827884` points (`strip_threshold`; note `715827884 + 357913940 = 2³⁰` exactly).
Against a code of dimension `k = finrank ≤ 2²⁹`, each bad scalar contributes a G87 block of
`t − k ≥ 178956972` functionals annihilating the (shared, nonzero) syndrome pair, living in the
`2(n−k) = 2³⁰`-dimensional syndrome-pair space.

## What the PROVEN parts cap — a constant, not a fraction of `2³⁰`

`plantable_linearIndependent_cap` (G86, restated in G87) gives, for a **linearly independent**
(syzygy-free) block family, `r·(t−k) + 1 ≤ 2(n−k)`.  Instantiated at the strip shape this is
`r·(715827884 − k) + 1 ≤ 2(2³⁰ − k)` with `k ≤ 2²⁹`, which forces **`r ≤ 5`**
(`strip_independent_cap`; the bound is sharp — `r = 5` is realizable at `k = 2²⁹`, `r = 6` is not for
any `k ≤ 2²⁹`).  So the entire independent/generic-position regime is capped, unconditionally, at a
constant **five** — utterly below the `2³⁰` budget.  Dually, any `r ≥ 6` bad scalars force an
explicit nontrivial **syzygy** among their witness functionals (`strip_six_bad_scalars_force_syzygy`,
`strip_six_bad_scalars_not_linearIndependent`) — the exact strip analogue of G87's `64`-scalar wall
corollary (there `64·(2²⁴+1)+1 > 2³⁰`; here the larger strip threshold makes the constant `6`).

Lifting to the concrete `mcaBadCount`: any stack whose bad count is `≥ 6` yields six distinct bad
scalars, hence carries a syzygy (`strip_count_ge_six_forces_syzygy`).  So the `2³⁰` budget of
`BadCountCeiling` lives **entirely** in the syzygy-carrying stacks: the proven independent cap
discharges every non-syzygy stack (bad count `≤ 5 ≤ 2³⁰`) outright.

## The (d) verdict: the composition does NOT close — the syzygy bulk is the residual

The remaining link `(d)` — "a functional dependence (syzygy) among the witness blocks forces a
degenerate/pencil-attributed core whose yield is bounded, so the ~`2³⁰` dependent scalars still fit
the budget" — is **not** discharged.  G86's dependence certificate is only an explicit linear
relation `∑ cc p • φ p = 0` among the `γ`-weighted parity rows; SYZ29's `bad_card_le_pool_add_fresh`
shows the honest accounting is `#B ≤ #pencilPool + #fresh` with `#pencilPool ≤ ∑(n − sᵢ)`
unconditionally, but the attribution step (`#fresh = 0`, i.e. every syzygy scalar is pencil-attributed
to a core, and the pencil pool itself sums to `≤ 2³⁰`) is exactly the SYZ29 named residual, and
SYZ56's cross-witness chaining is a proven **NO-GO** for forcing the merge inside the strip.  A raw
syzygy `cc` does not, on its own, hand back a pencil root: that scalar-level attribution is the open
input.

We therefore land the **honest conditional**: `BadCountCeiling` follows from a single sharply-named
residual `StripSyzygyControlledCeiling` — "every stack with `≥ 6` bad scalars (necessarily
syzygy-carrying, by `strip_count_ge_six_forces_syzygy`) has bad count `≤ 2³⁰`" — via a case split
that discharges the `≤ 5` (independent) regime with the proven cap
(`badCountCeiling_of_syzygyControlled`).  This quantifies exactly how much of the `2³⁰` budget the
proven parts already cap: **all of it below `6`**, i.e. the whole non-syzygy regime; the residual is
precisely the dependent/syzygy bulk `[6, 2³⁰]`, unchanged from SYZ29/SYZ56.  No `δ*` is closed.

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open scoped NNReal ENNReal
open Module Submodule

namespace ArkLib.ProximityGap.Frontier.SYZ66

open _root_.ProximityGap Code
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open ArkLib.ProximityGap.Frontier.SYZ46
open ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge

/-- The certified first prize field is a field (its modulus is prime). -/
local instance primeFactP30 : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance localInstance_SYZ66BadCountBridge_1 : NeZero ArkLib.ProximityGap.PrizeShapePrimeP30.P :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P.ne_zero⟩

/-! ## 1. The strip witness threshold -/

/-- **The strip witness threshold.**  At the strip predecessor radius
`predecessorRadius 2³⁰ stripNumerator = 357913940/2³⁰`, the `mcaEvent` witness set has at least
`t = 715827884` points.  (`715827884 + (357913941 − 1) = 2³⁰` exactly — the strip radius sits at the
`1/3` lattice predecessor, so the threshold is `2³⁰ − 357913940 = 715827884`.) -/
theorem strip_threshold :
    ((715827884 : ℕ) : ℝ≥0) ≤
      (1 - predecessorRadius (2 ^ 30) stripNumerator) *
        (Fintype.card (Fin (2 ^ 30)) : ℝ≥0) := by
  rw [show stripNumerator = 357913941 from rfl, Fintype.card_fin, predecessorRadius, tsub_mul,
    one_mul, div_mul_cancel₀ _ (by norm_num : ((2 ^ 30 : ℕ) : ℝ≥0) ≠ 0),
    le_tsub_iff_right (Nat.cast_le.mpr (by norm_num : (357913941 - 1 : ℕ) ≤ 2 ^ 30))]
  exact_mod_cast (by norm_num : (715827884 + (357913941 - 1) : ℕ) ≤ 2 ^ 30)

/-! ## 2. The proven independent cap: syzygy-free bad families have ≤ 5 scalars -/

/-- **The strip independent cap (proven).**  Given the G87 bridge functionals `φ` of an `r`-scalar
family, all annihilating a **nonzero** syndrome pair (`hann`, `hne`), if they are **linearly
independent** (generic position, no syzygy) then `r ≤ 5`.

This instantiates G86/G87's `plantable_linearIndependent_cap` at the strip shape:
`r·(715827884 − k) + 1 ≤ 2(2³⁰ − k)` with `k ≤ 2²⁹` forces `r ≤ 5`.  The bound is sharp
(`r = 5` at `k = 2²⁹`).  So the entire generic-position regime is capped at a constant, far below the
`2³⁰` budget. -/
theorem strip_independent_cap {r : ℕ}
    {u₀ u₁ : Fin (2 ^ 30) → ZMod P}
    {φ : Fin r × Fin (715827884 - Module.finrank (ZMod P) wallCode) →
        Module.Dual (ZMod P) (SyndromePair wallCode)}
    (hann : ∀ p, φ p (syndromePair wallCode u₀ u₁) = 0)
    (hne : syndromePair wallCode u₀ u₁ ≠ 0)
    (hli : LinearIndependent (ZMod P) φ) : r ≤ 5 := by
  have hplant : Plantable φ := ⟨syndromePair wallCode u₀ u₁, hne, hann⟩
  have hcap := plantable_linearIndependent_cap hplant hli
  rw [finrank_syndromePair wallCode] at hcap
  have hkle : Module.finrank (ZMod P) wallCode ≤ 536870912 :=
    le_trans finrank_wallCode_le (by norm_num)
  have hcard : Fintype.card (Fin (2 ^ 30)) = 1073741824 := by rw [Fintype.card_fin]; norm_num
  rw [hcard] at hcap
  by_contra h
  push_neg at h
  generalize hK : Module.finrank (ZMod P) wallCode = K at hcap hkle
  have h6 : 6 * (715827884 - K) ≤ r * (715827884 - K) := Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## 3. The strip force-syzygy corollaries (family form) -/

/-- **Strip force-syzygy (family form).**  Any `r ≥ 6` scalars each firing `mcaEvent` at the strip
predecessor radius yield witness functionals on the `2³⁰`-dimensional syndrome-pair space that
(a) all vanish on the stack's (nonzero) syndrome pair, (b) are linearly independent within each
witness block, and (c) globally admit an **explicit nontrivial syzygy** — because the generic
disjunct of the G86 dichotomy is numerically impossible at the strip shape:
`6·(715827884 − k) + 1 > 2(2³⁰ − k)` for every `k ≤ 2²⁹`.  The strip analogue of G87's `64`-scalar
wall corollary. -/
theorem strip_six_bad_scalars_force_syzygy
    {r : ℕ} (hr : 6 ≤ r) (u₀ u₁ : Fin (2 ^ 30) → ZMod P) (γ : Fin r → ZMod P)
    (hbad : ∀ i, mcaEvent
      (ArkLib.ProximityGap.KKH26.evalCode g (2 ^ 30) (2 ^ 29 - 1))
      (predecessorRadius (2 ^ 30) stripNumerator) u₀ u₁ (γ i)) :
    ∃ φ : Fin r × Fin (715827884 - Module.finrank (ZMod P) wallCode) →
        Module.Dual (ZMod P) (SyndromePair wallCode),
      (∀ p, φ p (syndromePair wallCode u₀ u₁) = 0) ∧
      (∀ i, LinearIndependent (ZMod P) fun j => φ (i, j)) ∧
      ∃ cc : Fin r × Fin (715827884 - Module.finrank (ZMod P) wallCode) → ZMod P,
        (∑ p, cc p • φ p = 0) ∧ ∃ p, cc p ≠ 0 := by
  have hbad' : ∀ i, mcaEvent (wallCode : Set (Fin (2 ^ 30) → ZMod P))
      (predecessorRadius (2 ^ 30) stripNumerator) u₀ u₁ (γ i) := by
    intro i; rw [wallCode_coe]; exact hbad i
  have hwit : ∀ i, ∃ S : Finset (Fin (2 ^ 30)), S.card = 715827884 ∧
      ∃ c ∈ wallCode, ∀ x ∈ S, c x = u₀ x + γ i * u₁ x :=
    fun i => mcaEvent_witness (hbad' i) strip_threshold
  have hstack : u₀ ∉ wallCode ∨ u₁ ∉ wallCode :=
    mcaEvent_not_both_mem wallCode (hbad' ⟨0, by omega⟩)
  obtain ⟨φ, hann, hblock, hdich⟩ := syndrome_dichotomy wallCode γ hstack hwit
  refine ⟨φ, hann, hblock, ?_⟩
  rcases hdich with hcap | hsyz
  · -- the generic cap is numerically impossible at the strip shape
    exfalso
    have hkle : Module.finrank (ZMod P) wallCode ≤ 536870912 :=
      le_trans finrank_wallCode_le (by norm_num)
    have hcard : Fintype.card (Fin (2 ^ 30)) = 1073741824 := by rw [Fintype.card_fin]; norm_num
    generalize hK : Module.finrank (ZMod P) wallCode = K at hcap hkle
    generalize hN : Fintype.card (Fin (2 ^ 30)) = N at hcap hcard
    have h6 : 6 * (715827884 - K) ≤ r * (715827884 - K) :=
      Nat.mul_le_mul_right _ hr
    have hcap' := le_trans (Nat.add_le_add_right h6 1) hcap
    omega
  · exact hsyz

/-- **Impossibility form.**  The witness functionals of `6` bad scalars at the strip shape can
**never** be linearly independent: independent-block planting is capped at `5`. -/
theorem strip_six_bad_scalars_not_linearIndependent
    {r : ℕ} (hr : 6 ≤ r) (u₀ u₁ : Fin (2 ^ 30) → ZMod P) (γ : Fin r → ZMod P)
    (hbad : ∀ i, mcaEvent
      (ArkLib.ProximityGap.KKH26.evalCode g (2 ^ 30) (2 ^ 29 - 1))
      (predecessorRadius (2 ^ 30) stripNumerator) u₀ u₁ (γ i)) :
    ∃ φ : Fin r × Fin (715827884 - Module.finrank (ZMod P) wallCode) →
        Module.Dual (ZMod P) (SyndromePair wallCode),
      (∀ p, φ p (syndromePair wallCode u₀ u₁) = 0) ∧
      (∀ i, LinearIndependent (ZMod P) fun j => φ (i, j)) ∧
      ¬ LinearIndependent (ZMod P) φ := by
  obtain ⟨φ, hann, hblock, cc, hcc, hne⟩ :=
    strip_six_bad_scalars_force_syzygy hr u₀ u₁ γ hbad
  exact ⟨φ, hann, hblock, Fintype.not_linearIndependent_iff.mpr ⟨cc, hcc, hne⟩⟩

/-! ## 4. Lifting to the concrete `mcaBadCount`: ≥ 6 bad scalars ⇒ syzygy -/

/-- **Six distinct bad scalars from a bad count `≥ 6`.**  If the concrete `mcaBadCount` is at least
`6`, six *distinct* scalars each fire `mcaEvent` — extracted from the bad-scalar filter set. -/
theorem six_bad_scalars_of_count_ge
    (C : Set (Fin (2 ^ 30) → ZMod P)) (δ : ℝ≥0) (u₀ u₁ : Fin (2 ^ 30) → ZMod P)
    (h : 6 ≤ mcaBadCount (F := ZMod P) C δ u₀ u₁) :
    ∃ γ : Fin 6 → ZMod P, Function.Injective γ ∧ ∀ i, mcaEvent C δ u₀ u₁ (γ i) := by
  classical
  rw [mcaBadCount] at h
  obtain ⟨S', hsub, hcard⟩ := Finset.exists_subset_card_eq h
  let e : Fin 6 ≃ (S' : Type _) := (S'.equivFin.trans (finCongr hcard)).symm
  refine ⟨fun i => (e i : ZMod P), ?_, ?_⟩
  · intro a b hab
    exact e.injective (Subtype.ext hab)
  · intro i
    have hmem : (e i : ZMod P) ∈
        Finset.univ.filter (fun γ : ZMod P => mcaEvent C δ u₀ u₁ γ) := hsub (e i).2
    exact (Finset.mem_filter.mp hmem).2

/-- **Bad count `≥ 6` forces a syzygy (concrete form).**  For the gate code at the strip predecessor
radius, any stack whose `mcaBadCount` is at least `6` carries an explicit nontrivial syzygy among the
witness functionals of six of its bad scalars.  Hence the `2³⁰` budget of `BadCountCeiling` lives
entirely in the syzygy-carrying stacks; every stack with bad count `≤ 5` is discharged by the proven
independent cap. -/
theorem strip_count_ge_six_forces_syzygy
    (u₀ u₁ : Fin (2 ^ 30) → ZMod P)
    (h : 6 ≤ mcaBadCount (F := ZMod P)
      (ArkLib.ProximityGap.KKH26.evalCode g (2 ^ 30) (2 ^ 29 - 1))
      (predecessorRadius (2 ^ 30) stripNumerator) u₀ u₁) :
    ∃ φ : Fin 6 × Fin (715827884 - Module.finrank (ZMod P) wallCode) →
        Module.Dual (ZMod P) (SyndromePair wallCode),
      (∀ p, φ p (syndromePair wallCode u₀ u₁) = 0) ∧
      (∀ i, LinearIndependent (ZMod P) fun j => φ (i, j)) ∧
      ∃ cc : Fin 6 × Fin (715827884 - Module.finrank (ZMod P) wallCode) → ZMod P,
        (∑ p, cc p • φ p = 0) ∧ ∃ p, cc p ≠ 0 := by
  obtain ⟨γ, _hinj, hbad⟩ := six_bad_scalars_of_count_ge _ _ u₀ u₁ h
  exact strip_six_bad_scalars_force_syzygy (le_refl 6) u₀ u₁ γ hbad

/-! ## 5. The honest conditional: BadCountCeiling ⟸ syzygy control -/

/-- **The isolated residual `(d)`.**  Every stack with `≥ 6` bad scalars — necessarily
syzygy-carrying by `strip_count_ge_six_forces_syzygy` — has bad count `≤ 2³⁰`.  This is exactly the
dependent/syzygy-block control that G86's raw dependence certificate does **not** supply and that
SYZ56's cross-witness chaining is a NO-GO for: the scalar-level pencil attribution of the syzygy bulk
(SYZ29's `#fresh = 0` residual). -/
def StripSyzygyControlledCeiling : Prop :=
  ∀ u : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)),
    6 ≤ mcaBadCount (F := ZMod P)
        (ArkLib.ProximityGap.KKH26.evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (predecessorRadius (2 ^ 30) stripNumerator) (u 0) (u 1) →
    mcaBadCount (F := ZMod P)
        (ArkLib.ProximityGap.KKH26.evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (predecessorRadius (2 ^ 30) stripNumerator) (u 0) (u 1) ≤ 2 ^ 30

/-- **The honest composition.**  `BadCountCeiling` follows from `StripSyzygyControlledCeiling`: the
low-count regime (`≤ 5` bad scalars, exactly the independent/generic-position stacks the proven
`strip_independent_cap` covers) satisfies `≤ 2³⁰` **unconditionally** (`5 ≤ 2³⁰`), and the residual
handles only the syzygy-carrying regime (`≥ 6`).  So the proven parts cap the entire non-syzygy
budget; the surviving content is precisely the dependent/syzygy bulk. -/
theorem badCountCeiling_of_syzygyControlled (h : StripSyzygyControlledCeiling) :
    ArkLib.ProximityGap.Frontier.SYZ60Dictionary.BadCountCeiling := by
  intro u
  by_cases hc : 6 ≤ mcaBadCount (F := ZMod P)
      (ArkLib.ProximityGap.KKH26.evalCode g (2 ^ 30) (2 ^ 29 - 1))
      (predecessorRadius (2 ^ 30) stripNumerator) (u 0) (u 1)
  · exact h u hc
  · push_neg at hc; exact le_trans hc.le (by norm_num)

/-- **The dictionary collapse, chained.**  Composing with SYZ60: syzygy control discharges the whole
counting dictionary. -/
theorem countingDictionary_of_syzygyControlled (h : StripSyzygyControlledCeiling) :
    ArkLib.ProximityGap.Frontier.SYZ57Transport.CountingDictionary :=
  ArkLib.ProximityGap.Frontier.SYZ60Dictionary.countingDictionary_of_badCountCeiling
    (badCountCeiling_of_syzygyControlled h)

end ArkLib.ProximityGap.Frontier.SYZ66

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.Frontier.SYZ66.strip_threshold
#print axioms ArkLib.ProximityGap.Frontier.SYZ66.strip_independent_cap
#print axioms ArkLib.ProximityGap.Frontier.SYZ66.strip_six_bad_scalars_force_syzygy
#print axioms ArkLib.ProximityGap.Frontier.SYZ66.strip_six_bad_scalars_not_linearIndependent
#print axioms ArkLib.ProximityGap.Frontier.SYZ66.six_bad_scalars_of_count_ge
#print axioms ArkLib.ProximityGap.Frontier.SYZ66.strip_count_ge_six_forces_syzygy
#print axioms ArkLib.ProximityGap.Frontier.SYZ66.badCountCeiling_of_syzygyControlled
#print axioms ArkLib.ProximityGap.Frontier.SYZ66.countingDictionary_of_syzygyControlled
