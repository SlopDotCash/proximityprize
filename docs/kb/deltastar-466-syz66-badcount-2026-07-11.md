# δ* #466 — SYZ66: the BadCountCeiling bridge (G87 syndrome dichotomy ∘ strip radius)

_2026-07-11. File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ66BadCountBridge.lean`.
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`) across all 8 theorems._

## Goal

SYZ60 collapsed the whole per-stack counting dictionary to a single scalar residual

    BadCountCeiling : ∀ u, mcaBadCount (evalCode g 2³⁰ (2²⁹−1))
                            (predecessorRadius 2³⁰ stripNumerator) (u 0)(u 1) ≤ 2³⁰

at the **strip** predecessor radius `357913940/2³⁰ < 1/3` (stripNumerator = 357913941). SYZ60 named
the supply chain but did not compose it. SYZ66 composes G87 (`mcaEvent`→syndrome→pencil bridge) with
the G86 rank-collapse dichotomy **at the strip radius**, as far as it honestly goes, and isolates the
one link that does not close.

## Composition status, per link

- **(a) witness extraction — LANDED.** `strip_threshold`: at the strip radius the `mcaEvent` witness
  set has `t = 715827884` points (`715827884 + 357913940 = 2³⁰` exactly). Feeds G87
  `mcaEvent_witness`.
- **(b) distinct supports — LANDED (SYZ18, cited).** Not needed for the two proven SYZ66 theorems
  (the dichotomy/cap hold for any family); used only in the narrative accounting.
- **(c) block construction + independent cap — LANDED & INSTANTIATED.** `strip_independent_cap`:
  the G87 bridge functionals of an `r`-scalar family, all annihilating the nonzero syndrome pair, if
  **linearly independent** force `r ≤ 5`. Arithmetic: `r·(715827884−k)+1 ≤ 2(2³⁰−k)`, `k ≤ 2²⁹` ⟹
  `r ≤ 5`. **Sharp**: `r = 5` realizable at `k = 2²⁹`; `r = 6` impossible for every `k ≤ 2²⁹`
  (verified `probe`-style: for all `K ≤ 2²⁹`, `6·(t−K)+1 > 2(2³⁰−K)` since the gap is
  `2147483657 − 4K > 0`).
- **(d) dependent ⟹ core-attributed pencil yield — NOT DISCHARGED (the gap).** A raw G86 dependence
  certificate `∑ cc p • φ p = 0` does not on its own return a pencil root `γ = −d₀(x)/d₁(x)`. SYZ29's
  honest accounting `#B ≤ #pencilPool + #fresh` (with `#pencilPool ≤ ∑(n−sᵢ)` unconditional) leaves
  the attribution `#fresh = 0` + pool-sum `≤ 2³⁰` as the named residual; SYZ56's cross-witness
  chaining is a proven NO-GO for forcing the merge inside the strip (the `m`-fold overlap
  `n − m(n−t)` is antitone and already `< k` at `m = 2`). The scalar-level attribution is the open
  input.

## The (d) verdict

**The composition does NOT close.** The PROVEN parts cap the entire **independent / generic-position**
regime at a *constant* — **five** scalars — utterly below the `2³⁰` budget. Dually, any `r ≥ 6` bad
scalars force an explicit nontrivial **syzygy** (`strip_six_bad_scalars_force_syzygy`,
`…_not_linearIndependent`) — the strip analogue of G87's `64`-scalar wall corollary (the larger strip
threshold shrinks the constant `64 → 6`). Lifting to the concrete count,
`strip_count_ge_six_forces_syzygy`: any stack with `mcaBadCount ≥ 6` carries a syzygy. So the whole
`2³⁰` budget lives in syzygy-carrying stacks; the residual is exactly `[6, 2³⁰]`, unchanged from
SYZ29/SYZ56.

**Quantified budget capture:** the proven parts discharge the *entire* non-syzygy regime
(bad count `≤ 5`); zero of the dependent bulk `[6, 2³⁰]` is newly closed.

## Landed statements (verbatim)

- `strip_threshold : ((715827884 : ℕ) : ℝ≥0) ≤ (1 - predecessorRadius (2^30) stripNumerator) *
  (Fintype.card (Fin (2^30)) : ℝ≥0)`
- `strip_independent_cap {r} {u₀ u₁} {φ …} (hann : ∀ p, φ p (syndromePair wallCode u₀ u₁) = 0)
  (hne : syndromePair wallCode u₀ u₁ ≠ 0) (hli : LinearIndependent (ZMod P) φ) : r ≤ 5`
- `strip_six_bad_scalars_force_syzygy {r} (hr : 6 ≤ r) (u₀ u₁) (γ)
  (hbad : ∀ i, mcaEvent (evalCode g 2³⁰ (2²⁹−1)) (predecessorRadius 2³⁰ stripNumerator) u₀ u₁ (γ i))
  : ∃ φ, (∀ p, φ p (syndromePair …) = 0) ∧ (∀ i, LinearIndependent … block) ∧
     ∃ cc, (∑ p, cc p • φ p = 0) ∧ ∃ p, cc p ≠ 0`
- `strip_six_bad_scalars_not_linearIndependent … : ∃ φ, … ∧ ¬ LinearIndependent (ZMod P) φ`
- `six_bad_scalars_of_count_ge (C δ u₀ u₁) (h : 6 ≤ mcaBadCount C δ u₀ u₁)
  : ∃ γ : Fin 6 → ZMod P, Function.Injective γ ∧ ∀ i, mcaEvent C δ u₀ u₁ (γ i)`
- `strip_count_ge_six_forces_syzygy (u₀ u₁) (h : 6 ≤ mcaBadCount (evalCode …)
  (predecessorRadius 2³⁰ stripNumerator) u₀ u₁) : ∃ φ, … ∧ ∃ cc, syzygy`
- `StripSyzygyControlledCeiling : Prop := ∀ u, 6 ≤ mcaBadCount … (u 0)(u 1) →
  mcaBadCount … (u 0)(u 1) ≤ 2³⁰`  (the isolated (d) residual)
- `badCountCeiling_of_syzygyControlled (h : StripSyzygyControlledCeiling)
  : SYZ60Dictionary.BadCountCeiling`  (case split: `≤ 5` discharged by the proven cap)
- `countingDictionary_of_syzygyControlled : StripSyzygyControlledCeiling →
  SYZ57Transport.CountingDictionary`  (chained through SYZ60)

## Honest scope

No `δ*` closed. The bridge tightens the residual's *shape*: `BadCountCeiling` is now equivalent (via
SYZ60) to controlling only the syzygy-carrying stacks, and the non-syzygy regime is proven capped at
5 unconditionally. The dependent/syzygy bulk `[6, 2³⁰]` — the SYZ29 `#fresh = 0` + pool-sum
attribution, SYZ56-blocked on the chaining route — is the surviving open (d).
