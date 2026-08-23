/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCountRatio

/-!
# The radius-one middle band: the two-regime cardinality bracket and the refuted
threshold law (Issue #39, §7 of `MIDDLE_BAND_RESOLUTION.md`)

Fix a Reed–Solomon code `RS[F, domain, k]` with `n := |ι|` distinct evaluation points over a
prime field `F = F_q`, `q := |F|`. At radius `δ = 1` the mutual-correlated-agreement error is
*exactly* the normalised bad-scalar count (`MCABadCount.lean`):

  `ε_mca(C, 1) = (⨆ (u₀,u₁), mcaBadCount C 1 u₀ u₁) / q`.

The **extremal count** `P(n,k,q) := max_{u₀,u₁} mcaBadCount(RS, 1, u₀, u₁)` is framed between two
**kernel-proven** bounds, both per-stack and both already in tree:

* **(UB) the `(k+1)`-subset cap** `mcaBadCount ≤ C(n, k+1)` — every bad `γ` selects a distinct
  `(k+1)`-subset (`MCABadCountRatio.mcaBadCount_one_le_choose`, the count-level form of
  `GrandChallengeRadiusOne.epsMCA_one_le_choose_div`).
* **(CARD) the cardinality cap** `mcaBadCount ≤ q` — only `q` scalars exist. This is the trivial
  but load-bearing bound; it gives `P(n,k,q) ≤ q` and hence the cardinality necessity
  `q*(n,k) ≥ smallest prime ≥ C(n, k+1)`.

## Main results

* `mcaBadCount_le_card_field` — **(CARD), fully general** (any code, any radius `δ`): the
  bad-scalar count is a cardinality of a subset of `Finset.univ : Finset F`, so
  `mcaBadCount C δ u₀ u₁ ≤ Fintype.card F`.
* `mcaBadCount_le_min` — **the two-regime bracket** for RS codes at radius `1`:
  `mcaBadCount(RS, 1, u₀, u₁) ≤ min (C(n, k+1)) q`, matching the doc's `P ≤ min(C(n,k+1), q)`
  (with equality for large `q`, `epsMCA_one_eq_choose_div`).

## Statement-defect record (F-series convention)

The prior wave conjectured the single-formula threshold law

  **(C0)** `q*(n,k) = smallest prime ≥ C(n, k+1)`.

`MIDDLE_BAND_RESOLUTION.md` §3 establishes, by an **unconditional exhaustive `q⁶`-pair sweep**,
that (C0) is **REFUTED**: for `(n,k) = (6,3)`, `C(6,4) = 15`, smallest prime `≥ 15` is `17`, yet

  `P(6,3,17) = 14`  and  `P(6,3,19) = 14`  (both `= C − 1`),

so the first `q` attaining `C = 15` is `q* = 23 ≠ 17`. Moreover `(6,1)` and `(6,3)` share
`C(n,k+1) = 15` but have `q*(6,1) = 17 ≠ 23 = q*(6,3)`, so `q*` is **not a function of `C` alone**.
Only the necessity direction `q*(n,k) ≥ smallest prime ≥ C(n, k+1)` (the content of
`mcaBadCount_le_card_field`) survives. Following the F-series statement-defect catalogue
convention (cf. `LineDecodingRefutation.lean`, `GrandChallengeCollapse.lean`), the refuted law is
recorded here only as a `def` + docstring — `mcaThresholdLawC0` together with the verdict
`mcaThresholdLawC0_refuted` — so the false **sufficiency** direction can never silently regress
into a theorem. It is deliberately *not* proved.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. §1, §4.3.
- `MIDDLE_BAND_RESOLUTION.md` (Issue #39 resolution writeup), §1, §3, §7.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

section CardinalityCap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **(CARD) the cardinality cap — the trivial-but-load-bearing bound.** For *any* code `C` and
*any* radius `δ`, the bad-scalar count is at most the number of field elements: it is the
cardinality of a subset of `Finset.univ : Finset F`. Specialised to `P(n,k,q) ≤ q`, this is the
only fully proven part of the refuted threshold law (C0): it yields the necessity direction
`q*(n,k) ≥ smallest prime ≥ C(n, k+1)` (you cannot realise `C` distinct bad scalars in `F_q` when
`q < C`). See `MIDDLE_BAND_RESOLUTION.md` §1 (CARD) and §3.3 (PROVEN cardinality necessity). -/
theorem mcaBadCount_le_card_field (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    mcaBadCount (F := F) C δ u₀ u₁ ≤ Fintype.card F := by
  classical
  unfold mcaBadCount
  calc (Finset.univ.filter (fun γ : F => mcaEvent C δ u₀ u₁ γ)).card
      ≤ (Finset.univ : Finset F).card := Finset.card_filter_le _ _
    _ = Fintype.card F := Finset.card_univ

end CardinalityCap

section MiddleBandBracket

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open ReedSolomon

/-- **The two-regime bracket `P(n,k,q) ≤ min(C(n,k+1), q)`.** Composing the `(k+1)`-subset cap
(UB, `mcaBadCount_one_le_choose`, the count-level form of `epsMCA_one_le_choose_div`) with the
cardinality cap (CARD, `mcaBadCount_le_card_field`) gives, per stack `(u₀, u₁)`,

  `mcaBadCount(RS[F, domain, k], 1, u₀, u₁) ≤ min (C(n, k+1)) (Fintype.card F)`.

This is the doc's framing bound `P(n,k,q) ≤ min(C(n,k+1), q)`, tight from both sides: for
`q < C(n,k+1)` the right (CARD) term binds and is attained (`P = q`, sub-`C` regime), while for
large `q` the left (UB) term binds and is attained (`epsMCA_one_eq_choose_div`). The undecided
**middle band** is exactly where neither extremal coincidence is forced. -/
theorem mcaBadCount_le_min (domain : ι ↪ F) (k : ℕ) (u₀ u₁ : ι → F) :
    mcaBadCount (F := F) (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ u₁ ≤
      min ((Fintype.card ι).choose (k + 1)) (Fintype.card F) :=
  le_min (mcaBadCount_one_le_choose domain k u₀ u₁)
    (mcaBadCount_le_card_field _ 1 u₀ u₁)

end MiddleBandBracket

section ThresholdLawDefect

/-- **Statement-defect record: the refuted single-formula threshold law (C0).** For a Reed–Solomon
code on `n` points with degree budget `k`, this is the *proposition* asserting the prior-wave
conjecture that the threshold field size `q*(n,k)` (the least prime `q` at which the radius-one
extremal bad-scalar count `P(n,k,q)` attains the `(k+1)`-subset cap `C(n,k+1)`) equals the smallest
prime `≥ C(n, k+1)`:

  `mcaThresholdLawC0 n k qStar  :≡  (qStar = Nat.nth Nat.Prime _  with  C(n,k+1) ≤ qStar minimal)`.

Encoded operationally as: `qStar` is prime, `C(n, k+1) ≤ qStar`, and `qStar` is the *least* such
prime. **This proposition is FALSE as a universal law** — see `mcaThresholdLawC0_refuted`. It is
recorded as a `def` (never a theorem) so the false **sufficiency** direction of (C0) cannot
silently regress into a proved statement, mirroring the F-series statement-defect convention
(`LineDecodingRefutation.lean`). The only surviving direction is the necessity
`qStar ≥ smallest prime ≥ C(n, k+1)`, formalized in fact form by `mcaBadCount_le_card_field`. -/
def mcaThresholdLawC0 (n k qStar : ℕ) : Prop :=
  Nat.Prime qStar ∧
    (n.choose (k + 1) ≤ qStar) ∧
    (∀ p : ℕ, Nat.Prime p → n.choose (k + 1) ≤ p → qStar ≤ p)

/-- **The (6,3) counterexample data — REFUTATION of (C0), `MIDDLE_BAND_RESOLUTION.md` §3.1.**
`C(6, 4) = 15`; the smallest prime `≥ 15` is `17`, so (C0) predicts `q*(6,3) = 17`. The doc's
**unconditional exhaustive `q⁶`-pair sweep** (`q⁶ ≈ 24M` at `q = 17`, `≈ 47M` at `q = 19`; no
search gap) computes the radius-one extremal count exactly as

  `P(6,3,17) = 14 = C − 1`   and   `P(6,3,19) = 14 = C − 1`,

i.e. `C = 15` is **not** attained at the predicted `q = 17` (nor at `19`). The actual threshold is
`q*(6,3) = 23` (a construction attains `15` at `23`, and there is no prime in `(19, 23)`). Hence
the `qStar = 17` instance of `mcaThresholdLawC0` is **false**: `17` satisfies the prime and
`C ≤ qStar` clauses but is *not* the attainment threshold, so the conjectured *sufficiency*
("smallest prime `≥ C` already attains `C`") fails. This is recorded as a docstring fact, not a
machine-checked sweep (the optional `Decidable`/`decide` reflection of the `q⁶` sweep is the
queued follow-up, §7); the bracket `mcaBadCount_le_min` is the proved content. -/
def mcaThresholdLawC0_refuted : Prop :=
  -- The witness `(n, k) = (6, 3)`: `C(6,4) = 15`, predicted `q* = 17`, observed `q* = 23`.
  (Nat.choose 6 4 = 15) ∧ (Nat.choose 6 4 = Nat.choose 6 2)

/-- `C(6,1) = C(6,3) = 15` yet `q*(6,1) = 17 ≠ 23 = q*(6,3)`: the threshold field size `q*` is
**not a function of `C(n,k+1)` alone** (`MIDDLE_BAND_RESOLUTION.md` §3.2). The arithmetic core —
that the two `(n,k)` cases genuinely share the same `(k+1)`-subset count — is the decidable
identity `C(6, 2) = C(6, 4)` (both `= 15`), recorded here so the "function of `C` alone" reading of
(C0) is visibly contradicted by data, not merely asserted. -/
theorem choose_six_two_eq_choose_six_four : Nat.choose 6 2 = Nat.choose 6 4 := by decide

end ThresholdLawDefect

end ProximityGap
