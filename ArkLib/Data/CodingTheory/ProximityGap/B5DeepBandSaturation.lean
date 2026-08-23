/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMomentInstance

/-!
# B5 — the deep-band second-moment saturation law (#389, boundary regime n ≈ √p)

This file proves the **B5 brick** as a single clean law plus its non-vacuity witness,
building only on the in-tree second-moment substrate
(`DeepBandSecondMoment.lean`: `sum_N2_le`, `deep_band_badSet_card_of_moments`,
`budget_of_numeric`, `deepPairs_card_le`; `DeepBandMomentInstance.lean`:
`budget_instance`).

## What B5 asserts

> For the boundary regime `n ≈ √p`, the deep-band second-moment saturation shows
> **every band radius admits a stack with `≥ V / L²` distinct bad scalars**, where
> `V` is the moment budget and `L` controls coherent-core overlap.

The mechanism (proven in the substrate, recapped here):

* `sum_N2_le` partitions the coherent-pair second moment into a small-overlap
  stratum (exact fiber `q^{M−(2m+1)}`) and a deep-pair / diagonal stratum
  (per-core fiber `q^{M−m}`), so the second moment is closed-form in
  `(n, k, m, q, M)`.
* The integer Cauchy–Schwarz step (`value_count_quadratic`,
  `2 L N₁ ≤ N₂ + #values · L²`) plus pigeonhole over the `q^M` generators turns a
  budget surplus into one generator whose coherent cores take **`≥ V / L²`
  distinct values** (`exists_generator_many_values`).
* Each distinct value `−coeff_k(I_T(Qc))` is a *certified* bad scalar
  (`mcaEvent_of_coherent`), so the value count is a bad-scalar count
  (`deep_band_badSet_card_of_moments`).

## The theorems

* `B5_deepBand_saturation_law` — the literal B5 statement: at **every** band
  radius `δ` (`(1−δ)·n ≤ k+m+1`), whenever the moment budget clears for `(L, V)`,
  some stack `(Q₀∘dom, x^k)` carries scalars `γ` each satisfying `mcaEvent`, with
  `V ≤ #{bad γ} · L²` (i.e. at least `V / L²` distinct bad scalars).

* `B5_deepBand_saturation_binomial` — the same law with the budget hypothesis
  replaced by the **pure-numeric** form
  `P²·q^{M−(2m+1)} + (D + P)·q^{M−m} + V·q^M ≤ 2L·P·q^{M−m}` (with
  `D ≤ P·C(k+m+1,k+1)·C(n−(k+1),m)` from `B5_deepPairs_binomial`), i.e. one
  binomial inequality in.

* `B5_deepBand_saturation_unconditional` — the **non-vacuity witness** at the
  boundary point `RS[F₁₃₁, {0,…,127}, k = 2]`, band `m = 1` (radius `δ = 31/32`,
  one granularity step below capacity `63/64`), `(M, L, V) = (8, 1050, 79 591 252)`:
  a concrete stack carries **`≥ 73` distinct certified bad scalars**
  (`73 / 131 ≈ 0.557` of the field — a *constant* fraction, the saturation the
  probe `probe_pair_coherence_rank.py` measures as median `#values = q`).  No
  hypotheses.

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## The literal B5 saturation law (budget-conditional, every band radius) -/

open Classical in
/-- **B5 — the deep-band saturation law.**  Fix an evaluation domain `dom`, a
code rate `k ≥ 1`, a band depth `m`, a generator width `M ≥ 2(k+m+1)`, and moment
parameters `(L, V)`.  Then at **every** band radius `δ` with
`(1−δ)·n ≤ k+m+1`, if the second-moment budget clears

  `P²·q^{M−(2m+1)} + (D + P)·q^{M−m} + V·q^M ≤ 2L·∑_c #coh(c)`

(`P = C(n,k+m+1)`, `D` the deep-pair count, `q = |F|`), then some stack
`(Q₀∘dom, x^k)` carries scalars `γ` **each a certified MCA failure**
(`mcaEvent` at `δ`) with `V ≤ #{bad γ} · L²` — at least `V / L²` distinct bad
scalars.

The content: the strata-partitioned second moment (`sum_N2_le`), the fiberwise
integer Cauchy–Schwarz (`value_count_quadratic`), pigeonhole over the `q^M`
generators (`exists_generator_many_values`), and the coherent-core ⇒ bad-scalar
certificate (`mcaEvent_of_coherent`). -/
theorem B5_deepBand_saturation_law (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) {L V : ℕ}
    (hbudget :
      ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2
          * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
            (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card
          + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card)
          * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (∑ c : Fin M → F,
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
            (fun T => IsCoherent dom k m T (genPoly c))).card)) :
    ∃ Q₀ : F[X],
      V ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
          * L ^ 2 :=
  deep_band_badSet_card_of_moments dom hk hhi hM hbudget

/-! ## The budget as one binomial inequality -/

/-- **B5 — the deep-pair count is binomial.**  Recap of `deepPairs_card_le`:
the deep-pair count `D` (distinct `(k+m+1)`-cores with overlap `> k`) obeys
`D ≤ P · C(k+m+1, k+1) · C(n−(k+1), m)`, the only non-leading-term contribution
to the binomial budget. -/
theorem B5_deepPairs_binomial (k m : ℕ) :
    (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
        (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
        (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card)
      ≤ ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
        * ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m) :=
  deepPairs_card_le k m

open Classical in
/-- **B5 — saturation from one binomial inequality.**  The same law as
`B5_deepBand_saturation_law`, but with the budget supplied in the **pure-numeric**
closed form

  `P²·q^{M−(2m+1)} + (D + P)·q^{M−m} + V·q^M ≤ 2L·P·q^{M−m}`,

reusing the exact first-moment `S₁ = P·q^{M−m}` (`budget_of_numeric` via
`sum_N1_eq`).  Combined with the deep-pair count bound `B5_deepPairs_binomial`
this is a single arithmetic obligation in `(n,k,m,q,M,L,V)`. -/
theorem B5_deepBand_saturation_binomial (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) {L V : ℕ}
    (hnum :
      ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2
          * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
            (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card
          + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card)
          * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
          * (Fintype.card F) ^ (M - m))) :
    ∃ Q₀ : F[X],
      V ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
          * L ^ 2 :=
  B5_deepBand_saturation_law dom hk hhi hM (budget_of_numeric dom k m hM hnum)

end ProximityGap.PairRank

/-! ## The non-vacuity witness at the boundary regime n ≈ √p -/

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

open Classical in
/-- **B5 — the saturation is non-vacuous at the boundary regime.**  At the
boundary point `RS[F₁₃₁, {0,…,127}, k = 2]`, band depth `m = 1` (radius
`δ = 31/32`, one granularity step **below** the capacity radius `63/64`),
generator width `M = 8`, and moment parameters `(L, V) = (1050, 79 591 252)`,
the law fires with **no hypotheses**: some stack carries at least

  `⌈V / L²⌉ = ⌈79 591 252 / 1050²⌉ = 73`

distinct certified bad scalars — a *constant fraction* `73 / 131 ≈ 0.557` of the
field, matching the probe's median `#values = q`.  (`72·L² = 79 380 000 < V`
strictly, so the count exceeds `72`.)

The budget is exactly `budget_instance` (the single binomial inequality
`P²·131⁵ + (D + P)·131⁷ + V·131⁸ ≤ 2L·P·131⁷` with `P = C(128,4) = 10 668 000`,
`D ≤ 5 334 000 000`), discharged in tree by `norm_num`. -/
theorem B5_deepBand_saturation_unconditional :
    ∃ Q₀ : F131[X],
      (73 : ℕ) ≤ (Finset.univ.filter (fun γ : F131 => mcaEvent (F := F131)
            ((rsCode dom131 2 : Submodule F131 (Fin 128 → F131)) :
              Set (Fin 128 → F131)) (31/32)
            (fun i => Q₀.eval (dom131 i)) (fun i => (dom131 i) ^ 2) γ)).card := by
  -- the band-radius geometric constraint  (1 − 31/32)·128 ≤ 4
  have hhi : (1 - (31/32 : ℝ≥0)) * (Fintype.card (Fin 128) : ℝ≥0)
      ≤ ((2 + 1 + 1 : ℕ) : ℝ≥0) := by
    have h132 : (1 : ℝ≥0) - 31/32 = 1/32 := by
      rw [tsub_eq_iff_eq_add_of_le (by
        rw [div_le_one (by norm_num : (0:ℝ≥0) < 32)]
        norm_num)]
      rw [← NNReal.coe_inj]
      push_cast
      norm_num
    rw [h132, Fintype.card_fin]
    rw [← NNReal.coe_le_coe]
    push_cast
    norm_num
  -- the moment budget clears (the single binomial inequality, `budget_instance`)
  obtain ⟨Q₀, hQ₀⟩ :=
    B5_deepBand_saturation_binomial (m := 1) (M := 8) (L := 1050) (V := 79591252)
      dom131 (by norm_num) hhi (by norm_num) budget_instance
  refine ⟨Q₀, ?_⟩
  -- hQ₀ : 79591252 ≤ #bad · 1050²;  72·1050² = 79380000 < 79591252 ⟹ 73 ≤ #bad
  set b := (Finset.univ.filter (fun γ : F131 => mcaEvent (F := F131)
      ((rsCode dom131 2 : Submodule F131 (Fin 128 → F131)) :
        Set (Fin 128 → F131)) (31/32)
      (fun i => Q₀.eval (dom131 i)) (fun i => (dom131 i) ^ 2) γ)).card with hb
  have hpow : (1050 : ℕ) ^ 2 = 1102500 := by norm_num
  rw [hpow] at hQ₀
  -- 79591252 ≤ b * 1102500
  by_contra hlt
  rw [Nat.not_le] at hlt   -- hlt : b < 73, i.e. b ≤ 72
  have hb72 : b ≤ 72 := by omega
  have : b * 1102500 ≤ 72 * 1102500 := Nat.mul_le_mul_right _ hb72
  omega

/-- **B5 — the saturation value is a constant fraction of the field.**  At the
boundary witness, `⌈V / L²⌉ = 73` (since `72·L² < V`) and `73 / q = 73 / 131
≈ 0.557`: a *constant* share of all scalars are certified bad one step below
capacity (not `O(n)/q`, the silent regime of the per-word supply wall this issue
tracks). -/
theorem B5_saturation_exceeds_72 : 72 * 1050 ^ 2 < 79591252 := by norm_num

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.B5_deepBand_saturation_law
#print axioms ProximityGap.PairRank.B5_deepPairs_binomial
#print axioms ProximityGap.PairRank.B5_deepBand_saturation_binomial
#print axioms ProximityGap.PairRank.B5_deepBand_saturation_unconditional
#print axioms ProximityGap.PairRank.B5_saturation_exceeds_72
