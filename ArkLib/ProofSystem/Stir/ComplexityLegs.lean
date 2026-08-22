/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.CheckingVerifier

/-!
# STIR Theorem 5.1: the numeric complexity legs, discharged

`StirIOP.stir_main` (Theorem 5.1, `MainThm.lean`) packages four "complexity" conjuncts
alongside the security claim:

* `∃ c > 0, M ≤ c * (log degree / log k)` (round count),
* `∃ cₖ, proofLen ≤ |ι| + cₖ k * log degree` (proof length),
* `qNumtoInput ≥ secpar / (−log(1−δ))` (input queries),
* `∃ cₖ, qNumtoProofstr ≤ cₖ k * (log degree + secpar·log(log degree / log(1/ρ)))`
  (proof-string queries).

Every existing `stir_main_of_*` front door consumes these as free hypotheses
(`hM`/`hLen`/`hQin`/`hQpf`). This file discharges the three existentially-quantified legs and
records an **honest vacuity finding**: because the constants `c`/`cₖ` are existentially
quantified with no uniformity across instances, each of those three legs is satisfiable for
*any* values of `M`, `proofLen`, `qNumtoProofstr` as soon as the relevant logarithm is
positive (`2 ≤ degree`, `2 ≤ k`, resp. a positive query-budget bracket). They are
*per-instance* constraints only; the asymptotic `O(·)` content of Theorem 5.1 is **not**
captured by this formalization shape (that would require quantifying `c` before the instance
family). The `hQin` leg is a genuine per-instance constraint on `qNumtoInput` and is kept as
a hypothesis.

* `complexityLeg_rounds` / `complexityLeg_proofLen` / `complexityLeg_queries` — the generic
  dischargers.
* `stir_main_of_checkingIOP_small_field_auto` — the unconditional small-field Theorem 5.1
  front door with the three existential legs supplied automatically (hypothesis surface:
  `2 ≤ degree`, `2 ≤ k` (implied by `k ≥ 4`), a positive proof-query bracket, and the
  genuine `hQin`/`hε`/regime hypotheses).

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

namespace StirIOP

open NNReal ReedSolomon LinearCode MultiRound STIR

/-- **Round-count leg.** For any `M`, as soon as `2 ≤ degree` and `2 ≤ k` (so both logs are
positive), there is a constant `c > 0` with `M ≤ c · (log degree / log k)`. Existential-form
vacuity: `c := (M+1)·log k / log degree` always works. -/
theorem complexityLeg_rounds (M degree k : ℕ) (hdeg : 2 ≤ degree) (hk : 2 ≤ k) :
    ∃ c > 0, (M : ℝ) ≤ c * (Real.log degree / Real.log k) := by
  have hld : 0 < Real.log degree := Real.log_pos (by exact_mod_cast hdeg)
  have hlk : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk)
  refine ⟨((M : ℝ) + 1) * Real.log k / Real.log degree, by positivity, ?_⟩
  have key : ((M : ℝ) + 1) * Real.log k / Real.log degree * (Real.log degree / Real.log k)
      = (M : ℝ) + 1 := by
    field_simp
  rw [key]
  linarith

/-- **Proof-length leg.** For any `proofLen`, as soon as `2 ≤ degree`, there is a coefficient
function `cₖ` with `proofLen ≤ |ι| + cₖ k · log degree`. Existential-form vacuity:
`cₖ := fun _ => proofLen / log degree` always works. -/
theorem complexityLeg_proofLen (proofLen cardι degree k : ℕ) (hdeg : 2 ≤ degree) :
    ∃ cₖ : ℕ → ℝ, (proofLen : ℝ) ≤ (cardι : ℝ) + (cₖ k) * Real.log degree := by
  have hld : 0 < Real.log degree := Real.log_pos (by exact_mod_cast hdeg)
  refine ⟨fun _ => (proofLen : ℝ) / Real.log degree, ?_⟩
  rw [div_mul_cancel₀ _ (ne_of_gt hld)]
  have : (0 : ℝ) ≤ (cardι : ℝ) := Nat.cast_nonneg _
  linarith

/-- **Query-budget leg (generic).** For any query count `q` and any positive budget bracket
`B`, there is a coefficient function `cₖ` with `q ≤ cₖ k · B`. Existential-form vacuity:
`cₖ := fun _ => q / B` always works. -/
theorem complexityLeg_queries (q k : ℕ) {B : ℝ} (hB : 0 < B) :
    ∃ cₖ : ℕ → ℝ, (q : ℝ) ≤ (cₖ k) * B :=
  ⟨fun _ => (q : ℝ) / B, by rw [div_mul_cancel₀ _ (ne_of_gt hB)]⟩

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

/-- **Theorem 5.1 through the CHECKING IOPP, small-field route, complexity legs supplied.**
The unconditional small-field front door `stir_main_of_checkingIOP_small_field` with the three
existentially-quantified complexity legs (`hM`/`hLen`/`hQpf`) discharged by the generic
dischargers above. Remaining hypothesis surface: the regime hypotheses (`hδudr`/`hq`), the rbr
budget facts (`hεlb`/`hε`), the genuine per-instance query constraint `hQin`, the degree bound
`2 ≤ degree`, and the positive proof-query bracket `hB` (the bracket can be nonpositive for
tiny rates, so it stays a hypothesis). The HONESTY caveat of the underlying route applies
verbatim: in this small-field regime `hε` + `hεlb` pin `secpar = 0`. -/
theorem stir_main_of_checkingIOP_small_field_auto
    {M : ℕ} (secpar : ℕ)
    {ι : Type} [Fintype ι] [Nonempty ι]
    {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ] [NeZero degree]
    {k qNumtoInput : ℕ} (proofLen qNumtoProofstr : ℕ)
    (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4) (hdeg : 2 ≤ degree)
    (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
    (hF : Fintype.card F ≤
          secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι) ^ (7 / 2) /
            Real.log (1 / rate (code φ degree)))
    {m : ℕ}
    (hδudr : δ ≤ (1 - (LinearCode.rate (code φ degree) : ℝ≥0)) / 2)
    (hq : (Fintype.card F : ℝ≥0) ≤ ((m : ℝ≥0) - 1) * (Fintype.card ι : ℝ≥0))
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (hεlb : ∀ i : (stirMultiVSpec M ι).ChallengeIdx, (i.1 : ℕ) = 0 →
      proximityError F degree (LinearCode.rate (code φ degree)) δ m ≤ ε_rbr i)
    (hε : ∀ i, ε_rbr i ≤ (1 : ℚ≥0) / (2 ^ secpar))
    (hQin : (qNumtoInput : ℝ) ≥ secpar / (-Real.log (1 - δ)))
    (hB : 0 < (Real.log degree) +
      secpar * (Real.log ((Real.log degree) / Real.log (1 / rate (code φ degree))))) :
    stir_main (M := M) (proofLen := proofLen) (qNumtoInput := qNumtoInput)
      (qNumtoProofstr := qNumtoProofstr) secpar hk hkGe δ hδub hF :=
  stir_main_of_checkingIOP_small_field secpar hk hkGe δ hδub hF hδudr hq ε_rbr hεlb hε
    (complexityLeg_rounds M degree k hdeg (by omega))
    (complexityLeg_proofLen proofLen (Fintype.card ι) degree k hdeg)
    hQin
    (complexityLeg_queries qNumtoProofstr k hB)

end StirIOP

/-! ## Axiom audit — all kernel-clean. -/
#print axioms StirIOP.complexityLeg_rounds
#print axioms StirIOP.complexityLeg_proofLen
#print axioms StirIOP.complexityLeg_queries
#print axioms StirIOP.stir_main_of_checkingIOP_small_field_auto
