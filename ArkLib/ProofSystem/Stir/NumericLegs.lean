/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.CheckingVerifier

/-!
# STIR Theorem 5.1 — the numeric complexity legs (#301)

Every `stir_main_of_checkingIOP_*` front door carries `stir_main`'s five free-parameter
numeric legs (`hε`/`hM`/`hLen`/`hQin`/`hQpf`) as hypotheses. This file discharges the four
complexity legs by elementary real arithmetic, and the rbr-budget leg `hε` in the (only)
regime where it is elementary — `secpar = 0`, exactly the security level the small-field
regime honestly pins (cf. the HONESTY note on `stir_main_of_checkingIOP_small_field`):

* `hM_leg_of_two_le` — the round-count leg `∃ c > 0, M ≤ c·(log d / log k)` for any
  `k, d ≥ 2` (witness `c = (M+1)·log k / log d`);
* `hM_leg_of_pow_le` — the *sharp* form with `c = 1` when the genuine STIR parameter
  relation `k^M ≤ d` holds (`M·log k = log(k^M) ≤ log d`);
* `hLen_leg` — the proof-length leg, witness `cₖ = proofLen / log d` for `d ≥ 2`;
* `hQin_leg_of_ceil_le` — the input-query leg for any
  `qNumtoInput ≥ ⌈secpar/(−log(1−δ))⌉₊` (the canonical query count);
* `hQpf_leg_of_pos` / `hQpf_leg_of_secpar_zero` — the proof-query leg from positivity of
  the budget bracket, resp. outright at `secpar = 0` where the bracket is `log d > 0`;
* `hε_leg_of_secpar_zero` — the rbr-budget leg at `secpar = 0` (`2^{-0} = 1` dominates any
  sub-unit error). For `secpar > 0` this leg is genuine security content (it is exactly the
  `ε_rbr ≤ 2^{-secpar}` guarantee), NOT an elementary inequality — it stays a hypothesis.

Capstone welds with the numeric legs GONE:

* `stir_main_of_checkingIOP_CA_numeric` — the headline CA-residual front door with only
  `hε` plus the named soundness residuals remaining (`hBridge`/`hCA`/`hPR`);
* `stir_main_of_checkingIOP_small_field_numeric` — the small-field unconditional route with
  NO numeric legs at all: hypotheses are the regime bounds, `secpar = 0` (forced by the
  regime anyway), a sub-unit rbr budget, `2 ≤ degree`, and the canonical query count.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open BigOperators Finset ListDecodable NNReal ReedSolomon VectorIOP OracleComp LinearCode STIR

namespace StirIOP

namespace NumericLegs

/-- Generic positive-budget domination: any natural is at most some coefficient times a
positive budget (witness `cₖ = q / B`). -/
theorem exists_coeff_mul_ge (q : ℕ) {B : ℝ} (hB : 0 < B) (k : ℕ) :
    ∃ cₖ : ℕ → ℝ, (q : ℝ) ≤ cₖ k * B :=
  ⟨fun _ => (q : ℝ) / B, by rw [div_mul_cancel₀ _ hB.ne']⟩

/-- **The `hM` leg, generic form**: for any `k, degree ≥ 2` the round-count bound
`∃ c > 0, M ≤ c·(log degree / log k)` holds (witness `c = (M+1)/(log degree / log k)`). -/
theorem hM_leg_of_two_le {M k degree : ℕ} (hk2 : 2 ≤ k) (hdeg2 : 2 ≤ degree) :
    ∃ c > (0 : ℝ), (M : ℝ) ≤ c * (Real.log degree / Real.log k) := by
  have hlogk : 0 < Real.log k :=
    Real.log_pos (by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hk2)
  have hlogd : 0 < Real.log degree :=
    Real.log_pos (by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hdeg2)
  have hB : 0 < Real.log degree / Real.log k := div_pos hlogd hlogk
  refine ⟨((M : ℝ) + 1) / (Real.log degree / Real.log k), by positivity, ?_⟩
  rw [div_mul_cancel₀ _ hB.ne']
  linarith

/-- **The `hM` leg, sharp form (`c = 1`)**: under the genuine STIR parameter relation
`k^M ≤ degree` (depth bounded by the folding budget), `M ≤ log degree / log k` outright:
`M·log k = log(k^M) ≤ log degree`. -/
theorem hM_leg_of_pow_le {M k degree : ℕ} (hk2 : 2 ≤ k) (hpow : k ^ M ≤ degree) :
    ∃ c > (0 : ℝ), (M : ℝ) ≤ c * (Real.log degree / Real.log k) := by
  have hk1 : (1 : ℝ) < (k : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hk2
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hlogk : 0 < Real.log k := Real.log_pos hk1
  have hcast : ((k : ℝ)) ^ M ≤ (degree : ℝ) := by exact_mod_cast hpow
  have hlog : (M : ℝ) * Real.log k ≤ Real.log degree := by
    rw [← Real.log_pow]
    exact Real.log_le_log (pow_pos hk0 M) hcast
  exact ⟨1, one_pos, by rw [one_mul, le_div_iff₀ hlogk]; exact hlog⟩

/-- **The `hLen` leg**: for `degree ≥ 2` the proof-length bound holds with witness
`cₖ = proofLen / log degree` (the `|ι|` summand is nonnegative slack). -/
theorem hLen_leg {ι : Type} [Fintype ι] {degree proofLen : ℕ} (k : ℕ) (hdeg2 : 2 ≤ degree) :
    ∃ cₖ : ℕ → ℝ, (proofLen : ℝ) ≤ (Fintype.card ι) + (cₖ k) * Real.log degree := by
  have hlog : 0 < Real.log degree :=
    Real.log_pos (by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hdeg2)
  refine ⟨fun _ => (proofLen : ℝ) / Real.log degree, ?_⟩
  rw [div_mul_cancel₀ _ hlog.ne']
  have : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  linarith

/-- **The `hQin` leg**: any query count at least the canonical
`⌈secpar/(−log(1−δ))⌉₊` satisfies `stir_main`'s input-query bound. -/
theorem hQin_leg_of_ceil_le {secpar qNumtoInput : ℕ} {δ : ℝ≥0}
    (h : ⌈(secpar : ℝ) / (-Real.log (1 - δ))⌉₊ ≤ qNumtoInput) :
    (qNumtoInput : ℝ) ≥ (secpar : ℝ) / (-Real.log (1 - δ)) :=
  le_trans (Nat.le_ceil _) (Nat.cast_le.mpr h)

/-- **The `hQpf` leg from bracket positivity**: whenever the proof-query budget bracket is
positive, the leg holds with witness `cₖ = qNumtoProofstr / bracket`. -/
theorem hQpf_leg_of_pos {qNumtoProofstr k secpar degree : ℕ} {R : ℝ}
    (hpos : 0 < Real.log degree + secpar * Real.log (Real.log degree / R)) :
    ∃ cₖ : ℕ → ℝ, (qNumtoProofstr : ℝ) ≤
      (cₖ k) * ((Real.log degree) + secpar * (Real.log ((Real.log degree) / R))) :=
  exists_coeff_mul_ge qNumtoProofstr hpos k

/-- **The `hQpf` leg at `secpar = 0`**: the bracket collapses to `log degree > 0` for
`degree ≥ 2`, so the leg holds outright. -/
theorem hQpf_leg_of_secpar_zero {qNumtoProofstr k secpar degree : ℕ} (R : ℝ)
    (hsec : secpar = 0) (hdeg2 : 2 ≤ degree) :
    ∃ cₖ : ℕ → ℝ, (qNumtoProofstr : ℝ) ≤
      (cₖ k) * ((Real.log degree) + secpar * (Real.log ((Real.log degree) / R))) := by
  subst hsec
  have hlog : 0 < Real.log degree :=
    Real.log_pos (by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hdeg2)
  exact hQpf_leg_of_pos (by simpa using hlog)

/-- **The `hε` leg at `secpar = 0`**: a sub-unit round-by-round budget satisfies
`ε_rbr ≤ 2^{-secpar}` when `secpar = 0`. For `secpar > 0` this leg is the genuine security
guarantee, not an elementary inequality. -/
theorem hε_leg_of_secpar_zero {A : Type*} {secpar : ℕ} (hsec : secpar = 0)
    {ε_rbr : A → ℝ≥0} (hone : ∀ i, ε_rbr i ≤ 1) :
    ∀ i, ε_rbr i ≤ (1 : ℚ≥0) / (2 ^ secpar) := by
  subst hsec
  intro i
  simpa using hone i

end NumericLegs

section CheckingFrontDoors

open MultiRound VectorIOP LinearCode ReedSolomon STIR NNReal Finset NumericLegs
open ArkLib.ProofSystem.Stir.ErrorAccumulation

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

/-- **Theorem 5.1 through the CHECKING IOPP with the complexity legs DISCHARGED**: as
`stir_main_of_checkingIOP_CA`, but `hM`/`hLen`/`hQin`/`hQpf` are produced by the elementary
numeric-leg lemmas from `2 ≤ degree` (with `2 ≤ k` from `hkGe`) and the canonical input-query
count. Remaining hypotheses: the named soundness residuals (`hBridge`/`hCA`/`hPR`) and the
genuine security leg `hε`. -/
theorem stir_main_of_checkingIOP_CA_numeric
    {M : ℕ} (secpar : ℕ)
    {ι : Type} [Fintype ι] [Nonempty ι]
    {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ]
    {k proofLen qNumtoInput qNumtoProofstr : ℕ}
    (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
    (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
    (hF : Fintype.card F ≤
          secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι) ^ (7 / 2) /
            Real.log (1 / rate (code φ degree)))
    (ε_rbr : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0)
    (e ProxGapBound : Fin (M + 1) → ℝ≥0)
    (hBridge : stirCheckingCABridge M φ degree δ ε_rbr e ProxGapBound)
    (hCA : ∀ k' : ℕ, 0 < k' →
      ProximityGap.StrictCoeffPolysResidual (ι := ι) (F := F)
        (k := k') (deg := degree) (domain := φ) (δ := δ))
    (hPR : PerRoundProximityGap e ProxGapBound)
    (hε : ∀ i, ε_rbr i ≤ (1 : ℚ≥0) / (2 ^ secpar))
    (hdeg2 : 2 ≤ degree)
    (hQpfPos : 0 < Real.log degree +
      secpar * Real.log (Real.log degree / Real.log (1 / rate (code φ degree))))
    (hQceil : ⌈(secpar : ℝ) / (-Real.log (1 - δ))⌉₊ ≤ qNumtoInput) :
    stir_main (M := M) (proofLen := proofLen) (qNumtoInput := qNumtoInput)
      (qNumtoProofstr := qNumtoProofstr) secpar hk hkGe δ hδub hF :=
  stir_main_of_checkingIOP_CA secpar hk hkGe δ hδub hF ε_rbr
    e ProxGapBound hBridge hCA hPR hε
    (hM_leg_of_two_le (le_trans (by norm_num) hkGe) hdeg2)
    (hLen_leg k hdeg2)
    (hQin_leg_of_ceil_le hQceil)
    (hQpf_leg_of_pos hQpfPos)

/-- **Theorem 5.1 through the CHECKING IOPP, small-field route, NO numeric legs**: the
small-field unconditional soundness discharge with all five of `stir_main`'s free-parameter
legs produced by elementary arithmetic. Inputs: the regime bounds (`hδudr`/`hq`/`hεlb`),
`secpar = 0` (the level the regime honestly pins — cf. the HONESTY note on
`stir_main_of_checkingIOP_small_field`), a sub-unit rbr budget, `2 ≤ degree`, and the
canonical input-query count. -/
theorem stir_main_of_checkingIOP_small_field_numeric
    {M : ℕ} (secpar : ℕ)
    {ι : Type} [Fintype ι] [Nonempty ι]
    {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ] [NeZero degree]
    {k proofLen qNumtoInput qNumtoProofstr : ℕ}
    (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
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
    (hsec : secpar = 0)
    (hone : ∀ i, ε_rbr i ≤ 1)
    (hdeg2 : 2 ≤ degree)
    (hQceil : ⌈(secpar : ℝ) / (-Real.log (1 - δ))⌉₊ ≤ qNumtoInput) :
    stir_main (M := M) (proofLen := proofLen) (qNumtoInput := qNumtoInput)
      (qNumtoProofstr := qNumtoProofstr) secpar hk hkGe δ hδub hF :=
  stir_main_of_checkingIOP_small_field secpar hk hkGe δ hδub hF hδudr hq ε_rbr hεlb
    (hε_leg_of_secpar_zero hsec hone)
    (hM_leg_of_two_le (le_trans (by norm_num) hkGe) hdeg2)
    (hLen_leg k hdeg2)
    (hQin_leg_of_ceil_le hQceil)
    (hQpf_leg_of_secpar_zero _ hsec hdeg2)

end CheckingFrontDoors

end StirIOP

/-! ## Axiom audit — all kernel-clean. -/
#print axioms StirIOP.NumericLegs.exists_coeff_mul_ge
#print axioms StirIOP.NumericLegs.hM_leg_of_two_le
#print axioms StirIOP.NumericLegs.hM_leg_of_pow_le
#print axioms StirIOP.NumericLegs.hLen_leg
#print axioms StirIOP.NumericLegs.hQin_leg_of_ceil_le
#print axioms StirIOP.NumericLegs.hQpf_leg_of_pos
#print axioms StirIOP.NumericLegs.hQpf_leg_of_secpar_zero
#print axioms StirIOP.NumericLegs.hε_leg_of_secpar_zero
#print axioms StirIOP.stir_main_of_checkingIOP_CA_numeric
#print axioms StirIOP.stir_main_of_checkingIOP_small_field_numeric
