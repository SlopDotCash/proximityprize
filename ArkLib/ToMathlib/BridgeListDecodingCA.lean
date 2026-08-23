/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting
import ArkLib.Data.CodingTheory.Connections.EpsMCABadGlue
import ArkLib.ToMathlib.Bridge2GCXK25
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bridge lemmas for the list-decoding ↔ correlated-agreement connection (ABF26 §5)

Reusable helper lemmas supporting
`ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean`.

The four ABF26 §5 theorems (`linear_listSize_to_epsMCA_gcxk25`,
`rs_epsCA_small_implies_lambda_lt_F_bchks25`, `rs_epsCA_implies_lambda_extended_cs25`,
`rs_epsCA_separation_bgks20`) bridge the *Grand List-Decoding Challenge* and the *Grand
MCA Challenge*.  Each cites a substantial external counting/probabilistic argument over a
*specific* code construction (deep holes, Frobenius/subfield structure, maximal correlated
agreement domains) whose code-theoretic core is not yet available in-tree.

This file provides:

1. **Trivial-direction error bounds** (`epsCA_le_one`, `epsMCA_le_one`).  Both `ε_ca` and
   `ε_mca` are suprema of PMF probabilities (or `0`), hence bounded by `1`.  These are
   genuine, fully-proven facts reused below.

2. **The CS25 (ABF26 T5.3) contradiction arithmetic** (`cs25_qeps_le_E`).  This is the
   *clean* half of CS25 Theorem 2: given the two numeric hypotheses on `ε := ε_ca.toReal`
   and the slack `η`, the list-size threshold algebra closes.  The genuinely external half
   (the deep-hole + Schwartz–Zippel construction relating `ε_ca` of `RS[k]` to the list of
   `RS[k+1]`, the paper's "Claim 3") is isolated as a named residual hypothesis in the
   companion `_of_residuals` theorem in `ListDecodingAndCA.lean`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- [CS25]  Crites, Stewart. eprint 2025/2046, Theorem 2.
- [GCXK25] Gao, Cai, Xu, Kan. eprint 2025/870, Theorem 3.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory.Bridge

open scoped NNReal
open ProximityGap

section ErrorLeOne

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **`ε_ca ≤ 1`.** The correlated-agreement error is a supremum of values each of which is
either `0` or a PMF probability, hence at most `1`. -/
theorem epsCA_le_one (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) :
    epsCA (F := F) (A := A) C δ_fld δ_int ≤ 1 := by
  classical
  unfold epsCA
  refine iSup_le fun u => ?_
  by_cases h : Code.jointProximity C (u := u) δ_int
  · rw [if_pos h]; exact zero_le_one
  · rw [if_neg h]
    exact pmf_prob_le_one (α := F) _

/-- **`ε_mca ≤ 1`.** The mutual-correlated-agreement error is a supremum of PMF
probabilities, hence at most `1`. -/
theorem epsMCA_le_one (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) C δ ≤ 1 := by
  classical
  unfold epsMCA
  refine iSup_le fun u => ?_
  exact pmf_prob_le_one (α := F) _

end ErrorLeOne

section CS25Arithmetic

/-- **CS25 / ABF26 T5.3 contradiction arithmetic.**

Let `s, m, k : ℝ` with `0 < s`, `1 ≤ k`, `1 ≤ m`, and `0 ≤ η < 1`.  Suppose
`ε` (the real CA error) satisfies the two ABF26 T5.3 numeric hypotheses, rewritten with
`s = q - n`, `q = |F|`:

- `q·ε ≤ η·s/k`   (from `ε ≤ η·(1/k − n/(k·q)) = η·(q−n)/(k·q)`), and
- `q·ε ≤ (1 − η)·m`   (from `m ≥ ⌈q·ε/(1−η)⌉ ≥ q·ε/(1−η)`).

Then `q·ε ≤ E` where `E := m·s/(m·k + s)` is CS25's Claim-3 lower bound on the number of
`λ`-points (divided by `q`).  This is the algebraic heart of the CS25 contradiction:
combining the two caps via `q·ε·(k/s + 1/m) ≤ η + (1 − η) = 1`. -/
theorem cs25_qeps_le_E
    {s m k η qε : ℝ}
    (hs : 0 < s) (hk : (1 : ℝ) ≤ k) (hm : (1 : ℝ) ≤ m)
    (_hη0 : 0 ≤ η) (_hη1 : η < 1)
    (hcap1 : qε ≤ η * s / k)
    (hcap2 : qε ≤ (1 - η) * m) :
    qε ≤ m * s / (m * k + s) := by
  have hmpos : 0 < m := lt_of_lt_of_le one_pos hm
  have hkpos : 0 < k := lt_of_lt_of_le one_pos hk
  have hden : 0 < m * k + s := by positivity
  -- From hcap1: qε ≤ η*s/k  ⇒  k * qε ≤ η * s.
  have h1 : k * qε ≤ η * s := by
    have h := mul_le_mul_of_nonneg_left hcap1 (le_of_lt hkpos)
    have he : k * (η * s / k) = η * s := by field_simp
    rwa [he] at h
  -- From hcap2: qε / m ≤ 1 - η  ⇒  qε ≤ (1 - η) * m  (already have).
  -- Combine: k*qε/s + qε/m ≤ η + (1-η) = 1, i.e. qε*(k*m + s) ≤ m*s.
  have key : qε * (m * k + s) ≤ m * s := by
    -- k*qε ≤ η*s  and  qε ≤ (1-η)*m
    -- multiply first by m, second by s? Use: qε*(m*k+s) = m*(k*qε) + s*qε
    have hA : m * (k * qε) ≤ m * (η * s) := by
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt hmpos)
    have hB : s * qε ≤ s * ((1 - η) * m) := by
      exact mul_le_mul_of_nonneg_left hcap2 (le_of_lt hs)
    calc qε * (m * k + s)
        = m * (k * qε) + s * qε := by ring
      _ ≤ m * (η * s) + s * ((1 - η) * m) := by linarith [hA, hB]
      _ = m * s := by ring
  -- Divide by the positive denominator.
  rw [le_div_iff₀ hden]
  linarith [key]

/-- Strict variant: if additionally `q·ε < (1 − η)·m` (which holds when the ceiling is a
*strict* over-estimate, i.e. `m > q·ε/(1−η)`), then `q·ε < E`.  CS25's contradiction needs
strictness; in the in-tree statement the strictness is supplied by the residual hypothesis,
but this lemma records that the arithmetic itself is strict whenever the second cap is. -/
theorem cs25_qeps_lt_E
    {s m k η qε : ℝ}
    (hs : 0 < s) (hk : (1 : ℝ) ≤ k) (hm : (1 : ℝ) ≤ m)
    (_hη0 : 0 ≤ η) (_hη1 : η < 1)
    (hcap1 : qε ≤ η * s / k)
    (hcap2 : qε < (1 - η) * m) :
    qε < m * s / (m * k + s) := by
  have hmpos : 0 < m := lt_of_lt_of_le one_pos hm
  have hkpos : 0 < k := lt_of_lt_of_le one_pos hk
  have hden : 0 < m * k + s := by positivity
  have h1 : k * qε ≤ η * s := by
    have h := mul_le_mul_of_nonneg_left hcap1 (le_of_lt hkpos)
    have he : k * (η * s / k) = η * s := by field_simp
    rwa [he] at h
  have key : qε * (m * k + s) < m * s := by
    have hA : m * (k * qε) ≤ m * (η * s) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hmpos)
    have hB : s * qε < s * ((1 - η) * m) :=
      mul_lt_mul_of_pos_left hcap2 hs
    calc qε * (m * k + s)
        = m * (k * qε) + s * qε := by ring
      _ < m * (η * s) + s * ((1 - η) * m) := by linarith [hA, hB]
      _ = m * s := by ring
  rw [lt_div_iff₀ hden]
  linarith [key]

end CS25Arithmetic

section GCXK25UnionBound

open ProximityGap Code
open scoped BigOperators ProbabilityTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **GCXK25 per-stack count from a per-codeword count + list-size factor.**

For a fixed stack `(u₀, u₁)`, suppose a finite codeword carrier `T ⊇ C` is given with at most
`B_T` codewords (`|T| ≤ B_T`), and every codeword `w ∈ T` witnesses at most `b` bad combining
points (`|mcaBadWitness C δ u₀ u₁ w| ≤ b`). Then the per-stack bad count is at most `B_T · b`:

  `|mcaBad C δ u₀ u₁| ≤ B_T · b`.

This is the cardinality form of GCXK25's union bound over the close-codeword list. With
`B_T = L²` (the list-size factor) and `b` the per-codeword agree-domain count `δ·n` (GCXK25's
`|Bad¹| ≤ pn`, plus the `1/η` second-moment summand), it yields the `L²·δ·n + 1/η` shape. -/
theorem mcaBad_card_le_listFactor_mul_perCodeword
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (T : Finset (ι → A)) (hT : ∀ w ∈ C, w ∈ T)
    {b B_T : ℝ} (hb0 : 0 ≤ b) (hb_card : (T.card : ℝ) ≤ B_T)
    (hper : ∀ w ∈ T, ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) ≤ b) :
    ((mcaBad (F := F) C δ u₀ u₁).card : ℝ) ≤ B_T * b := by
  have h1 : ((mcaBad (F := F) C δ u₀ u₁).card : ℝ) ≤ (T.card : ℝ) * b :=
    mcaBad_card_le_of_per_codeword C δ u₀ u₁ T hT hb0 hper
  calc ((mcaBad (F := F) C δ u₀ u₁).card : ℝ)
      ≤ (T.card : ℝ) * b := h1
    _ ≤ B_T * b := by exact mul_le_mul_of_nonneg_right hb_card hb0

/-- **Witness-cover form of the GCXK25 union bound.**

This is the same cardinality argument as `mcaBad_card_le_listFactor_mul_perCodeword`, but with
the carrier hypothesis weakened to the exact cover needed for the proof:

  `mcaBad C δ u₀ u₁ ⊆ ⋃ w ∈ T, mcaBadWitness C δ u₀ u₁ w`.

The older theorem obtains this cover from `T ⊇ C`. GCXK25/GKL-style list-decoding applications
instead want `T` to be the finite close-codeword / witness carrier for this stack, whose size is
bounded by `L²`, not the full code. This lemma exposes that lower-level interface directly. -/
theorem mcaBad_card_le_listFactor_mul_perCodeword_cover
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (T : Finset (ι → A))
    (hcover :
      mcaBad (F := F) C δ u₀ u₁ ⊆
        T.biUnion (fun w => mcaBadWitness (F := F) C δ u₀ u₁ w))
    {b B_T : ℝ} (hb0 : 0 ≤ b) (hb_card : (T.card : ℝ) ≤ B_T)
    (hper : ∀ w ∈ T, ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) ≤ b) :
    ((mcaBad (F := F) C δ u₀ u₁).card : ℝ) ≤ B_T * b := by
  classical
  have hsum : ((mcaBad (F := F) C δ u₀ u₁).card : ℝ) ≤
      ∑ w ∈ T, ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) := by
    calc ((mcaBad (F := F) C δ u₀ u₁).card : ℝ)
        ≤ ((T.biUnion (fun w => mcaBadWitness (F := F) C δ u₀ u₁ w)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hcover
      _ ≤ ((∑ w ∈ T, (mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ w ∈ T, ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) := by push_cast; ring
  calc ((mcaBad (F := F) C δ u₀ u₁).card : ℝ)
      ≤ ∑ w ∈ T, ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) := hsum
    _ ≤ ∑ _w ∈ T, b := Finset.sum_le_sum (fun w hw => hper w hw)
    _ = (T.card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ B_T * b := by exact mul_le_mul_of_nonneg_right hb_card hb0

/-- **GCXK25 / ABF26 T5.1 — `ε_mca` bound from a uniform per-codeword bad count.**

The full union-bound reduction: if for *every* stack `u` there is a finite codeword carrier
`T u ⊇ C` of size `≤ B_T`, each codeword of which witnesses at most `b` bad combining points,
then

  `ε_mca(C, δ) ≤ ENNReal.ofReal ((B_T · b) / |F|)`.

This composes the union-bound brick (`mcaBad_card_le_listFactor_mul_perCodeword`) with the
in-tree supremum-to-count glue (`ProximityGap.epsMCA_le_ofReal_of_forall_mcaBad_card_le`). The
two residual ingredients — `B_T = L²` (list-size factor) and `b = δ·n + (1/η)/L²` (per-codeword
agree-domain count = GCXK25's `|Bad¹| ≤ pn` plus second-moment `1/η`) — are exactly GCXK25's two
combinatorial parts, surfaced as named per-codeword data rather than a raw per-stack count. -/
theorem epsMCA_le_ofReal_of_per_codeword_count
    (C : Set (ι → A)) (δ : ℝ≥0)
    {b B_T : ℝ} (hb0 : 0 ≤ b)
    (hcount :
      ∀ u : WordStack A (Fin 2) ι,
        ∃ T : Finset (ι → A), (∀ w ∈ C, w ∈ T) ∧ (T.card : ℝ) ≤ B_T ∧
          ∀ w ∈ T, ((mcaBadWitness (F := F) C δ (u 0) (u 1) w).card : ℝ) ≤ b) :
    epsMCA (F := F) (A := A) C δ ≤ ENNReal.ofReal ((B_T * b) / Fintype.card F) := by
  refine epsMCA_le_ofReal_of_forall_mcaBad_card_le C δ ?_
  intro u
  obtain ⟨T, hT, hcard, hper⟩ := hcount u
  exact mcaBad_card_le_listFactor_mul_perCodeword C δ (u 0) (u 1) T hT hb0 hcard hper

/-- **Exact-shape connector to the read-only `hPerStack` residual of ABF26 Theorem 5.1.**

`linear_listSize_to_epsMCA_gcxk25_of_residuals` (in `Connections/ListDecodingAndCA.lean`) takes a
residual `hPerStack u : Pr_γ[mcaEvent] ≤ ENNReal.ofReal (B/|F|)` for *every* stack `u`. This
connector produces exactly that per-stack probability bound from a *per-codeword* bad-`γ` count
(GCXK25's union bound over the close-codeword list): if a finite carrier `T u ⊇ C` of size `≤ B_T`
has each codeword witnessing at most `b` bad `γ`, then `Pr_γ[mcaEvent] ≤ ofReal((B_T·b)/|F|)`.

Composing the union-bound brick with the per-stack probability glue
(`ProximityGap.mcaEvent_prob_le_of_mcaBad_card_le`), this reduces the caller's GCXK25 residual
to the per-codeword agree-domain count `b` and the list-size factor `B_T` — exactly the two
combinatorial parts (`|Bad¹| ≤ pn` first-moment and the `L²` list-size factor) of GCXK25 Thm 3. -/
theorem mcaEvent_prob_le_ofReal_of_per_codeword_count
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι)
    {b B_T : ℝ} (hb0 : 0 ≤ b)
    (T : Finset (ι → A)) (hT : ∀ w ∈ C, w ∈ T) (hcard : (T.card : ℝ) ≤ B_T)
    (hper : ∀ w ∈ T, ((mcaBadWitness (F := F) C δ (u 0) (u 1) w).card : ℝ) ≤ b) :
    Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ] ≤
      ENNReal.ofReal ((B_T * b) / Fintype.card F) :=
  ProximityGap.mcaEvent_prob_le_of_mcaBad_card_le C δ (u 0) (u 1)
    (mcaBad_card_le_listFactor_mul_perCodeword C δ (u 0) (u 1) T hT hb0 hcard hper)

/-- Probability-level companion to
`mcaBad_card_le_listFactor_mul_perCodeword_cover`. It converts an explicit witness-cover
carrier for one stack into the per-stack `mcaEvent` probability bound consumed by ABF26 T5.1
front doors. -/
theorem mcaEvent_prob_le_ofReal_of_per_codeword_cover
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι)
    {b B_T : ℝ} (hb0 : 0 ≤ b)
    (T : Finset (ι → A))
    (hcover :
      mcaBad (F := F) C δ (u 0) (u 1) ⊆
        T.biUnion (fun w => mcaBadWitness (F := F) C δ (u 0) (u 1) w))
    (hcard : (T.card : ℝ) ≤ B_T)
    (hper : ∀ w ∈ T, ((mcaBadWitness (F := F) C δ (u 0) (u 1) w).card : ℝ) ≤ b) :
    Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ] ≤
      ENNReal.ofReal ((B_T * b) / Fintype.card F) :=
  ProximityGap.mcaEvent_prob_le_of_mcaBad_card_le C δ (u 0) (u 1)
    (mcaBad_card_le_listFactor_mul_perCodeword_cover C δ (u 0) (u 1) T hcover hb0 hcard hper)

end GCXK25UnionBound

end CodingTheory.Bridge

/- Axiom audit for the witness-cover union-bound surfaces. -/
#print axioms CodingTheory.Bridge.mcaBad_card_le_listFactor_mul_perCodeword_cover
#print axioms CodingTheory.Bridge.mcaEvent_prob_le_ofReal_of_per_codeword_cover
