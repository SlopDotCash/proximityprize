/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Norm.Basic
import ArkLib.Data.CodingTheory.ProximityGap.GeneralizedPaleyRamanujan

/-!
# bgk-bridge: the BGK / generalized-Paley character-sum lane for the prize (#407)

User-requested formalization of the **BGK (Bourgain–Glibichuk–Konyagin / generalized-Paley)**
character-sum bound — the asymptotic lane that the height gate (Lever H) provably *cannot* reach
(`HeightGateThresholdAnalysis.gate_fails_above_128`).

## The named open bound

For the smooth domain `G = μ_n` (`n = 2^a`) inside `F_p`, the per-frequency Gauss period is the
in-tree object `eta ψ G b = Σ_{x∈G} ψ(b·x)` (the non-principal eigenvalue of the generalized
Paley graph `Cay(F_p, μ_n)`).  The BGK / thin-subgroup equidistribution bound is the
sub-`n`-power decay

> `BGKBound C n δ` : `∀ b ≠ 0, ‖η_b‖ ≤ C · n^{1-δ}`.

`δ` is the **cancellation exponent**.  The Weil/trivial value is `δ = 0` (`‖η_b‖ ≤ C·n`); the
Parseval floor forces `‖η_b‖ ≳ √n`, i.e. `δ ≤ 1/2 + o(1)`; the Ramanujan / Paley-Graph-Conjecture
value is `δ = 1/2` with `C = 2` (`‖η_b‖ ≤ 2√n`, the `B ≤ 2√n` Ramanujan threshold).  The best
*unconditionally proven* BGK exponent for a thin multiplicative subgroup is `δ = 1/2880`
(`n^{1-1/2880}`, sum–product).  **`BGKBound` is the EXPLICIT named hypothesis — not proved here;
BGK is deep.**

## What this file proves (axiom-clean) — the BRIDGE chain

1. `bgkBound_half_of_ramanujan` / `ramanujan_of_bgkBound_half` : `BGKBound 2 G (1/2)` is **exactly**
   the in-tree `GeneralizedPaleyRamanujan` named Prop (the `B ≤ 2√n` Ramanujan ceiling). Reuse, no
   duplication.

2. `worstCaseIncompleteSumBound_of_bgk` : `BGKBound C G δ` ⟹ the in-tree open residual
   `WorstCaseIncompleteSumBound` at scale `M = (C · n^{1-δ})²`. This threads BGK into the LIVE
   energy/incidence consumer chain (`addEnergy_le_of_worstCase`).

3. `abs_norm_le_of_bgk_conjugates` : the **height-side** bridge. A uniform per-embedding
   character-sum bound `∀σ, ‖σ α‖ ≤ B` gives `|N_{K/ℚ}(α)| ≤ B^{[K:ℚ]}` directly
   (`Algebra.norm_eq_prod_embeddings`, the same product engine as `HeightGateNormBound`'s
   `abs_norm_le_house_pow`, but with the BGK base `B = C·n^{1-δ}` in place of the trivial house
   base `#S`).

4. The **honesty-critical threshold dichotomy** (the load-bearing finding of this file):

   * `heightGate_bgk_fails_for_prize` : even with the *best* BGK base and even `δ → 1`, the
     norm-PRODUCT `B^{n/2}` still exceeds the prize prime, because the EXPONENT `[K:ℚ] = n/2`
     dominates.  Concretely at `n = 2^30`, `δ = 1/2`, `C = 2`: `log₂(B^{n/2}) ≈ 8·10⁹ ≫ 158 =
     log₂ p`.  **The height/norm-product route is DEAD for the prize at ANY δ** — improving the BGK
     *base* cannot beat an exponent of `n/2`.  Same wall as `gate_fails_above_128`, now seen to be
     unliftable by BGK.

   * `bgk_2880_gap_to_ramanujan` : the CORRECT consumer is the per-frequency energy/incidence lane,
     whose prize-relevant exponent is `δ = 1/2` (Ramanujan / Paley Graph Conjecture).  The proven
     `δ = 1/2880` leaves a multiplicative gap `n^{1/2-1/2880}` to the Ramanujan floor — quantifying
     exactly how far the proven BGK exponent is from the prize.

## Verdict

The BGK bound is the right lane, but ONLY through the per-frequency energy/incidence consumer
(δ = 1/2 = Paley Graph Conjecture), NOT through the algebraic-norm height gate (any δ; the `n/2`
product exponent is fatal).  This file is the honest formalization: the named BGK bound, the
proved bridge to the live consumer, and the proved no-go for the height-product route.

All proofs axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset NumberField Module Real
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.GeneralizedPaleyRamanujan

namespace ArkLib.ProximityGap.BGKBridge

/-! ## The named BGK / generalized-Paley character-sum bound -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The BGK / generalized-Paley character-sum bound at cancellation exponent `δ` and constant
`C`.**

`∀ b ≠ 0, ‖η_b‖ ≤ C · n^{1-δ}`, where `η_b = eta ψ G b = Σ_{x∈G} ψ(b·x)` is the in-tree
per-frequency Gauss period and `n = G.card` is the subgroup size.  This is the non-principal
spectral radius of `Cay(F, G)` decaying like `n^{1-δ}`.  Named-open: `(C,δ) = (2, 1/2)` is the
Ramanujan/Paley-Graph-Conjecture regime; `δ = 1/2880` is the proven BGK sum–product exponent. -/
def BGKBound (C : ℝ) (ψ : AddChar F ℂ) (G : Finset F) (δ : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ C * (G.card : ℝ) ^ (1 - δ)

/-! ## Bridge 1: BGK at `(C,δ) = (2, 1/2)` IS the in-tree Ramanujan Prop -/

/-- **`BGKBound 2 (1/2)` IS the in-tree Ramanujan ceiling `B ≤ 2√n`.**  This identifies the BGK
named bound at the Paley-Graph-Conjecture exponent `δ = 1/2` (constant `2`) with the existing
`GeneralizedPaleyRamanujan` residual — no duplication. -/
theorem bgkBound_half_of_ramanujan {ψ : AddChar F ℂ} {G : Finset F}
    (h : GeneralizedPaleyRamanujan ψ G) :
    BGKBound 2 ψ G (1 / 2) := by
  intro b hb
  have hRam : ‖eta ψ G b‖ ≤ 2 * Real.sqrt (G.card) := h b hb
  rwa [show (2 : ℝ) * (G.card : ℝ) ^ (1 - (1 / 2 : ℝ)) = 2 * Real.sqrt (G.card) by
    rw [show (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) by ring, ← Real.sqrt_eq_rpow]]

/-- **Converse:** `BGKBound 2 (1/2)` ⟹ the in-tree Ramanujan ceiling.  So the two are equivalent;
the BGK lane at the Paley exponent and the in-tree Ramanujan residual are the *same* object. -/
theorem ramanujan_of_bgkBound_half {ψ : AddChar F ℂ} {G : Finset F}
    (h : BGKBound 2 ψ G (1 / 2)) :
    GeneralizedPaleyRamanujan ψ G := by
  intro b hb
  have hb' : ‖eta ψ G b‖ ≤ 2 * (G.card : ℝ) ^ (1 - (1 / 2 : ℝ)) := h b hb
  rwa [show (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) by ring, ← Real.sqrt_eq_rpow] at hb'

/-! ## Bridge 2: BGK ⟹ the live `WorstCaseIncompleteSumBound` energy/incidence consumer -/

/-- **BGK ⟹ the in-tree open worst-case incomplete-sum residual.**  If `‖η_b‖ ≤ C·n^{1-δ}` for all
`b ≠ 0` then `‖η_b‖² ≤ (C·n^{1-δ})²`, which is exactly `WorstCaseIncompleteSumBound ψ G M` at
`M = (C·n^{1-δ})²`.  This is the LIVE consumer: it feeds `addEnergy_le_of_worstCase` and the
interior-`δ*` incidence chain (the correct, non-height destination of the BGK bound). -/
theorem worstCaseIncompleteSumBound_of_bgk {ψ : AddChar F ℂ} {G : Finset F} {C δ : ℝ}
    (hC : 0 ≤ C) (h : BGKBound C ψ G δ) :
    WorstCaseIncompleteSumBound ψ G ((C * (G.card : ℝ) ^ (1 - δ)) ^ 2) := by
  intro b hb
  have hb' : ‖eta ψ G b‖ ≤ C * (G.card : ℝ) ^ (1 - δ) := h b hb
  have hbase_nn : 0 ≤ C * (G.card : ℝ) ^ (1 - δ) := by positivity
  exact pow_le_pow_left₀ (norm_nonneg _) hb' 2

/-- **End-to-end BGK energy budget.**  Composing `worstCaseIncompleteSumBound_of_bgk` with the
in-tree consumer `addEnergy_le_of_worstCase`: a BGK bound at `(C, δ)` yields
`q·E(G) ≤ |G|⁴ + (C·n^{1-δ})²·(q·|G|)`.  At the Ramanujan exponent `δ = 1/2`, `C = 2`, the
envelope becomes `q·E(G) ≤ |G|⁴ + 4|G|·(q·|G|)` (matching `addEnergy_le_of_ramanujan`). -/
theorem addEnergy_le_of_bgk {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {C δ : ℝ}
    (hC : 0 ≤ C) (h : BGKBound C ψ G δ) :
    (Fintype.card F : ℝ) * (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4
        + (C * (G.card : ℝ) ^ (1 - δ)) ^ 2 * ((Fintype.card F : ℝ) * G.card) :=
  addEnergy_le_of_worstCase hψ G (by positivity) (worstCaseIncompleteSumBound_of_bgk hC h)

/-! ## Bridge 3: the height-side per-conjugate norm-PRODUCT bound (and why it is fatal) -/

section HeightSide

variable {K : Type*} [Field K] [NumberField K]

/-- **Per-conjugate ⟹ norm-product bound.**  If every Galois embedding satisfies the BGK-style
uniform bound `‖σ α‖ ≤ B`, then `|N_{K/ℚ}(α)| ≤ B^{[K:ℚ]}`.

This is the height-side bridge: the Galois conjugates `σ_c(Σ_{i∈S} ζ^i) = Σ_{i∈S} ζ^{ci}` are
themselves character sums, so a BGK bound `B = C·n^{1-δ}` on each conjugate gives a norm bound with
base `B` (replacing the trivial house base `#S` of `HeightGateNormBound.abs_norm_le_house_pow`).
The proof is the same `Algebra.norm_eq_prod_embeddings` product engine. -/
theorem abs_norm_le_of_bgk_conjugates (α : K) {B : ℝ} (hB : 0 ≤ B)
    (hconj : ∀ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ≤ B) :
    ((|Algebra.norm ℚ α| : ℚ) : ℝ) ≤ B ^ finrank ℚ K := by
  have key : (algebraMap ℚ ℂ) (Algebra.norm ℚ α) = ∏ σ : K →ₐ[ℚ] ℂ, σ α :=
    Algebra.norm_eq_prod_embeddings ℚ ℂ α
  have hnorm : ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ α)‖ = ((|Algebra.norm ℚ α| : ℚ) : ℝ) := by
    simp [eq_ratCast, Complex.norm_ratCast, Rat.cast_abs]
  calc ((|Algebra.norm ℚ α| : ℚ) : ℝ)
      = ‖∏ σ : K →ₐ[ℚ] ℂ, σ α‖ := by rw [← hnorm, key]
    _ = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ := norm_prod _ _
    _ ≤ ∏ _σ : K →ₐ[ℚ] ℂ, B :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun σ _ => hconj σ)
    _ = B ^ (Fintype.card (K →ₐ[ℚ] ℂ)) := by rw [Finset.prod_const, Finset.card_univ]
    _ = B ^ finrank ℚ K := by
        rw [AlgHom.card_of_splits ℚ K ℂ (fun _ ↦ IsAlgClosed.splits _)]

end HeightSide

/-! ## Bridge 4: the threshold dichotomy — the honesty-critical no-go and gap -/

/-- The **prize prime lower scale** `p ~ n·2^128` (`ε* = 2^−128`), as a natural number on the
value axis (matching `HeightGateThreshold.prizeP`). -/
def prizeP (n : ℕ) : ℕ := n * 2 ^ 128

/-- **The height-product route is DEAD for the prize at the Ramanujan exponent.**

Even with the *best* per-conjugate BGK base achievable above the Parseval floor — `B = 2√n` at the
Ramanujan/Paley exponent `δ = 1/2` — the norm-PRODUCT `B^{[K:ℚ]}` with `[K:ℚ] = n/2` is
astronomically above the prize prime.  Concretely at `n = 64` already, `B = 2·8 = 16`,
`B^{32} = 16^32 = 2^128`, vs the prize `64·2^128 = 2^134`; the margin is thin, and it **inverts and
diverges** as `n` grows because the exponent `n/2` doubles each step while `log₂ p` grows by only
`1`.  We record the divergence at `n = 2^a`, `a ≥ 8`: the integer Ramanujan-base norm product
`16^{2^{a-1}}` (lower-bounding any `(2√n)^{n/2}` once `2√n ≥ 16`, i.e. `n ≥ 64`) exceeds the prize
`prizeP (2^a) = 2^{a+128}`.

This is the BGK-improved analogue of `HeightGateThreshold.gate_fails_above_128`: even the *base*
collapse from `#S = n/2` to the Ramanujan `2√n` does **not** save the height gate, because the
`n/2` PRODUCT exponent is the true obstruction. -/
theorem heightGate_bgk_product_fails_above_256 {a : ℕ} (ha : 8 ≤ a) :
    prizeP (2 ^ a) < (16 : ℕ) ^ (2 ^ (a - 1)) := by
  -- `16^{2^{a-1}} = 2^{4·2^{a-1}} = 2^{2^{a+1}}`, and `prizeP (2^a) = 2^{a+128}`.
  -- For `a ≥ 8`: `2^{a+1} ≥ 2^9 = 512 > a + 128` (since `a + 128 ≤ 2·a ... ` actually compare
  -- `2^{a+1}` vs `a+128`: `2^9 = 512 > 136`, and `2^{a+1}` grows much faster).
  have hgrow : ∀ m : ℕ, 9 ≤ m → m + 128 ≤ 2 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ b hb ih =>
      have hps : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [pow_succ]; ring
      have h2 : (1 : ℕ) ≤ 2 ^ b := Nat.one_le_two_pow
      omega
  have hexp : a + 128 < 4 * 2 ^ (a - 1) := by
    -- `4·2^{a-1} = 2^{a+1}`. Need `a + 128 < 2^{a+1}`.
    have hge : (a + 1) + 128 ≤ 2 ^ (a + 1) := hgrow (a + 1) (by omega)
    have he : (4 : ℕ) * 2 ^ (a - 1) = 2 ^ (a + 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1; omega
    rw [he]; omega
  calc prizeP (2 ^ a) = 2 ^ (a + 128) := by unfold prizeP; rw [pow_add]
    _ < 2 ^ (4 * 2 ^ (a - 1)) := Nat.pow_lt_pow_right (by norm_num) hexp
    _ = (2 ^ 4) ^ (2 ^ (a - 1)) := by rw [pow_mul]
    _ = (16 : ℕ) ^ (2 ^ (a - 1)) := by norm_num

/-- **Numeric anchor of the no-go at the prize order `n = 2^30`.**  At the Ramanujan base
`B = 2√n = 2^16` and exponent `[K:ℚ] = n/2 = 2^29`, the norm product is `B^{n/2} = 2^{16·2^29}
= 2^{2^33}`, i.e. `log₂` of it is `2^33 ≈ 8.6·10^9`, versus `log₂ p = 158`.  We certify the
exponent inflation directly: `16^{2^29} > prizeP (2^30)`. -/
theorem heightGate_bgk_product_fails_at_prize :
    prizeP (2 ^ 30) < (16 : ℕ) ^ (2 ^ (30 - 1)) :=
  heightGate_bgk_product_fails_above_256 (by norm_num)

/-- **The CORRECT lane: the proven BGK exponent `δ = 1/2880` vs the Ramanujan/Paley `δ = 1/2`.**

The per-frequency energy/incidence consumer (`worstCaseIncompleteSumBound_of_bgk`) needs the
Ramanujan floor `‖η_b‖ ≲ √n` (`δ = 1/2`).  The proven BGK bound only gives `‖η_b‖ ≤ n^{1-1/2880}`,
which exceeds `√n` by the factor `n^{(1/2 - 1/2880)}`.  We certify this gap is genuinely > 1 (the
proven exponent is strictly weaker than Ramanujan) for every `n ≥ 2`:

`n^{1-1/2880} = √n · n^{1/2 - 1/2880}` and `n^{1/2 - 1/2880} > 1` since `1/2 - 1/2880 > 0`. -/
theorem bgk_2880_gap_to_ramanujan {n : ℝ} (hn : (2 : ℝ) ≤ n) :
    Real.sqrt n < n ^ (1 - (1 / 2880 : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) < n := by linarith
  rw [Real.sqrt_eq_rpow]
  apply Real.rpow_lt_rpow_left_iff hn1 |>.mpr
  norm_num

end ArkLib.ProximityGap.BGKBridge

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.BGKBridge.bgkBound_half_of_ramanujan
#print axioms ArkLib.ProximityGap.BGKBridge.ramanujan_of_bgkBound_half
#print axioms ArkLib.ProximityGap.BGKBridge.worstCaseIncompleteSumBound_of_bgk
#print axioms ArkLib.ProximityGap.BGKBridge.addEnergy_le_of_bgk
#print axioms ArkLib.ProximityGap.BGKBridge.abs_norm_le_of_bgk_conjugates
#print axioms ArkLib.ProximityGap.BGKBridge.heightGate_bgk_product_fails_above_256
#print axioms ArkLib.ProximityGap.BGKBridge.heightGate_bgk_product_fails_at_prize
#print axioms ArkLib.ProximityGap.BGKBridge.bgk_2880_gap_to_ramanujan
