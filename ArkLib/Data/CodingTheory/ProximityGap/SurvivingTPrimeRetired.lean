/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
# Retiring the `SurvivingTPrimeCoord` residual via the exact high-overlap count (#389, route 2)

GOAL: Show that the named residual `SurvivingTPrimeCoord` (and its consumer
`deep_pair_rank_ge_m_succ`) is RETIRED — its `rank ≥ m+1` conclusion follows
UNCONDITIONALLY and DIRECTLY from the exact unconditional high-overlap count
`card_pair_coherent_high_eq` (FarPairRankSupply.lean), with NO separate
moving-direction machinery and NO `SurvivingTPrimeCoord` hypothesis.

KEY ARITHMETIC.  On the deep stratum `k+1 ≤ o ≤ k+m` (o = |T∩T'|), the exact
high-overlap count gives `#kernel · q^d = q^M` with `d = |T∪T'| − (k+1)`.
Since `|T∪T'| = 2(k+m+1) − o`, `d = 2m+1 − (o−k) ≥ m+1`  iff  `o ≤ k+m`.
Hence `#kernel · q^(m+1) ≤ #kernel · q^d = q^M`.  Pure inequality, no per-pair
linear-algebra witness needed.

Both `FarPairRankSupply.card_pair_coherent_high_eq` and the `genPoly`-form
two-band count are imported; `coeffFamily M c` and `genPoly c` are the SAME
polynomial `∑ j, C (c j) * X^j` (defeq), so the two filters coincide by rfl.
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarPairRankSupply
import ArkLib.Data.CodingTheory.ProximityGap.DeepStratumRankUnconditional

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.SurvivingTPrimeRetired

open ProximityGap ProximityGap.PairRank ProximityGap.Ownership
open ProximityGap.DeepStratumUncond

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

omit [Fintype F] [DecidableEq F] in
/-- `coeffFamily M c` and `genPoly c` are the same polynomial (defeq sums). -/
theorem coeffFamily_eq_genPoly {M : ℕ} (c : Fin M → F) :
    coeffFamily M c = genPoly c := rfl

open Classical in
/-- **THE RETIREMENT BRICK.**  The deep-stratum rank `≥ m+1`
(`deep_pair_rank_ge_m_succ`'s conclusion) holds UNCONDITIONALLY on the proper
deep stratum `k+1 ≤ |T∩T'| ≤ k+m`, derived DIRECTLY from the exact unconditional
high-overlap count `card_pair_coherent_high_eq` — no `SurvivingTPrimeCoord`
hypothesis and no moving-direction apparatus.

The mechanism: the exact count says the two-band kernel has card `q^{M−d}` with
`d = |T∪T'| − (k+1)`.  On `o ≤ k+m` we have `d = 2m+1 − (o−k) ≥ m+1`, so the
`q^(m+1)` factor is dominated by the exact `q^d`.  This RETIRES the residual:
the single-functional surviving-coordinate fact is unnecessary, the exact
union-band count already delivers the bound (and more — the exact rank). -/
theorem deep_pair_rank_ge_m_succ_via_exact_count (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hlo : k + 1 ≤ (T ∩ T').card) (hhi : (T ∩ T').card ≤ k + m)
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) :
    (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k)).card
      * (Fintype.card F) ^ (m + 1) ≤ (Fintype.card F) ^ M := by
  classical
  set q := Fintype.card F with hq
  have hqpos : 0 < q := by rw [hq]; exact Fintype.card_pos
  -- overlap bookkeeping
  have hover : k < (T ∩ T').card := hlo
  -- union card and the exact dimension `d`
  have hub : k + m + 1 ≤ (T ∪ T').card := by
    calc k + m + 1 = T.card := hT.symm
      _ ≤ (T ∪ T').card := Finset.card_le_card Finset.subset_union_left
  have huv := Finset.card_union_add_card_inter T T'
  rw [hT, hT'] at huv
  have hocap : (T ∩ T').card ≤ k + m + 1 := by
    calc (T ∩ T').card ≤ T.card := Finset.card_le_card Finset.inter_subset_left
      _ = k + m + 1 := hT
  -- write the union card as (k+1) + d
  set d := (T ∪ T').card - (k + 1) with hddef
  have hu : (T ∪ T').card = k + 1 + d := by omega
  -- d ≥ m+1 on the proper deep stratum (o ≤ k+m)
  have hdge : m + 1 ≤ d := by
    -- |T∪T'| = 2(k+m+1) − o, so d = 2m+1 − (o−k); o ≤ k+m ⟹ d ≥ m+1
    omega
  -- the exact unconditional count (coeffFamily form)
  have hexact := card_pair_coherent_high_eq dom hT hT' hover hM hu
  rw [← hq] at hexact
  -- transport the filter predicate from coeffFamily to genPoly (defeq)
  set K := (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k)).card with hK
  have hKeq : (Finset.univ.filter (fun c : Fin M → F =>
        (IsCoherent dom k m T (coeffFamily M c)
          ∧ IsCoherent dom k m T' (coeffFamily M c))
        ∧ (coreInterp dom T (coeffFamily M c)).coeff k
            = (coreInterp dom T' (coeffFamily M c)).coeff k)).card = K := by
    rw [hK]
    congr 1
    apply Finset.filter_congr
    intro c _
    -- coeffFamily M c = genPoly c (rfl), so predicates coincide; reassociate ∧
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  rw [hKeq] at hexact
  -- now hexact : K * q^d = q^M; and m+1 ≤ d, so K * q^(m+1) ≤ K * q^d = q^M
  calc K * q ^ (m + 1)
      ≤ K * q ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hqpos hdge)
    _ = q ^ M := hexact

end ProximityGap.SurvivingTPrimeRetired

