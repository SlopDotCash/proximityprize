/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.AGL24DeterministicChain
import ArkLib.Data.CodingTheory.AGL24ListDecodingBridge

/-!
# [AGL24] the Reed–Solomon instance chain (issue #346, brick 8)

The localization of the composed deterministic chain at the in-tree Reed–Solomon code:

* `mem_code_iff_exists_coeffs` — codewords of `ReedSolomon.code φ k` are exactly the
  monomial-coefficient evaluations `i ↦ ∑ₘ fₘ·(φ i)ᵐ` (the `rsEval` shape the AGL24 chain
  speaks), via the in-tree `mem_code_iff_exists_polynomial` and the degree-`< k` coefficient
  expansion;
* `not_listDecodable_RS_gives_wpc_rank_deficit` — **the full instance chain**: a failure of
  `(r, L)`-list decodability of the Reed–Solomon code (with the [AGL24] radius arithmetic)
  yields `t + 1 ≤ L + 1` and a coefficient subfamily whose agreement hypergraph is
  `k`-weakly-partition-connected with an evaluated-RIM rank deficit — the event the
  Theorem 1.1 union bound prices through the named Lemma 3.1 interface.

After this brick the campaign's remaining items are exactly the distribution bridge and the
§3 certificate machinery.
-/

open Finset Polynomial

namespace AGL24

variable {ι F : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F]
  [DecidableEq F]

/-- **The coefficient localization**: membership in the in-tree Reed–Solomon code is exactly
the `rsEval`-shaped monomial evaluation. -/
theorem mem_code_iff_exists_coeffs {k : ℕ} (φ : ι ↪ F) (c : ι → F) :
    c ∈ ReedSolomon.code φ k
      ↔ ∃ f : Fin k → F, c = fun i => ∑ m : Fin k, f m * (φ i) ^ (m : ℕ) := by
  rw [ReedSolomon.mem_code_iff_exists_polynomial]
  constructor
  · rintro ⟨p, hdeg, rfl⟩
    refine ⟨fun m => p.coeff m, ?_⟩
    funext i
    show p.eval (φ i) = _
    rcases eq_or_ne p 0 with rfl | hp
    · simp
    · have hnat : p.natDegree < k := natDegree_lt_iff_degree_lt hp |>.mpr hdeg
      rw [Polynomial.eval_eq_sum_range' hnat]
      rw [← Fin.sum_univ_eq_sum_range (fun m => p.coeff m * (φ i) ^ m)]
  · rintro ⟨f, rfl⟩
    refine ⟨∑ m : Fin k, Polynomial.C (f m) * Polynomial.X ^ (m : ℕ), ?_, ?_⟩
    · refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe k)]
      intro m _
      calc (Polynomial.C (f m) * Polynomial.X ^ (m : ℕ)).degree
          ≤ (Polynomial.C (f m)).degree + (Polynomial.X ^ (m : ℕ) : Polynomial F).degree :=
            Polynomial.degree_mul_le _ _
      _ ≤ 0 + (m : ℕ) := by
            refine add_le_add Polynomial.degree_C_le ?_
            rw [Polynomial.degree_X_pow]
      _ < (k : WithBot ℕ) := by
            rw [zero_add]
            exact_mod_cast m.isLt
    · funext i
      show _ = Polynomial.eval (φ i) _
      rw [Polynomial.eval_finset_sum]
      exact Finset.sum_congr rfl fun m _ => by
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

open ListDecodable in
/-- **The full Reed–Solomon instance chain** ([AGL24] deterministic layer, end to end): a
failure of `(r, L)`-list decodability of `ReedSolomon.code φ k` under the radius arithmetic
`(L+1)·r·n ≤ L(n−k)` forces a vertex count `t+1 ≤ L+1` and a coefficient subfamily `g` whose
agreement hypergraph is `k`-weakly-partition-connected with a nonzero evaluated-RIM kernel
vector. -/
theorem not_listDecodable_RS_gives_wpc_rank_deficit
    {k L : ℕ} (hL : 1 ≤ L) (φ : ι ↪ F) {r : ℝ} (hr : 0 ≤ r)
    (hk : k ≤ Fintype.card ι)
    (hrad : (L + 1 : ℝ) * r * (Fintype.card ι : ℝ)
      ≤ ((L * (Fintype.card ι - k) : ℕ) : ℝ))
    (h : ¬ listDecodable (ReedSolomon.code φ k : Set (ι → F)) r (L : ℝ)) :
    ∃ t : ℕ, t + 1 ≤ L + 1 ∧ 1 ≤ t ∧ ∃ g : Fin (t + 1) → Fin k → F,
      ∃ y : ι → F,
      WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1)))
        (agreementEdge y (rsEval (fun i => φ i) g)) ∧
      ∃ v : Fin t × Fin k → F, v ≠ 0 ∧
        ((RIM F (agreementEdge y (rsEval (fun i => φ i) g))).map
          (MvPolynomial.eval (fun i => φ i))).mulVec v = 0 := by
  classical
  -- The notion bridge: the bad configuration of codewords.
  obtain ⟨y, c, hinj, hmem, hdist⟩ := exists_bad_config_of_not_listDecodable hr hrad h
  -- Localize each codeword to its coefficient vector.
  have hcoeffs : ∀ j, ∃ f : Fin k → F,
      c j = fun i => ∑ m : Fin k, f m * (φ i) ^ (m : ℕ) := fun j =>
    (mem_code_iff_exists_coeffs φ (c j)).mp (hmem j)
  choose f hf using hcoeffs
  -- The coefficient family inherits injectivity, and the codewords are its rsEval.
  have hceq : ∀ j, c j = rsEval (fun i => φ i) f j := by
    intro j
    rw [hf j]
    rfl
  have hfinj : Function.Injective f := by
    intro j j' hjj'
    apply hinj
    rw [hceq j, hceq j']
    unfold rsEval
    rw [hjj']
  -- The distance hypothesis transports along the rewrite.
  have hdist' : ∑ j, hammingDist y (rsEval (fun i => φ i) f j)
      ≤ L * (Fintype.card ι - k) := by
    calc ∑ j, hammingDist y (rsEval (fun i => φ i) f j)
        = ∑ j, hammingDist y (c j) :=
          Finset.sum_congr rfl fun j _ => by rw [hceq j]
    _ ≤ L * (Fintype.card ι - k) := hdist
  -- The composed deterministic chain.
  obtain ⟨t, htL, ht1, g, hwpc, hker⟩ :=
    bad_list_gives_wpc_rank_deficit hL (fun i => φ i) f y hfinj hk hdist'
  exact ⟨t, htL, ht1, g, y, hwpc, hker⟩

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.mem_code_iff_exists_coeffs
#print axioms AGL24.not_listDecodable_RS_gives_wpc_rank_deficit
