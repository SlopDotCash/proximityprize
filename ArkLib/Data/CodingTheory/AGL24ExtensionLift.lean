/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24SymbolicRank

/-!
# [AGL24] Remark 2.12: the extension lifting (issue #354)

The symbolic full-rank interface descends along field extensions: the RIM's entries live
over the prime field (`±Xᵢᵐ`), so a kernel vector over `F` maps to one over any extension
`F'`, and triviality over `F'` forces triviality over `F`. Consequently **the GM-MDS/Frank
work may assume the field is as large as convenient** — discharging
`SymbolicFullRankResidual` for one extension of each field discharges it everywhere.

* `RIM_map_algebraMap` — the RIM commutes with coefficient extension;
* `symbolicFullRankResidual_of_extension` — **the descent**.
-/

open Finset

namespace AGL24

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The reduced intersection matrix commutes with coefficient extension (its entries are
`±Xᵢᵐ`, defined over the prime field). -/
theorem RIM_map_algebraMap {F F' : Type*} [Field F] [Field F'] [Algebra F F']
    {t k : ℕ} (e : ι → Finset (Fin (t + 1))) (r : RIMRowIdx e) (c : Fin t × Fin k) :
    MvPolynomial.map (algebraMap F F') (RIM F e r c) = RIM F' e r c := by
  obtain ⟨i, j⟩ := r
  unfold RIM
  by_cases h1 : c.1.castSucc = (e i).min' ⟨j.val, j.property.1⟩
  · rw [if_pos h1, if_pos h1, map_pow, MvPolynomial.map_X]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : c.1.castSucc = j.val
    · rw [if_pos h2, if_pos h2, map_neg, map_pow, MvPolynomial.map_X]
    · rw [if_neg h2, if_neg h2, map_zero]

/-- **[AGL24] Remark 2.12 (the extension lifting)**: the symbolic full-rank interface over
any field extension descends to the base field. GM-MDS/Frank formalizations may therefore
assume the field is as large as convenient. -/
theorem symbolicFullRankResidual_of_extension
    (F F' : Type*) [Field F] [Field F'] [Algebra F F'] {k : ℕ}
    (h' : SymbolicFullRankResidual (ι := ι) F' k) :
    SymbolicFullRankResidual (ι := ι) F k := by
  intro t ht e hwpc v hker
  classical
  -- Extend the kernel vector.
  set v' : Fin t × Fin k → MvPolynomial ι F' :=
    fun c => MvPolynomial.map (algebraMap F F') (v c) with hv'
  have hker' : (RIM F' e).mulVec v' = 0 := by
    funext r
    have hrow := congrFun hker r
    rw [show (0 : RIMRowIdx e → MvPolynomial ι F) r = 0 from rfl] at hrow
    rw [show (0 : RIMRowIdx e → MvPolynomial ι F') r = 0 from rfl]
    calc (RIM F' e).mulVec v' r
        = ∑ c, RIM F' e r c * v' c := rfl
    _ = ∑ c, MvPolynomial.map (algebraMap F F') (RIM F e r c * v c) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [map_mul, RIM_map_algebraMap]
    _ = MvPolynomial.map (algebraMap F F') (∑ c, RIM F e r c * v c) := by
          rw [map_sum]
    _ = MvPolynomial.map (algebraMap F F') ((RIM F e).mulVec v r) := rfl
    _ = 0 := by rw [hrow, map_zero]
  -- Triviality over F' descends (the coefficient map is injective).
  have hv0 := h' ht e hwpc v' hker'
  funext c
  have hthis : MvPolynomial.map (algebraMap F F') (v c) = 0 := congrFun hv0 c
  have hinj : Function.Injective (MvPolynomial.map (algebraMap F F')
      : MvPolynomial ι F → MvPolynomial ι F') :=
    MvPolynomial.map_injective _ (algebraMap F F').injective
  rw [show (0 : Fin t × Fin k → MvPolynomial ι F) c = 0 from rfl]
  exact hinj (by rw [hthis, map_zero])

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.RIM_map_algebraMap
#print axioms AGL24.symbolicFullRankResidual_of_extension
