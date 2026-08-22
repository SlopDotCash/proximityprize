/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS11GenericDepthDecomposition

/-!
# LANE FS12 (#466, Fable session 2026-07-09): THE SHIFT BIJECTION — the two-sided depth-`r`
  trivial count is a ONE-SIDED zero-sum count, `trivialCountG m r = zeroSumCount m (r + r)`

The negated folded monomial is itself a folded monomial at the `m`-shifted exponent:
`−μ(x) = μ(x ± m)` (`monomF_mshift`).  So the two-sided pattern
`Σᵢ μ(aᵢ) − Σⱼ μ(bⱼ)` equals the ONE-SIDED sum `Σᵢ μ(aᵢ) + Σⱼ μ(shift(bⱼ))`, and shifting
the `b`-side is a bijection (`Fin.append` on exponent tuples).  Hence

  `trivialCountG m r = zeroSumCount m (r + r)`,

where `zeroSumCount m N := #{c : Fin N → [0, 2m) : Σᵢ μ(cᵢ) = 0}` — a single-tuple object.

**Why this matters:** the remaining census input of the depth-generic ledger (spawned task
"depth-generic T=1 ledger") is the Wick union bound `trivialCountG m r ≤ (2r−1)‼·(2m)^r`.
On the one-sided object this becomes the clean pairing induction
`Z(N) ≤ (N−1)·2m·Z(N−2)` (the last item must cancel against an `m`-shifted partner; odd `N`
gives `Z = 0`), with no two-sided bookkeeping.  This brick lands the reduction; the
induction itself is NOT claimed here.

Issue #466, lane FS12.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS12ZeroSumCountBijection

open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open ArkLib.ProximityGap.Frontier.FS11GenericDepthDecomposition

open scoped Classical

/-- The `m`-shift on `[0, 2m)` exponents: `x ↦ x ± m` (fold flip). -/
def mshift (m x : ℕ) : ℕ := if x < m then x + m else x - m

theorem mshift_lt {m x : ℕ} (hx : x < 2 * m) : mshift m x < 2 * m := by
  unfold mshift; split_ifs <;> omega

theorem mshift_involutive {m x : ℕ} (hx : x < 2 * m) :
    mshift m (mshift m x) = x := by
  unfold mshift; split_ifs <;> omega

/-- **The sign flip:** `μ(shift(x)) = −μ(x)`. -/
theorem monomF_mshift {m x : ℕ} (hx : x < 2 * m) :
    monomF m (mshift m x) = -(monomF m x) := by
  by_cases h : x < m
  · have h1 : ¬ (x + m < m) := by omega
    have h2 : x + m - m = x := by omega
    simp [mshift, monomF, h, h1, h2]
  · have h1 : x - m < m := by omega
    simp [mshift, monomF, h, h1]

/-- Evaluate `Fin.append` below the split point. -/
theorem append_apply_lt {α : Type*} {r : ℕ} (u v : Fin r → α) (i : Fin (r + r))
    (h : (i : ℕ) < r) : Fin.append u v i = u ⟨(i : ℕ), h⟩ := by
  have hi : i = Fin.castAdd r ⟨(i : ℕ), h⟩ := by ext; rfl
  conv_lhs => rw [hi]
  rw [Fin.append_left]

/-- Evaluate `Fin.append` above the split point. -/
theorem append_apply_ge {α : Type*} {r : ℕ} (u v : Fin r → α) (i : Fin (r + r))
    (h : ¬ (i : ℕ) < r) : Fin.append u v i = v ⟨(i : ℕ) - r, by omega⟩ := by
  have hi : i = Fin.natAdd r ⟨(i : ℕ) - r, by omega⟩ := by
    ext
    simp [Fin.natAdd]
    omega
  conv_lhs => rw [hi]
  rw [Fin.append_right]

/-- The one-sided zero-sum count: `N`-tuples of `[0, 2m)` exponents whose folded-monomial
sum vanishes in `ℤ[X]`. -/
noncomputable def zeroSumCount (m N : ℕ) : ℕ :=
  ((expTuples (2 * m) N).filter (fun c => (∑ i, monomF m (c i)) = 0)).card

/-- The one-sided sum of an appended pair is the two-sided pattern. -/
theorem sum_append_eq_pattern {m r : ℕ} (a b : Fin r → ℕ)
    (hb : ∀ j, b j < 2 * m) :
    (∑ i : Fin (r + r), monomF m (Fin.append a (fun j => mshift m (b j)) i))
      = patternPolyG m a b := by
  rw [Fin.sum_univ_add]
  unfold patternPolyG
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [Fin.append_left])
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fin.append_right, monomF_mshift (hb j)]

/-- **THE SHIFT BIJECTION.**  The two-sided depth-`r` trivial count equals the one-sided
zero-sum count at length `r + r`. -/
theorem trivialCountG_eq_zeroSumCount (m r : ℕ) :
    trivialCountG m r = zeroSumCount m (r + r) := by
  unfold trivialCountG zeroSumCount
  refine Finset.card_bij
    (fun ab _ => Fin.append ab.1 (fun j => mshift m (ab.2 j))) ?_ ?_ ?_
  · -- maps into the filtered one-sided set
    rintro ⟨a, b⟩ hab
    dsimp only
    rw [Finset.mem_filter] at hab ⊢
    obtain ⟨hmem, hzero⟩ := hab
    rw [Finset.mem_product] at hmem
    obtain ⟨hma, hmb⟩ := hmem
    rw [expTuples, Fintype.mem_piFinset] at hma hmb
    have hb_lt : ∀ j : Fin r, b j < 2 * m := fun j => mem_range.mp (hmb j)
    constructor
    · rw [expTuples, Fintype.mem_piFinset]
      intro i
      rw [mem_range]
      by_cases h : (i : ℕ) < r
      · rw [append_apply_lt _ _ _ h]
        exact mem_range.mp (hma _)
      · rw [append_apply_ge _ _ _ h]
        exact mshift_lt (hb_lt _)
    · rw [sum_append_eq_pattern a b hb_lt]
      exact hzero
  · -- injective
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    dsimp only at heq
    rw [Finset.mem_filter, Finset.mem_product] at hab hab'
    have hmb := hab.1.2
    have hmb' := hab'.1.2
    rw [expTuples, Fintype.mem_piFinset] at hmb hmb'
    have hb_lt : ∀ j : Fin r, b j < 2 * m := fun j => mem_range.mp (hmb j)
    have hb'_lt : ∀ j : Fin r, b' j < 2 * m := fun j => mem_range.mp (hmb' j)
    have ha_eq : a = a' := by
      funext i
      have h := congrFun heq (Fin.castAdd r i)
      rwa [Fin.append_left, Fin.append_left] at h
    have hb_eq : b = b' := by
      funext j
      have h := congrFun heq (Fin.natAdd r j)
      rw [Fin.append_right, Fin.append_right] at h
      calc b j = mshift m (mshift m (b j)) := (mshift_involutive (hb_lt j)).symm
        _ = mshift m (mshift m (b' j)) := by rw [h]
        _ = b' j := mshift_involutive (hb'_lt j)
    rw [Prod.ext_iff]
    exact ⟨ha_eq, hb_eq⟩
  · -- surjective
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hmem, hzero⟩ := hc
    rw [expTuples, Fintype.mem_piFinset] at hmem
    have hc_lt : ∀ i, c i < 2 * m := fun i => mem_range.mp (hmem i)
    refine ⟨(fun i : Fin r => c (Fin.castAdd r i),
             fun j : Fin r => mshift m (c (Fin.natAdd r j))), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product]
      have hround : Fin.append (fun i : Fin r => c (Fin.castAdd r i))
          (fun j : Fin r => mshift m (mshift m (c (Fin.natAdd r j)))) = c := by
        funext i
        by_cases h : (i : ℕ) < r
        · rw [append_apply_lt _ _ _ h]
          congr 1
        · rw [append_apply_ge _ _ _ h, mshift_involutive (hc_lt _)]
          congr 1
          ext
          simp [Fin.natAdd]
          omega
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [expTuples, Fintype.mem_piFinset]
        intro i
        exact mem_range.mpr (hc_lt _)
      · rw [expTuples, Fintype.mem_piFinset]
        intro j
        exact mem_range.mpr (mshift_lt (hc_lt _))
      · -- the pattern of the preimage vanishes
        have hbl : ∀ j : Fin r, mshift m (c (Fin.natAdd r j)) < 2 * m :=
          fun j => mshift_lt (hc_lt _)
        have := sum_append_eq_pattern (m := m)
          (fun i : Fin r => c (Fin.castAdd r i))
          (fun j : Fin r => mshift m (c (Fin.natAdd r j))) hbl
        rw [hround] at this
        rw [← this]
        exact hzero
    · dsimp only
      funext i
      by_cases h : (i : ℕ) < r
      · rw [append_apply_lt _ _ _ h]
        congr 1
      · rw [append_apply_ge _ _ _ h, mshift_involutive (hc_lt _)]
        congr 1
        ext
        simp [Fin.natAdd]
        omega

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms monomF_mshift
#print axioms sum_append_eq_pattern
#print axioms trivialCountG_eq_zeroSumCount

end ArkLib.ProximityGap.Frontier.FS12ZeroSumCountBijection
