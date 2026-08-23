/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RigidityIterated2kLift
import ArkLib.Data.CodingTheory.ProximityGap.BoundedCyclotomicIndep

/-!
# The bounded bridge — `BoundedHalfBasisIndep` suffices for the rigidity chain (#407)

The antipodal-structure chain (`bridgeZ → disjoint_equal_sum_antipodal_int → … → RepK`) uses the
independence hypothesis `HalfBasisIndepZ` at exactly **one** place: `bridgeZ`, on the coefficient
vector `j ↦ contribZ A j − contribZ B j`. Because `fiber A j ⊆ {(j,true),(j,false)}`, each
`contribZ A j ∈ {−1,0,1}`, so that coefficient vector is bounded by `4` in sup-norm — **independent of
the tuple size**. Hence the *bounded* hypothesis `BoundedHalfBasisIndep ζ N 4` already drives the whole
chain:

> **`bridgeZ_bounded`** — `BoundedHalfBasisIndep ζ N C` (`C ≥ 4`) `⟹ ∀ j, contribZ A j = contribZ B j`
> for equal signed-point sums.

This is what makes `BoundedHalfBasisIndep` (which CAN hold in char-`p`, unlike `HalfBasisIndepZ`) the
single char-`p` input for **every** rung `RepK` at once — the unification anchoring the definitive
open-core characterization (the prize = `BoundedHalfBasisIndep ω (2^{m-1}) 4` mod the prize prime).

Issue #407.
-/

open Round25General Round29IteratedLift
open ArkLib.ProximityGap.BoundedCyclotomicIndep

namespace ArkLib.ProximityGap.BridgeBounded

variable {F : Type*} [Field F] {N : ℕ} {ζ : F}

/-- Each index contributes at most an antipodal pair, so `|contribZ A j| ≤ 2`. -/
theorem contribZ_natAbs_le_two (A : Finset (Fin N × Bool)) (j : Fin N) :
    (contribZ A j).natAbs ≤ 2 := by
  have habs : |contribZ A j| ≤ 2 := by
    unfold contribZ
    calc |∑ p ∈ fiber A j, isgn p|
        ≤ ∑ p ∈ fiber A j, |isgn p| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ p ∈ fiber A j, 1 := by
          apply Finset.sum_congr rfl; intro p _; rcases hb : p.2 <;> simp [isgn, hb]
      _ = ((fiber A j).card : ℤ) := by simp
      _ ≤ 2 := by
          have := Finset.card_le_card (fiber_subset_pair A j)
          have h2 : ({((j : Fin N), true), (j, false)} : Finset (Fin N × Bool)).card ≤ 2 :=
            (Finset.card_insert_le _ _).trans (by simp)
          exact_mod_cast le_trans this h2
  rw [Int.abs_eq_natAbs] at habs
  exact_mod_cast habs

/-- **Tight per-index bound.** Each index's integer contribution lies in `{-1,0,1}`: the fiber is
empty (`0`), a singleton (`±1`), or the full antipodal pair whose signs cancel (`0`). Strictly
tighter than `contribZ_natAbs_le_two` (which used only `card ≤ 2`, ignoring sign cancellation). -/
theorem contribZ_natAbs_le_one (A : Finset (Fin N × Bool)) (j : Fin N) :
    (contribZ A j).natAbs ≤ 1 := by
  rcases fiber_trichotomy A j with h0 | ⟨p, hp⟩ | ⟨_, hzero⟩
  · have : contribZ A j = 0 := by unfold contribZ; rw [h0]; rfl
    rw [this]; simp
  · have hc : contribZ A j = isgn p := by
      unfold contribZ; rw [hp]; exact Finset.sum_singleton _ _
    rw [hc]; unfold isgn; rcases p.2 <;> simp
  · rw [hzero]; simp

/-- **The bounded bridge.** `BoundedHalfBasisIndep ζ N C` with `C ≥ 4` forces equal integer
contributions from equal signed-point sums — exactly as `bridgeZ` does from the (char-`p`-false)
unbounded `HalfBasisIndepZ`. The coefficient vector is `{−2,…,2}`-bounded, so `C = 4` suffices for
every tuple size. -/
theorem bridgeZ_bounded {C : ℕ} (hC : 4 ≤ C) (hindep : BoundedHalfBasisIndep ζ N C)
    {A B : Finset (Fin N × Bool)}
    (hsum : (∑ p ∈ A, sval ζ p) = ∑ p ∈ B, sval ζ p) :
    ∀ j, contribZ A j = contribZ B j := by
  intro j
  have hF : (∑ j : Fin N, (((contribZ A j - contribZ B j : ℤ) : F) * ζ ^ (j : ℕ))) = 0 := by
    have expand : ∀ (S : Finset (Fin N × Bool)),
        (∑ p ∈ S, sval ζ p) = ∑ j : Fin N, ((contribZ S j : ℤ) : F) * ζ ^ (j : ℕ) := by
      intro S
      rw [Finset.sum_congr rfl (fun p _ => sval_eq_sum (ζ := ζ) p), Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← sum_coefAt S j]
      push_cast
      rw [Finset.sum_mul]
    calc (∑ j : Fin N, (((contribZ A j - contribZ B j : ℤ) : F) * ζ ^ (j : ℕ)))
        = (∑ p ∈ A, sval ζ p) - (∑ p ∈ B, sval ζ p) := by
          rw [expand A, expand B, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          push_cast
          ring
      _ = 0 := by rw [hsum]; ring
  have hbound : ∀ k, (contribZ A k - contribZ B k).natAbs ≤ C := by
    intro k
    have ha := contribZ_natAbs_le_two A k
    have hb := contribZ_natAbs_le_two B k
    have hsub := Int.natAbs_sub_le (contribZ A k) (contribZ B k)
    omega
  have hz : contribZ A j - contribZ B j = 0 :=
    hindep (fun k => contribZ A k - contribZ B k) hbound hF j
  omega

/-- **The bounded bridge at `C ≥ 2` (tight).** Since each `contribZ ∈ {-1,0,1}`
(`contribZ_natAbs_le_one`), the difference coefficient vector is `{-2,…,2}`-bounded, so
`BoundedHalfBasisIndep ζ N C` with `C ≥ 2` already forces equal contributions — improving
`bridgeZ_bounded`'s `C ≥ 4` (which double-counted the loose `≤ 2` per side). The prize hypothesis
thus sharpens from `BoundedHalfBasisIndep ω (2^{m-1}) 4` to support `2`. -/
theorem bridgeZ_bounded_two {C : ℕ} (hC : 2 ≤ C) (hindep : BoundedHalfBasisIndep ζ N C)
    {A B : Finset (Fin N × Bool)}
    (hsum : (∑ p ∈ A, sval ζ p) = ∑ p ∈ B, sval ζ p) :
    ∀ j, contribZ A j = contribZ B j := by
  intro j
  have hF : (∑ j : Fin N, (((contribZ A j - contribZ B j : ℤ) : F) * ζ ^ (j : ℕ))) = 0 := by
    have expand : ∀ (S : Finset (Fin N × Bool)),
        (∑ p ∈ S, sval ζ p) = ∑ j : Fin N, ((contribZ S j : ℤ) : F) * ζ ^ (j : ℕ) := by
      intro S
      rw [Finset.sum_congr rfl (fun p _ => sval_eq_sum (ζ := ζ) p), Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← sum_coefAt S j]
      push_cast
      rw [Finset.sum_mul]
    calc (∑ j : Fin N, (((contribZ A j - contribZ B j : ℤ) : F) * ζ ^ (j : ℕ)))
        = (∑ p ∈ A, sval ζ p) - (∑ p ∈ B, sval ζ p) := by
          rw [expand A, expand B, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          push_cast
          ring
      _ = 0 := by rw [hsum]; ring
  have hbound : ∀ k, (contribZ A k - contribZ B k).natAbs ≤ C := by
    intro k
    have ha := contribZ_natAbs_le_one A k
    have hb := contribZ_natAbs_le_one B k
    have hsub := Int.natAbs_sub_le (contribZ A k) (contribZ B k)
    omega
  have hz : contribZ A j - contribZ B j = 0 :=
    hindep (fun k => contribZ A k - contribZ B k) hbound hF j
  omega

/-- **Bounded antipodal closure.** The `t = 1` rigidity from the *bounded* hypothesis: disjoint
signed-point sets with equal sums are antipode-closed, driven by `BoundedHalfBasisIndep ζ N C`
(`C ≥ 4`). The exact in-tree `disjoint_equal_sum_antipodal_int` with its char-`p`-false unbounded
`HalfBasisIndepZ` replaced by the char-`p`-realizable bounded hypothesis — so this (and hence every
`RepK`) follows from the single char-`p` input. -/
theorem disjoint_equal_sum_antipodal_int_bounded {C : ℕ} (hC : 4 ≤ C)
    (hindep : BoundedHalfBasisIndep ζ N C)
    {A B : Finset (Fin N × Bool)}
    (hsum : (∑ p ∈ A, sval ζ p) = ∑ p ∈ B, sval ζ p)
    (hdisj : Disjoint A B) :
    ∀ p ∈ A, antipode p ∈ A := by
  intro p hp
  by_contra hnot
  have hfib : fiber A p.1 = {p} := by
    apply Finset.Subset.antisymm
    · intro q hq
      obtain ⟨hqA, hqj⟩ := Finset.mem_filter.mp hq
      rw [Finset.mem_singleton]
      by_cases hs : q.2 = p.2
      · exact Prod.ext hqj hs
      · exfalso
        apply hnot
        have hqap : q = antipode p := by
          unfold antipode
          refine Prod.ext hqj ?_
          rcases hp2 : p.2 <;> rcases hq2 : q.2 <;> simp_all
        rw [← hqap]
        exact hqA
    · intro q hq
      rw [Finset.mem_singleton] at hq
      rw [hq]
      exact mem_fiber_self.mpr hp
  have hcA : contribZ A p.1 = isgn p := contrib_of_singleton hfib
  have hbridge := bridgeZ_bounded hC hindep hsum p.1
  have hcB : contribZ B p.1 = isgn p := by omega
  rcases fiber_trichotomy B p.1 with h0 | ⟨q, hq⟩ | ⟨_, hzero⟩
  · rw [show contribZ B p.1 = 0 by unfold contribZ; rw [h0]; rfl] at hcB
    unfold isgn at hcB
    rcases p with ⟨_, (_|_)⟩ <;> simp_all
  · have hcq : contribZ B p.1 = isgn q := contrib_of_singleton hq
    have hsgn : isgn q = isgn p := by omega
    have hqj : q.1 = p.1 := by
      have hmem : q ∈ fiber B p.1 := by rw [hq]; exact Finset.mem_singleton_self q
      exact (Finset.mem_filter.mp hmem).2
    have hqB : q ∈ B := by
      have hmem : q ∈ fiber B p.1 := by rw [hq]; exact Finset.mem_singleton_self q
      exact (Finset.mem_filter.mp hmem).1
    have hqp : q = p := by
      unfold isgn at hsgn
      rcases p with ⟨pj, (_|_)⟩ <;> rcases q with ⟨qj, (_|_)⟩ <;> simp_all
    rw [hqp] at hqB
    exact (Finset.disjoint_left.mp hdisj hp) hqB
  · rw [hzero] at hcB
    unfold isgn at hcB
    rcases p with ⟨_, (_|_)⟩ <;> simp_all <;> omega

end ArkLib.ProximityGap.BridgeBounded
#print axioms ArkLib.ProximityGap.BridgeBounded.contribZ_natAbs_le_one
#print axioms ArkLib.ProximityGap.BridgeBounded.bridgeZ_bounded
#print axioms ArkLib.ProximityGap.BridgeBounded.bridgeZ_bounded_two
#print axioms ArkLib.ProximityGap.BridgeBounded.disjoint_equal_sum_antipodal_int_bounded
