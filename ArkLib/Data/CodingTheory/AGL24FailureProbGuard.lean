/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24ProbDischarge
import ArkLib.Data.CodingTheory.AGL24WeakPartition

/-!
# [AGL24] §3: guarding the Lemma 3.1 failure-probability interface

`RIMFullRankFailureProbResidual` (AGL24UnionBound) records the [AGL24] Lemma 3.1
interface: *the probability that the evaluated reduced intersection matrix fails full
column rank is at most `bound`*. Its docstring states the paper's side conditions —
"under the evaluation-point distribution, for every
`(k + ⌈εn⌉)`-weakly-partition-connected `n`-edge hypergraph on `t + 1 ≥ 2` vertices" —
but the Lean definition quantifies over its three parameters with none of them.

This file kernel-checks that both omissions are load-bearing, and states the guarded
repair:

* `not_RIMFullRankFailureProbResidual_empty_family` — at the empty one-slot family the
  reduced intersection matrix has no rows, so *every* evaluation lies in the deficit set,
  and the bound fails under the paper's own uniform distribution
  (`PMF.uniformOfFintype`) already at `bound = 1/2`. The WPC / nonempty-edge / `1 ≤ t`
  guard of the prose is necessary.
* `not_RIMFullRankFailureProbResidual_wpc_point_mass` — at a genuinely
  `2`-weakly-partition-connected family (both slots the complete edge on two vertices;
  see `wpc_two_complete_family`) the bound still fails at a point-mass distribution:
  the all-zero evaluation lies in the deficit set with kernel witness `(0, 1)`, so the
  mass is `1` while `bound = 1/2`. The distribution hypothesis — the uniform one used
  by the conditional provider `rimFailureProb_of_symbolic` — is necessary.
* `RIMFailureProbUniformResidual` — the guarded repair: the paper's side conditions as
  premises, the uniform evaluation distribution baked in, `bound` kept as a parameter
  for the §3 value.
* `rimFailureProbUniformResidual_of_symbolic` — the guarded interface holds at the
  Schwartz–Zippel bound conditional only on `SymbolicFullRankResidual`, exactly the
  input that issue #354 left open.

The unguarded `RIMFullRankFailureProbResidual` is retained untouched for the historical
record: the Theorem 1.1 conditional assembly (`AGL24ConditionalAssembly`) quantifies
over arbitrary mapped evaluation PMFs, so its hypothesis instantiates at the unguarded
interface as an unprovable side condition, never as a proof. The census records the
unguarded form as refuted at the two instances above; downstream consumers use the
guarded form.
-/

open Finset

namespace AGL24

/-! ## The unguarded interface: two kernel-checked refutations -/

/-- The deficit set at the empty one-slot family is everything: the reduced
intersection matrix has no rows, so `mulVec` is vacuously zero. -/
theorem rimRankDeficitSet_empty_family :
    RIMRankDeficitSet (F := ZMod 2) (k := 1) (fun _ : Fin 1 => (∅ : Finset (Fin 2)))
      = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun α => ⟨fun _ => 1, ?_, ?_⟩
  · intro hzero
    exact one_ne_zero (congrFun hzero (⟨(0 : Fin 1), (0 : Fin 1)⟩ : Fin 1 × Fin 1))
  · funext r
    exact absurd r.2.2.1 (by simp)

/-- **The unguarded interface fails at the empty family under the paper's own uniform
distribution.** The written residual has no WPC / nonempty-edge / `1 ≤ t` guard, and
this family satisfies none of them: the deficit set is everything
(`rimRankDeficitSet_empty_family`), so the uniform evaluation distribution gives it
measure `1` while `bound = 1/2`. -/
theorem not_RIMFullRankFailureProbResidual_empty_family :
    ¬ RIMFullRankFailureProbResidual (F := ZMod 2) (k := 1)
        (PMF.uniformOfFintype (Fin 1 → ZMod 2))
        (fun _ : Fin 1 => (∅ : Finset (Fin 2)))
        ((1 : ENNReal) / 2) := by
  intro h
  unfold RIMFullRankFailureProbResidual at h
  have hone : (PMF.uniformOfFintype (Fin 1 → ZMod 2)).toOuterMeasure Set.univ = 1 :=
    (PMF.toOuterMeasure_apply_eq_one_iff (PMF.uniformOfFintype (Fin 1 → ZMod 2))
      Set.univ).2 (Set.subset_univ _)
  rw [rimRankDeficitSet_empty_family, hone] at h
  exact absurd h (by norm_num)

/-! ### A genuinely 2-WPC family -/

/-- The complete two-slot family on two vertices is genuinely
`2`-weakly-partition-connected: a partition of two vertices has at most two cells
(`Finpartition.card_parts_le_card`); with one cell the left side is zero, and with two
cells every cell is nonempty (`Finpartition.nonempty_of_mem_parts`), so the complete
edge touches both and the defining sum is exactly `2`. -/
theorem wpc_two_complete_family :
    WeaklyPartitionConnected 2 (Finset.univ : Finset (Fin 2))
      (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) := by
  intro P
  have hcardle : P.parts.card ≤ 2 := by
    have h := P.card_parts_le_card
    simpa using h
  have htouch : ∀ i : Fin 2, (touchedCells P
      ((fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) i ∩ Finset.univ)).card
      = P.parts.card := by
    intro i
    have hfil : P.parts.filter (fun c =>
        (((fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) i ∩
          Finset.univ) ∩ c).Nonempty) = P.parts :=
      Finset.filter_eq_self.mpr fun c hc => by
        simpa using P.nonempty_of_mem_parts hc
    simp only [touchedCells, hfil]
  rcases Nat.lt_or_ge P.parts.card 2 with hlt | hge
  · calc (2 : ℕ) * (P.parts.card - 1) = 0 := by omega
      _ ≤ ∑ i : Fin 2, ((touchedCells P
          ((fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) i ∩
            Finset.univ)).card - 1) := Nat.zero_le _
  · have hcard : P.parts.card = 2 := le_antisymm hcardle hge
    have hsum : ∑ i : Fin 2, ((touchedCells P
        ((fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) i ∩
          Finset.univ)).card - 1) = 2 := by
      have hev : ∑ i : Fin 2, ((touchedCells P
          ((fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) i ∩
            Finset.univ)).card - 1)
          = ∑ i : Fin 2, (2 - 1) :=
        Finset.sum_congr rfl fun i _ => by rw [htouch i, hcard]
      rw [hev]
      simp
    rw [show (2 : ℕ) * (P.parts.card - 1) = 2 from by omega, hsum]

/-! ### The point-mass refutation -/

/-- The all-zero evaluation lies in the deficit set of the complete two-slot family at
`k = 2`: the minimal vertex of the complete edge is `0`, so every column's vertex is the
minimal one and the evaluated matrix entries are `0 ^ c.2.val`; the kernel column
vector `v = fun c => c.2.val` annihilates both rows (`0 ^ 0 * 0 = 0` and
`0 ^ 1 * 1 = 0`). -/
theorem zero_eval_mem_rimRankDeficitSet_complete_family :
    (fun _ : Fin 2 => (0 : ZMod 2)) ∈
      RIMRankDeficitSet (F := ZMod 2) (k := 2)
        (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) := by
  refine ⟨fun c => (c.2.val : ZMod 2), fun hzero => ?_, ?_⟩
  · exact one_ne_zero (congrFun hzero
      (⟨(0 : Fin 1), (1 : Fin 2)⟩ : Fin 1 × Fin 2))
  · funext r
    obtain ⟨i, ⟨j, hy⟩⟩ := r
    have hy1 : j ∈ (Finset.univ : Finset (Fin 2)) := hy.1
    have hmin : (Finset.univ : Finset (Fin 2)).min' ⟨j, hy1⟩ = (0 : Fin 2) :=
      Fin.le_antisymm
        ((Finset.univ : Finset (Fin 2)).min'_le (0 : Fin 2) (Finset.mem_univ _))
        (Fin.zero_le _)
    -- every column's vertex is the minimal vertex `0`
    have hcast : ∀ c : Fin 1 × Fin 2, (c.1).castSucc = (0 : Fin 2) := by
      intro c
      have hc1 : c.1 = (0 : Fin 1) := Fin.val_injective (Nat.lt_one_iff.mp c.1.isLt)
      rw [hc1]
      rfl
    show (∑ c : Fin 1 × Fin 2,
        MvPolynomial.eval (fun _ : Fin 2 => (0 : ZMod 2))
          ((RIM (ZMod 2) (k := 2)
            (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) ⟨i, j, hy⟩) c)
        * ((fun c : Fin 1 × Fin 2 => (c.2.val : ZMod 2)) c)) = 0
    refine Finset.sum_eq_zero fun c _ => ?_
    have hRIM : (RIM (ZMod 2) (k := 2) (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2)))
        ⟨i, j, hy⟩) c
        = (MvPolynomial.X i : MvPolynomial (Fin 2) (ZMod 2)) ^ (c.2 : ℕ) :=
      RIM_apply_min (ZMod 2) (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2)))
        ⟨i, j, hy⟩ c ((hcast c).trans hmin.symm)
    rw [hRIM, map_pow, MvPolynomial.eval_X]
    rcases Nat.lt_or_ge c.2.val 1 with hc2 | hc2
    · have hc20 : c.2.val = 0 := by omega
      simp [hc20]
    · have hc21 : c.2.val = 1 := by omega
      simp [hc21]

/-- **Even a genuinely `2`-WPC family fails the unguarded interface at a point-mass
distribution**: the all-zero evaluation is a deficit point
(`zero_eval_mem_rimRankDeficitSet_complete_family`), so the point-mass distribution on it
gives the deficit set measure `1` while `bound = 1/2`. The distribution guard — the
uniform evaluation distribution, exactly as the conditional provider
`rimFailureProb_of_symbolic` instantiates it — is load-bearing. -/
theorem not_RIMFullRankFailureProbResidual_wpc_point_mass :
    ¬ RIMFullRankFailureProbResidual (F := ZMod 2) (k := 2)
        (PMF.pure (fun _ : Fin 2 => (0 : ZMod 2)))
        (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2)))
        ((1 : ENNReal) / 2) := by
  intro h
  unfold RIMFullRankFailureProbResidual at h
  rw [PMF.toOuterMeasure_pure_apply,
    if_pos zero_eval_mem_rimRankDeficitSet_complete_family] at h
  exact absurd h (by norm_num)

/-! ## The guarded repair -/

/-- **[AGL24] Lemma 3.1 interface, guarded** — the honest repair of
`RIMFullRankFailureProbResidual` for downstream consumers: under the uniform evaluation
distribution on `ι → F`, a family with nonempty edges on `t + 1 ≥ 2` vertices that is
`k`-weakly-partition-connected has deficit probability at most `bound`. The premises are
the paper's own side conditions, omitted by the unguarded form (see the two refutations
above); `bound` stays a parameter for the §3 value, discharged by
`rimFailureProbUniformResidual_of_symbolic` at the Schwartz–Zippel bound. -/
def RIMFailureProbUniformResidual (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {t k : ℕ}
    (e : ι → Finset (Fin (t + 1))) (bound : ENNReal) : Prop :=
  1 ≤ t → (∀ i, (e i).Nonempty) →
    WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
    (PMF.uniformOfFintype (ι → F)).toOuterMeasure
      (RIMRankDeficitSet (F := F) (k := k) e) ≤ bound

/-- The guarded interface holds at the Schwartz–Zippel bound conditional only on
`SymbolicFullRankResidual` — the single remaining input of issue #354, exactly as the
census records. -/
theorem rimFailureProbUniformResidual_of_symbolic {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}
    (hsym : SymbolicFullRankResidual (ι := ι) F k)
    {t : ℕ} (ht : 1 ≤ t) (e : ι → Finset (Fin (t + 1)))
    (hwpc : WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e) :
    RIMFailureProbUniformResidual (F := F) (k := k) e
      ((t * k * (k - 1) : ℕ) / (Fintype.card F : ENNReal)) :=
  fun _ _ _ => rimFailureProb_of_symbolic hsym ht e hwpc

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.rimRankDeficitSet_empty_family
#print axioms AGL24.not_RIMFullRankFailureProbResidual_empty_family
#print axioms AGL24.wpc_two_complete_family
#print axioms AGL24.zero_eval_mem_rimRankDeficitSet_complete_family
#print axioms AGL24.not_RIMFullRankFailureProbResidual_wpc_point_mass
#print axioms AGL24.rimFailureProbUniformResidual_of_symbolic
