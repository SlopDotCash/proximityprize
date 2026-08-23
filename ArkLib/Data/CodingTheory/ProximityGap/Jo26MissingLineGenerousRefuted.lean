/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Jo26ObstructionCount

/-!
# S2(b) (#357): the GENEROUS missing-line statement is FALSE — the cocycle construction

Hypothesis S2(b) hoped: no single stack realizes all `q+1` lines of `F²` as obstruction
subspaces `jointStackSubmodule C T U`, so the `≤ q` family demanded by `ObstructionBound`
always exists. This file refutes the **generous form** (where `T` ranges over *all* witness
sets), by an explicit machine-checked counterexample — and isolates exactly what any future
proof of the in-tree `MissingLine` (the constrained, bad-seed-witness form) must use.

**The cocycle mechanism.** For the constants code, the obstruction subspace of a pair
witness `T = {i, j}` for a one-row stack with columns `(w₀, w₁)` is the kernel line of the
*difference vector* `d_{ij} = (w₀ i − w₀ j, w₁ i − w₁ j)`. Difference vectors satisfy the
cocycle relation `d_{ij} + d_{jk} = d_{ik}` — at `n = 3` only three differences exist (which
is why exhaustive search at `n = 3` *appears* to confirm the missing line), but at `n = 4`
the four directions `(1,0), (0,1), (1,1), (1,2)` are simultaneously realizable: take
`w₀ = (0,1,0,1)`, `w₁ = (0,0,1,1)` over `F₃`. All `q + 1 = 4` lines occur as exact
obstruction subspaces:

| `T` | obstruction line |
|---|---|
| `{0,1}` | `span (0,1)` |
| `{0,2}` | `span (1,0)` |
| `{1,2}` | `span (1,1)` |
| `{0,3}` | `span (1,2)` |

`generous_missing_line_refuted` formalizes the consequence: **no** family of `≤ q` proper
subspaces covers all proper obstruction subspaces of this stack.

**What survives.** The in-tree `MissingLine C δ G U` quantifies only over witnesses of
*bad seeds* (`mcaEventG`/`mcaWitnessG`, with the `(1−δ)n` size clause). This refutation
shows its truth — if it is true — cannot come from the linear algebra of the
`jointStackSubmodule` family alone: it must use the badness clause and/or the witness-size
clause. Conversely it hands the S2(b) attack its blueprint: force `q+1` *bad seeds* onto the
`q+1` distinct cocycle lines (the affine design class cannot do this — the in-tree
proportionality trap — but the cocycle class is different). Probe record: exhaustive at
`(F₃, n = 3)` the maximum number of realized lines is exactly `q = 3` for the constants code
(never `q+1`) — the `n = 3` confirmation of S2(b) was a small-`n` artifact of the cocycle
relation, not evidence.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (the δ* campaign; hypothesis S2(b)); [Jo26] ePrint 2026/891 §3–4.
- `Jo26ObstructionCount.lean` (S2(a): `ObstructionBound ⟹` exactness; the named
  `MissingLine` target), `A3ProportionalityTrap.lean` (the affine-class no-go).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators

namespace ProximityGap.Jo26MissingLineGenerous

open ProximityGap

abbrev F3 := ZMod 3

/-- The constants code over `F₃` on 4 points (rate `1/4`). -/
def constC : Submodule F3 (Fin 4 → F3) where
  carrier := {w | ∃ c : F3, ∀ i, w i = c}
  zero_mem' := ⟨0, fun _ => rfl⟩
  add_mem' := by
    rintro w w' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c + c', fun i => by show w i + w' i = c + c'; rw [hc i, hc' i]⟩
  smul_mem' := by
    rintro a w ⟨c, hc⟩
    exact ⟨a * c, fun i => by show a * w i = a * c; rw [hc i]⟩

/-- First column of the cocycle stack. -/
def w0 : Fin 4 → F3 := ![0, 1, 0, 1]

/-- Second column of the cocycle stack. -/
def w1 : Fin 4 → F3 := ![0, 0, 1, 1]

/-- The cocycle stack: one row, two interleaved columns `(w₀, w₁)` — the four pairwise
difference vectors point in all four directions of `F₃²`. -/
def Ucoc : Fin 1 → Fin 4 → Fin 2 → F3 := fun _ i k => if k = 0 then w0 i else w1 i

/-- The plain decidable form of obstruction-subspace membership for the constants code:
the `λ`-combination of the columns is constant on `T`. -/
def inK (T : Finset (Fin 4)) (lam : Fin 2 → F3) : Prop :=
  ∃ c : F3, ∀ i ∈ T, lam 0 * w0 i + lam 1 * w1 i = c

instance (T : Finset (Fin 4)) (lam : Fin 2 → F3) : Decidable (inK T lam) := by
  unfold inK; infer_instance

/-- The bridge: membership in `jointStackSubmodule constC T Ucoc` is exactly `inK T`. -/
theorem mem_jSS_iff_inK (T : Finset (Fin 4)) (lam : Fin 2 → F3) :
    lam ∈ jointStackSubmodule constC T Ucoc ↔ inK T lam := by
  constructor
  · rintro ⟨cs, hcs, hag⟩
    obtain ⟨c, hc⟩ := hcs 0
    refine ⟨c, fun i hi => ?_⟩
    have h : cs 0 i = ∑ k, lam k • Ucoc 0 i k := hag i hi 0
    have hsum : (∑ k, lam k • Ucoc 0 i k) = lam 0 * w0 i + lam 1 * w1 i := by
      rw [Fin.sum_univ_two]
      simp [Ucoc, smul_eq_mul]
    rw [← hsum, ← h]
    exact hc i
  · rintro ⟨c, hc⟩
    refine ⟨fun _ _ => c, fun j => ⟨c, fun _ => rfl⟩, fun i hi j => ?_⟩
    have hsum : (∑ k, lam k • Ucoc j i k) = lam 0 * w0 i + lam 1 * w1 i := by
      rw [Fin.sum_univ_two]
      simp [Ucoc, smul_eq_mul]
    show c = ∑ k, lam k • Ucoc j i k
    rw [hsum, hc i hi]

/-! ### The four realized obstruction lines (membership facts by `decide`) -/

/-- `(0,1) ∈ K_{01}` — and the other three direction vectors are *not* in `K_{01}`. -/
theorem sep01_mem : (![0, 1] : Fin 2 → F3) ∈ jointStackSubmodule constC {0, 1} Ucoc :=
  (mem_jSS_iff_inK _ _).mpr (by decide)

theorem sep02_mem : (![1, 0] : Fin 2 → F3) ∈ jointStackSubmodule constC {0, 2} Ucoc :=
  (mem_jSS_iff_inK _ _).mpr (by decide)

theorem sep12_mem : (![1, 1] : Fin 2 → F3) ∈ jointStackSubmodule constC {1, 2} Ucoc :=
  (mem_jSS_iff_inK _ _).mpr (by decide)

theorem sep03_mem : (![1, 2] : Fin 2 → F3) ∈ jointStackSubmodule constC {0, 3} Ucoc :=
  (mem_jSS_iff_inK _ _).mpr (by decide)

/-- Cross-exclusions: each direction vector lies in exactly its own line (12 facts), plus
each line misses some vector (properness). Bundled as one decidable conjunction. -/
theorem cross_exclusions :
    (¬ inK {0, 1} ![1, 0]) ∧ (¬ inK {0, 1} ![1, 1]) ∧ (¬ inK {0, 1} ![1, 2]) ∧
    (¬ inK {0, 2} ![0, 1]) ∧ (¬ inK {0, 2} ![1, 1]) ∧ (¬ inK {0, 2} ![1, 2]) ∧
    (¬ inK {1, 2} ![0, 1]) ∧ (¬ inK {1, 2} ![1, 0]) ∧ (¬ inK {1, 2} ![1, 2]) ∧
    (¬ inK {0, 3} ![0, 1]) ∧ (¬ inK {0, 3} ![1, 0]) ∧ (¬ inK {0, 3} ![1, 1]) := by
  decide

/-- Not-mem at the submodule level, from `cross_exclusions`. -/
theorem notMem_of_not_inK {T : Finset (Fin 4)} {lam : Fin 2 → F3} (h : ¬ inK T lam) :
    lam ∉ jointStackSubmodule constC T Ucoc :=
  fun hm => h ((mem_jSS_iff_inK T lam).mp hm)

/-! ### The refutation -/

open Classical in
/-- **The generous missing-line statement is FALSE.** For the cocycle stack over `F₃` on
4 points, *no* family of at most `q = 3` proper subspaces of `F₃²` contains every proper
obstruction subspace `jointStackSubmodule constC T Ucoc`: the four witness sets
`{0,1}, {0,2}, {1,2}, {0,3}` realize four pairwise-distinct proper subspaces. Any proof of
the in-tree `MissingLine` must therefore use the bad-seed/witness-size clauses — the
linear-algebraic obstruction-family geometry alone cannot deliver it. -/
theorem generous_missing_line_refuted :
    ¬ ∃ Ls : Finset (Submodule F3 (Fin 2 → F3)),
        Ls.card ≤ Fintype.card F3 ∧ (∀ K ∈ Ls, K ≠ ⊤) ∧
        ∀ T : Finset (Fin 4), jointStackSubmodule constC T Ucoc ≠ ⊤ →
          jointStackSubmodule constC T Ucoc ∈ Ls := by
  rintro ⟨Ls, hcard, _hproper, hcover⟩
  obtain ⟨h01_10, h01_11, h01_12, h02_01, h02_11, h02_12,
    h12_01, h12_10, h12_12, h03_01, h03_10, h03_11⟩ := cross_exclusions
  set K01 := jointStackSubmodule constC ({0, 1} : Finset (Fin 4)) Ucoc with hK01
  set K02 := jointStackSubmodule constC ({0, 2} : Finset (Fin 4)) Ucoc with hK02
  set K12 := jointStackSubmodule constC ({1, 2} : Finset (Fin 4)) Ucoc with hK12
  set K03 := jointStackSubmodule constC ({0, 3} : Finset (Fin 4)) Ucoc with hK03
  -- the K-typed membership facts
  have hs01 : (![0, 1] : Fin 2 → F3) ∈ K01 := sep01_mem
  have hs02 : (![1, 0] : Fin 2 → F3) ∈ K02 := sep02_mem
  have hs12 : (![1, 1] : Fin 2 → F3) ∈ K12 := sep12_mem
  have hn01_10 : (![1, 0] : Fin 2 → F3) ∉ K01 := notMem_of_not_inK h01_10
  have hn02_01 : (![0, 1] : Fin 2 → F3) ∉ K02 := notMem_of_not_inK h02_01
  have hn12_01 : (![0, 1] : Fin 2 → F3) ∉ K12 := notMem_of_not_inK h12_01
  have hn03_01 : (![0, 1] : Fin 2 → F3) ∉ K03 := notMem_of_not_inK h03_01
  have hn12_10 : (![1, 0] : Fin 2 → F3) ∉ K12 := notMem_of_not_inK h12_10
  have hn03_10 : (![1, 0] : Fin 2 → F3) ∉ K03 := notMem_of_not_inK h03_10
  have hn03_11 : (![1, 1] : Fin 2 → F3) ∉ K03 := notMem_of_not_inK h03_11
  -- properness (each line misses a vector)
  have hne01 : K01 ≠ ⊤ := fun h => hn01_10 (h.symm ▸ Submodule.mem_top)
  have hne02 : K02 ≠ ⊤ := fun h => hn02_01 (h.symm ▸ Submodule.mem_top)
  have hne12 : K12 ≠ ⊤ := fun h => hn12_01 (h.symm ▸ Submodule.mem_top)
  have hne03 : K03 ≠ ⊤ := fun h => hn03_01 (h.symm ▸ Submodule.mem_top)
  -- all four are covered
  have hm01 : K01 ∈ Ls := hcover _ hne01
  have hm02 : K02 ∈ Ls := hcover _ hne02
  have hm12 : K12 ∈ Ls := hcover _ hne12
  have hm03 : K03 ∈ Ls := hcover _ hne03
  -- pairwise distinct (separator vectors)
  have hd_01_02 : K01 ≠ K02 := fun h => hn02_01 (h ▸ hs01)
  have hd_01_12 : K01 ≠ K12 := fun h => hn12_01 (h ▸ hs01)
  have hd_01_03 : K01 ≠ K03 := fun h => hn03_01 (h ▸ hs01)
  have hd_02_12 : K02 ≠ K12 := fun h => hn12_10 (h ▸ hs02)
  have hd_02_03 : K02 ≠ K03 := fun h => hn03_10 (h ▸ hs02)
  have hd_12_03 : K12 ≠ K03 := fun h => hn03_11 (h ▸ hs12)
  -- the 4-element subfamily has card 4, but |Ls| ≤ |F₃| = 3
  have hsub : ({K01, K02, K12, K03} : Finset (Submodule F3 (Fin 2 → F3))) ⊆ Ls := by
    intro K hK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hK
    rcases hK with rfl | rfl | rfl | rfl
    exacts [hm01, hm02, hm12, hm03]
  have hcard4 : ({K01, K02, K12, K03} : Finset (Submodule F3 (Fin 2 → F3))).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hd_01_02, hd_01_12, hd_01_03⟩)]
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hd_02_12, hd_02_03⟩)]
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact hd_12_03)]
    rfl
  have h4le : (4 : ℕ) ≤ Ls.card := hcard4 ▸ Finset.card_le_card hsub
  have h3 : Fintype.card F3 = 3 := by rw [ZMod.card]
  omega

/-! ## Source audit -/

#print axioms mem_jSS_iff_inK
#print axioms cross_exclusions
#print axioms generous_missing_line_refuted

end ProximityGap.Jo26MissingLineGenerous
