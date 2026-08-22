/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ28D3CoplanarCrack

/-!
# G170 — the general-`D` envelope-partition upper bound on cross-core generation

## What this closes

SYZ28 §1 proved, for `D = 3`, that a joint syndrome span is confined by a *pair-union
envelope*: if `A₀ ⊔ A₁ ≤ B` then `finrank (⨆ᵢ<₃ Aᵢ) ≤ finrank B + finrank A₂`, and if this
count falls below the ceiling `finrank W` then generation fails (over every field).  This is the
mechanism behind the field-independent `D = 3` interior deficiency.

The exact deterministic probe `scripts/probes/probe_466_g170_envelope_partition.py`
establishes the **general-`D` characterization** (2836/2836 covers, `D ∈ {3,4,5}`, strip
interior, `p = 65537`, cross-checked field-independent):

  `d  =  max(0, (n − k) − min over set-partitions P of  Σ_{G ∈ P} (|⋃_{i∈G} Cᵢ| − k)₊)`.

i.e. the joint RS-dual generation deficiency equals the *best* (smallest) envelope-partition
count deficit.  This generalizes SYZ28's `D = 3` pair-union defect to all `D`, and pins the
generation invariant of SYZ33 lemma 2 completely.

This file formalizes the binding (upper-bound / no-go) direction of that characterization — the
one that *forces* deficiency and is field-independent because it is a pure dimension count:

* `partialSup_le_block_envelope` — general-`D` **two-block** envelope split: if the first `m`
  cores sit in an envelope `B`, the whole joint span sits in `B ⊔ (⨆ of the tail)`.
* `finrank_partialSup_le_block_envelope` — the dimension count `finrank ≤ finrank B + Σ tail`.
* `block_envelope_forces_deficiency` — envelope deficit `< finrank W` ⟹ generation fails.

Combined with the `D = 3` instance already in SYZ28, this is the general no-go: **no covering /
overlap-counting argument can license generation once any block of cores has a collapsed union
envelope**, over every field.

## Honest scope

This is the *upper-bound* (deficiency-forcing) half.  It does **not** claim generation ever
holds; the matching lower bound (`d ≤` the best partition count, i.e. that the envelope
partition is *attained*) is the genuinely MDS-arithmetic-essential residual and is left open —
consistent with the companion no-go `probe_466_g170_incremental_prefix_nogo.py`, which shows
that the SYZ26 incremental-prefix covering route provably *cannot* supply that lower bound
(generation `d = 0` holds on concrete interior covers admitting **no** incremental-prefix
ordering).  No new unconditional δ\* claim; CORE remains OPEN / ON-BGK.

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.G170

open Finset Module Submodule
open ArkLib.ProximityGap.Frontier

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-! ## General-`D` two-block envelope split -/

/-- **Tail reindexing.**  The joint span of the last `t` of `A 0 … A (m+t-1)` equals the joint
span of the shifted family `fun j => A (j + m)` over its first `t` indices.  Pure unfolding of
`partialSup` as an `iSup` over `Finset.range`. -/
theorem partialSup_shift (A : ℕ → Submodule F V) (m t : ℕ) :
    SYZ23.partialSup (fun j => A (j + m)) t
      = ⨆ i ∈ Finset.range t, A (i + m) := by
  rfl

/-- **General-`D` two-block envelope split.**  Suppose the first `m` cores collapse into a
common envelope `B` (`⨆_{i<m} A i ≤ B`; for RS cores `B = A_{⋃_{i<m} Cᵢ}`).  Then the entire
`D`-fold joint span sits inside `B ⊔ (tail joint span)` for any `D = m + t`.  This is the
general-`D` avatar of SYZ28's `partialSup_three_le_envelope` (the `m = 2, t = 1` case). -/
theorem partialSup_le_block_envelope (A : ℕ → Submodule F V) (B : Submodule F V)
    (m t : ℕ) (hB : SYZ23.partialSup A m ≤ B) :
    SYZ23.partialSup A (m + t)
      ≤ B ⊔ SYZ23.partialSup (fun j => A (j + m)) t := by
  refine SYZ24.partialSup_le A (B ⊔ SYZ23.partialSup (fun j => A (j + m)) t) (m + t) ?_
  intro i hi
  simp only [Finset.mem_range] at hi
  by_cases hlt : i < m
  · -- `A i` is one of the first block: it lands in `B`.
    refine le_trans ?_ le_sup_left
    refine le_trans ?_ hB
    -- `A i ≤ partialSup A m`
    have : A i ≤ SYZ23.partialSup A m := by
      unfold SYZ23.partialSup
      exact le_iSup_of_le i (le_iSup_of_le (Finset.mem_range.mpr hlt) le_rfl)
    exact this
  · -- `A i` is in the tail: write `i = j + m` and land in the tail joint span.
    refine le_trans ?_ le_sup_right
    have hj : i - m < t := by omega
    have hrw : i = (i - m) + m := by omega
    have : A i ≤ SYZ23.partialSup (fun j => A (j + m)) t := by
      rw [partialSup_shift]
      refine le_iSup_of_le (i - m) (le_iSup_of_le (Finset.mem_range.mpr hj) ?_)
      rw [← hrw]
    exact this

/-- **Envelope count caps the joint rank (general `D`).**  Dimension consequence of the block
split: the joint rank is bounded by the envelope rank plus the tail joint rank.  Valid over
every field — a pure dimension count, the formal reason interior deficiency is
field-independent. -/
theorem finrank_partialSup_le_block_envelope (A : ℕ → Submodule F V) (B : Submodule F V)
    (m t : ℕ) (hB : SYZ23.partialSup A m ≤ B) :
    finrank F (SYZ23.partialSup A (m + t))
      ≤ finrank F B + finrank F (SYZ23.partialSup (fun j => A (j + m)) t) := by
  have h1 : finrank F (SYZ23.partialSup A (m + t))
      ≤ finrank F (B ⊔ SYZ23.partialSup (fun j => A (j + m)) t : Submodule F V) :=
    Submodule.finrank_mono (partialSup_le_block_envelope A B m t hB)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    B (SYZ23.partialSup (fun j => A (j + m)) t)
  omega

/-- **Envelope deficit forces deficiency (general `D`).**  If the first `m` cores collapse into
`B` and the envelope count `finrank B + finrank (tail)` falls strictly below the ceiling
`finrank W`, the full `D`-fold joint span cannot reach `W`: generation fails.  This is the
general-`D` no-go generalizing SYZ28 `envelope_forces_deficiency` — over every field. -/
theorem block_envelope_forces_deficiency (A : ℕ → Submodule F V) (W B : Submodule F V)
    (m t : ℕ) (hB : SYZ23.partialSup A m ≤ B)
    (hcount : finrank F B + finrank F (SYZ23.partialSup (fun j => A (j + m)) t)
      < finrank F W) :
    SYZ23.partialSup A (m + t) ≠ W := by
  intro h
  have hle := finrank_partialSup_le_block_envelope A B m t hB
  rw [h] at hle
  omega

/-- **Consistency with SYZ28 `D = 3`.**  Taking `m = 2, t = 1` recovers exactly the pair-union
envelope split of SYZ28 (`A 0 ⊔ A 1 ≤ B ⟹ partialSup A 3 ≤ B ⊔ A 2`), confirming the general
lemma specializes to the already-landed `D = 3` mechanism. -/
theorem block_envelope_specializes_to_D3 (A : ℕ → Submodule F V) (B : Submodule F V)
    (h01 : A 0 ⊔ A 1 ≤ B) :
    SYZ23.partialSup A 3 ≤ B ⊔ A 2 := by
  have hB : SYZ23.partialSup A 2 ≤ B := by
    rw [SYZ23.partialSup_succ, SYZ23.partialSup_succ, SYZ23.partialSup_zero, sup_bot_eq]
    -- goal: A 1 ⊔ A 0 ≤ B
    rw [sup_comm]
    exact h01
  have hstep := partialSup_le_block_envelope A B 2 1 hB
  -- reduce the tail `partialSup (fun j => A (j+2)) 1` to `A 2`
  have htail : SYZ23.partialSup (fun j => A (j + 2)) 1 = A 2 := by
    rw [SYZ23.partialSup_succ, SYZ23.partialSup_zero, sup_bot_eq]
  rw [htail] at hstep
  simpa using hstep

#print axioms partialSup_le_block_envelope
#print axioms finrank_partialSup_le_block_envelope
#print axioms block_envelope_forces_deficiency
#print axioms block_envelope_specializes_to_D3

end ArkLib.ProximityGap.Frontier.G170
