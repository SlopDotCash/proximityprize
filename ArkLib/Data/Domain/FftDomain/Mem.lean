/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ArkLib.Data.Domain.CosetFftDomain.Mem
import ArkLib.Data.Domain.FftDomain.Defs
import ArkLib.ToMathlib.Finset.ToListWithProof

/-!
# Membership for FFT domains

We specialize the coset membership theory to FFT domains: `one_mem`, the existence
characterizations `mem_iff_exists` and `mem_iff_mem_toCosetFftDomain`, and their `toFinset`
counterparts (`mem_toFinset_iff_exists`, `mem_toFinset_iff_mem`). A `Decidable (x ∈ ω)` instance
is also provided.
-/

namespace Domain

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace FftDomainClass

variable {D : Type} [FunLike D ι F] [FftDomainClass D ι F]
variable {ω : D}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma one_mem : 1 ∈ ω := ⟨0, FftDomainClass.generator_eq_one ω⟩

end FftDomainClass

namespace FftDomain

open CosetFftDomain

variable {ω : FftDomain ι F} {x : F}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mem_iff_exists :
    x ∈ ω ↔ ∃ i, x = ω.subgroupDomain i := by
  aesop (add simp [Membership.mem])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mem_iff_mem_toCosetFftDomain :
    x ∈ ω ↔ x ∈ ω.toCosetFftDomain := by
  simp [mem_iff_exists, mem_iff_exists_mul, ω.cosetGenerator_one]

omit [DecidableEq ι] in
lemma mem_toFinset_iff_exists :
    x ∈ ω.toFinset ↔ ∃ i, x = ω.subgroupDomain i := by
  rw [CosetFftDomainClass.mem_toFinset_iff_mem,
      CosetFftDomainClass.mem_def]
  aesop

omit [DecidableEq ι] in
@[simp]
lemma mem_toFinset_iff_mem :
    x ∈ ω.toFinset ↔ x ∈ ω := by
  rw [CosetFftDomainClass.mem_toFinset_iff_mem,
      mem_iff_mem_toCosetFftDomain]

end FftDomain

instance {x : F} {ω : FftDomain ι F} : Decidable (x ∈ ω) :=
  decidable_of_iff _ FftDomain.mem_toFinset_iff_mem

end Domain
