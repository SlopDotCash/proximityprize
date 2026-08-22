/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ArkLib.Data.Domain.CosetFftDomain.Defs
import ArkLib.ToMathlib.Finset.ToListWithProof

/-!
# Membership for coset FFT domains

We equip a coset FFT domain `D` with a `Membership F D` instance (`x ∈ φ ↔ ∃ i, φ i = x`) and
prove the basic membership characterizations: `mem_def`, `mem_self`, the bridges
`mem_toCosetFftDomain_iff_mem` / `mem_toFinset_iff_mem`, `not_zero_mem`, and
`mem_iff_exists_mul`. `Inhabited` instances for the underlying domain and its `toFinset` are also
provided.
-/

namespace Domain

open Function

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

instance {D : Type}
  [FunLike D ι F] [CosetFftDomainClass D ι F] : Membership F D where
  mem φ x := ∃ i, φ i = x

instance
    {ι : Type} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F] :
  CoeSort D Type where
    coe d := CosetFftDomainClass.toFinset d

namespace CosetFftDomainClass

variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F] {ω : D}
variable {x : F}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mem_def : x ∈ ω ↔ ∃ i, x = ω i := by aesop (add simp [Membership.mem])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp high]
lemma mem_self {i : ι} :
    ω i ∈ ω := by simp [mem_def]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma mem_toCosetFftDomain_iff_mem :
    x ∈ toCosetFftDomain ω ↔ x ∈ ω := by
  aesop (add simp
          [mkSubgroupUnit,
            mem_def,
            toCosetFftDomain,
            CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])

omit [DecidableEq ι] in
@[simp]
lemma mem_toFinset_iff_mem :
    x ∈ toFinset ω ↔ x ∈ ω := by aesop (add simp [toFinset, mem_def])

omit [DecidableEq ι] in
@[simp high]
lemma mem_toFinset_self {i : ι} :
    ω i ∈ toFinset ω := by simp

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
@[simp]
lemma not_zero_mem :
    0 ∉ ω := fun contra ↦ by
  rw [mem_def] at contra
  obtain ⟨i, contra⟩ := contra
  exact CosetFftDomainClass.ne_zero ω i (by simp_all)

omit [DecidableEq ι] in
@[simp high]
lemma not_zero_mem_toFinset :
  0 ∉ toFinset ω := by simp

end CosetFftDomainClass

instance {ω : CosetFftDomain ι F} : Inhabited ω.toFinset where
  default := ⟨ω 0, by simp [CosetFftDomainClass.toFinset]⟩

instance {ω : CosetFftDomain ι F} : Inhabited ω where
  default := ⟨ω 0, by simp [CosetFftDomainClass.toFinset]⟩


namespace CosetFftDomain

variable {ω : CosetFftDomain ι F} {x : F}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma mem_iff_exists_mul :
    x ∈ ω ↔ ∃ i, x = ω.cosetGenerator * ω.subgroupDomain i := by
  aesop (add simp [Membership.mem])

omit [DecidableEq ι] in
lemma mem_toFinset_iff_exists_mul :
    x ∈ ω.toFinset ↔ ∃ i, x = ω.cosetGenerator * ω.subgroupDomain i := by
  aesop (add simp [CosetFftDomainClass.toFinset])

omit [DecidableEq ι] in
@[simp]
lemma mem_toFinset_iff_mem :
    x ∈ ω.toFinset ↔ x ∈ ω := CosetFftDomainClass.mem_toFinset_iff_mem

omit [DecidableEq ι] in
@[simp high]
lemma mem_toFinset_self {i : ι} :
    ω i ∈ ω.toFinset := CosetFftDomainClass.mem_toFinset_self

end CosetFftDomain

instance {x : F} {ω : CosetFftDomain ι F} : Decidable (x ∈ ω) :=
  decidable_of_iff _ CosetFftDomain.mem_toFinset_iff_mem

end Domain
