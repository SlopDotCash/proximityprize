/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ArkLib.Data.Domain.CosetFftDomain.Mem
import ArkLib.Data.Domain.CosetFftDomain.ToFftDomain
import ArkLib.Data.Domain.FftDomain.Ops

/-!
# Pointwise operations on coset FFT domains

We compute how the coset FFT domain map interacts with the additive group structure on indices:
`apply_zero`, `apply_add_eq_inv_mul_mul`, `apply_neg_eq_sq_mul_inv`, and `apply_sub_eq_mul_div`.

We also relate negation of indices to domain membership (`neg_mem_domain_of_mem`,
`neg_mem_domain_iff_mem`) and derive `domain_implies_char_ne_2`.
-/

namespace Domain

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomain

variable {ω : CosetFftDomain ι F} {i j : ι}

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma apply_zero : ω 0 = ω.cosetGenerator := by
  simp only [eval_coset_fft_domain_eq_eval_generator_mul_domain, subgroupUnit_zero,
    Units.val_one, mul_one]

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma apply_add_eq_inv_mul_mul :
    ω (i + j) = ω.cosetGenerator⁻¹ * ω i * ω j := by
  simpa only [apply_zero, Units.val_inv_eq_inv_val] using
    CosetFftDomainClass.map_add ω i j

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma apply_neg_eq_sq_mul_inv :
    ω (-i) = ω.cosetGenerator ^ 2 * (ω i)⁻¹ := by
  simpa only [apply_zero] using CosetFftDomainClass.map_neg ω i

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma apply_sub_eq_mul_div :
    ω (i - j) = ω.cosetGenerator * ω i / ω j := by
  rw [sub_eq_add_neg, apply_add_eq_inv_mul_mul, apply_neg_eq_sq_mul_inv]
  have h := Units.ne_zero ω.cosetGenerator
  push_cast
  field_simp

end CosetFftDomain

namespace CosetFftDomainClass

section Smooth

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [CosetFftDomainClass D (Fin (2 ^ n)) F]
variable {ω : D} {x : F}

omit [DecidableEq F] in
theorem neg_mem_domain_of_mem [nz : NeZero n] (h : x ∈ ω) :
    -x ∈ ω := by
  rw [show -x = (-1) * x by simp]
  exact CosetFftDomainClass.mul_mem_of_mem_toFftDomain_of_mem (by simp) h

omit [DecidableEq F] in
@[simp]
lemma neg_mem_domain_iff_mem [nz : NeZero n] :
    -x ∈ ω ↔ x ∈ ω := by
  constructor <;> intro h
  · rw [show x = -(-x) by simp]
    exact neg_mem_domain_of_mem h
  · exact neg_mem_domain_of_mem h

omit [DecidableEq F] in
lemma domain_implies_char_ne_2 [NeZero n] (ω : D) :
    ¬CharP F 2 := FftDomainClass.domain_implies_char_ne_2 (toFftDomain ω)

end Smooth

end CosetFftDomainClass

end Domain
