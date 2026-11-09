/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Domain.CosetFftDomain.Subdomain

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ArkLib.Data.Domain.CosetFftDomain.Ops
import ArkLib.Data.Domain.FftDomain.Ops

/-!
# Subdomains of coset FFT domains

For a coset FFT domain `ω` over `Fin (2 ^ n)` and a depth `i`, we construct the `i`-th subdomain
of size `2 ^ (n - i)`. `subdomain_embed` is the index embedding (shown additive, zero-preserving
and injective via `subdomain_embed_add` / `subdomain_embed_zero` / `subdomain_embed_injective`),
and `subdomain` is the resulting smaller coset FFT domain.

Membership lemmas (`mem_subdomain_of_eq_vals`, `mem_subdomain_0_iff_mem`,
`mem_subdomain_n_iff_eq_pow_generator`) and generator-power computations relate the subdomain back
to the ambient domain.
-/

namespace Domain

variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomainClass

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [CosetFftDomainClass D (Fin (2 ^ n)) F]

variable {ω : D} {x : F}

/-- The zeroth subdomain has the same finite set of field points as the ambient domain. -/
noncomputable def subdomainZeroEquiv (ω : D) :
    (subdomain ω 0) ≃ ω where
  toFun x := by
    refine ⟨x.1, ?_⟩
    rw [mem_toFinset_iff_mem]
    rw [← mem_subdomain_0_iff_mem]
    rw [← mem_toFinset_iff_mem]
    exact x.2
  invFun x := by
    refine ⟨x.1, ?_⟩
    rw [mem_toFinset_iff_mem]
    rw [mem_subdomain_0_iff_mem]
    rw [← mem_toFinset_iff_mem]
    exact x.2
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

lemma card_roots {i j : ℕ} (hij : i + j ≤ n) (h : x ∈ subdomain ω (i + j)) :
    Finset.card {y ∈ (subdomain ω i).toFinset | y ^ (2 ^ j) = x} = 2 ^ j := by
  simpa only [block] using (card_block_of_mem_subdomain hij h)

end CosetFftDomainClass

namespace CosetFftDomain

open CosetFftDomainClass

end CosetFftDomain


/-- Compatibility form of the smooth-coset domain size: the `toFinset` of a
`SmoothCosetFftDomain n F` has exactly `2 ^ n` elements. -/
@[simp]
lemma size_of_smooth_coset_domain_eq_pow_of_2 {F : Type} [Field F] [DecidableEq F]
    {n : ℕ} {ω : SmoothCosetFftDomain n F} :
    Finset.card (Domain.CosetFftDomainClass.toFinset ω) = 2 ^ n := by
  rw [Domain.CosetFftDomainClass.card_toFinset]
  simp

end Domain
