/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-! Scratch: does Mathlib have a fewnomial/Descartes root bound by support card? -/
open Polynomial

-- The bound we'd need: #roots <= f(support.card), independent of degree, over roots of unity.
-- Mathlib has: Polynomial.card_roots' : (p.roots).card <= p.natDegree  (degree-governed, NOT support)
#check @Polynomial.card_roots'
-- UnitTrinomial: only card_support_eq_three, no root bound.
-- So a Schlickewei-Evertse / Mann bound is NOT in Mathlib. Must be built from scratch.

-- Can we even state the n-independent ragged bound as a clean Prop? Yes (matches in-tree
-- SparseRaggedExcessBound). The CONTENT (f exists, char-free) is the open math.
example (t : ℕ) : ∃ f : ℕ → ℕ, ∀ (S : Finset ℂ) (P : ℂ[X]),
    P ≠ 0 → P.support.card = t → (∀ x ∈ S, P.IsRoot x) →
    -- ragged excess (after stripping cyclotomic-coset factors) <= f t :
    True := ⟨fun _ => 0, by intros; trivial⟩
