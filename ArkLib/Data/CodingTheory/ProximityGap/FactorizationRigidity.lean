/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots

/-!
# Factorization Rigidity (proximity-prize δ* optimality core, #407)

The two faces of the lemma `∏_{z∈S}(X-z)` is `m`-sparse ⟺ `S` is a union of cosets of `μ_m`,
the machinery that reduces the Kambiré-construction optimality (the δ* lower bracket) to known
polynomial-in-`Xᵐ` structure.  Both faces are proved here, axiom-clean, from `Polynomial.expand`.
-/

namespace ArkLib.ProximityGap.FactorizationRigidity

open Polynomial

variable {R : Type*} [CommRing R]

/-- **Factorization rigidity — support face.** A polynomial is in the image of `expand R m`
(a polynomial in `Xᵐ`, i.e. "`m`-sparse": supported only on degrees divisible by `m`) **iff**
its support lies in the multiples of `m`. -/
theorem mem_range_expand_iff {m : ℕ} (hm : m ≠ 0) (f : R[X]) :
    (∃ g, expand R m g = f) ↔ ∀ n, ¬ m ∣ n → f.coeff n = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ n hn
    rw [coeff_expand (Nat.pos_of_ne_zero hm)]; exact if_neg hn
  · intro h
    refine ⟨contract m f, ?_⟩
    ext n
    rw [coeff_expand (Nat.pos_of_ne_zero hm)]
    split_ifs with hdvd
    · obtain ⟨k, rfl⟩ := hdvd
      rw [Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hm), coeff_contract hm, Nat.mul_comm]
    · exact (h n hdvd).symm

/-- **Factorization rigidity — root face.** If `f = g(Xᵐ)` is a polynomial in `Xᵐ` and `ω` is an
`m`-th root of unity, then the root set of `f` is closed under multiplication by `ω`. Hence the
agreement set of an `m`-sparse near-codeword `Xᵃ + γXᵇ − c` (`a,b` multiples of `m`) is a union of
cosets of `μ_m` — the structural input that turns the bad-scalar count into the subgroup sumset. -/
theorem isRoot_smul_of_mem_range_expand {m : ℕ} {g : R[X]} {ω z : R}
    (hω : ω ^ m = 1) (hz : (expand R m g).IsRoot z) :
    (expand R m g).IsRoot (ω * z) := by
  simp only [IsRoot.def, expand_eval, mul_pow, hω, one_mul] at hz ⊢
  exact hz

/-- Convenience corollary: divisible-support polynomials have `μ_m`-invariant root sets directly. -/
theorem isRoot_smul_of_support {m : ℕ} (hm : m ≠ 0) {f : R[X]} {ω z : R}
    (hsupp : ∀ n, ¬ m ∣ n → f.coeff n = 0) (hω : ω ^ m = 1) (hz : f.IsRoot z) :
    f.IsRoot (ω * z) := by
  obtain ⟨g, rfl⟩ := (mem_range_expand_iff hm f).2 hsupp
  exact isRoot_smul_of_mem_range_expand hω hz

end ArkLib.ProximityGap.FactorizationRigidity
