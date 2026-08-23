/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BadScalarSingleWord

/-!
# THE STRUCTURED SUPPLY BOUND via the collapse (#389): `Λ ≤ 1`, `#badScalars ≤ ⌊n/a⌋`

The line-list collapse (`lineList_card_le_codeword_list`) reduced the supply to a single-word
list one dimension up.  For a **structured** word `u₀ = U(dom)` with `deg U < a`, that
single-word list is `≤ 1` by a pure degree argument — so the whole structured supply collapses:

* `structured_codeword_list_le_one` — for `u₀ = U(dom)` with `U.natDegree < a` and the dimension
  `d ≤ a`, the agreement-`≥ a` list of `rsCode dom d` codewords near `u₀` has size `≤ 1`: any
  list codeword `Q` has `Q − U` vanishing on `≥ a` points with `deg(Q − U) ≤ a − 1`, forcing
  `Q = U`, so all list members coincide.
* `structured_badScalar_card_le` — composing with the two reductions, for the MCA direction `xᵏ`
  over a `0∉` domain (`k < n`, `k + 1 ≤ a`), the **structured** bad scalars number `≤ ⌊n/a⌋`.

This is the honest *structured* half of the supply wall (matching `StructuredLineCoherence`'s
`Λ ∈ {0,1}` probe), proven through the collapse: the degree argument that closes it is the same
one that fails for **unstructured** `u₀` (degree `≥ a`), where the list can be large — the
recognized open core.  Issue #389.
-/

open Finset Polynomial

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **THE STRUCTURED LIST COLLAPSE**: for `u₀ = U(dom)` with `deg U < a` and dimension `d ≤ a`,
every agreement-`≥ a` codeword of `rsCode dom d` near `u₀` equals `U(dom)` — so the list has
size `≤ 1`.  (A degree-`< a` difference vanishing on `≥ a` points is zero.) -/
theorem structured_codeword_list_le_one (dom : Fin n ↪ F) {d a : ℕ} (hda : d ≤ a)
    {U : F[X]} (hU : U.natDegree < a) :
    ((Finset.univ : Finset (Fin n → F)).filter
        (fun Q => Q ∈ (rsCode dom d : Submodule F (Fin n → F))
          ∧ a ≤ (agreeSet Q (fun i => U.eval (dom i))).card)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro Q hQ Q' hQ'
  obtain ⟨-, ⟨P, hPdeg, hPeq⟩, hQa⟩ := Finset.mem_filter.mp hQ
  obtain ⟨-, ⟨P', hP'deg, hP'eq⟩, hQ'a⟩ := Finset.mem_filter.mp hQ'
  -- each `P − U` vanishes on `≥ a` distinct domain points and has degree `< a` ⟹ `P = U`
  have key : ∀ R : F[X], R.degree < (d : WithBot ℕ) →
      a ≤ (agreeSet (fun i => R.eval (dom i)) (fun i => U.eval (dom i))).card → R = U := by
    intro R hRdeg hRa
    by_contra hne
    have hsub0 : R - U ≠ 0 := sub_ne_zero.mpr hne
    have hRUdeg : (R - U).natDegree < a := by
      have h1 : (R - U).degree < (a : WithBot ℕ) := by
        refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
        · exact lt_of_lt_of_le hRdeg (by exact_mod_cast hda)
        · exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hU)
      exact (natDegree_lt_iff_degree_lt hsub0).mpr h1
    -- the agreement set gives `≥ a` roots of `R − U`
    set S := agreeSet (fun i => R.eval (dom i)) (fun i => U.eval (dom i)) with hS
    have hroots : ∀ i ∈ S, (R - U).IsRoot (dom i) := by
      intro i hi
      rw [hS, agreeSet, Finset.mem_filter] at hi
      simp only [IsRoot, eval_sub]
      rw [hi.2, sub_self]
    have hcard : a ≤ (R - U).natDegree := by
      calc a ≤ S.card := hRa
        _ = (S.image dom).card := (Finset.card_image_of_injective _ dom.injective).symm
        _ ≤ (R - U).roots.toFinset.card := by
            apply Finset.card_le_card
            intro x hx
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
            rw [Multiset.mem_toFinset, mem_roots hsub0]; exact hroots i hi
        _ ≤ Multiset.card (R - U).roots := Multiset.toFinset_card_le _
        _ ≤ (R - U).natDegree := card_roots' _
    omega
  have hPU : P = U := key P hPdeg (by rw [hPeq] at hQa; exact hQa)
  have hP'U : P' = U := key P' hP'deg (by rw [hP'eq] at hQ'a; exact hQ'a)
  rw [hPeq, hP'eq, hPU, hP'U]

open Classical in
/-- **THE STRUCTURED SUPPLY BOUND**: for `u₀ = U(dom)` with `deg U < a`, the MCA direction `xᵏ`
over a `0∉` domain (`k < n`, `k + 1 ≤ a`), the structured bad scalars number `≤ ⌊n/a⌋`. -/
theorem structured_badScalar_card_le (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a)
    (hk : k < n) (hka : k + 1 ≤ a) (hdom : ∀ i, dom i ≠ 0)
    {U : F[X]} (hU : U.natDegree < a) :
    ((Finset.univ : Finset F).filter
        (fun γ => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
          a ≤ (agreeSet c (fun i => U.eval (dom i) + γ • (dom i) ^ k)).card)).card
      ≤ n / a := by
  calc ((Finset.univ : Finset F).filter
        (fun γ => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
          a ≤ (agreeSet c (fun i => U.eval (dom i) + γ • (dom i) ^ k)).card)).card
      ≤ ((Finset.univ : Finset (Fin n → F)).filter
          (fun Q => Q ∈ (rsCode dom (k + 1) : Submodule F (Fin n → F))
            ∧ a ≤ (agreeSet Q (fun i => U.eval (dom i))).card)).card * (n / a) :=
        badScalar_card_le_codeword_list_mul dom k a ha hk _ hdom
    _ ≤ 1 * (n / a) :=
        Nat.mul_le_mul_right _ (structured_codeword_list_le_one dom hka hU)
    _ = n / a := one_mul _

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.structured_codeword_list_le_one
#print axioms ProximityGap.Ownership.structured_badScalar_card_le
