/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude

Ported from mitschabaude-bot/ArkLib:reduced-rate (commit 93fd4833b88fb0b964a29d9ca8cbbcd7ca781ba4).
-/

import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Descent of Reed–Solomon codewords along field embeddings

A codeword over an extension field that agrees with base-field values on at least its dimension
is defined over the base field. Interpolation on the agreement set proves descent without a
finite-field or characteristic assumption.
-/


namespace ReedSolomon

/-- Agreement on at least the dimension with base-field data forces base-field coefficients. -/
theorem exists_base_codeword_of_agreement {I K E : Type} [Field K] [Field E]
    (domain : I ↪ K) (ι : K →+* E) (k : ℕ) (received : I → K) (candidate : I → E)
    (mem : candidate ∈ code ⟨fun i => ι (domain i), ι.injective.comp domain.injective⟩ k)
    (T : Finset I) (large : k ≤ T.card)
    (agree : ∀ i ∈ T, candidate i = ι (received i)) :
    ∃ base : I → K, base ∈ code domain k ∧ candidate = fun i => ι (base i) := by
  classical
  let extended : I ↪ E := ⟨fun i => ι (domain i), ι.injective.comp domain.injective⟩
  obtain ⟨p, hp, heval⟩ := mem_code_iff_eval.mp mem
  let q := Lagrange.interpolate T domain received
  have qdegree : q.degree < T.card := Lagrange.degree_interpolate_lt received domain.injective.injOn
  have same : p = q.map ι := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq T extended.injective.injOn
      (hp.trans_le (by exact_mod_cast large)) (Polynomial.degree_map_le.trans_lt qdegree)
    intro i hi
    change p.eval (ι (domain i)) = (q.map ι).eval (ι (domain i))
    rw [Polynomial.eval_map_apply,
      show q.eval (domain i) = received i from
        Lagrange.eval_interpolate_at_node received domain.injective.injOn hi]
    exact (heval i).trans (agree i hi)
  have qsmall : q.degree < k := by
    rw [← Polynomial.degree_map_eq_of_injective ι.injective q, ← same]
    exact hp
  refine ⟨fun i => q.eval (domain i),
    mem_code_of_polynomial_of_degree_lt_of_eval q qsmall (fun _ => rfl), ?_⟩
  funext i
  rw [← heval i, same]
  exact Polynomial.eval_map_apply _ _

end ReedSolomon

#print axioms ReedSolomon.exists_base_codeword_of_agreement
