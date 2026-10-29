/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
-- ([propext, Classical.choice, Quot.sound] per decl; verified 2026-06-10 via
-- `lake env lean /tmp/a2_prodmarginal.lean`).
import ProximityPrize.Compatibility.DiscreteProbability
import ArkLib.Data.Probability.MarginalBound

/-!
# Issue #335 (A2) — PRODUCT-marginal domination for one uniformly-drawn vector challenge

The `t`-repetition upgrade of `probEvent_bind_le_uniform_marginal(_comap)`: for a game that
draws ONE vector challenge `v : Vector F t` whose distribution is dominated by the uniform one
(`Pr[= v] ≤ |F|⁻ᵗ`), and whose event is supported inside per-coordinate avoid-sets
(`∃ i, v.get i ∉ L i` kills the continuation), the event probability is at most
`∏ i, |L i| / |F|` — the product budget of paper-STIR's per-round `t`-fold repetition.

* `Vector.card_filter_forall_get_mem` — the counting core: the coordinatewise-membership
  Finset of `Vector F t` has cardinality `∏ i, |L i|` (via `Equiv.rootVectorEquivFin` and
  `Fintype.piFinset`).
* `probEvent_bind_le_uniform_vector_marginal` — the direct product-marginal bound.
* `probEvent_bind_le_uniform_vector_marginal_comap` — the carried-value (comap) form, the
  shape that arises when decomposing a protocol run around the challenge query.
* `probOutput_uniform_vector` — the uniformity supplier for the actual challenge draw:
  `Pr[= v | $ᵗ (Vector F t)] = |F|⁻ᵗ`.
* `probEvent_uniform_vector_bind_le` — the weld: the direct bound with the first stage
  instantiated at the uniform draw, `hunif` discharged by the supplier.
-/

open OracleComp OracleSpec ProbabilityTheory
open scoped ENNReal NNReal

universe u v

section Counting

variable {F : Type u} [Fintype F] {t : ℕ}

/-- **The counting core**: the Finset of vectors whose every coordinate lands in its
per-coordinate set `L i` has cardinality `∏ i, |L i|`. -/
lemma Vector.card_filter_forall_get_mem [Fintype (Vector F t)]
    (L : Fin t → Set F) [∀ i, DecidablePred (· ∈ L i)] :
    (Finset.univ.filter (fun v : Vector F t => ∀ i, v.get i ∈ L i)).card
      = ∏ i : Fin t, (Finset.univ.filter (· ∈ L i)).card := by
  classical
  rw [← Fintype.card_piFinset]
  refine Finset.card_equiv Equiv.rootVectorEquivFin (fun v => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
    Equiv.rootVectorEquivFin, Equiv.coe_fn_mk]

/-- The product budget `∏ i, |L i| / |F|` rewritten as
`(#{v | ∀ i, v.get i ∈ L i}) · (|F|⁻¹)ᵗ` — the shape produced by the counting step. -/
lemma prod_filter_card_div_card_eq [Fintype (Vector F t)]
    (L : Fin t → Set F) [∀ i, DecidablePred (· ∈ L i)] :
    ∏ i : Fin t, (((Finset.univ.filter (· ∈ L i)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
      = ((Finset.univ.filter (fun v : Vector F t => ∀ i, v.get i ∈ L i)).card : ℝ≥0∞)
          * ((Fintype.card F : ℝ≥0∞)⁻¹) ^ t := by
  rw [Vector.card_filter_forall_get_mem L, Nat.cast_prod]
  simp_rw [div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Counting

section VectorMarginal

variable {α β : Type} {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
variable {F : Type} [Fintype F] {t : ℕ}

/-- **Product-marginal domination (card form, direct).**  If the first stage's output
distribution over `Vector F t` is dominated by the uniform one (`Pr[= v] ≤ |F|⁻ᵗ`), and the
event is supported inside the per-coordinate sets `L i` through the drawn vector (any vector
with some coordinate outside its `L i` gives the event probability `0`), then the game's
event probability is at most `∏ i, |L i| / |F|`. -/
theorem probEvent_bind_le_uniform_vector_marginal
    (mx : m (Vector F t)) (k : Vector F t → m β) (q : β → Prop)
    (L : Fin t → Set F) [∀ i, DecidablePred (· ∈ L i)]
    (hunif : ∀ v : Vector F t, probOutput (mx) (v) ≤ (Fintype.card F : ℝ≥0∞)⁻¹ ^ t)
    (hsupp : ∀ v : Vector F t, (∃ i : Fin t, v.get i ∉ L i) → probEvent (q) (k v) = 0) :
    probEvent (q) (mx >>= k)
      ≤ ∏ i : Fin t,
          (((Finset.univ.filter (· ∈ L i)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) := by
  classical
  let : Fintype (Vector F t) := Fintype.ofEquiv _ Equiv.rootVectorEquivFin.symm
  have hcard : Fintype.card (Vector F t) = Fintype.card F ^ t := by
    rw [Fintype.card_congr Equiv.rootVectorEquivFin, Fintype.card_fun, Fintype.card_fin]
  have hbound := probEvent_bind_le_uniform_marginal mx k q
    {v | ∀ i, v.get i ∈ L i}
    (fun v => by simpa only [hcard, Nat.cast_pow, ENNReal.inv_pow] using hunif v)
    (fun v hnot => hsupp v (by simpa only [Set.mem_ofPred_eq, not_forall] using hnot))
  rw [prod_filter_card_div_card_eq L]
  simpa only [Set.mem_ofPred_eq, hcard, Nat.cast_pow, div_eq_mul_inv, ENNReal.inv_pow] using hbound

/-- **Product-marginal domination through a projection (comap form).**  The same bound when the
drawn vector is *carried inside* the first stage's output (the shape that arises when
decomposing a protocol run around the challenge round): `hunif` bounds the carried marginal,
`hsupp` kills continuations whose carried vector has a coordinate outside its `L i`. -/
theorem probEvent_bind_le_uniform_vector_marginal_comap
    (mx : m α) (f : α → Vector F t) (k : α → m β) (q : β → Prop)
    (L : Fin t → Set F) [∀ i, DecidablePred (· ∈ L i)]
    (hunif : ∀ v : Vector F t, probEvent (fun a => f a = v) (mx) ≤ (Fintype.card F : ℝ≥0∞)⁻¹ ^ t)
    (hsupp : ∀ a : α, (∃ i : Fin t, (f a).get i ∉ L i) → probEvent (q) (k a) = 0) :
    probEvent (q) (mx >>= k)
      ≤ ∏ i : Fin t,
          (((Finset.univ.filter (· ∈ L i)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) := by
  classical
  let : Fintype (Vector F t) := Fintype.ofEquiv _ Equiv.rootVectorEquivFin.symm
  have hcard : Fintype.card (Vector F t) = Fintype.card F ^ t := by
    rw [Fintype.card_congr Equiv.rootVectorEquivFin, Fintype.card_fun, Fintype.card_fin]
  have hbound := probEvent_bind_le_uniform_marginal_comap mx f k q
    {v | ∀ i, v.get i ∈ L i}
    (fun v => by simpa only [hcard, Nat.cast_pow, ENNReal.inv_pow] using hunif v)
    (fun a hnot => hsupp a (by simpa only [Set.mem_ofPred_eq, not_forall] using hnot))
  rw [prod_filter_card_div_card_eq L]
  simpa only [Set.mem_ofPred_eq, hcard, Nat.cast_pow, div_eq_mul_inv, ENNReal.inv_pow] using hbound

end VectorMarginal

section UniformSupplier

variable {F : Type} [Fintype F] {t : ℕ}

/-- **The uniformity supplier for the vector challenge draw**: a uniformly drawn
`v : Vector F t` has `Pr[= v] = |F|⁻ᵗ` — the `hunif` side condition of the product-marginal
lemmas at the actual challenge draw (any `SampleableType` instance on `Vector F t`). -/
lemma probOutput_uniform_vector [SampleableType (Vector F t)] (v : Vector F t) :
    probOutput ($ᵗ (Vector F t)) (v) = (Fintype.card F : ℝ≥0∞)⁻¹ ^ t := by
  let : Fintype (Vector F t) := Fintype.ofEquiv _ Equiv.rootVectorEquivFin.symm
  have hcard : Fintype.card (Vector F t) = Fintype.card F ^ t := by
    rw [Fintype.card_congr Equiv.rootVectorEquivFin, Fintype.card_fun, Fintype.card_fin]
  rw [probOutput, SampleableType.prEvent_uniformSample_eq_singleton, hcard, Nat.cast_pow, ENNReal.inv_pow]

/-- **The weld**: the product-marginal bound at the uniform vector challenge draw itself —
`hunif` discharged by `probOutput_uniform_vector`. -/
theorem probEvent_uniform_vector_bind_le [SampleableType (Vector F t)] {β : Type}
    (k : Vector F t → ProbComp β) (q : β → Prop)
    (L : Fin t → Set F) [∀ i, DecidablePred (· ∈ L i)]
    (hsupp : ∀ v : Vector F t, (∃ i : Fin t, v.get i ∉ L i) → probEvent (q) (k v) = 0) :
    probEvent (q) ($ᵗ (Vector F t) >>= k)
      ≤ ∏ i : Fin t,
          (((Finset.univ.filter (· ∈ L i)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  probEvent_bind_le_uniform_vector_marginal ($ᵗ (Vector F t)) k q L
    (fun v => le_of_eq (probOutput_uniform_vector v)) hsupp

end UniformSupplier

/-! ### Axiom audit (issue #335 A2 product-marginal bricks) -/

#print axioms Vector.card_filter_forall_get_mem
#print axioms prod_filter_card_div_card_eq
#print axioms probEvent_bind_le_uniform_vector_marginal
#print axioms probEvent_bind_le_uniform_vector_marginal_comap
#print axioms probOutput_uniform_vector
#print axioms probEvent_uniform_vector_bind_le
