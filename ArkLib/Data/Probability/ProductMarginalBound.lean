/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Compatibility.DiscreteProbability
import ArkLib.Data.Probability.MarginalBound
import ArkLib.Data.Probability.ProductMarginal

/-!
# Product-marginal / repetition-amplification bricks (issue #301, hypothesis A2)

Protocol-independent probability lemmas isolating the *per-coordinate factorization* of a
uniformly-dominated vector-challenge draw — hypothesis A2 of the #301 portfolio.  Where
`MarginalBound.lean` bounds a single-challenge game by the uniform measure of one bad set `L`,
these bricks bound a *vector*-challenge game (a draw from `Vector F t`, the Array-based core
vector used by `VectorIOR`) by the **product** of the per-coordinate uniform measures:

* `card_filter_forall_get_mem` — the counting kernel: the number of vectors landing
  coordinatewise in `L i` is `∏ i, |L i|`.

* `card_vector_pow` — `|Vector F t| = |F| ^ t`, transported through the
  `Equiv.rootVectorEquivFin` bridge to `Fin t → F`.

* `probEvent_bind_le_uniform_marginal_product` — **product-marginal domination**: if the first
  stage's output distribution on `Vector F t` is dominated by the uniform one
  (`Pr[= v] ≤ 1/|F|^t`) and the event is supported inside the coordinatewise bad set
  (`v.get i ∈ L i` for all `i`), then the game's event probability is at most
  `∏ i, |L i| / |F|`.

* `probEvent_bind_le_pow_uniform_marginal` — the **repetition-amplification headline**: with a
  uniform per-coordinate bound `|L i| ≤ s`, the game's event probability is at most
  `(s / |F|) ^ t`.

These are consumed by the repetition lift (hypothesis A1 of #301): `t`-point checking verifiers
achieving `(·)^t` round budgets — the path to genuine `2^{-secpar}` round-by-round budgets in
the STIR/WHIR wire models, where a single per-round bad-set bound `s / |F|` is amplified to
`(s / |F|)^t` by drawing `t` independent challenge points.

Relationship to `ProductMarginal.lean` (the #335 lane's independently-landed sibling): that file
provides the linear-budget direct/comap/weld forms over `Set`-valued per-coordinate constraints
(`probEvent_bind_le_uniform_vector_marginal(_comap)`, `probEvent_uniform_vector_bind_le`); this
file provides the `Finset`-interface counting kernel, `card_vector_pow`, and the `(s/|F|)^t`
power forms.  The comap/weld POWER corollaries below complete the matrix by composing the two:
they are the shapes the `t`-point checking-verifier soundness (A1) consumes when the drawn
vector is carried inside a transcript tuple, resp. drawn directly by `$ᵗ`.
-/

open OracleComp OracleSpec ProbabilityTheory
open scoped ENNReal NNReal

universe u v

section Counting

variable {α : Type u}

/-- **Counting kernel.**  The number of vectors `v : Vector α t` landing coordinatewise in the
sets `L i` is the product of the coordinatewise cardinalities `∏ i, |L i|`. -/
lemma card_filter_forall_get_mem [DecidableEq α] {t : ℕ} [Fintype (Vector α t)]
    (L : Fin t → Finset α) :
    (Finset.univ.filter (fun v : Vector α t => ∀ i, v.get i ∈ L i)).card
      = ∏ i, (L i).card := by
  rw [show (Finset.univ.filter (fun v : Vector α t => ∀ i, v.get i ∈ L i)).card
        = (Fintype.piFinset L).card from
      Finset.card_equiv Equiv.rootVectorEquivFin (fun v => by
        simp [Equiv.rootVectorEquivFin, Fintype.mem_piFinset])]
  exact Fintype.card_piFinset L

/-- **Vector cardinality.**  `|Vector α t| = |α| ^ t`, via the `Fin t → α` bridge. -/
lemma card_vector_pow [Fintype α] {t : ℕ} [Fintype (Vector α t)] :
    Fintype.card (Vector α t) = Fintype.card α ^ t := by
  rw [Fintype.card_congr (Equiv.rootVectorEquivFin (α := α) (n := t)),
    Fintype.card_fun, Fintype.card_fin]

end Counting

section ProductMarginal

variable {β : Type} {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **Product-marginal domination.**  If the first stage's output distribution on `Vector F t`
is dominated by the uniform one (`Pr[= v] ≤ 1/|F|^t`, true in particular for `t` independent
uniform draws), and the event is supported inside the coordinatewise bad set (`q` has
probability `0` after drawing any `v` with some `v.get i ∉ L i`), then the game's event
probability is at most the product of the per-coordinate uniform measures `∏ i, |L i| / |F|`. -/
lemma probEvent_bind_le_uniform_marginal_product {F : Type} [Fintype F] [DecidableEq F]
    {t : ℕ} (mx : m (Vector F t)) (k : Vector F t → m β) (q : β → Prop) (L : Fin t → Finset F)
    (hunif : ∀ v : Vector F t, probOutput (mx) (v) ≤ ((Fintype.card F : ℝ≥0∞) ^ t)⁻¹)
    (hsupp : ∀ v : Vector F t, (¬ ∀ i, v.get i ∈ L i) → probEvent (q) (k v) = 0) :
    probEvent (q) (mx >>= k)
      ≤ ∏ i, ((L i).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  have hbound := probEvent_bind_le_uniform_vector_marginal mx k q
    (fun i => (L i : Set F))
    (fun v => by simpa only [ENNReal.inv_pow] using hunif v)
    (fun v hv => hsupp v (not_forall.mpr hv))
  simpa using hbound

/-- **Repetition-amplification headline.**  Under the hypotheses of
`probEvent_bind_le_uniform_marginal_product`, a uniform per-coordinate bound `|L i| ≤ s`
amplifies to the `t`-fold power bound `(s / |F|) ^ t` — the `(·)^t` round-budget shape of the
#301 repetition lift. -/
lemma probEvent_bind_le_pow_uniform_marginal {F : Type} [Fintype F] [DecidableEq F]
    {t : ℕ} (mx : m (Vector F t)) (k : Vector F t → m β) (q : β → Prop) (L : Fin t → Finset F)
    (s : ℕ)
    (hunif : ∀ v : Vector F t, probOutput (mx) (v) ≤ ((Fintype.card F : ℝ≥0∞) ^ t)⁻¹)
    (hsupp : ∀ v : Vector F t, (¬ ∀ i, v.get i ∈ L i) → probEvent (q) (k v) = 0)
    (hL : ∀ i, (L i).card ≤ s) :
    probEvent (q) (mx >>= k) ≤ ((s : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ^ t := by
  refine le_trans
    (probEvent_bind_le_uniform_marginal_product mx k q L hunif hsupp) ?_
  calc ∏ i, ((L i).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ ∏ _i : Fin t, (s : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
        Finset.prod_le_prod (fun i _ =>
          ENNReal.div_le_div_right (Nat.cast_le.mpr (hL i)) _)
    _ = ((s : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ^ t := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end ProductMarginal

section PowMatrix

variable {α β : Type} {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
variable {F : Type} [Fintype F] {t : ℕ}

private lemma prod_filter_le_pow (L : Fin t → Set F) [∀ i, DecidablePred (· ∈ L i)] (s : ℕ)
    (hL : ∀ i, (Finset.univ.filter (· ∈ L i)).card ≤ s) :
    ∏ i : Fin t, (((Finset.univ.filter (· ∈ L i)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
      ≤ ((s : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ^ t :=
  calc ∏ i : Fin t, (((Finset.univ.filter (· ∈ L i)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
      ≤ ∏ _i : Fin t, (s : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
        Finset.prod_le_prod (fun i _ =>
          ENNReal.div_le_div_right (Nat.cast_le.mpr (hL i)) _)
    _ = ((s : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ^ t := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Repetition amplification, comap form.**  The `(s / |F|) ^ t` power bound when the drawn
vector is *carried inside* the first stage's output (the shape arising when a protocol run is
decomposed around the vector-challenge round) — composing
`ProductMarginal.probEvent_bind_le_uniform_vector_marginal_comap` with the per-coordinate
cardinality bound. -/
theorem probEvent_bind_le_pow_uniform_marginal_comap
    (mx : m α) (f : α → Vector F t) (k : α → m β) (q : β → Prop)
    (L : Fin t → Set F) [∀ i, DecidablePred (· ∈ L i)] (s : ℕ)
    (hunif : ∀ v : Vector F t, probEvent (fun a => f a = v) (mx) ≤ (Fintype.card F : ℝ≥0∞)⁻¹ ^ t)
    (hsupp : ∀ a : α, (∃ i : Fin t, (f a).get i ∉ L i) → probEvent (q) (k a) = 0)
    (hL : ∀ i, (Finset.univ.filter (· ∈ L i)).card ≤ s) :
    probEvent (q) (mx >>= k) ≤ ((s : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ^ t :=
  le_trans
    (probEvent_bind_le_uniform_vector_marginal_comap mx f k q L hunif hsupp)
    (prod_filter_le_pow L s hL)

end PowMatrix

section PowWeld

variable {F : Type} [Fintype F] {t : ℕ}

/-- **Repetition amplification at the uniform draw itself (weld form).**  The `(s / |F|) ^ t`
power bound for a game drawing its vector challenge directly by `$ᵗ` — `hunif` discharged by
`ProductMarginal.probOutput_uniform_vector`. -/
theorem probEvent_uniform_vector_bind_le_pow [SampleableType (Vector F t)] {β : Type}
    (k : Vector F t → ProbComp β) (q : β → Prop)
    (L : Fin t → Set F) [∀ i, DecidablePred (· ∈ L i)] (s : ℕ)
    (hsupp : ∀ v : Vector F t, (∃ i : Fin t, v.get i ∉ L i) → probEvent (q) (k v) = 0)
    (hL : ∀ i, (Finset.univ.filter (· ∈ L i)).card ≤ s) :
    probEvent (q) ($ᵗ (Vector F t) >>= k) ≤ ((s : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ^ t :=
  le_trans
    (probEvent_uniform_vector_bind_le k q L hsupp)
    (prod_filter_le_pow L s hL)

end PowWeld

/-! ### Axiom audit (issue #301 product-marginal bricks) -/

#print axioms card_filter_forall_get_mem
#print axioms card_vector_pow
#print axioms probEvent_bind_le_uniform_marginal_product
#print axioms probEvent_bind_le_pow_uniform_marginal
#print axioms probEvent_bind_le_pow_uniform_marginal_comap
#print axioms probEvent_uniform_vector_bind_le_pow
