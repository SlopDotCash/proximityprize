# #466 lane G93 — additive-model production theorem (Tier-3 "function-field model" lane, additive branch): LANDED, axiom-clean (2026-07-10)

`Frontier/_G93AdditiveModelDissolution.lean` (457 lines, 20 audited decls, all ⊆
`[propext, Classical.choice, Quot.sound]`, pg-iterate 47s, no sorry/axiom/native_decide;
Fable swarm, session 7f328bcc).

Completes the unformalized residue of lanes L5 (`_AdditiveDomainDissolution(-Dual).lean`) and
W4 (`_FunctionFieldModelSubfieldDegeneracy.lean`) — no duplication of their landed dichotomy
(`η_b(S) ∈ {0,|S|}`), spike localization, coset blindness, or the multiplicative `F_q[t]`
transplant kill.

## New theorems (all elementary — zero Weil input anywhere)

1. **Exact index law** — `card_annihilator_mul_card`, `card_annihilator`: for primitive `ψ` on a
   finite commutative ring and any additive subgroup/`F₂`-subspace `s`, `|s^⊥|·|s| = |F|`, i.e.
   `|s^⊥| = |F|/|s| = m` exactly (the L5 kb note's unformalized Parseval cross-check, now a
   theorem via a `sum_mulShift` first-moment double-count — no conjugation). The model reproduces
   the prize index `m` as the exact size of the spike locus.
2. **Double annihilator** — `annihilator_annihilator`: `S^⊥⊥ = S`. Makes the relocation lossless.
3. **Coset faithfulness (the relocation theorem)** — `sub_mem_iff_annihilator_phase_eq`:
   `y−y′ ∈ S ⟺ ∀ b ∈ S^⊥, ψ(by) = ψ(by′)`. With L5 coset blindness: the `S^⊥`-phase vector is a
   complete invariant of the `S`-coset; directions off `S^⊥` carry nothing.
4. **The production-shaped model theorem** — `model_production_bound`: for every `b ∉ S^⊥`,
   `‖Σ_{x∈S} ψ(bx)‖ ≤ √(|S|·log(|F|/|S|))` — the verbatim shape of the open core
   `M(μ_n) ≤ C√(n log(p/n))`, unconditional, `C = 1`; in fact the LHS is identically 0
   (`model_offSpike_norm_eq_zero`): the Johnson→capacity character-sum gap VANISHES in the
   additive model. First machine-checked production-shaped closure in any model.
5. **Necessity of the excision** — `exists_nonzero_spike` / `naive_model_sup_attains_card`: for
   proper `S` the naive sup over all `b ≠ 0` attains `|S|` exactly — excising the index-sized
   `S^⊥` is necessary.
6. Binius/`F₂` instantiations (`binius_*` via `annihilator_toAddSubgroup`) and finite-field forms
   needing only `ψ ≠ 1`.

## Honest scope / relocation

Model theorem, NOT the F_p prize: nothing constrains `M(μ_n)`, `E(μ_n)`, or δ*; the open core is
untouched. The blocking feature of `F_p` is pinned as **additive non-closure of `μ_n`**, not
thinness — the model reproduces the exact prize index unconstrained. The hardness relocates,
losslessly (thms 2–3), to the coset geometry of the exactly-index-sized dual `S^⊥` (Binius:
trace-dual flag). Beyond-Johnson MCA for additive-NTT RS remains OPEN; agreement on proper
subsets of `S` is invisible to ambient characters.
