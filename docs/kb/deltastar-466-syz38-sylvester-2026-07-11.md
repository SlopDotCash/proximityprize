# δ*/#466 — SYZ38: the 3-support residual is a Sylvester/resultant injectivity (2026-07-11)

## TL;DR

SYZ37 reduced the rate-1/2 union-generation gate to the vanishing of the **in-budget syzygy
module** of the reduced pairwise-coprime triple `(W_AB, W_AC, W_BC)`, discharged the 0- and
2-support strata unconditionally, and carried the 3-support stratum as an **abstract finrank
residual** `InBudgetSyzygyModuleVanishes`. SYZ38 does two things:

1. **Sharpens that residual from an abstract finrank restatement to one concrete, classical
   polynomial statement** — `SylvesterInjective`: the divisibility `W_AB ∣ (W_AC r_AC − W_BC r_BC)`
   restricted to the in-budget cofactor window has only the trivial solution. This is the
   generalized Sylvester-map injectivity = resultant nonvanishing = μ-basis balance.
2. **Collapses the whole module — all supports — to that single statement** unconditionally:
   `module_vanishes_of_sylvester_injective`.

The 3-support case is **not** an elementary degree collapse (a naive mod-reduction "congruence
becomes equality" needs a *saturated* modulus, `deg W ≥ k−t`, which is vacuous at rate 1/2 — the
same wall SYZ37 hit). It is genuinely resultant-type and **field-dependent** (SYZ36/37 probes: a
thin residual flips with the prime, e.g. `n=13,k=7`: 10 fails at p=31, 0 at p=101), so
`SylvesterInjective` is carried as a named hypothesis, not proved.

## The mechanism

Syzygy `W_AB r_AB − W_AC r_AC + W_BC r_BC = 0` rearranges to `W_AB r_AB = W_AC r_AC − W_BC r_BC`,
so unconditionally

  `W_AB ∣ (W_AC r_AC − W_BC r_BC)`.                              (†)  `three_support_divides`

`W_AC, W_BC` are units mod `W_AB` (pairwise coprimality), so (†) is the single congruence
`r_AC ≡ W_AC⁻¹ W_BC r_BC (mod W_AB)`. At rate 1/2 the Koszul budget fails
(`k−1 < m_AB+m_AC−t`, SYZ37 `koszul_out_of_budget_rate_half`), which forces every per-pair budget
strictly below `deg W_AB`:

  `b_AC = k−1−m_AC < m_AB−t = deg W_AB`  (`budget_lt_degWAB`, needs `t < m_AB`).

Hence a low-degree `r_AC` is its own residue and (†) *determines* `r_AC` from `r_BC`. A nonzero
in-budget 3-support syzygy exists **iff** the forced representative of `W_AC⁻¹ W_BC r_BC` mod `W_AB`
lands back in the degree-`b_AC` window for some nonzero low-degree `r_BC` — a resultant/μ-basis
balance condition, field-dependent, hence `SylvesterInjective`.

### Dimension bookkeeping (why injectivity is even possible)

Reduction map `(r_AC, r_BC) ↦ (W_AC r_AC − W_BC r_BC) mod W_AB`: domain dim
`(b_AC+1)+(b_BC+1) = 2k − m_AC − m_BC`, codomain dim `deg W_AB = m_AB − t`. Injective needs
`2k ≤ Σpair − t = 3s − |U|`; with `s > 2n/3`, `|U| ≤ n = 2k` gives `3s − |U| > 2k`. So the
dimension condition holds with room — consistent with (but not implying) injectivity. Full
injectivity is the residual.

## Lean landed: `Frontier/_SYZ38SylvesterInjectivity.lean` (4 thms + 1 def, axiom-clean)

`propext`/`Classical.choice`/`Quot.sound` only; no `sorry`, no `native_decide`.

- `budget_lt_degWAB` — Koszul-out ⇒ `k−1−m_AC < deg W_AB` (arith; needs `t < m_AB`, the
  nondegenerate modulus).
- `three_support_divides` — the syzygy yields (†) with no side hypotheses.
- `SylvesterInjective` (def) — the concrete named residual: (†) on the in-budget window ⇒ trivial.
- `module_vanishes_of_sylvester_injective` — **main**: `W_AB ≠ 0` + `SylvesterInjective` ⇒
  `r_AB = r_AC = r_BC = 0` for every in-budget syzygy (all strata at once).
- `inbudget_module_vanishes_of_sylvester_injective` — packaged corollary = the SYZ36
  union-generation input, now field-explicit (replaces SYZ37's abstract finrank
  `InBudgetSyzygyModuleVanishes`).

## Honest final state — what remains for the full strip theorem

SYZ38 localizes the entire rate-1/2 residual to a **single classical divisibility-injectivity
statement** and collapses all three support strata to it. Strictly sharper than SYZ37's abstract
finrank residual. It does **not** deliver an unconditional δ*. Remaining (SYZ33 caveats, precise):

1. **`SylvesterInjective` itself** — the resultant nonvanishing / μ-basis balance of the coprime
   band triple. Probe-verified (0 counterexamples over thousands of RS/`μ_n` + 14 908 random
   coprime triples), **field-dependent**, unproved. This is now the *sole* polynomial residual.
2. **Lemma-1 input instantiation** — SYZ33 lemma 1's hypotheses are not yet discharged from the
   band geometry.
3. **General-`D` peel** — SYZ34/35 handle the pair/interior law; the general-`D` induction (peeling
   arbitrary core count) is not wired.
4. **Integration wiring** — connecting the module-vanishing to the SYZ35 `finrank` equivalence and
   thence SYZ33 lemma 2 is documented (SYZ37 `rate_half_gate_closed_of_module_vanishes`) but the
   polynomial↔finrank bridge (SYZ36's `d = syzdim`) is not a single Lean handle.
5. **Production-ledger join** — SYZ22 realizability / the δ* ledger bridge remain open.
