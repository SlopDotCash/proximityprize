> **Superseded for the Johnson-radius refutation by the upstream integration.** Canonical
> `Jqℓ` uses `(ℓ - 1) / ℓ`, and `CodingTheory.johnson_bound_lambda_le_ell` is now proved.
> The old inverse-factor diagnostic and inconsistency conclusion below are historical and
> have been retired. See [the current integration note](../../../../wiki/upstream-integration.md#corrected-johnson-radius)
> and [the retirement record](../../../../../scripts/integration/johnson-radius-retirement.json).
> The remaining text records the earlier downstream state, not the current theorem status.

STATUS: CLOSED — Johnson-family deliverables resolved in-tree; only stale `sorry`-wording remained, now corrected. Regression check below returns zero raw-hole hits.

# issue-49 — Johnson-family list-decoding bounds (Joh62 Jqℓ + MDS corollary)

Tracking issue: lalalune/ArkLib#49
Files:
* `ArkLib/Data/CodingTheory/JohnsonBound/Family.lean`
* `ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean`
* `ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeLDThresholdJohnsonSq.lean`

## Finding

The issue asked for three things. On audit, all three are already settled in the tree;
the only genuine defect was documentation that still described a `sorry` which no longer
exists.

### 1. `johnson_bound_lambda_le_ell` (Jqℓ radius form, ABF26 Theorem 3.2 *as stated*)

**Refuted, not pending.** `Jqℓ q ℓ δ = (1 − 1/q)·(1 − √(1 − (q/(q−1))·(ℓ/(ℓ−1))·δ))`
is a valid list-of-`ℓ` radius only when the radicand is nonnegative. The statement in
the issue carries no such hypothesis, and `Real.sqrt` clamps negative inputs to `0`, so
once `(q/(q−1))·(ℓ/(ℓ−1))·δ_min > 1` the "radius" collapses to `(1 − 1/q)` and a ball of
that radius can hold far more than `ℓ` codewords.

`FamilyRefutationComplete.lean` proves this with an explicit, axiom-audited
counterexample (`johnson_bound_lambda_le_ell_false`): `ι = α = Fin 2`, `ℓ = 2`,
`C = {![0,0], ![0,1], ![1,0]}` has `minDist = 1`, `δ_min = 1/2`, radicand `−1`,
`Jqℓ = 1/2`, and `Λ(C, 1/2) ≥ 3 > 2`. `upstream_theorem_is_inconsistent` shows any
universally-quantified proof of the bare form yields `False`. Axiom audit is exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

Consequently `johnson_bound_lambda_le_ell` is exposed as a `def … : Prop` predicate,
NOT a `theorem := sorry`, and is **not consumed as a hypothesis anywhere** in the tree
(verified: the only references are its own definition and the refutation file). A faithful
formalization would require adding the proximity hypothesis the bare predicate omits.

### 2. `mds_johnson_lambda_le` (MDS / Reed-Solomon corollary, ABF26 C3.3)

**Fully proved, sorry-free** in `Family.lean`. For a linear MDS code `C` with rate
`ρ = k/n` and `η > 0`, `Λ(C, 1 − √ρ − η) ≤ 1/(2ηρ)`. The proof uses the radical-free
Johnson quadratic cap (`CodeGeometry.johnson_quadratic_cap`) with shift `β = √ρ`,
the closed-form off-/on-diagonal Gram bounds, the core polynomial inequality
`mds_core_ineq` (sorry-free), and the `Lambda`/`closeCodewordsRel` → `Finset` transport.
This is the Johnson output the faithful Grand LD threshold actually needs.

### 3. Squared-form reconciliation

**Already done.** `GrandChallengeLDThresholdJohnsonSq.lean` does not duplicate the
Johnson machinery: it consumes the canonical
`JohnsonBound.closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_sq_dist` from
`Family.lean` (the optimal-β radical-free condition) and lifts it through
`Lambda_le_of_johnson_sq` → `mem_listLatticeSet_of_johnson_sq` →
`le_listLatticeThreshold_of_johnson_sq` into the lattice-threshold API. The squared
inequality `(ℓ+1)·((n−j) − n/q)² > n(1−1/q)·(n(1−1/q) + ℓ·((n−d) − n/q))` is
`norm_num`-checkable on numeric instances at grid radius `j/n`.

## Disposition: correct stale wording, add this note (no new theorems needed)

The math is settled; the closure work is documentation hygiene:

* `Family.lean`: the `johnson_bound_lambda_le_ell` docstring said
  "**Admitted (tagged sorry).**" — false; it is a refuted predicate with no `sorry`.
  Rewritten to say so and to point at the refutation + the usable outputs. The
  "Remaining mechanical gaps" list (alphabet/list-packaging/radius-algebra) was reframed
  as moot, since the as-stated claim cannot be discharged. A broken disposition path
  (`research/proximity-prize/dispositions/pc-w1-T3.2-johnson.md`, never in tree) now
  points here.
* `FamilyRefutationComplete.lean`: module + theorem docstrings that called the predicate
  "a documented `sorry`" / "still-`sorry`'d" were corrected to "`Prop`-valued predicate".

## Regression check

No raw proof holes in the Johnson development, and the refuted statement must stay a
predicate (never re-tagged as a `sorry` or consumed as a hypothesis):

```sh
rg -n --pcre2 '(?<![`\w])(sorry|admit)\b' ArkLib/Data/CodingTheory/JohnsonBound   # expect: no code hits (docstring mentions only)
rg -n 'Admitted \(tagged sorry\)|documented `sorry`' ArkLib/Data/CodingTheory/JohnsonBound   # expect: no hits
rg -n 'johnson_bound_lambda_le_ell' ArkLib --glob '*.lean'   # expect: only Family.lean (def) + FamilyRefutationComplete.lean (refutation)
```

If the missing proximity hypothesis is ever added so the conditioned Johnson bound
becomes a theorem, update this note and the `Family.lean` docstring accordingly.
