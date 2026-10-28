# Honesty Audit Playbook

How to find unproven-but-presented-as-proven content: the laundering patterns the CI gates miss,
how to detect each one, and confirmed historical findings. Use this when auditing a landing report,
a "PROVEN" issue comment, or a grant-completion claim.

## What the gates already catch

`./scripts/validate.sh` catches: `sorry`/`admit` holes (`sorry_census.py`), forbidden tokens
(`native_decide`, `bv_decide`, `unsafe` declarations, `unsafeCast`, `implemented_by`,
undocumented `axiom` — `forbidden_tokens.py`), flagship-theorem axiom drift
(`axiom_audit.py`). An auditor's job is everything those *cannot* see.

The optional post-build `python3 scripts/proximity_prize_cleanroom_audit.py` checks
the apex declarations listed in `scripts/proximity_prize_cleanroom_targets.txt`.
It locates the declaration's result after binders and top-level arrow premises
before looking for the expected predicate. A signature such as
`(h : mcaPrize domain) : True` or `mcaPrize domain → True` fails even when its
axiom report is empty. Predicate occurrences solely in those premises cannot
certify a prize conclusion, and neither can occurrences nested inside the result
in an arrow premise or binder type, such as `True ∧ (mcaPrize domain → True)`.
This remains a syntactic audit; it does not establish
that a predicate's definition captures the intended mathematical statement.
The manifest uses `Research.ProximityPrize.Resolution` for the retained resolution
declarations. A dry run also rejects active `ArkLib`/`Research` modules whose
source no longer exists; pending future entries remain permitted.
Delimiter and predicate searches ignore quoted identifiers, strings and character literals,
so quoted arrows cannot split the result and literal brackets cannot hide a premise.
Run its regression and independent Lean-output fixture with
`python3 -m unittest discover -s scripts/tests -p 'test_cleanroom_conclusion.py'`.

`forbidden_tokens.py` also enforces one declaration per `scripts/residual_axioms.txt` entry: the
allowlist stores simple names, so an entry would otherwise transfer to a second `axiom` declared
under the same name in a fresh namespace. That check needs the full-tree scan (what CI and
`validate.sh` run); a file-scoped run only sees duplicates inside the file it was given.

## Current shortcut snapshot (2026-06-11)

A comment/string-stripped scan of `ArkLib/**/*.lean` found:

- Live `axiom` / bodyless `constant` / bodyless `opaque` declarations: **0**.
- Live `sorry` / `admit` tokens: **0**.
- Live `theorem` / `lemma` / `def` / `abbrev` / `instance` declarations with a top-level
  `: True`, `True :=`, or `:= True` shape: **0**.
- Remaining `def` / `abbrev` / `class ... : Prop` declarations: **91**. These are not all
  dishonest: many are genuine bad-event predicates, conjecture statements, or refutation/spec
  predicates. The audit job is to distinguish those from residual obligations that still need
  proof.

Current issue routing for the residual-shaped surface:

- Binius class-carried residual obligations: [#317](https://github.com/lalalune/ArkLib/issues/317)
  (six `class ...Residual : Prop` declarations).
- Fiat-Shamir duplex sponge Lemma 5.8 residuals:
  [#316](https://github.com/lalalune/ArkLib/issues/316).
- Proximity/coding-theory residuals and conjecture/spec predicates:
  [#334](https://github.com/lalalune/ArkLib/issues/334), with BCIKS20 core work also in
  [#304](https://github.com/lalalune/ArkLib/issues/304). The latest clean-origin scan includes
  `Hab25JohnsonDischarge.lean:53` `JohnsonDischargeStatement` in this bucket.
- Spartan residual Props: [#329](https://github.com/lalalune/ArkLib/issues/329).
- WHIR soundness work: [#302](https://github.com/lalalune/ArkLib/issues/302); current direct
  WHIR shortcut scan has no `def/class ... : Prop` hit under `ArkLib/ProofSystem/Whir`.
- Logup residual Props after the old #13 closeout:
  [#337](https://github.com/lalalune/ArkLib/issues/337).
- RingSwitching completeness residual Props after the old #19 closeout:
  [#338](https://github.com/lalalune/ArkLib/issues/338).
- ToyProblem leaderboard residual Props after the old #18 closeout:
  [#339](https://github.com/lalalune/ArkLib/issues/339).

When extending this audit, keep the raw finding list in the relevant issue comment, not only in
chat. In particular, do not treat every `def ... : Prop` as a bug: event predicates such as the
duplex-sponge bad events are the specification language. The shortcut is when such a predicate is
presented as a discharged theorem, hidden as a typeclass obligation, or used to assert a security
front door without a proof of the predicate.

## Laundering patterns the gates miss

1. **`def … : Prop` presented as a theorem.** A `Prop` *statement* compiles green forever without
   being proven. Check: is the headline name a `theorem`, or a `def`/`structure` whose *discharge*
   is what actually matters? Find the discharging declaration and audit *that*.

2. **Hypothesis smuggling.** A "proof" of `P` that is really `H → P` with `H` doing all the work.
   Check the full hypothesis list of the discharging theorem, not the issue-comment prose. The
   repo convention is honest *named* residuals (e.g. `stirCheckingCABridge`,
   `StrictCoeffPolysResidual`) — a hypothesis with an innocuous binder name (`h`, `hAux`) that
   encodes the open core is the dishonest variant.

3. **Vacuous-regime unconditionality.** A theorem can be unconditional because its regime makes
   the bound trivial (error budget `≥ 1` = no security). Confirmed instances (honestly flagged at
   landing, kept as exemplars): the small-field STIR discharge (`err⋆ ≥ 1` pins `secpar = 0`); the
   small-field `mca_johnson_bound_CONJECTURE_smallField`. Audit question: *is there a satisfiable
   parameter set where the statement says something nontrivial?* Demand a non-vacuity witness.

4. **Unsatisfiable statements.** The dual failure: a residual stated against the wrong object can
   be *false*, so "discharging" work grinds an impossible goal — e.g. rbr-soundness stated against
   a forwarding-shell verifier that checks nothing (#301, caught in audit 2026-06-10). Audit
   question: can a trivial adversary win the stated game outright?

5. **Stale-olean / elaboration laundering.** `#print axioms` run against stale `.olean`s, or a
   declaration that silently picked up `sorryAx` through a failing dependency, reports clean while
   the source no longer elaborates. Confirmed instance: the `hQin` `=`→`≥` drift left three
   `stir_main_of_checkingIOP_*` welds elaborating via `sorryAx` while the build "passed" on stale
   artifacts. Detection: rebuild the focused module from scratch, then `#print axioms` — and never
   pipe `lake env lean` through `tail`/`head` (it masks the exit code; capture to a file and check
   `$?`).

6. **Phantom landings.** Issue comments claiming "pushed `X`" where the commit never reached any
   ref (lost worktree, interrupted lane). Confirmed instance: `PzFamilyUD.lean` was imported by a
   merged commit but exists in no ref — every full build broke. Detection:
   `git log --all -S <symbol>` before believing any landing report.

7. **Probe-free conjecture formalization.** Formalizing a quantified statement nobody
   counterexample-searched. House rule (from #232): write an exact-arithmetic probe under
   `scripts/probes/` and run it *before* formalizing; cite the probe counts. Several would-be
   "theorems" died as probes (see `Data/CodingTheory/ProximityGap/DISPROOF_LOG.md`).

8. **Misformalization of a paper invariant.** The statement proves/refutes something subtly
   different from the paper (wrong quantifier order, wrong normalization, an invariant the paper
   treats as an *output* hypothesized as an *input*). Detection: re-derive the statement from the
   paper independently before trusting a refutation or a proof; record the paper-to-Lean mapping
   next to the statement.

## Audit checklist (per claimed landing)

- [ ] `git log --all -S <headline-name>` — the commit exists and is on `main`.
- [ ] The headline is a `theorem` (or its discharge is identified and audited).
- [ ] Full hypothesis list read; every nontrivial hypothesis is a *named*, tracked residual.
- [ ] Non-vacuity: a satisfiable nontrivial parameter regime exists (or the vacuity is flagged).
- [ ] Fresh focused rebuild + `#print axioms` shows exactly `[propext, Classical.choice, Quot.sound]`.
- [ ] No new `axiom`, `native_decide`, `unsafe`, `unsafeCast`, `implemented_by` in the diff (CI gate 1 now rejects the last three in live source; still re-check the diff);
      no second declaration of an allowlisted residual axiom name.
- [ ] Issue comment matches what was actually proven (regime, budget, verifier variant).
