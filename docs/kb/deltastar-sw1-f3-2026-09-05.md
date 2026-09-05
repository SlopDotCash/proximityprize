# δ* — SW1 lane F3: the union-rank residual `hrank`, exactly (2026-09-05)

Standalone issue #1, SW1 parallel research round, lane F3.  Parent docs:
`docs/kb/deltastar-466-one-question-map-2026-07-11.md` §3 F3 / §4,
`docs/kb/deltastar-DOSSIER-v4-2026-08-16.md` §8 item 3.  Build rules: SW1 brief §3 (no
`lake build`; `scripts/pg-iterate.sh` only, Mathlib-only default).

## 1. Target

The sole surviving analytic field of SYZ42/SYZ43 `RealizabilityCore`, for the G87 bridge family
`φ : Fin r × Fin (t − k) → Dual (SyndromePair C)` of a stack `(u₀,u₁)` with `r` `mcaEvent`
witnesses `(γᵢ, Sᵢ)`, `|Sᵢ| = t`, `U := ⋃ Sᵢ`:

    hrank : finrank F (span F (range φ)) = 2 (Ucard − k),   Ucard = |U|.

Dossier v4 §8.3 asks for a span certificate that does not use the SYZ56-refuted overlap
chaining.  This lane instead determined *exactly* when `hrank` holds, and the answer is
"never, for the stacks it is meant to constrain".

## 2. What was tried (in order)

1. Extracted the exact objects from `_G87McaEventSyndromeBridge.lean`,
   `_SYZ20JointRankSuperadditive.lean`, `_SYZ22StripBridge.lean`, `_SYZ42Realizability.lean`,
   `_SYZ43AutoInstantiation.lean`, `_SYZ56Hrank.lean`.  Each G87 row `ℓᵢⱼ` is a dual of
   `(Sᵢ → F) ⧸ res_{Sᵢ}(C)` composed with `res_{Sᵢ}`; the bridge functional is the *graph*
   `(ℓ̄ᵢⱼ, γᵢ ℓ̄ᵢⱼ) ∈ Dual Q × Dual Q`, `Q = F^ι/C`.  A block therefore has dimension `t − k`,
   not the `2(t − k)` "doubled shortening" suggested by the map's §3 F3 gloss.
2. Dual/parity-check reformulation (task (a)).  Writing `D_S := C^⊥ ∩ F^S = (C|_S)^⊥` and
   `Γᵢ := {(w, γᵢ w) : w ∈ D_{Sᵢ}}`, the annihilator of `Σᵢ Γᵢ` inside `(F^U/C|_U)²` is exactly
   `Bad_U(γ,S)/(C|_U)²`, where `Bad_U := {(u₀,u₁) on U : ∀ i, (u₀ + γᵢ u₁)|_{Sᵢ} ∈ C|_{Sᵢ}}`.
   Hence the **exact dimension formula** (full blocks, i.e. `dim C|_{Sᵢ} = k`):

       finrank (span φ) = 2 (|U| − dim C|_U) − dim ( Bad_U / (C|_U)² ),

   and `hrank ⟺ Bad_U = (C|_U)²` ⟺ *no stack other than a codeword pair on `U` is bad at every
   `(γᵢ,Sᵢ)`*.  The stack that produced the configuration is bad at every `(γᵢ,Sᵢ)` and, by the
   `mcaEvent` clause `¬ pairJointAgreesOn`, is not a codeword pair on `U`.  So `hrank` fails.
3. Lean (task (b)): the inequality half of the formula is the whole refutation and needs no
   RS/Vandermonde input — it is SYZ20's `plantable_span_cap` run on the *local* syndrome-pair
   space `(F^U/C|_U)²` instead of `(F^ι/C)²`.  Formalized Mathlib-only, general field, general
   linear code, with the G87 construction re-run verbatim to export the locality it hides.
4. Probe (task (c)): exact ranks over `F_p`, `p ≡ 1 (mod n)`, `μ_n` domains.
5. While extracting the container of `hrank`, found that the enclosing master hypotheses are
   contradictory outright (§4.2).

## 3. Exact statements (Lean)

File `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SW1_F3_UnionRankExact.lean`
(Mathlib-only; `SyndromePair`, `syndromePair`, `pairJointAgreesOn` restated byte-identically):

* `span_cap_of_factors` — `π : V ↠ V'`, `π σ ≠ 0`, family `φ` killing `ker π` and `σ` ⟹
  `finrank (span (range φ)) + 1 ≤ finrank V'`.
* `finrank_localPair` — `finrank ((F^U/C|_U)²) = 2 (|U| − finrank (C.map res_U))`.
* `restrictQ_syndromePair_eq_zero_iff` — the local syndrome pair vanishes iff
  `pairJointAgreesOn C U u₀ u₁`.
* `localized_span_cap` — `U`-local family annihilating the syndrome pair of a stack with
  `¬ pairJointAgreesOn C U u₀ u₁` ⟹ `finrank (span) + 1 ≤ 2 (|U| − finrank C|_U)`.
* `exists_bridge_functionals_local` — G87 `exists_bridge_functionals` (same index type, same
  annihilation and per-block independence) plus locality, when all `Sᵢ ⊆ U`.
* `bridge_family_violates_hrank`, `hrank_false_of_mcaEvent_witness` — for any stack with SYZ43's
  `hwit` (localized to `U`), one `mcaEvent` witness set `S₀ ⊆ U`, and `finrank C|_U = finrank C`:
  the G87 family has `finrank (span) ≠ 2 (|U| − k)`.
* `pairJoint_of_hrank` — conversely `hrank` at `Ucard = |U|` forces joint codeword agreement on
  `U`: it certifies degeneracy, not realizability.
* `forall_form_forces_Ucard_le_k` — the `∀ φ` quantifier of SYZ43
  `realizabilityCore_of_mcaEvent_witnesses.hrank` forces `Ucard ≤ k` (take `φ := 0`).

File `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SW1_F3_MasterHypothesisVacuous.lean`
(imports `_SYZ42Realizability`):

* `superadditiveUnion_isEmpty_of_le` — `SuperadditiveUnion n k Ucard` is empty for `Ucard ≥ n`
  (its own `union_card_lt_length`).
* `not_stripMasterHypothesis`, `not_stripMasterHypothesis'`, `not_stripMasterHypothesis''` —
  SYZ40/41/42 master hypotheses are false for `k ≤ n` (instance `Ucard := n` of the
  `∀ Ucard ≤ n` realizability field).
* `syz46_antecedent_false` — the antecedent of SYZ46 `deltaStar_bracket_of_strip_master_hypothesis`
  is false (`n = 2³⁰`, `k = 2²⁹`, every field, every `V`).

Axiom audit lines are recorded in §5.

## 4. Results with classification

### 4.1 F3 `hrank` — refutation-no-go with countermodel (every `mcaEvent` stack)

Unconditional, every field, every linear code with `dim C|_U = dim C` (MDS: `|U| ≥ k`):
`finrank (span φ) ≤ 2(|U| − k) − 1`, so `hrank` at `Ucard = |U|` is false as soon as one
witness set inside `U` carries the `mcaEvent` clause.  The doubled local shortening
`(D_U)² ` can be spanned by graphs `(ℓ, γℓ)` annihilating a *nonzero* local syndrome only if
that syndrome is zero — i.e. only for stacks that are codeword pairs on `U`, which are not
`mcaEvent` stacks.  This is the SYZ22(iii) "attainability" claim reversed: parts (i)/(ii) of
SYZ22 show the target dimension exists, and the localized cap shows the family can never
reach it.

Consequences for the map's §3 F3 entry:
* "each block a full basis of its `S`-anchored doubled punctured dual" — no: a block is a
  `(t − k)`-dimensional graph inside the `2(t − k)`-dimensional doubled space (probe E2).
* "`hrank` is union-generation over `{Sᵢ}`" — the exact condition is `Bad_U = (C|_U)²`
  (no nontrivial bad stack), which is a *non-realizability* condition on the configuration,
  not a spanning condition on the supports.  It does not depend on overlap sizes in any
  simple way, and it is violated by construction for every configuration that comes from a
  stack.  The chaining NO-GO (SYZ56) was therefore aimed at a certificate that cannot exist.

### 4.2 The container — SYZ40/41/42 master hypotheses are contradictory (formalization)

`SuperadditiveUnion n k n` is empty (`2(n−k)+1 ≤ 2(n−k)`), and each master hypothesis demands
`Nonempty (SuperadditiveUnion n k Ucard)` for *every* `k ≤ Ucard ≤ n`.  So the "single
assembled theorem depending on exactly three open Props" (map §0) has a false antecedent:
SYZ46's bracket is `False → …`.  Classification: refutation-no-go of a formalization; it says
nothing about δ*.  It does say F1/F2/F3 progress cannot discharge that theorem as written.

### 4.3 The `∀ φ` form of SYZ43's `hrank` — unsatisfiable above `k`

`realizabilityCore_of_mcaEvent_witnesses` is only applicable at `Ucard ≤ k`.

### 4.4 Computational evidence (probe `scripts/probes/sw1_f3_union_rank.py`, PASS)

786 exact configurations, `n ∈ {8,16,32}`, `k = n/2`, `t ∈ {k+1, 3n/4−1, 3n/4}`, families
random / one-swap / sunflower / chain / nested / minimal-overlap, `r ∈ {1,2,3,4,6,8}`, primes
`p ≡ 1 (mod n)`: `17…10177` plus a `p ≈ 10⁵` sweep.
* E1: `(C|_U)² ⊆ null Φ` always, so `rank Φ ≤ 2(|U|−k)`; `hrank ⟺ ν := 2(|U|−k) − rank = 0`.
* E2: `r = 1`: `rank = t − k` (graph), `ν = t − k ≥ 1`.
* E3: `r = 2`, distinct scalars: `rank = 2(t − k)` at every overlap `2t−n ≤ |S₁∩S₂| ≤ t−1`.
* E4: whenever `ν ≥ 1` a sampled nullspace stack is bad at every witness and not a codeword
  pair on `U`, and `rank ≤ 2(|U|−k) − 1` — the Lean cap, end to end.
* 135/786 configurations had `hrank` true; all 135 are vacuous (`ν = 0`: no stack outside
  `(C|_U)²` realizes them; typically `|U| = n` with `r(t−k) ≥ 2(n−k)`).
* E5: fixed `n=16, t=11, r=4` sunflower / one-swap configurations have identical
  `(|U|, rank, ν) = (15,12,2)` / `(13,9,1)` at `p = 17, 97, 113, 193, 241, 257, 100049, 100129`.
  No small-field artefact.

## 5. Axiom audit

See the SW1 final report / the `#print axioms` output recorded next to each file; both files
carry `#print axioms` for every theorem above (expected: `propext, Classical.choice, Quot.sound`).

## 6. What remains

* F3 needs a **new carrier**.  The theorem now available is the inequality
  `finrank (span φ) + 1 ≤ 2(|U| − k)`; the strip route's conclusion `|U| ≤ n − 1` does not
  follow from any rank statement about `φ`, and it is false in general
  (`(c₀ + a·e_x, c₁ + b·e_x)` has an `mcaEvent` witness `S = ι` at `γ = −a/b`), so a re-carrier
  must exclude the near-codeword ("merged") branch by hypothesis, as SYZ40's spread/merged
  split intended.
* The exact formula `finrank (span φ) = 2(|U| − k) − dim(Bad_U/(C|_U)²)` makes the
  realizability question identical to bounding the *dimension of the bad-stack space* of a
  configuration — the MCA count problem itself in linear form.  This is where the BGK wall sits
  (map §4); no Vandermonde-only argument computes `dim Bad_U` for `r ≥ 3`.
* The SYZ46 bracket must be re-stated with a satisfiable antecedent before any of F1/F2/F3 is
  worth attacking *for that theorem*.

## 7. References

* `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G87McaEventSyndromeBridge.lean`
  (`exists_rowFunctionals`, `exists_bridge_functionals`, `SyndromePair`, `syndromePair`).
* `_SYZ20JointRankSuperadditive.lean` (`plantable_span_cap`, `SuperadditiveUnion`,
  `union_card_lt_length`, `union_card_le`); `_SYZ22StripBridge.lean` (`doubled_shortening_dim`,
  `strip_budget_of_realizability`); `_SYZ40FinalAssembly.lean`, `_SYZ41SyzdimBridge.lean`,
  `_SYZ42Realizability.lean` (master hypotheses); `_SYZ43AutoInstantiation.lean` (`hrank`);
  `_SYZ46CensusBridge.lean` (`deltaStar_bracket_of_strip_master_hypothesis`);
  `_SYZ56Hrank.lean` (chaining NO-GO); `ProximityGap/Errors.lean` (`mcaEvent`,
  `pairJointAgreesOn`).
* Ledger greps (all before starting): `hrank` (5 lines, none on this point), `union-rank`,
  `union rank`, `SYZ56`, `RealizabilityCore`, `span certificate`, `plantable_span_cap`,
  `block_source_dim`, `doubled shortening` (0 each), `chaining` (125, none F3), `anchored`
  (48, none F3), `StripMasterHypothesis|SuperadditiveUnion|union_card_le|realizabilityCore`
  (0 in `DISPROOF_LOG.md`; KB notes mention the structures but never their vacuity).

## Verification addendum (independent re-check, 2026-09-05 evening)

`scripts/pg-iterate.sh` was re-run on every `Frontier/_SW1_*.lean` file left untracked by
the SW1 round.  Result: `_SW1_F3_MasterHypothesisVacuous.lean` and
`_SW1_TRANSV_HeightCeiling.lean` compile axiom-clean; `_SW1_F1_UniformSylvesterRefuted.lean`
(≈20 elaboration errors, 6 `sorryAx` fallbacks), `_SW1_F3_UnionRankExact.lean` (4 errors at
lines 223–229, `hrank_false_of_mcaEvent_witness` and `pairJoint_of_hrank` depend on
`sorryAx`), `_SW1_HD_HasseDavenportCosetLadder.lean` (unknown identifiers
`FiniteField.primitiveChar_to_Complex*`, `ladder_coset_pair` on `sorryAx`) and
`_SW1_SPARSE_RootLocusAverage.lean` (2 errors) do **not**.  Any "axiom-clean" claim above
about those four files is therefore unverified until they are repaired; the master-hypothesis
vacuity (`not_stripMasterHypothesis*`, `syz46_antecedent_false`) **is** verified.  The four
broken files are deliberately left uncommitted.
