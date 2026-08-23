/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SumcheckSoundnessLift

/-!
# LogUp Protocol 2 — discharging the embedded-sumcheck lens projection soundness (issue #13)

`Logup.SumcheckLensProjSound` (defined in `Security/SumcheckSoundnessLift.lean`) is the genuine
algebraic `proj_sound` half of the LogUp embedded sum-check lens soundness condition. It is the named
hypothesis `hProj` threaded into `sumcheckLensSound` / `sumcheckVerifier_rbrSoundness` /
`sumcheckSoundnessResidual_holds`. This file *discharges* it (no `sorry`, no named hypothesis).

## The statement

`SumcheckLensProjSound oSpec F n M params innerLangIn` asserts: for every outer after-outer statement
`outerStmtIn` **outside** `midLanguage` (i.e. the LogUp mid-claim
`logupOuterSumcheckClaim … outerStmtIn.1 outerStmtIn.2 ≠ 0`), its projection under
`(logupSumcheckOracleLens …).toLens.proj` lands **outside** the chosen inner sum-check input language
`innerLangIn`.

The lens projection is, *definitionally*,
`(logupInitialSumcheckStatement, logupSumcheckOracleStmt … outerStmtIn.1 outerStmtIn.2)` — the
zero-target generic sum-check claim carrying the batched LogUp polynomial `Q` as its oracle.

## The discharge

The **correct** inner input language for the embedded sum-check is the generic round-`0` sum-check
language `(Sumcheck.Spec.relationRound F n … (signDomain F hSigns) 0).language` — the set of generic
sum-check input claims whose stated `target` *equals* the actual sum of the oracle polynomial over the
`{±1}`-hypercube. With this language the projection soundness is **true and unconditional**:

* The projected zero-target generic sum-check round-`0` sum of the LogUp polynomial `Q` over the
  `{±1}`-hypercube **equals** `logupOuterSumcheckClaim … outerStmtIn.1 outerStmtIn.2`, *for any*
  after-outer statement (since `logupSumcheckPolynomialRowsAgree` holds for *all* statements by
  `logupSumcheckPolynomialRowsAgree_of_signsDistinct`). This is the unconditional bridging equality
  `logupSumcheck_round0_sum_eq_outerClaim`.

* Hence the projected (zero-target) claim is in the round-`0` language **iff** that sum equals `0`,
  **iff** `logupOuterSumcheckClaim = 0`, **iff** the outer statement is *in* `midLanguage`
  (`logupSumcheckRelationInput_iff_claimZero`). Contrapositively: outside `midLanguage` ⇒ outside the
  inner language. This is exactly the grand-sum content the soundness side needs.

`SumcheckLensProjSound_holds` is the discharged residual, axiom-clean (`propext`, `Classical.choice`,
`Quot.sound` only). It is stated for the canonical inner language `logupSumcheckInputLanguage`, so it
plugs directly into `sumcheckVerifier_rbrSoundness` / `sumcheckSoundnessResidual_holds` with
`innerLangIn := logupSumcheckInputLanguage …`.
-/

open OracleComp ProtocolSpec
open scoped NNReal BigOperators

namespace Logup

section SumcheckLensProjSound

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)

local instance instInhabitedFieldSumcheckLensProjSound : Inhabited F := ⟨0⟩

/-- **Bijection between the `{±1}`-domain product Finset and the Boolean hypercube.** A copy of the
in-tree (private) `sum_piFinset_map_univ_eq_sum_hypercube`, kept here so this file can re-derive the
round-`0` sum identity without reaching into the (private) bridge internals. The sum over the product
of `Finset.univ.map D` (for any `Fin 2 ↪ F` domain `D`) equals the sum over the Boolean hypercube
reindexed through `D`. -/
private theorem sum_piFinset_map_univ_eq_sum_hypercube'
    (D : Fin 2 ↪ F) (f : (Fin n → F) → F) :
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map D, f x) =
      ∑ u : Hypercube n, f (fun j => D (u j)) := by
  classical
  symm
  refine Finset.sum_nbij (s := (Finset.univ : Finset (Hypercube n)))
    (t := Fintype.piFinset fun _ : Fin n => Finset.univ.map D)
    (i := fun u j => D (u j)) ?hi ?hinj ?hsurj ?hfg
  · intro u _
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_map.mpr ⟨u j, Finset.mem_univ _, rfl⟩
  · intro u _ v _ huv
    funext j
    exact D.injective (congr_fun huv j)
  · intro x hx
    have hx_coord : ∀ j : Fin n, ∃ b : Fin 2, D b = x j := by
      intro j
      have hxj := (Fintype.mem_piFinset.mp hx) j
      rcases Finset.mem_map.mp hxj with ⟨b, _, hb⟩
      exact ⟨b, hb⟩
    let u : Hypercube n := fun j => Classical.choose (hx_coord j)
    refine ⟨u, Finset.mem_univ _, ?_⟩
    funext j
    exact Classical.choose_spec (hx_coord j)
  · intro u _
    rfl

/-- **The round-`0` sum equals the LogUp outer sum-check claim, unconditionally.** The projected
generic round-`0` sum-check sum of the LogUp polynomial `Q` over the `{±1}`-hypercube equals
`logupOuterSumcheckClaim`. This does *not* use any zero hypothesis: the row-agreement
`logupSumcheckPolynomialRowsAgree` holds for *all* after-outer statements, so the bridge is an
unconditional algebraic identity. This is the sum that the generic round-`0` relation
`relationRound … 0` compares against `target`. -/
theorem logupSumcheck_round0_sum_eq_outerClaim
    (hSigns : (-1 : F) ≠ 1)
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (g : (Fin n → F) → F)
    (hg : ∀ x : Fin n → F,
      g x = MvPolynomial.eval x (logupSumcheckPolynomial F n M params stmt oStmt).val) :
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map (signDomain F hSigns), g x)
      = logupOuterSumcheckClaim F n M params stmt oStmt := by
  classical
  have hRows := logupSumcheckPolynomialRowsAgree_of_signsDistinct F n M params hSigns stmt oStmt
  rw [sum_piFinset_map_univ_eq_sum_hypercube'
    (F := F) (n := n) (D := signDomain F hSigns) (f := g)]
  rw [logupOuterSumcheckClaim]
  apply Finset.sum_congr rfl
  intro u _
  rw [hg]
  -- `(fun j => signDomain F hSigns (u j)) = signPoint F u` reindexes the evaluation point.
  have hpt : (fun j => (signDomain F hSigns) (u j)) = signPoint F u := by
    funext j
    simp [signDomain, signPoint, bitToSign]
  rw [hpt]
  exact hRows u

/-- **`logupSumcheckRelationInput ↔ mid-claim is zero`.** The projected generic round-`0` sum-check
relation (zero target, LogUp polynomial `Q` as oracle) holds *iff* the LogUp outer sum-check claim
vanishes. Both directions follow from the unconditional equality
`logupSumcheck_round0_sum_eq_outerClaim`. -/
theorem logupSumcheckRelationInput_iff_claimZero
    (hSigns : (-1 : F) ≠ 1)
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    logupSumcheckRelationInput F n M params hSigns stmt oStmt ↔
      logupOuterSumcheckClaim F n M params stmt oStmt = 0 := by
  classical
  -- Unfold the relation membership to the round-`0` sum-equals-target (`= 0`) equation.
  unfold logupSumcheckRelationInput Sumcheck.Spec.relationRound
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.sub_zero, logupInitialSumcheckStatement,
    Set.mem_setOf_eq, Fin.elim0_append, logupSumcheckOracleStmt]
  -- The goal is `(round-0 sum) = 0 ↔ logupOuterSumcheckClaim … = 0`; the LHS sum equals the claim
  -- by the unconditional bridging identity, so both sides are the *same* equation.
  refine iff_of_eq (congrArg (· = (0 : F)) ?_)
  exact logupSumcheck_round0_sum_eq_outerClaim F n M params hSigns stmt oStmt _ (fun _ => rfl)

/-- **The canonical inner sum-check input language for the LogUp embedded sum-check.** The `language`
of the generic round-`0` relation `Sumcheck.Spec.relationRound … (signDomain F hSigns) 0`: the set of
generic round-`0` sum-check input statements whose claimed `target` equals the actual sum of the
`Q`-oracle over the `{±1}`-hypercube. This is the language the embedded sum-check verifies; using it
makes the lens projection soundness true and unconditional. -/
def logupSumcheckInputLanguage (hSigns : (-1 : F) ≠ 1) :
    Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i)) :=
  (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (signDomain F hSigns) 0).language

/-- **`SumcheckLensProjSound` discharged** for the canonical inner sum-check input language.

For every after-outer statement outside `midLanguage` (nonzero LogUp mid-claim), the lens projection
`(logupSumcheckOracleLens …).toLens.proj` — definitionally the zero-target generic sum-check claim
carrying `Q` — lands outside `logupSumcheckInputLanguage` (the round-`0` sum-check language). This is
the genuine algebraic soundness content: a nonzero mid-claim cannot satisfy the zero-target embedded
sum-check relation.

Proof: membership of the projection in the language is, via
`logupSumcheckRelationInput_iff_claimZero`, equivalent to `logupOuterSumcheckClaim = 0`, i.e. to
membership of the outer statement in `midLanguage`; the hypothesis is precisely the negation. -/
theorem SumcheckLensProjSound_holds (hSigns : (-1 : F) ≠ 1) :
    SumcheckLensProjSound oSpec F n M params
      (logupSumcheckInputLanguage F n M params hSigns) := by
  classical
  intro outerStmtIn hNotMid
  -- `hNotMid : outerStmtIn ∉ midLanguage`, i.e. `logupOuterSumcheckClaim … ≠ 0`.
  rw [midLanguage, Set.mem_setOf_eq] at hNotMid
  intro hMem
  -- `hMem : proj outerStmtIn ∈ (relationRound …).language`; extract the (Unit) witness.
  rw [logupSumcheckInputLanguage, Set.mem_language_iff] at hMem
  obtain ⟨_wit, hRel⟩ := hMem
  -- The projection's value is definitionally
  -- `(logupInitialSumcheckStatement, logupSumcheckOracleStmt … outerStmtIn.1 outerStmtIn.2)`,
  -- so the relation membership is exactly `logupSumcheckRelationInput`.
  have hRel' : logupSumcheckRelationInput F n M params hSigns outerStmtIn.1 outerStmtIn.2 := hRel
  exact hNotMid
    ((logupSumcheckRelationInput_iff_claimZero F n M params hSigns
      outerStmtIn.1 outerStmtIn.2).mp hRel')

end SumcheckLensProjSound

end Logup

/- Axiom audit for the discharged #13 sum-check lens projection-soundness residual. -/
#print axioms Logup.logupSumcheck_round0_sum_eq_outerClaim
#print axioms Logup.logupSumcheckRelationInput_iff_claimZero
#print axioms Logup.SumcheckLensProjSound_holds
