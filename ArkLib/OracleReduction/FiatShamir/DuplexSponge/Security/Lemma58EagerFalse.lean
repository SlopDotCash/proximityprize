/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BirthdayBound

/-!
# #314 — `Lemma5_8EagerBirthdayFalseStatement` is FALSE as stated: a machine-checked countermodel

The in-tree combined bad event `E` (BadEvents.lean) deviates from CO25 Eq. 26: the 5th
disjunct of `capacitySegmentDupPermInv` anchors on the **answer** capacity of an inverse
entry with `j' ≤ j`, so at `j' = j` it compares the answer capacity with itself and fires
unconditionally. The paper's disjunct anchors on the **input** (query) capacity, which at
`j' = j` is the non-trivial "loop" coincidence. Machine-checked consequence
(`Sponge316.hasInvEntry_implies_E`): the in-tree `E` holds on *any* trace containing a
`p⁻¹` entry.

Therefore no probability bound `< 1` over `E` can hold against inverse-querying
adversaries: this file exhibits the single-inverse-query adversary `P := p⁻¹(0)` at
`StmtIn := Unit`, `U := UInt8`, sponge width 2 / rate 1, where `Pr[E] = 1` while the
claimed CO25 Lemma 5.8 bound at `T = 1` is `lemma5_8Bound UInt8 1 = 4/(2·256) < 1`.

This is the third statement-level defect record in the M2/birthday cluster, joining
`Lemma516TimePFalse` and `Lemma514ForkFalse` (both rooted in the `redundantEntryDS`
same-direction certificates, CO25 Def. 5.5 deviation). The repair set is shared: anchor
the `E_pinv` 5th disjunct on the query capacity (Eq. 26) and use opposite-direction
redundancy certificates (Def. 5.5); the Def-5.5/Eq-26-faithful re-statements and their
proofs are the active wave-4 work (issue #314 thread).

Note: every consumer of the residual (`honestBad_birthday_of_residuals`,
`dedupTimeHonest_birthday_of_residuals`, `honestBadDedupTime_birthday_of_residuals`)
is conditioned on a hypothesis this file proves false; they remain sound as
implications but are unwitnessable until the event repair lands.
-/

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS
open DuplexSpongeFS.KeyLemmaFoundations

-- The cosmetic `constructorNameAsVariable` naming linter overflows its recursion budget
-- on the large eager-game terms in the statements below and aborts with a `maxRecDepth`
-- error even at depth 100000 (it inspects binder names only, no proof content). Disabled
-- file-wide, matching the local-opt-out precedent of the sibling DSFS security modules.
set_option linter.constructorNameAsVariable false

namespace DuplexSpongeFS.Sponge314.K1

/-- Tiny sponge geometry: width 2, rate 1, capacity 1 (same as `Lemma516TimePFalse`). -/
instance smallSponge : SpongeSize := { N := 2, R := 1 }

noncomputable instance : Fintype (CanonicalSpongeState UInt8) :=
  Fintype.ofEquiv (Fin SpongeSize.N → UInt8) Equiv.rootVectorEquivFin.symm

noncomputable instance : SampleableType (Equiv.Perm (CanonicalSpongeState UInt8)) :=
  DuplexSpongeFS.KeyLemmaFoundations.sampleableTypePermCanonicalSpongeState UInt8

noncomputable instance : Fintype (Vector UInt8 SpongeSize.C) :=
  Fintype.ofEquiv (Fin SpongeSize.C → UInt8) Equiv.rootVectorEquivFin.symm

noncomputable instance : SampleableType (Unit → Vector UInt8 SpongeSize.C) :=
  SampleableType.ofFintype _

/-- The probed inverse-query state: the all-zero sponge state. -/
def s₀ : CanonicalSpongeState UInt8 := #v[0, 0]

/-- The oracle index of the single adversary query: `p⁻¹(s₀)`. -/
abbrev qIdx : (duplexSpongeChallengeOracle Unit UInt8).Domain := Sum.inr (Sum.inr s₀)

/-- The one-query adversary: a single inverse-permutation query. -/
noncomputable def P : OracleComp (duplexSpongeChallengeOracle Unit UInt8)
    (CanonicalSpongeState UInt8) :=
  liftM (OracleSpec.query qIdx)

/-- `P` makes exactly one query. -/
lemma isTotalQueryBound_P : IsTotalQueryBound P 1 := by
  rw [show P = liftM (OracleSpec.query qIdx) >>= pure from (bind_pure _).symm]
  exact isTotalQueryBound_query_bind_iff.mpr ⟨Nat.one_pos, fun u => trivial⟩

/-- For every sampled carrier `c`, the logged eager game on `P` is deterministic: it returns
the inverse image `c.2.symm s₀` and the singleton trace `[⟨p⁻¹(s₀), c.2.symm s₀⟩]`. -/
lemma game_apply_eq (c : (D_DS Unit UInt8).Carrier) :
    simulateQ ((D_DS Unit UInt8).toImpl c) ((simulateQ loggingOracle P).run)
    = pure (c.2.symm s₀,
        [(⟨qIdx, c.2.symm s₀⟩ : (t : (duplexSpongeChallengeOracle Unit UInt8).Domain) ×
          (duplexSpongeChallengeOracle Unit UInt8).Range t)]) := by
  simp [P, loggingOracle, QueryImpl.withLogging_apply, OracleQuery.cont_query,
    Function.id_def, D_DS, qIdx]

/-- The full game equals sampling a carrier and returning the deterministic logged output. -/
lemma game_eq :
    (do
      let c ← (D_DS Unit UInt8).sample
      simulateQ ((D_DS Unit UInt8).toImpl c)
        ((simulateQ loggingOracle P).run))
    = (D_DS Unit UInt8).sample >>= fun c =>
        pure (c.2.symm s₀,
          [(⟨qIdx, c.2.symm s₀⟩ : (t : (duplexSpongeChallengeOracle Unit UInt8).Domain) ×
            (duplexSpongeChallengeOracle Unit UInt8).Range t)]) :=
  bind_congr game_apply_eq

/-- The combined bad event `E` fires with probability **1** in the eager logged game on the
single-inverse-query adversary: the trace always contains a `p⁻¹` entry, and any inverse
entry fires `E` (`Sponge316.hasInvEntry_implies_E`, the machine-checked B1 artifact). -/
lemma probEvent_E_eq_one :
    Pr[ fun z : (CanonicalSpongeState UInt8) ×
          QueryLog (duplexSpongeChallengeOracle Unit UInt8) => E z.2 |
      do
        let c ← (D_DS Unit UInt8).sample
        simulateQ ((D_DS Unit UInt8).toImpl c)
          ((simulateQ loggingOracle P).run)] = 1 := by
  rw [game_eq]
  refine probEvent_eq_one ⟨?_, ?_⟩
  · -- the game never fails
    rw [probFailure_bind_eq_zero_iff]
    refine ⟨?_, fun c _ => by simp⟩
    simp [D_DS]
  · -- every output trace contains the inverse entry, hence fires `E`
    intro z hz
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨c, _, hz⟩ := hz
    subst hz
    exact DuplexSpongeFS.Sponge316.hasInvEntry_implies_E _
      ⟨s₀, c.2.symm s₀, List.mem_singleton_self _⟩

/-- The claimed CO25 Lemma 5.8 bound at `T = 1` is `4/(2·256) < 1`. -/
lemma lemma5_8Bound_one_lt_one :
    DuplexSpongeFS.BirthdayBound.lemma5_8Bound UInt8 1 < 1 := by
  have hcard : (2 : ℕ) < Fintype.card UInt8 :=
    Fintype.two_lt_card_iff.mpr ⟨0, 1, 2, by decide, by decide, by decide⟩
  have hcardR : (3 : ℝ) ≤ (Fintype.card UInt8 : ℝ) := by exact_mod_cast hcard
  unfold DuplexSpongeFS.BirthdayBound.lemma5_8Bound
  rw [show SpongeSize.C = 1 from rfl, pow_one]
  rw [div_lt_one (by linarith)]
  norm_num
  linarith

/-- **#314 K1 — the eager birthday residual is FALSE as stated** (at `StmtIn := Unit`,
`U := UInt8`, sponge width 2 / rate 1): the single-inverse-query adversary realizes the
combined bad event `E` with probability `1`, exceeding the claimed bound
`lemma5_8Bound UInt8 1 < 1`. The culprit is the B1 self-firing defect of
`capacitySegmentDupPermInv` (its 5th disjunct anchors on the answer capacity with
`j' ≤ j`), via the keystone `Sponge316.hasInvEntry_implies_E`. Statement repair of the
`E_pinv` disjunct (anchor on the *query* capacity, CO25 Eq. 26) is required before
CO25 Lemma 5.8 can be discharged over this event. -/
theorem lemma5_8EagerBirthdayFalseStatement_false :
    ¬ DuplexSpongeFS.BirthdayBound.Lemma5_8EagerBirthdayFalseStatement Unit UInt8 := by
  intro h
  have hb := h P 1 isTotalQueryBound_P
  rw [probEvent_E_eq_one] at hb
  rw [ENNReal.toReal_one] at hb
  exact absurd hb (not_le.mpr lemma5_8Bound_one_lt_one)

end DuplexSpongeFS.Sponge314.K1

#print axioms DuplexSpongeFS.Sponge314.K1.probEvent_E_eq_one
#print axioms DuplexSpongeFS.Sponge314.K1.lemma5_8EagerBirthdayFalseStatement_false
