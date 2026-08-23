/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb23Bricks
import ArkLib.OracleReduction.Security.OracleDistribution
import ArkLib.ToVCVio.UniformFamilyComap

/-!
# H23-7: the Claim 5.23 table coupling — uniform `f`-table comaps to a uniform `e`-table

The probabilistic core of `Δ(Hyb₂, Hyb₃) = 0`: reading a uniform **salted basic-FS** table
`f` through the `β` re-keying `(i, 𝕩, τ̂, α̂) ↦ (i, ((𝕩, bin(τ̂)), φ⁻¹(α̂)))` on
decode-success keys is distributed exactly as a uniform **decoded challenge** table `e` on
those keys.

This instantiates the generic uniform-family comap (H23-5,
`evalDist_uniformFamily_comap_injective`) at the `betaKey` injection (H23-4',
`betaKey_injOn` — axiom-clean since the `dite` repair):

* index injection — `betaKeyOf : DecodeSuccessKey → (fsChallengeOracle (StmtIn × Salt)
  pSpec).Domain`, injective because `bin` is injective (class law) and `φ⁻¹` is injective
  on its success domain (H23-4);
* range agreement — both tables answer with `pSpec.Challenge i` at matching rounds, so the
  per-key transport is `Equiv.refl`.

Downstream (H23-8..10), this equality replaces the `Hyb₃` table reads by `Hyb₂` table
reads under the relational `simulateQ` lift: distinct `Hyb₂` memo misses read distinct
(hence i.i.d. uniform) cells of the coupled `f`-table, which is exactly the distribution
`Hyb₂`'s own `e`-table provides.

Finiteness: the ambient-domain `Finite` hypotheses are inherited from the H23-5 proof
route. At the DSFS use sites the reachable salted keys carry salts in
`Set.range SaltCodec.encode ≃ Vector U δ` (finite) and finitely many message prefixes, so
the hypotheses are satisfiable at every instantiation that actually samples the table.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb23Bricks

open TraceTransform ProverTransform

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)]
  {δ : Nat} {Salt : Type} [SaltCodec U δ Salt]

/-- The decode-success keys of the `Hyb₂` encoded challenge surface: `eSpec` keys whose
encoded message prefix parses under `φ⁻¹`. These are exactly the keys reachable behind the
simulator's codec-image guard (H23-2). -/
def DecodeSuccessKey (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [DecidableEq U] [Codec pSpec U]
    [∀ i, Fintype (pSpec.Message i)] (δ : ℕ) : Type :=
  {q : (eSpec (U := U) StmtIn pSpec δ).Domain //
    (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) q.1 q.2.2.2).isSome}

/-- The `β` re-keying on decode-success keys, with the decoded prefix extracted from the
success certificate. -/
def betaKeyOf (s : DecodeSuccessKey StmtIn pSpec U δ) :
    (fsChallengeOracle (StmtIn × Salt) pSpec).Domain :=
  betaKey (Salt := Salt) (StmtIn := StmtIn) s.1
    ((hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) s.1.1 s.1.2.2.2).get s.2)

/-- **`betaKeyOf` is injective** — the bundled form of H23-4' on the success subtype. -/
lemma betaKeyOf_injective :
    Function.Injective (betaKeyOf (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (δ := δ) (Salt := Salt)) := by
  rintro ⟨q, hq⟩ ⟨q', hq'⟩ heq
  exact Subtype.ext (betaKey_injOn (Option.some_get hq).symm (Option.some_get hq').symm heq)

/-- **H23-7 — the table coupling.** Reading a uniform salted basic-FS table through
`betaKeyOf` on the decode-success keys is distributed as a uniform decoded challenge table
on those keys. -/
theorem evalDist_fTable_comap_betaKeyOf_eq_uniform
    [Finite (DecodeSuccessKey StmtIn pSpec U δ)]
    [Finite ((fsChallengeOracle (StmtIn × Salt) pSpec).Domain)]
    [∀ q : (fsChallengeOracle (StmtIn × Salt) pSpec).Domain,
      Fintype ((fsChallengeOracle (StmtIn × Salt) pSpec).Range q)]
    [∀ q : (fsChallengeOracle (StmtIn × Salt) pSpec).Domain,
      Nonempty ((fsChallengeOracle (StmtIn × Salt) pSpec).Range q)]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [SampleableType ((s : DecodeSuccessKey StmtIn pSpec U δ) →
      (eSpec (U := U) StmtIn pSpec δ).Range s.1)] :
    𝒟[do
        let f ← $ᵗ OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)
        pure (fun s : DecodeSuccessKey StmtIn pSpec U δ =>
          f (betaKeyOf (Salt := Salt) s))]
      = 𝒟[$ᵗ ((s : DecodeSuccessKey StmtIn pSpec U δ) →
          (eSpec (U := U) StmtIn pSpec δ).Range s.1)] := by
  have h := evalDist_uniformFamily_comap_injective
    (specA := fun s : DecodeSuccessKey StmtIn pSpec U δ =>
      (eSpec (U := U) StmtIn pSpec δ).Range s.1)
    (specB := fsChallengeOracle (StmtIn × Salt) pSpec)
    (betaKeyOf (Salt := Salt))
    (betaKeyOf_injective (Salt := Salt))
    (fun s => Equiv.refl (pSpec.Challenge s.1.1))
  simp only [Equiv.refl_apply] at h
  exact h

end DuplexSpongeFS.Hyb23Bricks

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.Hyb23Bricks.betaKeyOf_injective
#print axioms DuplexSpongeFS.Hyb23Bricks.evalDist_fTable_comap_betaKeyOf_eq_uniform
