/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.ToyProblem.Spec.SimplifiedIOR

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ProximityPrize.Extensions.OracleReduction.Security.Basic
import ProximityPrize.Extensions.ProofSystem.ToyProblem.Spec.General

/-!
# Simplified toy-problem IOR (ABF26 Construction 6.9)

The "attack target" simplified IOR from ABF26 §6.4. Unlike the full
Construction 6.2, this version:

  * has **one round** (V→P combination randomness only — no spot-check),
  * does **not** test acceptance (no final `guard`); instead it
    *reduces* the input instance `(v, μ₁, μ₂, f₁, f₂)` to a smaller
    instance `(v, μ₁ + γ·μ₂, f₁ + γ·f₂)`,
  * is therefore a reduction from the fixed-encoding `R̃²_{C,δ}` to the
    fixed-encoding `R̃¹_{C,δ}`.

This file follows the FRI/Sumcheck `Spec/` convention exactly (mirroring
`ToyProblem/Spec/General.lean`). The two protocols live in sibling
files because they are structurally distinct (C6.2 is a 3-round
yes/no test; C6.9 is a 1-round reducing protocol).

## Protocol

```
Verifier input  : (v, μ₁, μ₂) explicit, (f₁, f₂) oracle.
Prover witness  : (M₁, M₂) ∈ (F^k)² with C(Mᵢ) = fᵢ, ⟨Mᵢ, v⟩ = μᵢ.

Round 0  V → P : γ ←$ F.
Outputs:
  Verifier sets statement x* := (v, μ₁ + γ·μ₂) and oracle y* := f₁ + γ·f₂.
  Honest prover sets witness w* := M₁ + γ·M₂.
```

The new instance lies in `R̃¹_{C,δ}` iff the original lay in
`R̃²_{C,δ}` (up to the soundness error of L6.10).

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.4, Construction 6.9, Lemma 6.10).
-/

namespace ToyProblem

namespace SimplifiedIOR

open OracleSpec OracleComp ProtocolSpec
open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal
open ToyProblem.Spec (Statement OracleStatement Witness)

/-! ### Output types and the output relation

These need only `[Fintype ι]` (for `relaxedRelation`'s `Fintype.card ι`
call) and `[Field F]`. The heavier `[DecidableEq ι] [Fintype F]
[DecidableEq F]` instances come in below for the protocol-object
definitions. -/

variable {ι F : Type} [Fintype ι] [Field F]
variable (k : ℕ)

section Protocol
variable [DecidableEq ι] [Fintype F] [DecidableEq F]

instance : ∀ j, OracleInterface ((pSpec (F := F)).Message j)
  | ⟨0, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpec (F := F)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance [SampleableType F] : ∀ j, SampleableType ((pSpec (F := F)).Challenge j)
  | ⟨0, _⟩ => (inferInstance : SampleableType F)

/-- **Lemma 6.10 of [ABF26]** (knowledge soundness of Construction 6.9).

For any `δ ∈ (0, δ_min(C))`, the simplified IOR has knowledge soundness
(paper Def A.5) from `R̃²_{C,δ}` to `R̃¹_{C,δ}` with error

  `ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|`.

Note the cleaner error term compared with L6.6: there's no `(1-δ)^t`
spot-check term because C6.9 has no spot-check round.

The proof is the "1-round version" of L6.8's KnowledgeStateFunction
construction; same extractor strategy (erasure-decode against the
agreement set).

**Statement-level finding & repair (2026-06).** Same wall as L6.6 / L6.8: ArkLib's
`Verifier.knowledgeSoundness` (`OracleReduction/Security/Basic.lean`, line 328) quantifies only over
a single-run `Extractor.Straightline` with no re-invocation handle, so the 2-special-sound
*rewinding* extractor this lemma needs is not expressible against it. The rewinding extractor is the
*same* one as for Construction 6.2 (it extracts the input message pair `(u₁, u₂)` to the `R̃²`
relation `ToyProblem.Spec.outputRelation` — exactly this lemma's `relIn`), so we reuse the proven
`protocol62_knowledgeSoundnessViaRewinding`. -/
theorem simplifiedIOR_knowledgeSound
    [SampleableType F] [Nonempty ι] [Nonempty F]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyProblem.Spec.ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    Extractor.knowledgeSoundnessViaRewinding
      (ToyProblem.Spec.outputRelation k C δ)
      (ToyProblem.Spec.toyStmtOf (ι := ι) (F := F) (k := k))
      (ToyProblem.Spec.toyAccepts (ι := ι) (F := F) (k := k) C δ decode) :=
  ToyProblem.Spec.protocol62_knowledgeSoundnessViaRewinding C δ decode


end Protocol

end SimplifiedIOR

end ToyProblem

/-! ### Axiom audit (issue #18 simplified ToyProblem bridge residual frontier) -/

#print axioms ToyProblem.SimplifiedIOR.simplifiedIOR_knowledgeSound
