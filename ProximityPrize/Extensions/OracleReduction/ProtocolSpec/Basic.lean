/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.ProtocolSpec.Basic

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.Data.Fin.Tuple.Lemmas
import ProximityPrize.Extensions.OracleReduction.Prelude
import ProximityPrize.Extensions.OracleReduction.OracleInterface

/-!
# Interactive and Oracle Protocol Specifications

This module formalizes the structural specifications of interactive and interactive oracle proof
protocols. In a multi-round interactive setting, a protocol specification dictates the communication
topology
between a Prover and a Verifier. We represent this via the `ProtocolSpec` structure, which models
the protocol as a sequence of discrete communication steps (or rounds).

For each step $i \in \{0, \dots, n-1\}$, the specification defines:
1. The direction of communication (`Direction`), distinguishing between prover-to-verifier messages
   (`.P_to_V`) and verifier-to-prover challenges (`.V_to_P`).
2. The message space (`«Type»`), which is the set of all possible messages or challenges
   transmittable at step $i$.

We define projections and operations on partial and full transcripts of these communication
protocols, facilitating the formalization of round-by-round and straightline extractors.
-/

universe u v

open OracleComp OracleSpec

variable {n : ℕ}

namespace ProtocolSpec

section Defs

section Restrict

variable {n : ℕ}

variable {m start stop : ℕ} {h : m ≤ n} {h1 : start ≤ stop} {h2 : stop ≤ n}
  {pSpec : ProtocolSpec n}

namespace FullTranscript

variable {pSpec : ProtocolSpec n}

variable {m start stop : ℕ} {h : m ≤ n} {h1 : start ≤ stop} {h2 : stop ≤ n}
  {pSpec : ProtocolSpec n} {transcript : FullTranscript pSpec}

end FullTranscript

end Restrict

end Defs

section Instances

/-- There is only one protocol specification with 0 messages (the empty one) -/
instance : Unique (ProtocolSpec 0) where
  default := empty
  uniq := fun ⟨_, _⟩ => by
    simp only [mk.injEq]; constructor <;> (funext i; exact Fin.elim0 i)

-- Note these strange instance syntheses. This is necessary to avoid diamonds later on when
-- going to sequential composition.

variable {Msg Chal : Type}

variable {pSpec : ProtocolSpec n}

end Instances

variable {pSpec : ProtocolSpec n}

namespace MessagesUpTo

variable {k : Fin (n + 1)}

end MessagesUpTo

namespace Messages

end Messages

namespace ChallengesUpTo

variable {k : Fin (n + 1)}

end ChallengesUpTo

namespace Challenges

end Challenges

namespace MessagesUpTo

end MessagesUpTo

namespace ChallengesUpTo

end ChallengesUpTo

namespace Transcript

variable {k : Fin (n + 1)}

@[simp]
theorem equivMessagesChallenges_fst_apply (transcript : Transcript k pSpec)
    (i : MessageIdxUpTo k pSpec) :
    (Transcript.equivMessagesChallenges transcript).1 i = transcript i.val := rfl

@[simp]
theorem equivMessagesChallenges_snd_apply (transcript : Transcript k pSpec)
    (i : ChallengeIdxUpTo k pSpec) :
    (Transcript.equivMessagesChallenges transcript).2 i = transcript i.val := rfl

end Transcript

namespace FullTranscript

@[simp]
theorem messages_apply (transcript : FullTranscript pSpec) (i : MessageIdx pSpec) :
    messages transcript i = transcript i.val := rfl

@[simp]
theorem challenges_apply (transcript : FullTranscript pSpec) (i : ChallengeIdx pSpec) :
    challenges transcript i = transcript i.val := rfl

@[simp]
theorem equivMessagesChallenges_fst_apply (transcript : FullTranscript pSpec)
    (i : MessageIdx pSpec) :
    (FullTranscript.equivMessagesChallenges transcript).1 i = transcript.messages i := rfl

@[simp]
theorem equivMessagesChallenges_snd_apply (transcript : FullTranscript pSpec)
    (i : ChallengeIdx pSpec) :
    (FullTranscript.equivMessagesChallenges transcript).2 i = transcript.challenges i := rfl

end FullTranscript

section OracleInterfaces

variable (pSpec : ProtocolSpec n) [inst : OracleInterfaces pSpec]

end OracleInterfaces

/-- Decidable equality for state-restoration and Fiat-Shamir oracle responses. -/
instance {pSpec : ProtocolSpec n} {Statement : Type}
    [h : ∀ i, DecidableEq (pSpec.Challenge i)] :
    ∀ q, DecidableEq (srChallengeOracle Statement pSpec q) := fun q => h q.1

/-- Finite state-restoration and Fiat-Shamir oracle responses. -/
instance {pSpec : ProtocolSpec n} {Statement : Type} [∀ i, VCVCompatible (pSpec.Challenge i)] :
    ∀ q, Fintype (srChallengeOracle Statement pSpec q) := fun q =>
  inferInstanceAs (Fintype (pSpec.Challenge q.1))

/- `fsChallengeOracle` is the canonical alias of `srChallengeOracle`, so these native
pointwise instances supply both interfaces. Query equality uses ordinary Sigma instances. -/

namespace MessagesUpTo

end MessagesUpTo

namespace Messages

end Messages

end ProtocolSpec
