# #466 R394 — the ℓ1 kernel certificate + the FIRST concrete machine-checked K = 0 instance

## What landed (axiom-clean incl. the decide certificate, real locked build)

`Frontier/_R394L1KernelCertificate.lean`:

- **ℓ1 ledger**: keys have `ℓ1 ≤ r`, relations have `ℓ1 ≤ 2r` (`l1_le_of_mem_keysR`,
  `sectorRelations_l1_le`);
- **`relationCount_zero_of_no_l1_short_kernel`**: the CORRECT SVP-type sufficient
  condition — no nonzero kernel vector of `ℓ1 ≤ 2r` ⟹ `RealizedRelationCountBound 0`.
  (Empirical finding logged: the r393 ℓ∞ form is strictly too weak — at p=1409 there are
  16 kernel vectors with `ℓ∞ ≤ 6`, min `ℓ1 = 13`; ℓ1 is the realizability norm.)
- **`ShortKernelFreeL1`** decidable box form + bridge;
- **`n8_r3_p1409_relationCount_zero`**: `RealizedRelationCountBound (72 : ZMod 1409) 8 4 3 0`
  by plain kernel `decide` (no native_decide, no census input; `72⁴ = −1` also decided).
  Via r392, the depth-3 moment control at this instance holds with the unconditional
  char-0 constant — end-to-end inside Lean.

## Why this matters

This is the certification path made real: the arc's open Prop is DISCHARGED at a concrete
instance by finite enumeration, proving the pipeline consumes certificates as designed.
The path scales as (2·2r+1)^m kernel evaluations per instance — practical for small-m
deployment-shaped lattices (BabyBear/KoalaBear f-lattices), infeasible at prize m = 2²⁹.
The prize-scale Prop remains open. CORE OPEN, ON-BGK — with the first unconditional
instance certificate on the books.
