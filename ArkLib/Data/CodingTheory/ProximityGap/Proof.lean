/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# ABF26 Grand Challenge 1 — honest status (issue #141)

**De-larped.** The previous content of this file was a fabricated "Master Theorem"
`grand_challenge_1_breakthrough : mcaConjecture := by use 2, 5, 14; …; sorry; sorry`, which
*claimed to resolve* ABF26 Grand Challenge 1 with magic constants `(2, 5, 14)` attributed to a
non-existent `breakthrough_research.md`, behind two `sorry`s. It proved nothing: it asserted the
unsolved `mcaConjecture` via `sorry`.

`mcaConjecture` (`GrandChallenges.lean`) is the genuine **open research problem** — a uniform
`poly(|ι|, 1/ρ)/|F|` MCA-error bound for Reed–Solomon codes up to capacity radius `1 − ρ`,
equivalent to a beyond-Johnson list-decoding-radius result. It is **unsolved by anyone**, and the
naive `δ → 1 − ρ` capacity direction was **disproven in November 2025** (Crites–Stewart 2025/2046,
BCKHS25 2025/2055, Diamond–Gruen 2025/2010). There is no proof to record here; the conjecture is
deliberately carried as a non-asserting `def : Prop` in `GrandChallenges.lean` / `MCAGS.lean`.

Genuine, axiom-clean progress toward it lives in:
* `GSInterpolationExistence.lean` — the Guruswami–Sudan bivariate interpolation **existence**
  (under-determined-system kernel + multiplicity-budget), the linear-algebra core that the
  Johnson-window slice consumes.
* `MCAGSWitness.lean` — the Johnson-window list-size kernel and conditional lower-witness bridges
  (honestly conditional on the named external GS list-decoder obligations).

No theorem in this file asserts the conjecture.
-/
