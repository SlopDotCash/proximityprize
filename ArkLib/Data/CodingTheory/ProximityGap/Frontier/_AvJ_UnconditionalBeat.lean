/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvT3a_DiBenedettoBeatAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiBenedettoNearSidonImprovement

/-!
# [A3-assemble-beat] di-Benedetto near-Sidon BEAT at β=4 — assembled, with the all-prime input named (#444, AvJ)

This file is the **ASSEMBLY** requested by the [A3] task: wire the (attempted-)unconditional
`T₂ = O(n²)`, `T₃ = O(n³)` inputs from Attacks A1/A2 into the conditional di-Benedetto beat of
`_AvT3a_DiBenedettoBeatAssembly`, to state the realised sup-norm exponent at the prize aspect ratio
`β = 4` and confirm it BEATS the published SOTA there.

## The headline arithmetic (PROVEN axiom-clean, exponent bookkeeping)

* `beatExponent = 23/24 = 0.9583…` — the realised sup-norm exponent
  `M ≤ |μ_n|^{1 − 1/24} · p^{1/72}` at near-Sidon energies `(t₂,t₃) = (2,3)`, `β = 4`
  (`diBenedettoSaving 2 3 = 1/24`, file `_DiBenedettoNearSidonImprovement`).
* `beats_published_SOTA` — `1/24 > 31/2880` (factor `≈ 3.87`). The published di-Benedetto edge
  saving at the general-subgroup inputs `(49/20, 4)` is `31/2880`, attained only at the Burgess
  edge `|H| = p^{1/4}`; the trilinear `H^{1−31/2880}` is **trivial (≥ |H|) at β = 4** for the thin
  `μ_n` (its nontriviality needs `|H| > p^{1/4}`, i.e. `β < 4`). The near-Sidon beat is nontrivial
  for `|H| > p^{1/7}`, i.e. all the way to `β = 7`, hence strictly covers `β = 4`. So at the prize
  aspect ratio the near-Sidon `23/24` bound is a genuine improvement over the published bound,
  which there gives nothing.

## ⚠️ The all-prime input is NOT available — the beat stays GOOD-PRIME-conditional

The [A3] task asks to "make the beat exponent at β=4 UNCONDITIONAL" by feeding in
`T₂ = O(n²)`, `T₃ = O(n³)` **for ALL primes** from A1/A2. The in-tree exact-integer computation
shows that the all-prime input is **FALSE**, so the unconditional upgrade is provably unavailable:

* The wraparound excess `W₃(n,p) = E₃(n,p) − E₃^{char0}(n)` is NOT a Weil-boundable
  `O(deg·√p)` error. The relevant difference variety `V₃` is **0-dimensional**, so Lang–Weil/Weil
  is VACUOUS (`d = 0`: the main term IS the count, no `√p` cancellation). Instead `W₃ = 0` exactly
  for every prime OUTSIDE a finite bad set `D₃(n)`, and `W₃ > 0` exactly on `D₃(n)`
  (`_AvW3_Depth3BadPrimeSet`, `_AvCP_W3UnconditionalOutsideD3`).
* At `n = 16` the bad set is contained below the prize scale (`max D₃(16) = 41521 < n⁴ = 65536`),
  so every prize-regime prime is good and `W₃ = 0` there — but this is `n ∈ {8,16}`-specific.
* At `n = 32` the pattern **BREAKS**: `D₃(32)` contains split primes `≡ 1 mod 32` up to
  `3 487 801 441 ≫ n⁴ = 1 048 576` (with the Fermat prime `65537 ∈ D₃(32)`), i.e. ~230 genuine
  prize-regime bad primes. So `T₃(n,p) = O(n³)` **fails for all primes** (it fails on the infinitely
  many `p ∈ D₃(n)` whose max grows `~n⁶`).

Therefore: A1/A2 deliver the energy bound only on `p ∉ D_r(n)` (a GOOD-PRIME predicate about a
single prime), exactly what `_AvT3a`'s `GoodPrimeEnergyTransfer` already names. There is **no
all-prime / for-all-`q` upgrade**, because the all-prime statement is refuted by exact integers.
The prize is for-all-`q` (`mcaConjecture`, [ABF26] §4.5), so this beat is NOT prize closure.

`isAllPrime = false`. `isPrizeClosure = false`. The beat is honestly **good-prime-conditional**,
discharged by the named `GoodPrimeEnergyTransfer p` per prime; the all-prime quantifier cannot be
filled. This file states that conditional beat cleanly and pins the SOTA comparison.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open ArkLib.ProximityGap.Frontier.AvT3aDiBenedettoBeat (beatExponent DiBenedettoThm31
  GoodPrimeEnergyTransfer diBenedetto_beat beatExponent_between)
open ProximityGap.Frontier.DiBenedettoNearSidon (diBenedettoSaving)

namespace ArkLib.ProximityGap.Frontier.AvJUnconditionalBeat

variable {L : Type*} [Field L] [DecidableEq L] [CharZero L]

/-- The realised sup-norm exponent of the assembled beat at `β = 4` is `23/24` (the near-Sidon
saving `1/24` subtracted from the trivial `1`). Restated here for the headline. -/
theorem realised_exponent_eq : (beatExponent : ℚ) = 1 - diBenedettoSaving 2 3 := by
  have : diBenedettoSaving 2 3 = 1 / 24 := by unfold diBenedettoSaving; norm_num
  rw [this]; unfold beatExponent; norm_num

/-- **The beat BEATS the published SOTA at β=4.** The near-Sidon power saving `1/24` strictly
exceeds the published general-subgroup edge saving `31/2880` (factor `≈ 3.87`). At `β = 4` the
published `H^{1−31/2880}` trilinear bound is trivial for the thin `μ_n` (needs `|H| > p^{1/4}`),
whereas the near-Sidon `23/24` bound is nontrivial down to `β = 7 > 4`. Exponent-level, exact. -/
theorem beats_published_SOTA : diBenedettoSaving (49 / 20) 4 < diBenedettoSaving 2 3 := by
  unfold diBenedettoSaving; norm_num

/-- **The assembled (good-prime-conditional) beat.** Given the EXTERNAL di-Benedetto Thm 3.1
estimate `hThm` (arXiv:2003.06165, the trilinear character-sum machinery specialized to `μ_n`) and
the per-prime energy transfer `hTransfer : GoodPrimeEnergyTransfer G` (the char-0 cubic-energy
bound `E₃ ≤ 15·|G|³` reduced mod `p`, valid exactly when `p ∉ D₃(n)`), the worst-case complete
character sum obeys

  `M ≤ |G|^{23/24} · p^{1/72}`.

This is `_AvT3a.diBenedetto_beat` re-exported under the [A3] headline. The conclusion is the
realised `β = 4` beat exponent `23/24`. It remains GOOD-PRIME-conditional: `hTransfer` is a
statement about the single prime `p`, and the all-prime upgrade is provably unavailable (see
the file header — `D₃(32)` has bad primes `≫ n⁴`). -/
theorem assembled_beat (G : Finset L) (Mval pval : ℝ)
    (hThm : DiBenedettoThm31 G Mval pval)
    (hTransfer : GoodPrimeEnergyTransfer G) :
    Mval ≤ (G.card : ℝ) ^ (beatExponent : ℝ) * pval ^ ((1 : ℝ) / 72) :=
  diBenedetto_beat G Mval pval hThm hTransfer

/-- **The honest scope flag, as a proposition.** The realised exponent is `23/24`, which is strictly
between the prize target `1/2` and the trivial `1`: the beat is a SOTA-direction gain on the HIGH
side of the BGK/Paley wall, NOT a crossing of it. (`23/24 ≫ 1/2`.) -/
theorem beat_is_high_side_of_wall : (1 : ℚ) / 2 < beatExponent ∧ beatExponent < 1 :=
  beatExponent_between

end ArkLib.ProximityGap.Frontier.AvJUnconditionalBeat

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.AvJUnconditionalBeat.realised_exponent_eq
#print axioms ArkLib.ProximityGap.Frontier.AvJUnconditionalBeat.beats_published_SOTA
#print axioms ArkLib.ProximityGap.Frontier.AvJUnconditionalBeat.assembled_beat
#print axioms ArkLib.ProximityGap.Frontier.AvJUnconditionalBeat.beat_is_high_side_of_wall
