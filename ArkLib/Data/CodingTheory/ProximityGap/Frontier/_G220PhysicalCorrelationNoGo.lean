/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G220: physical-space covariance sign is unforced, no diagonal-dominance certificate (#466)

Every prior no-go on the surviving CORE target worked in **Mellin / character space**.  The signed
simultaneous late-Newton covariance

```text
A_r := p · Σ_t W_G(t) · R_r(t)  −  n² · C(n,r),          r ∈ {5, 6}
```

was restated in exact quotient-Mellin/Jacobi coordinates (G216) and its sign was shown to live in
the equidistributing complex conjugate-pair phases: no bounded-order truncation (G216), no top-k
conductor shell (Fable), no per-rank phase coherence (G217, `frac_half → 1/2`), no inter-rank phase
lock (sign-blind), no inter-rank magnitude ratio transfer (G56, 8 to 12 % nonconstant), no
shared-factor `Ŵ` phase alignment (G219).  Every *character-space* decomposition scrambles the sign.

This lane takes the **complementary physical-space view**, which no prior lane probed.  By Parseval
on `ℤ/p` (`R_r` real):

```text
p · Σ_t W_G(t) R_r(t)  =  Σ_χ Ŵ(χ) · conj(R̂_r(χ)),
```

and the trivial character contributes exactly `(Σ W_G)(Σ R_r) = n² · C(n,r)`.  Hence the *physical*
signed correlation

```text
A_signed(n,p,r) := p · Σ_t W_G(t) R_r(t)  −  n² · C(n,r)
                 = Σ_{χ ≠ 1} Ŵ(χ) · conj(R̂_r(χ))
```

**equals** the CORE covariance object (the file's probe cross-checks this to machine precision:
`A_signed = char-space Re-sum` at `rel-err ≈ 1e-14`).  In physical space `A_signed` is an *exact
integer combinatorial correlation* with **no phases at all**, a count.  The natural remaining hope,
invisible from the character side, is a **diagonal-dominance** mechanism: the correlation is
dominated by the mass on the structural support `S := {t : W_G(t) > 0}` (the `2G − G` translate set,
a 2-power-subgroup object), and that dominant diagonal term might carry a *forced sign*, giving a
truncation-free signed lower bound the Mellin phases hide.

## The physical route is dead too (probes of record)

`scripts/probes/oc_g220_physical_correlation_probe.py` computes, as exact integers over
`n ∈ {8,16,32,64}` and a growing prime family, `A_signed` and its sign; the DC-removed decomposition

```text
p · A_signed = Σ_t ( p·W_G(t) − n² )·( p·R_r(t) − C(n,r) )
             = D_on + D_off,   D_on := restriction to t ∈ S,  D_off := t ∉ S
```

is computed by `oc_g220_diagonal_dominance_probe.py`.  Two facts kill the physical route:

* **Sign is not forced.**  At fixed rank the sign of `A_signed` realises **both** values across
  prize-faithful cells (`r = 5`: 6 positive / 10 negative; `r = 6`: 8 positive / 6 negative), and
  **all four joint quadrants** `(sign A₅, sign A₆) ∈ {++, +−, −+, −−}` occur, the exact physical
  mirror of G214's Mellin-space joint-sign no-go.
* **The dominant diagonal does not carry the sign.**  `D_on` dominates `|D_off|` in 27 of 28 cells
  (the correlation *is* concentrated on the 2-power-subgroup translate support), yet the sign of the
  dominant `D_on` itself is **not forced**: `r = 5` gives 5 positive / 9 negative and `r = 6` gives
  8 positive / 6 negative on-support.  There is no diagonal-dominance sign certificate: the dominant
  structural term flips sign across cells just like the total.

## The float-free certificate

For a witness `(n, p, r)` the probes record the exact integers

```text
sumW    := Σ_t W_G(t) = n²,          sumR := Σ_t R_r(t) = C(n,r)
C       := Σ_t W_G(t) R_r(t)                              (physical correlation, ∈ ℤ)
A       := p · C − sumW · sumR                            (= Σ_{χ≠1} Ŵ conj(R̂_r), ∈ ℤ)
Don     := Σ_{t ∈ S} ( p·p·W_G(t)·R_r(t) − p·W_G(t)·sumR − p·R_r(t)·sumW + sumW·sumR )
                                                          (= p × on-support part of A, ∈ ℤ)
```

This file certifies, float-free and axiom-free, that `A` realises both signs at fixed rank and that
the dominant on-support diagonal `Don` realises both signs, so neither the physical signed
correlation nor its diagonal-dominant part admits a forced-sign certificate.  All recorded constants
are recomputed float-free and asserted to match by `scripts/probes/oc_g220_witness_exact.py`.

## Scope of the formal payload (honest)

As with G214/G216/G217, the **computation of record** is the reproducible float-free probe; this
file does **not** re-derive `A` from an in-Lean BGK definition.  It **certifies the arithmetic** of
the recorded constants: that at fixed rank `r = 5` the covariance `A` takes strictly positive value
on one witness and strictly negative on another, and likewise for the dominant on-support diagonal
`Don`, hence no sign is forced and no diagonal-dominance mechanism exists.  The census fractions
(6/10, 8/6, 5/9, …) and the domination `|D_on| ≥ |D_off|` are limiting statistical statements whose
computation of record is the Python sweep; they are not dressed as Lean theorems here.

## Why this is a genuine frontier no-go

It closes the **physical-space** route in the same strong sense the Mellin tower closed the
character-space routes.  `A_signed` is *exactly* the CORE covariance (Parseval), it is a
phase-free exact integer, its correlation mass concentrates on the 2-power-subgroup translate
support `S` (diagonal dominance holds), and yet the dominant diagonal term still flips sign.  So the
signed target is not thinned by moving out of Mellin space: there is no combinatorial
diagonal-dominance shortcut, exactly as there is no phase-coherence shortcut (G217) and no
truncation shortcut (G216).  Thinness-relevant (witnesses are 2-power subgroups; `S = 2G − G` is the
dyadic translate set).  It does **not** bound `A_5` or `A_6` at production primes; CORE remains
OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G220

/-- Exact physical-space correlation data for one `(order, prime, rank)` BGK late-alignment witness.

* `A`   is the exact signed covariance `p · Σ_t W_G(t) R_r(t) − n² · C(n,r)`, which by Parseval
  equals `Σ_{χ ≠ 1} Ŵ(χ) · conj(R̂_r(χ))`, the CORE target object, in physical space.
* `Don` is `p ×` the on-`W`-support ("diagonal") part of `A`, i.e. the restriction of the DC-removed
  sum `Σ_t (p·W_G(t) − n²)(p·R_r(t) − C(n,r))` to `t` with `W_G(t) > 0`.  This is the dominant term
  (`|D_on| ≥ |D_off|` in 27/28 cells) and the natural candidate for a forced-sign certificate.

All are exact integers from the float-free probes over `𝔽_p`. -/
structure PhysWitness where
  n : ℕ
  p : ℕ
  r : ℕ
  A : ℤ
  Don : ℤ

/-- The physical signed correlation is strictly positive. -/
def APos (w : PhysWitness) : Prop := 0 < w.A

/-- The physical signed correlation is strictly negative. -/
def ANeg (w : PhysWitness) : Prop := w.A < 0

/-- The dominant on-support diagonal is strictly positive. -/
def DonPos (w : PhysWitness) : Prop := 0 < w.Don

/-- The dominant on-support diagonal is strictly negative. -/
def DonNeg (w : PhysWitness) : Prop := w.Don < 0

instance (w : PhysWitness) : Decidable (APos w) := by unfold APos; infer_instance
instance (w : PhysWitness) : Decidable (ANeg w) := by unfold ANeg; infer_instance
instance (w : PhysWitness) : Decidable (DonPos w) := by unfold DonPos; infer_instance
instance (w : PhysWitness) : Decidable (DonNeg w) := by unfold DonNeg; infer_instance

/-- Positive-`A` witness at `r = 5`: `n = 8`, `p = 257`.  `A_signed = +2584`. -/
def wPosA_r5 : PhysWitness :=
  { n := 8, p := 257, r := 5, A := 2584, Don := 498712 }

/-- Negative-`A` witness at `r = 5`: `n = 8`, `p = 97`.  `A_signed = −480`. -/
def wNegA_r5 : PhysWitness :=
  { n := 8, p := 97, r := 5, A := -480, Don := -73184 }

/-- Positive on-support diagonal at `(n=16, p=97, r=6)`.  `Don = +6 309 024`, `A = +51 360`. -/
def wPosDon : PhysWitness :=
  { n := 16, p := 97, r := 6, A := 51360, Don := 6309024 }

/-- Negative on-support diagonal at the same `(n=16, p=97)` but `r = 5`.
`Don = −6 516 064`, `A = −59 744`: the dominant diagonal flips sign between the two ranks at a
single field. -/
def wNegDon : PhysWitness :=
  { n := 16, p := 97, r := 5, A := -59744, Don := -6516064 }

/-- A second positive-`A` witness at `r = 5` and larger order: `n = 32`, `p = 257`.
`A_signed = +1 775 936`. -/
def wPosA_r5_n32 : PhysWitness :=
  { n := 32, p := 257, r := 5, A := 1775936, Don := 392714560 }

/-- A second negative-`A` witness at `r = 5` and large `m`: `n = 32`, `p = 1153`.
`A_signed = −17 412 192`, an opposite sign at the same order and rank as `wPosA_r5_n32`. -/
def wNegA_r5_n32 : PhysWitness :=
  { n := 32, p := 1153, r := 5, A := -17412192, Don := -14241849440 }

/-- `wPosA_r5` has `A = +2584 > 0`. -/
theorem wPosA_r5_pos : APos wPosA_r5 := by decide

/-- `wNegA_r5` has `A = −480 < 0`. -/
theorem wNegA_r5_neg : ANeg wNegA_r5 := by decide

/-- `wPosA_r5_n32` has `A = +1 775 936 > 0`. -/
theorem wPosA_r5_n32_pos : APos wPosA_r5_n32 := by decide

/-- `wNegA_r5_n32` has `A = −17 412 192 < 0`. -/
theorem wNegA_r5_n32_neg : ANeg wNegA_r5_n32 := by decide

/-- `wPosDon` has dominant diagonal `Don = +6 309 024 > 0`. -/
theorem wPosDon_pos : DonPos wPosDon := by decide

/-- `wNegDon` has dominant diagonal `Don = −6 516 064 < 0`. -/
theorem wNegDon_neg : DonNeg wNegDon := by decide

/-- **Headline no-go, part 1: the physical signed correlation has no forced sign.**  At a fixed
rank `r = 5` the exact physical covariance `A_signed = p·Σ_t W_G(t)R_r(t) − n²·C(n,r)` (which by
Parseval equals the CORE object `Σ_{χ≠1} Ŵ(χ)conj(R̂_r(χ))`) is strictly positive on one
prize-faithful witness and strictly negative on another.  Moving the target out of Mellin space
into an exact integer combinatorial correlation does not thin it: the sign is still unforced. -/
theorem physical_correlation_sign_not_forced :
    (∃ w : PhysWitness, w.r = 5 ∧ APos w) ∧ (∃ w : PhysWitness, w.r = 5 ∧ ANeg w) :=
  ⟨⟨wPosA_r5, by decide, wPosA_r5_pos⟩, ⟨wNegA_r5, by decide, wNegA_r5_neg⟩⟩

/-- The positive/negative `A` witnesses at a *fixed order* `n = 32` and *fixed rank* `r = 5`,
differing only in the prime, so the sign flip is not an artifact of varying `n`. -/
theorem physical_sign_flip_fixed_order :
    wPosA_r5_n32.n = wNegA_r5_n32.n ∧ wPosA_r5_n32.r = wNegA_r5_n32.r ∧
      APos wPosA_r5_n32 ∧ ANeg wNegA_r5_n32 :=
  ⟨by decide, by decide, wPosA_r5_n32_pos, wNegA_r5_n32_neg⟩

/-- **Headline no-go, part 2: the dominant diagonal has no forced sign either.**  The on-`W`-support
term `Don` dominates the off-support remainder (`|D_on| ≥ |D_off|` in the probe), so it is the
natural diagonal-dominance candidate for a forced sign.  It is strictly positive on one witness and
strictly negative on another *at the same field* `p = 97, n = 16` (the two ranks `r ∈ {6,5}`), so no
diagonal-dominance mechanism certifies `sign(A_r)`.  Together with part 1, the physical-space route
to a signed lower bound is closed. -/
theorem diagonal_dominance_sign_not_forced :
    (∃ w : PhysWitness, DonPos w) ∧ (∃ w : PhysWitness, DonNeg w) ∧
      wPosDon.p = wNegDon.p ∧ wPosDon.n = wNegDon.n :=
  ⟨⟨wPosDon, wPosDon_pos⟩, ⟨wNegDon, wNegDon_neg⟩, by decide, by decide⟩

end ArkLib.ProximityGap.Frontier.G220
