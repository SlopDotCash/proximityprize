/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# G280: the sponsor covariance is a real signed inner product; its cone is antipode-free (#466)

## Frontier context

The Fable critic (G276/G279) retired every **polarity-invariant** (even) lower certificate for the
CORE covariance

```text
B(W, R) := p · Σ_x W_G(x) R_r(x) − (Σ_x W_G(x))·(Σ_x R_r(x)),
```

via the exact involution `B(W, −R) = −B(W, R)`, under which every currently available datum (norms,
energies, `|Gram|` entries, operator ceilings) is unchanged.  Any PSD/energy consequence
`B ≥ Q ≥ 0` then also gives `−B ≥ Q ≥ 0`, forcing `Q = 0` and `B = 0`, contradicting the census.
The **single surviving escape hatch** Fable identified is a *sponsor-specific* quadratic
certificate on the narrow cone of actual subset-correlation profiles, caveated as alive only
*"because
that cone need not contain `−R`"*.  This file decides that caveat.

## The two structural facts (probe of record: `scripts/probes/g280_sponsor_cone_antipode_probe.py`)

**Fact 1 — real-Fourier / signed-inner-product structure (thinness-essential).**
Because the thin order-`n` subgroup `G` is a 2-power subgroup of `𝔽_p^*`, it contains `−1`, so both
sponsor factors are **coordinate-even**: `W_G(−x) = W_G(x)` and `R_r(−x) = R_r(x)`.  Hence their
discrete Fourier transforms are **real**, and the covariance is an *honest real signed inner
product* of two real frequency sequences,

```text
B = Σ_{χ≠0} Ŵ(χ)·R̂(χ)      (real, no complex phase, no magnitude positivity).
```

Equivalently, float-free, the pairing **folds** onto the half-line: with `half = (p−1)/2`,

```text
B = p·[ W_G(0)R_r(0) + 2·Σ_{x=1}^{half} W_G(x)R_r(x) ] − (Σ W_G)(Σ R_r).
```

The probe verifies this folded identity exactly (`B_folded = B_direct`) on all recorded cells and
that `B` realises **both signs** across sponsors.  So polarity is carried entirely by the *relative
sign pattern* of two real even sequences across frequencies — never by any magnitude — which is
exactly why every even/PSD certificate is polarity-blind (matching Fable's `H_odd` necessity).

**Fact 2 — the sponsor cone is antipode-free.**
Fable's involution sends the centered profile `c(x) := p·R_r(x) − ΣR_r` to `−c`.  An exhaustive
search shows `−c` is **not** realizable as any sponsor centered profile: over all ranks
`r' = 1..n`, all multiplicative dilations `x ↦ a·x` (`a ∈ G`), the coordinate antipode `x ↦ −x`,
and all affine shifts, no realizable profile equals `−c` (or any negative multiple of `c`).
Census across
`n ∈ {8, 16}`, genuine ranks, seven sponsor cells: `0/12` antipode hits, `12/12` coordinate-even.

## What this closes and what survives

- It **confirms Fable's escape hatch is genuinely live, not vacuous**: because the actual profile
  cone does not contain `−R`, the polarity involution does *not* auto-kill a sponsor certificate.
- It **sharpens the surviving route to a hard shape**: by Fact 1 the covariance is a real signed
  inner product whose sign lives in the relative sign pattern of two real even Fourier sequences.
  Any sponsor-specific certificate must therefore be an **odd, real-sign alignment statement** on
  that
  cone (exactly `H_odd`), with *no* PSD, magnitude, energy, or operator-norm shortcut — every such
  shortcut is polarity-invariant and dies to `B(W,−R) = −B(W,R)`.
- CORE remains **OPEN / ON-BGK**.  This is a structural localization + no-go on certificate *shape*,
  not a bound on `B` at production primes.

## Formal payload (honest scope)

The **odd-symmetry law** `B(W, −R) = −B(W, R)` is proved abstractly in-Lean for the exact bilinear
covariance functional (`covOdd`), giving a genuine theorem, not a `decide` fact: this is the
algebraic engine behind the even-certificate no-go.  The recorded-cell data (the folded-pairing
`B = p·fold − SW·SR` and both-sign realisation) are certified by `decide` on the exact integers from
the probe.  The antipode-free census (`0/12`) is a search whose record is the Python sweep; the Lean
file does not re-run the exhaustive orbit search.  Computation of record is the float-free probe.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G280

/-! ### The abstract odd-symmetry law (the engine of the even-certificate no-go) -/

/-- The exact centered covariance functional on a finite index set `ι`, as an integer bilinear form:

`covOdd p W R = p · Σ_x W(x)·R(x) − (Σ_x W(x))·(Σ_x R(x))`.

This is the frontier CORE covariance `B(W, R)` with `W = W_G` the double-shift sponsor weight and
`R = R_r` the adjacent-rank subset-correlation profile. -/
def covOdd {ι : Type*} [Fintype ι] (p : ℤ) (W R : ι → ℤ) : ℤ :=
  p * (∑ x, W x * R x) - (∑ x, W x) * (∑ x, R x)

/-- **The polarity involution (Fable's `B(W,−R) = −B(W,R)`).**  Negating the profile `R` negates the
covariance exactly.  This is the algebraic reason every profile-even certificate (norms, energies,
`|Gram|`, operator ceilings) is polarity-blind: such data are invariant under `R ↦ −R`, so a
consequence `B ≥ Q ≥ 0` also gives `−B ≥ Q ≥ 0`, forcing `Q = 0` and `B = 0`. -/
theorem covOdd_neg_right {ι : Type*} [Fintype ι] (p : ℤ) (W R : ι → ℤ) :
    covOdd p W (fun x => -R x) = -covOdd p W R := by
  unfold covOdd
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

/-- Symmetrically, the covariance is odd in the sponsor weight `W` as well. -/
theorem covOdd_neg_left {ι : Type*} [Fintype ι] (p : ℤ) (W R : ι → ℤ) :
    covOdd p (fun x => -W x) R = -covOdd p W R := by
  unfold covOdd
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

/-- **Even-data no-go, abstractly.**  If a putative lower form `Q W R` is *profile-even*
(`Q W (−R) = Q W R`) and universally dominates the covariance (`Q W R ≤ covOdd p W R` for all `R`),
then it cannot be nonnegative unless it is identically the zero bound at that point: any such `Q`
forces `covOdd p W R = 0`.  This is Fable's `H_PSD` death, stated once and for all. -/
theorem even_lower_certificate_forces_zero {ι : Type*} [Fintype ι] (p : ℤ) (W R : ι → ℤ)
    (Q : (ι → ℤ) → (ι → ℤ) → ℤ)
    (hEven : Q W (fun x => -R x) = Q W R)
    (hNonneg : 0 ≤ Q W R)
    (hDom : ∀ S : ι → ℤ, Q W S ≤ covOdd p W S) :
    covOdd p W R = 0 := by
  have h1 : Q W R ≤ covOdd p W R := hDom R
  have h2 : Q W R ≤ covOdd p W (fun x => -R x) := by
    have := hDom (fun x => -R x); rwa [hEven] at this
  rw [covOdd_neg_right] at h2
  -- Q W R ≤ covOdd  and  Q W R ≤ -covOdd, with 0 ≤ Q W R
  -- ⇒ 0 ≤ covOdd and 0 ≤ -covOdd ⇒ covOdd = 0
  have hle : (0 : ℤ) ≤ covOdd p W R := le_trans hNonneg h1
  have hge : covOdd p W R ≤ 0 := by linarith
  linarith

/-! ### Recorded-cell certificates (exact integers, `decide`) -/

/-- Exact folded-pairing data for one genuine `(order, prime)` sponsor cell at rank `r = 5`, from
the float-free probe.  By Fact 1 (`−1 ∈ G ⇒ W_G, R_5` coordinate-even) the covariance folds onto the
half-line: with `half = (p−1)/2`,

`B = p · [W0·R0 + 2·(Σ_{x=1}^{half} W_G(x)R_5(x))] − SW·SR`,

where `fold := W0·R0 + 2·Σ_{x=1}^{half} W_G(x)R_5(x)` is the exact integer folded correlation,
`SW := Σ W_G`, `SR := Σ R_5`, and `B` is the exact covariance. -/
structure FoldWitness where
  n : ℕ
  p : ℕ
  W0 : ℤ
  R0 : ℤ
  SW : ℤ
  SR : ℤ
  fold : ℤ
  B : ℤ

/-- The folded-pairing identity for a cell: `B = p·fold − SW·SR` (evenness collapses the full sum to
the half-line fold, exactly). -/
def FoldHolds (w : FoldWitness) : Prop := w.B = (w.p : ℤ) * w.fold - w.SW * w.SR

/-- The covariance is strictly positive at this cell. -/
def BPos (w : FoldWitness) : Prop := 0 < w.B

/-- The covariance is strictly negative at this cell. -/
def BNeg (w : FoldWitness) : Prop := w.B < 0

instance (w : FoldWitness) : Decidable (FoldHolds w) := by unfold FoldHolds; infer_instance
instance (w : FoldWitness) : Decidable (BPos w) := by unfold BPos; infer_instance
instance (w : FoldWitness) : Decidable (BNeg w) := by unfold BNeg; infer_instance

/-- `(16, 97)`, `r = 5`: `B = −6 285 008 < 0`.  Note `W_G(0) = 0` (DC term purely `R_5`-driven); the
fold `20 916 016` is a genuine half-line correlation. -/
def cell_97 : FoldWitness :=
  { n := 16, p := 97, W0 := 0, R0 := 77856, SW := 256, SR := 7949760,
    fold := 20916016, B := -6285008 }

/-- `(16, 433)`, `r = 5`: `B = +3 425 440 > 0`. -/
def cell_433 : FoldWitness :=
  { n := 16, p := 433, W0 := 0, R0 := 20304, SW := 256, SR := 7949760,
    fold := 4708000, B := 3425440 }

/-- `(16, 977)`, `r = 5`: `B = −8 434 128 < 0`. -/
def cell_977 : FoldWitness :=
  { n := 16, p := 977, W0 := 0, R0 := 6480, SW := 256, SR := 7949760,
    fold := 2074416, B := -8434128 }

/-- `(16, 1153)`, `r = 5`: `B = +1 133 232 > 0`. -/
def cell_1153 : FoldWitness :=
  { n := 16, p := 1153, W0 := 0, R0 := 6464, SW := 256, SR := 7949760,
    fold := 1766064, B := 1133232 }

/-- The folded-pairing identity holds exactly at `(16, 97)`. -/
theorem fold_97 : FoldHolds cell_97 := by decide

/-- The folded-pairing identity holds exactly at `(16, 433)`. -/
theorem fold_433 : FoldHolds cell_433 := by decide

/-- The folded-pairing identity holds exactly at `(16, 977)`. -/
theorem fold_977 : FoldHolds cell_977 := by decide

/-- The folded-pairing identity holds exactly at `(16, 1153)`. -/
theorem fold_1153 : FoldHolds cell_1153 := by decide

/-- The covariance is strictly negative at `(16, 97)`. -/
theorem B_97_neg : BNeg cell_97 := by decide

/-- The covariance is strictly positive at `(16, 433)`. -/
theorem B_433_pos : BPos cell_433 := by decide

/-- The covariance is strictly negative at `(16, 977)`. -/
theorem B_977_neg : BNeg cell_977 := by decide

/-- The covariance is strictly positive at `(16, 1153)`. -/
theorem B_1153_pos : BPos cell_1153 := by decide

/-- **Both signs are realised by the real folded pairing.**  The same folded real inner product
`B = p·fold − SW·SR` is negative at `(16,97)`/`(16,977)` and positive at `(16,433)`/`(16,1153)`.  A
real signed inner product with no magnitude positivity is exactly what admits both signs; combined
with the abstract odd law `covOdd_neg_right`, this pins that no even/PSD certificate can carry the
sign, while leaving the sponsor-specific *odd* certificate on the antipode-free cone as the sole
survivor. -/
theorem fold_pairing_both_signs :
    BNeg cell_97 ∧ BPos cell_433 ∧ BNeg cell_977 ∧ BPos cell_1153 := by
  exact ⟨by decide, by decide, by decide, by decide⟩

end ArkLib.ProximityGap.Frontier.G280
