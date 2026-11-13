/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G224: exact witnesses for the Newton parity packet `PAR⁻` (#466)

The referee lane (Fable, G223) closed every coarse regrouping of the Newton cycle-index
decomposition of the CORE covariance

```text
A_r := p · Σ_t W_G(t) · R_r(t)  −  n² · C(n,r) · C(n,r−1),          r ∈ {5, 6}
```

as a sign-forecasting route, but flagged **one surviving unexplained regularity**: the
negative-coefficient parity packet

```text
PAR⁻ := Σ_{(λ,μ) : (−1)^{(r−ℓ(λ)) + (r−1−ℓ(μ))} = −1}  coeff(λ)·coeff(μ)·S_{λ,μ}
```

(the sum of Newton sectors of *odd* total co-length) is **negative in every observed cell**, while
`A_r` itself flips sign prime-to-prime.  Fable called this "the single surviving unexplained
regularity in the Newton coordinates" and left open whether it is a genuine sign-forced structural
invariant (a candidate seed for a one-sided estimate on `A_r`) or a finite-size coincidence.

This lane records exact witnesses bearing on that question (scope corrected below).  Write the parity split in physical space via the even/odd Newton half-sums
`E_r, O_r` (the sub-sums of Newton's `R_r = E_r + O_r` over partitions of even / odd co-length).
Grouping the CORE correlation by `(parity_r, parity_{r−1})`,

```text
PAR⁺ = p·⟨W, E_r ⋆ E_{r−1} + O_r ⋆ O_{r−1}⟩ − DC,
PAR⁻ = p·⟨W, E_r ⋆ O_{r−1} + O_r ⋆ E_{r−1}⟩ − DC,      A_r = PAR⁺ + PAR⁻,
```

where `⋆` is the CORE correlation and `DC` the trivial-character subtraction.  Per additive
character `χ` (additive Fourier transform `^`), the `PAR⁻` integrand is

```text
k(χ) := conj(Ŵ(χ)) · ( Ê_r(χ)·conj(Ô_{r−1}(χ)) + Ô_r(χ)·conj(Ê_{r−1}(χ)) ),
        PAR⁻ = Σ_{χ ≠ 1} Re k(χ).
```

## Two exact facts (probes of record)

1. **`PAR⁻ < 0` is robust and structural, not a coincidence.**
   `scripts/probes/oc_g224_parity_packet_exact.py` recomputes `PAR⁻` as an *exact integer*
   (all Newton coefficients cleared by the global `lcm` of the `z_λ`) over
   `n ∈ {8, 16, 32, 64}`, `r ∈ {5, 6}`, and a prime family up to `3617`.  `PAR⁻ < 0` in **all 72
   cells**, far beyond the 20 float cells that first flagged it, while `A_r` realises both signs.
   The cross-check `PAR⁺ + PAR⁻ = A_r` holds exactly on every cell.

2. **`PAR⁻` is not termwise sign-definite (corrected scope, audit finding L106).**
   `scripts/probes/oc_g224_mode_signs.py` (a *floating-point* FFT census, not a certificate) reports
   additive-character modes `Re k(χ)` of both signs, with the negative mode mass dominating the
   positive by 5 to 8 orders of magnitude.  The only float-free per-mode statement recorded here is
   for the quadratic character `χ₂` (Legendre symbol), which is a **multiplicative** character.
   Writing `X := E_r ⋆ O_{r−1} + O_r ⋆ E_{r−1}` for the actual additive cross-correlation packet (so
   `PAR⁻ = p·⟨W, X⟩ − DC`; at a multiplicative character `ψ`, `F̂(ψ) := Σ_{t≠0} ψ(t)·F(t)`),
   multiplicative Parseval on `𝔽_p^×` gives
   `Σ_{t≠0} W(t)X(t) = (p−1)⁻¹ Σ_ψ conj(Ŵ(ψ))·X̂(ψ)`, so the `χ₂`-mode of `p·⟨W,X⟩` is
   `p/(p−1) · Ŵ(χ₂)·X̂(χ₂)`, with the sign of `chi2Pair := Ŵ(χ₂)·X̂(χ₂)`.
   `scripts/probes/oc_g224_witness_exact.py` computes `chi2Pair` exactly from the actual correlation
   `X` and finds it **positive** at both `(n=16, r=5, p=257)` (`+15 408 783 360`) and
   `(n=16, r=5, p=97)` (`+1 278 443 520`), while `PAR⁻ < 0` at both.  So the multiplicative-character
   decomposition of `PAR⁻` has a strictly positive mode inside a strictly negative packet.

   *Correction.*  An earlier revision used instead the product of **separate** Legendre transforms
   `sepProd := Ŵ(χ₂)·( Ê_r(χ₂)·Ô_{r−1}(χ₂) + Ô_r(χ₂)·Ê_{r−1}(χ₂) )` (`+12 734 300 160` at `p = 257`,
   `−2 477 260 800` at `p = 97`) and called it the `χ₂`-mode of `PAR⁻`.  That is wrong: multiplicative
   transforms do not diagonalise additive correlation, so `sepProd` is not a mode of `PAR⁻`, and its
   sign disagreement between the two witnesses carries no packet meaning (under the genuine pairing
   both witnesses are positive).  `sepProd` is retained below only as recorded provenance.

## Consequence (honest scope)

The exact `χ₂` witnesses show that `PAR⁻`'s constant negativity is not forced termwise in the
multiplicative-character decomposition: there is a strictly positive exact mode inside each negative
packet, so no per-`ψ`-mode certificate in that decomposition explains it.  Positivity of some
*additive*-character mode is supported only by the float census.  Neither statement proves that no
other decomposition or structural argument forces `PAR⁻ < 0`; this file does not establish or refute
any packet-sign theorem.  Separately, `PAR⁻ < 0` co-exists with an `A_r` sign flip (witness `w3`), so
the packet sign by itself forecasts nothing about the CORE sign.

## The float-free certificate (honest scope)

As with G214/G216/G217/G220, the **computation of record** is the reproducible float-free probe.
This file does not re-derive `PAR⁻` from an in-Lean BGK definition.  It **certifies the arithmetic**
of the recorded exact-integer constants of the three witnesses `w1, w2, w3`.  The "all 72 cells
negative" census and the additive-mode sign census are statistical statements whose computation of
record is the Python sweep; they are not dressed as Lean theorems.  It does **not** bound `A_5` or
`A_6` at production primes; CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G224

/-- Exact Newton-parity-packet data for one `(order, prime, rank)` BGK late-alignment witness.

* `sepProd` is the product of *separate* Legendre (multiplicative quadratic-character) transforms
  `Ŵ(χ₂)·( Ê_r(χ₂)·Ô_{r−1}(χ₂) + Ô_r(χ₂)·Ê_{r−1}(χ₂) )`.  It is **not** a mode of `PAR⁻`
  (audit finding L106); it is kept only as recorded provenance of the earlier revision.
* `chi2Pair` is `Ŵ(χ₂)·X̂(χ₂)` for the actual additive cross-correlation packet
  `X = E_r ⋆ O_{r−1} + O_r ⋆ E_{r−1}`; its sign is the sign of the quadratic-character mode of
  `p·⟨W, X⟩` in the multiplicative Parseval decomposition over `𝔽_p^×`.
* `parm` is `PAR⁻` in the `lcm`-cleared normalisation (`PAR⁺ + PAR⁻ = A_r`); its sign is the packet
  sign.
* `A` is the exact signed covariance `p·Σ_t W_G(t)R_r(t) − n²·C(n,r)C(n,r−1)` in the same
  normalisation, the CORE target.

All are exact integers from the float-free probe `scripts/probes/oc_g224_witness_exact.py`; this
structure is plain data and carries no in-Lean link to their definitions. -/
structure ParityWitness where
  n : ℕ
  p : ℕ
  r : ℕ
  sepProd : ℤ
  chi2Pair : ℤ
  parm : ℤ
  A : ℤ

/-- The genuine quadratic-character pairing is strictly positive. -/
def Chi2Pos (w : ParityWitness) : Prop := 0 < w.chi2Pair

/-- The `PAR⁻` packet total is strictly negative. -/
def ParmNeg (w : ParityWitness) : Prop := w.parm < 0

/-- The CORE covariance `A_r` is strictly positive. -/
def APos (w : ParityWitness) : Prop := 0 < w.A

/-- The CORE covariance `A_r` is strictly negative. -/
def ANeg (w : ParityWitness) : Prop := w.A < 0

instance (w : ParityWitness) : Decidable (Chi2Pos w) := by unfold Chi2Pos; infer_instance
instance (w : ParityWitness) : Decidable (ParmNeg w) := by unfold ParmNeg; infer_instance
instance (w : ParityWitness) : Decidable (APos w) := by unfold APos; infer_instance
instance (w : ParityWitness) : Decidable (ANeg w) := by unfold ANeg; infer_instance

/-- Witness at `(n=16, r=5, p=257)`: genuine `χ₂` pairing `+15 408 783 360 > 0` inside a packet with
`PAR⁻ < 0`, and `A < 0`.  (Provenance: `sepProd = +12 734 300 160`, not a packet mode.) -/
def w1 : ParityWitness :=
  { n := 16, p := 257, r := 5, sepProd := 12734300160, chi2Pair := 15408783360,
    parm := -1409838243840, A := -3028055040 }

/-- Witness at `(n=16, r=5, p=97)`: genuine `χ₂` pairing `+1 278 443 520 > 0` inside a packet with
`PAR⁻ < 0`, and `A < 0`.  (Provenance: `sepProd = −2 477 260 800`, not a packet mode.) -/
def w2 : ParityWitness :=
  { n := 16, p := 97, r := 5, sepProd := -2477260800, chi2Pair := 1278443520,
    parm := -6385190400, A := -18100823040 }

/-- **`A`-flip witness** at `(n=16, r=5, p=113)`.  Here the CORE covariance is `A = +4 974 105 600`,
strictly positive, while the packet total is still `PAR⁻ = −45 119 024 640 < 0` (here `Ŵ(χ₂) = 0`). -/
def w3 : ParityWitness :=
  { n := 16, p := 113, r := 5, sepProd := 0, chi2Pair := 0, parm := -45119024640,
    A := 4974105600 }

/-- `w1` has strictly positive genuine `χ₂` pairing. -/
theorem w1_chi2_pos : Chi2Pos w1 := by decide

/-- `w2` has strictly positive genuine `χ₂` pairing. -/
theorem w2_chi2_pos : Chi2Pos w2 := by decide

/-- `w1`'s packet total is `PAR⁻ < 0`. -/
theorem w1_parm_neg : ParmNeg w1 := by decide

/-- `w2`'s packet total is `PAR⁻ < 0`. -/
theorem w2_parm_neg : ParmNeg w2 := by decide

/-- `w3`'s packet total is `PAR⁻ < 0`. -/
theorem w3_parm_neg : ParmNeg w3 := by decide

/-- `w2` has `A < 0`. -/
theorem w2_A_neg : ANeg w2 := by decide

/-- `w3` has `A > 0`. -/
theorem w3_A_pos : APos w3 := by decide

/-- **Positive exact `χ₂` mode inside a negative packet** (arithmetic certificate of the recorded
constants).  On both recorded witnesses `w1, w2` (same order and rank `n = 16, r = 5`) the genuine
quadratic-character pairing is strictly positive while `PAR⁻ < 0`.  Read through the probe's
multiplicative Parseval identity, the multiplicative-character decomposition of `PAR⁻` is therefore
not termwise of the packet's sign.  This replaces an earlier statement built on `sepProd`, which is
not a packet mode (audit finding L106). -/
theorem chi2_mode_positive_in_negative_packet :
    (w1.n = 16 ∧ w1.r = 5 ∧ Chi2Pos w1 ∧ ParmNeg w1) ∧
      (w2.n = 16 ∧ w2.r = 5 ∧ Chi2Pos w2 ∧ ParmNeg w2) :=
  ⟨⟨rfl, rfl, w1_chi2_pos, w1_parm_neg⟩, ⟨rfl, rfl, w2_chi2_pos, w2_parm_neg⟩⟩

/-- **Supporting no-go: the packet negativity carries no information about `A_r`'s sign.**  On the
witnesses `w2` (with `A < 0`) and `w3` (with `A > 0`), *both at the same order and rank*
`n = 16, r = 5`, the packet total `PAR⁻` is strictly negative regardless.  So `PAR⁻ < 0` co-exists
with an `A_r` sign flip: it forecasts nothing about the CORE sign. -/
theorem parity_packet_forecast_free :
    w2.n = w3.n ∧ w2.r = w3.r ∧ ParmNeg w2 ∧ ParmNeg w3 ∧ ANeg w2 ∧ APos w3 :=
  ⟨by decide, by decide, w2_parm_neg, w3_parm_neg, w2_A_neg, w3_A_pos⟩

/-- Combined certificate of the recorded G224 witness arithmetic: positive exact `χ₂` pairing inside
negative packets (`w1`, `w2`), and `PAR⁻ < 0` across an `A_r` sign flip (`w2`, `w3`).  This does not
prove or refute any packet-sign theorem. -/
theorem newton_parity_witness_certificate :
    ((w1.n = 16 ∧ w1.r = 5 ∧ Chi2Pos w1 ∧ ParmNeg w1) ∧
        (w2.n = 16 ∧ w2.r = 5 ∧ Chi2Pos w2 ∧ ParmNeg w2)) ∧
      (ParmNeg w2 ∧ ParmNeg w3 ∧ ANeg w2 ∧ APos w3) :=
  ⟨chi2_mode_positive_in_negative_packet, w2_parm_neg, w3_parm_neg, w2_A_neg, w3_A_pos⟩

end ArkLib.ProximityGap.Frontier.G224
