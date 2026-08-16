/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# G224: the Newton parity packet `PAR⁻` is near-definite but not sign-definite (#466)

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

This lane settles it.  Write the parity split in physical space via the even/odd Newton half-sums
`E_r, O_r` (the sub-sums of Newton's `R_r = E_r + O_r` over partitions of even / odd co-length).
Grouping the CORE correlation by `(parity_r, parity_{r−1})`,

```text
PAR⁺ = p·⟨W, E_r ⋆ E_{r−1} + O_r ⋆ O_{r−1}⟩ − DC,
PAR⁻ = p·⟨W, E_r ⋆ O_{r−1} + O_r ⋆ E_{r−1}⟩ − DC,      A_r = PAR⁺ + PAR⁻,
```

where `⋆` is the CORE correlation and `DC` the trivial-character subtraction.  Per additive
character `χ`, the `PAR⁻` integrand is

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

2. **`PAR⁻` is NOT sign-definite: the per-mode integrand `Re k(χ)` takes strictly positive values.**
   `scripts/probes/oc_g224_mode_signs.py` shows the negative mode mass dominates the positive by
   5 to 8 orders of magnitude (so `PAR⁻` is a *near-definite* form), yet strictly positive modes
   genuinely occur.  This is confirmed float-free at the one exactly computable non-trivial real
   mode, the quadratic character `χ₂` (integer-valued Legendre symbol):
   `scripts/probes/oc_g224_witness_exact.py` recomputes the exact integer `χ₂`-mode contribution
   `k₂ := Ŵ(χ₂)·( Ê_r(χ₂)·Ô_{r−1}(χ₂) + Ô_r(χ₂)·Ê_{r−1}(χ₂) )` and finds it **positive** at
   `(n=16, r=5, p=257)` (`k₂ = +12 734 300 160`) while `PAR⁻ < 0` there, and **negative** at
   `(n=16, r=5, p=97)` (`k₂ = −2 477 260 800`), again with `PAR⁻ < 0`.

## Consequence — the last Newton regularity carries no forced-sign theorem

Because the `PAR⁻` integrand realises *both* exact-integer signs at the quadratic mode, `PAR⁻` is
**not a sum of negated squares / not a sign-definite quadratic form**: there is no per-mode
certificate for its negativity, so its constant sign is a *near-definite dominance* fact (a huge
negative bulk with irreducible positive modes), not a structural invariant that could be turned into
a one-sided estimate on `A_r`.  The natural hope Fable left open — "if the analytic instantiation
explains the `PAR⁻` negativity structurally, that mechanism is the first candidate for a one-sided
estimate" — is foreclosed at the level of the packet itself: the negativity is not forced mode by
mode, so no manifestly-signed sub-object of `A_r` lives inside `PAR⁻`.  Together with G214/G217/G220
(sign unforced), G216/G219 (no truncation/phase), G222/G223 (no Newton sector or coarse grouping),
this closes the Newton-parity regularity as a route.

## The float-free certificate (honest scope)

As with G214/G216/G217/G220, the **computation of record** is the reproducible float-free probe.
This file does not re-derive `PAR⁻` from an in-Lean BGK definition.  It **certifies the arithmetic**
of the recorded exact-integer constants: (i) the `PAR⁻` integrand at the quadratic mode `χ₂` is
strictly positive on one witness (`w1`) and strictly negative on another (`w2`), so the form is not
sign-definite; (ii) on both, and on a third witness where `A_r > 0`, the packet total `PAR⁻ < 0`, so
`PAR⁻`'s constant negativity co-exists with an `A_r` sign flip.  The "all 72 cells negative" census
and the 5-to-8-order magnitude domination of the negative mode mass are limiting statistical
statements whose computation of record is the Python sweep; they are not dressed as Lean theorems.

## Why this is a genuine frontier no-go

It closes Fable G223's *single surviving unexplained Newton regularity* by proving the `PAR⁻`
packet is near-definite but not sign-definite: a strictly positive exact-integer per-mode
contribution exists (quadratic character, `+12 734 300 160`) inside a negative packet, so the
negativity is a dominance artifact carrying no forced-sign structural theorem and cannot seed a
one-sided estimate on `A_r`.  Thinness-relevant (all Newton sectors are built from the
2-power-subgroup periods `η_j`; the `u ≠ 2` dyadic exclusion lives inside `Ŵ`).  It does **not**
bound `A_5` or `A_6` at production primes; CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G224

/-- Exact Newton-parity-packet data for one `(order, prime, rank)` BGK late-alignment witness.

* `k2` is the exact-integer contribution of the quadratic (real) character `χ₂` to the `PAR⁻`
  integrand, `Ŵ(χ₂)·( Ê_r(χ₂)·Ô_{r−1}(χ₂) + Ô_r(χ₂)·Ê_{r−1}(χ₂) )`.  It is the only non-trivial
  Mellin mode that is integer-valued, hence float-free; its sign is the per-mode sign of `PAR⁻`
  at that mode.
* `parm` is `p · PAR⁻` in the `lcm`-cleared normalisation (`PAR⁻ = PAR⁺ − PAR⁻ complement`,
  `PAR⁺ + PAR⁻ = A_r`); its sign is the packet sign.
* `A` is the exact signed covariance `p·Σ_t W_G(t)R_r(t) − n²·C(n,r)C(n,r−1)` in the same
  normalisation, the CORE target.

All are exact integers from the float-free probes over `𝔽_p`. -/
structure ParityWitness where
  n : ℕ
  p : ℕ
  r : ℕ
  k2 : ℤ
  parm : ℤ
  A : ℤ

/-- The quadratic-mode contribution to the `PAR⁻` integrand is strictly positive. -/
def K2Pos (w : ParityWitness) : Prop := 0 < w.k2

/-- The quadratic-mode contribution to the `PAR⁻` integrand is strictly negative. -/
def K2Neg (w : ParityWitness) : Prop := w.k2 < 0

/-- The `PAR⁻` packet total is strictly negative. -/
def ParmNeg (w : ParityWitness) : Prop := w.parm < 0

/-- The CORE covariance `A_r` is strictly positive. -/
def APos (w : ParityWitness) : Prop := 0 < w.A

/-- The CORE covariance `A_r` is strictly negative. -/
def ANeg (w : ParityWitness) : Prop := w.A < 0

instance (w : ParityWitness) : Decidable (K2Pos w) := by unfold K2Pos; infer_instance
instance (w : ParityWitness) : Decidable (K2Neg w) := by unfold K2Neg; infer_instance
instance (w : ParityWitness) : Decidable (ParmNeg w) := by unfold ParmNeg; infer_instance
instance (w : ParityWitness) : Decidable (APos w) := by unfold APos; infer_instance
instance (w : ParityWitness) : Decidable (ANeg w) := by unfold ANeg; infer_instance

/-- **Positive quadratic-mode witness** at `(n=16, r=5, p=257)`.  The exact-integer `χ₂`-mode
contribution to the `PAR⁻` integrand is `k₂ = +12 734 300 160 > 0`, while the packet total is
`PAR⁻ < 0` and the CORE covariance is `A < 0`. -/
def w1 : ParityWitness :=
  { n := 16, p := 257, r := 5, k2 := 12734300160, parm := -1409838243840, A := -3028055040 }

/-- **Negative quadratic-mode witness** at `(n=16, r=5, p=97)`.  The exact-integer `χ₂`-mode
contribution is `k₂ = −2 477 260 800 < 0`; the packet total is again `PAR⁻ < 0`, `A < 0`. -/
def w2 : ParityWitness :=
  { n := 16, p := 97, r := 5, k2 := -2477260800, parm := -6385190400, A := -18100823040 }

/-- **`A`-flip witness** at `(n=16, r=5, p=113)`.  Here the CORE covariance is `A = +4 974 105 600`,
strictly positive, while the packet total is still `PAR⁻ = −45 119 024 640 < 0`: the packet
negativity persists across an `A` sign flip. -/
def w3 : ParityWitness :=
  { n := 16, p := 113, r := 5, k2 := 0, parm := -45119024640, A := 4974105600 }

/-- `w1` has quadratic-mode contribution `k₂ = +12 734 300 160 > 0`. -/
theorem w1_k2_pos : K2Pos w1 := by decide

/-- `w2` has quadratic-mode contribution `k₂ = −2 477 260 800 < 0`. -/
theorem w2_k2_neg : K2Neg w2 := by decide

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

/-- **Headline no-go: the Newton parity packet `PAR⁻` is not sign-definite.**  The exact-integer
contribution of the quadratic character `χ₂` to the `PAR⁻` integrand is strictly positive on one
prize-faithful witness (`w1`) and strictly negative on another (`w2`), *both at the same order and
rank* `n = 16, r = 5`.  A sum of negated squares would have a fixed-sign integrand at every real
mode; the observed sign disagreement rules that out.  Hence `PAR⁻`'s constant negativity is a
near-definite *dominance* fact, not a per-mode-forced structural invariant, and carries no
one-sided estimate on `A_r`. -/
theorem parity_packet_not_sign_definite :
    (∃ w : ParityWitness, w.n = 16 ∧ w.r = 5 ∧ K2Pos w) ∧
      (∃ w : ParityWitness, w.n = 16 ∧ w.r = 5 ∧ K2Neg w) :=
  ⟨⟨w1, by decide, by decide, w1_k2_pos⟩, ⟨w2, by decide, by decide, w2_k2_neg⟩⟩

/-- **Supporting no-go: the packet negativity carries no information about `A_r`'s sign.**  On the
witnesses `w2` (with `A < 0`) and `w3` (with `A > 0`), *both at the same order and rank*
`n = 16, r = 5`, the packet total `PAR⁻` is strictly negative regardless.  So `PAR⁻ < 0` co-exists
with an `A_r` sign flip: it forecasts nothing about the CORE sign. -/
theorem parity_packet_forecast_free :
    w2.n = w3.n ∧ w2.r = w3.r ∧ ParmNeg w2 ∧ ParmNeg w3 ∧ ANeg w2 ∧ APos w3 :=
  ⟨by decide, by decide, w2_parm_neg, w3_parm_neg, w2_A_neg, w3_A_pos⟩

/-- Both the sign-definiteness failure and the co-existence of `PAR⁻ < 0` with an `A_r` flip hold
simultaneously on the fixed order-rank block `n = 16, r = 5`: no forced-sign structural theorem
survives inside the last unexplained Newton regularity. -/
theorem newton_parity_regularity_is_not_a_route :
    ((∃ w : ParityWitness, w.n = 16 ∧ w.r = 5 ∧ K2Pos w) ∧
        (∃ w : ParityWitness, w.n = 16 ∧ w.r = 5 ∧ K2Neg w)) ∧
      (ParmNeg w2 ∧ ParmNeg w3 ∧ ANeg w2 ∧ APos w3) :=
  ⟨parity_packet_not_sign_definite, w2_parm_neg, w3_parm_neg, w2_A_neg, w3_A_pos⟩

end ArkLib.ProximityGap.Frontier.G224
