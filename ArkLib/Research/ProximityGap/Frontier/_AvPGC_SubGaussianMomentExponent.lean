/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-!
# `_AvPGC_SubGaussianMomentExponent` — the sub-Gaussian-tail / moment route, measured exactly

Issue #444.  Target (the recognized OPEN problem): the Paley/BGK bound
`M(μ_n) = max_{b≠0} |η_b| ≤ C √(n log p)`, `η_b = Σ_{x∈μ_n} e_p(b x)`, `μ_n` = `n`-th roots of
unity in `F_p^×` with `n = 2^μ | p−1`, in the THIN regime `n ≈ p^{1/4}` (`β = 4`), `C` an
ABSOLUTE constant uniform in `p`.

This file records — axiom-clean, exact-integer — what the **moment / sub-Gaussian-tail route**
actually delivers, and pins the precise gap.  It does NOT claim the prize.

## The route and its exact arithmetic

The even-moment / union bound gives a handle on `M` from the spectral measure:
`M^{2r} ≤ Σ_{b≠0} |η_b|^{2r} = p · N_r − n^{2r} =: Eb(p,n,r)`, where
`N_r = #{(x,y) ∈ μ_n^r × μ_n^r : Σ x_i ≡ Σ y_j (mod p)}` is an exact integer count.
Minimizing `Eb^{1/2r}` over `r` gives the best `M` bound this particular method provides.  The Wick
reference is `(2r−1)‼ · n^r`.

## What the EXACT integers say (`β = 4`, one cell)

`n = 16`, `p = 65537` (`N_2 = 720`, `N_3 = 50560`, `N_14` below were independently reproduced by
exact sparse cyclic convolution on `μ_16 ⊂ F_65537`, generator `64`, in the 2026-10-28 audit):
* ACTUAL `M = 13.838…`, so `M / √(n log p) = 1.039` in this one cell.  (Computed by exact DFT over
  all `p−1` frequencies.)  A single cell does not establish a uniform absolute constant.
* MOMENT ENVELOPE `Eb^{1/2r}` minimized over `r ≤ 14` gives `15.415` at `r = 14`, i.e.
  `log_n (envelope) = 0.9866`.  This is an UPPER envelope for `M`; a lower bound on the envelope is
  not a lower bound on `M` (the actual `M ≈ 13.838 < 15`).

So in this cell the moment envelope at accessible `r ≤ 14` sits near exponent `1`, because the
union over `p` frequencies is only beaten down to `p^{1/2r}`.  A finite effective exponent above
`1/2` at one cell does not rule out a `√(n log p)` estimate with a finite constant, and does not
prove an asymptotic optimality/no-go for all moments or for other methods.

## The proposed log-concavity lever (status corrected per audit R-309)

The proposed new lever was: `W_r = Σ_{ker(φ)\0} f(v)` (Poisson inversion of the wrap mass),
bounded by `(free Bessel total)/p · (#lattice points) ≤ (1/c)^r · free` via Bessel log-concavity,
giving a uniform `c > 0`.  An earlier version of this header claimed to **refute** it on two
grounds. Both arguments are invalid as stated:

1. (lattice existence) The earlier claim "there is no `ker(φ)` sublattice of covolume `p`" is
   FALSE. The coefficient evaluation homomorphism `ℤ^d → F_p`, `v ↦ Σ_j v_j g^j`, is surjective
   (the constant coefficient maps to `1`), so its kernel is an index-`p` lattice. What is genuinely
   unjustified is identifying the multiplicities `f(v)` with a continuous Bessel density on that
   lattice; that weighted-count identification would need its own hypotheses, and its difficulty
   is distinct from lattice existence.

2. (wrong quantity) The earlier numeric "refutation" compared `Eb / Wick ≈ p`. But
   `Eb = p·N_r − n^{2r}` is the unnormalized NONZERO-FREQUENCY moment, not the wrapping excess
   `W_r = N_r − N_r^{char0}`. In the very cell used, `N_2 = 720 = N_2^{char0}` (`= 3n² − 3n`), so the
   wrapping excess is ZERO, even though `Eb_2 = 47121104` and `Eb_2 / Wick_2 ≈ 61356`. The large
   factor comes from summing `p − 1` frequency samples; it says nothing about suppression of a mass
   that is `0` in the example.

So the lever is **neither refuted nor established** here. A valid test must compare the proposed
bound with the actual `W_r` under a consistent normalization and supply the weight/kernel
hypotheses the proposal needs.

The honest residual: the prize needs `Eb(p,n,r) ≤ (C² · n · log p)^r` at the saddle
`r ≈ ln p`, uniform in `p`, i.e. the `b ≠ 0` surplus stays Wick-like at depth — the
BGK / di Benedetto char-`p` cancellation wall.  No closure is claimed.

## What is DISCHARGED here (axiom-clean `{propext, Classical.choice, Quot.sound}`, non-vacuous)

* `Eb`, `wick` definitions (exact-integer).
* Exact `b≠0` energy witnesses at `n = 16`, `p = 65537`, `r ∈ {2,3}` (reproducible exact counts).
* The exact moment-envelope arithmetic at `r = 14`: `15^28 ≤ Eb < 16^28`, so the envelope
  `Eb^{1/28}` (an upper bound for `M`, via the informal `M^{28} ≤ Eb`, not formalized here) lies in
  `[15, 16)`, exponent `∈ [log_16 15, 1) ⊂ (0.97, 1.0)`. This locates the ENVELOPE, not actual `M`.
* `Eb_not_p_suppressed_n16`: the arithmetic fact `Eb_2 ≥ 50000 · Wick_2` about the nonzero-frequency
  moment. It is NOT a statement about the wrapping excess (which is `0` in this cell).
-/

namespace ProximityGap.Frontier.AvPGC

/-- Wick reference `(2r−1)‼ · n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

/-- Exact `b ≠ 0` energy `Eb = p · N_r − n^{2r}`, `N_r` the additive-`r`-energy count of `μ_n`. -/
def Eb (p n : ℤ) (r : ℕ) (Nr : ℤ) : ℤ := p * Nr - n ^ (2 * r)

/-! ## Exact `N_r` witnesses, `n = 16`, `p = 65537` (`β = 4`), reproducible exact counts. -/

/-- `N_2(μ_16) = 720` over `F_{65537}`. -/
def N2_n16 : ℤ := 720
/-- `N_3(μ_16) = 50560` over `F_{65537}`. -/
def N3_n16 : ℤ := 50560

/-- The exact `b≠0` energy at `r = 2` is `47121104 = 65537·720 − 16^4`. -/
theorem Eb_n16_r2 : Eb 65537 16 2 N2_n16 = 47121104 := by
  simp only [Eb, N2_n16]; norm_num

/-- The exact `b≠0` energy at `r = 3` is `3296773504 = 65537·50560 − 16^6`. -/
theorem Eb_n16_r3 : Eb 65537 16 3 N3_n16 = 3296773504 := by
  simp only [Eb, N3_n16]; norm_num

/-! ## The moment-bound exponent certificate (`β = 4`, the EFFECTIVE-EXPONENT result)

`N_14(μ_16)` over `F_{65537}` (exact additive-14-energy count); the `b≠0` energy
`Eb_14 = 65537 · N14 − 16^{28}`.  The exact-integer moment certificate is the two-sided bound
`15^{28} ≤ Eb_14 < 16^{28}`, i.e. `15 ≤ Eb_14^{1/28} < 16`, so the moment-bound exponent
`log_16 (Eb_14^{1/28}) ∈ (log_16 15, 1) = (0.9765, 1)`.

This locates the moment ENVELOPE at this one cell: its exponent is strictly below `1` and strictly
above `1/2`. It is not a lower bound on actual `M` (≈ `13.838`), and it is not a uniform asymptotic
statement about moment methods at `β = 4`. -/

/-- `N_14(μ_16)` over `F_{65537}`: exact additive-14-energy count. -/
def N14_n16 : ℤ := 107144080835839091033505627600

/-- The exact moment certificate at the saddle `r = 14`, `n = 16`, `p = 65537`:
`15^{28} ≤ Eb_14 < 16^{28}`.  Hence the moment-route envelope `Eb_14^{1/28}` (an upper bound for `M`)
lies in `[15, 16)`, envelope exponent `∈ [0.9765, 1)`. Actual `M ≈ 13.838` is below this envelope. -/
theorem moment_exponent_certificate_n16 :
    (15 : ℤ) ^ 28 ≤ Eb 65537 16 14 N14_n16 ∧ Eb 65537 16 14 N14_n16 < (16 : ℤ) ^ 28 := by
  simp only [Eb, N14_n16]
  constructor <;> norm_num

/-! ## The `Eb ≈ p · Wick` arithmetic (NOT a refutation of wrap-mass suppression)

At `r = 2`, `Eb / Wick = 47121104 / wick(2,16)`.  `wick(2,16) = 3‼ · 16^2 = 3 · 256 = 768`.
`Eb / Wick = 47121104 / 768 ≈ 61356`.  This ratio measures the unnormalized nonzero-frequency
moment, which sums `p − 1` frequency samples. The wrapping excess `W_2 = N_2 − N_2^{char0}` is `0`
in this cell (`N_2 = 720 = 3n² − 3n`), so this arithmetic does not refute a `1/p`-suppressed
wrap-mass bound (audit R-309). -/

/-- `wick(2,16) = 768`. -/
theorem wick_two_n16 : wick 2 16 = 768 := by simp [wick, Nat.doubleFactorial]

/-- Exact arithmetic: `Eb(r=2) ≥ 50000 · wick(2,16)`, i.e. the unnormalized `b≠0` moment exceeds the
Wick reference by a factor `> 5·10^4`.  Concretely `47121104 ≥ 50000 · 768 = 38400000`.  Despite the
name, this is not about the wrapping excess `W_2` (which is `0` here) and refutes no wrap-mass
suppression estimate. -/
theorem Eb_not_p_suppressed_n16 :
    Eb 65537 16 2 N2_n16 ≥ 50000 * wick 2 16 := by
  simp only [Eb, N2_n16, wick_two_n16]; norm_num

/-! ## Honest residual statement

In the single cell `n = 16`, `p = 65537`, actual `M / √(n log p) ≈ 1.04` (measured), while the
moment envelope at `r ≤ 14` has exponent `∈ (0.97, 1)` (`moment_exponent_certificate_n16`).  Neither
fact is uniform in `p`.  The proposed Bessel-log-concavity lever is NOT refuted here (the kernel
lattice exists, and `Eb` is not the wrapping excess; see the module header).  The genuine open
content is unchanged: bound `Eb(p,n,r) ≤ (C² n log p)^r` at `r ≈ ln p` uniform in
`p` (the BGK / di Benedetto char-`p` cancellation wall).  No closure claimed. -/

theorem honest_summary :
    (15 : ℤ) ^ 28 ≤ Eb 65537 16 14 N14_n16 ∧
    Eb 65537 16 14 N14_n16 < (16 : ℤ) ^ 28 ∧
    Eb 65537 16 2 N2_n16 ≥ 50000 * wick 2 16 :=
  ⟨moment_exponent_certificate_n16.1, moment_exponent_certificate_n16.2, Eb_not_p_suppressed_n16⟩

#print axioms Eb_n16_r2
#print axioms Eb_n16_r3
#print axioms moment_exponent_certificate_n16
#print axioms Eb_not_p_suppressed_n16
#print axioms honest_summary

end ProximityGap.Frontier.AvPGC
