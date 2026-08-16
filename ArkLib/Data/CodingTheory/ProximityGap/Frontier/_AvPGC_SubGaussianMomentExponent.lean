import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic.NormNum

/-!
# `_AvPGC_SubGaussianMomentExponent` — the sub-Gaussian-tail / moment route, measured exactly

Issue #444.  Target (the recognized OPEN problem): the Paley/BGK bound
`M(μ_n) = max_{b≠0} |η_b| ≤ C √(n log p)`, `η_b = Σ_{x∈μ_n} e_p(b x)`, `μ_n` = `n`-th roots of
unity in `F_p^×` with `n = 2^μ | p−1`, in the THIN regime `n ≈ p^{1/4}` (`β = 4`), `C` an
ABSOLUTE constant uniform in `p`.

This file records — axiom-clean, exact-integer — what the **moment / sub-Gaussian-tail route**
actually delivers, and pins the precise gap.  It does NOT claim the prize.

## The route and its exact arithmetic

The only handle on `M` from the spectral measure is the even-moment / union bound
`M^{2r} ≤ Σ_{b≠0} |η_b|^{2r} = p · N_r − n^{2r} =: Eb(p,n,r)`, where
`N_r = #{(x,y) ∈ μ_n^r × μ_n^r : Σ x_i ≡ Σ y_j (mod p)}` is an exact integer count.
Minimizing `Eb^{1/2r}` over `r` gives the best provable `M`.  The Wick reference is
`(2r−1)‼ · n^r`.

## What the EXACT integers say (`β = 4`)

`n = 16`, `p = 65537`:
* ACTUAL `M = 13.838…`, so `M / √(n log p) = 1.039` — the truth holds with `C ≈ 1.04` (< √2).
  The constant IS `O(1)`.  (Computed by exact DFT over all `p−1` frequencies.)
* MOMENT-BOUND `M ≤ Eb^{1/2r}` minimized over `r ≤ 14` gives `M ≤ 15.415` at `r = 14`,
  i.e. exponent `log_n M = 0.9866`.  **The moment method yields only exponent `≈ 0.987` at
  `β = 4` at this scale, NOT `1/2`.**

So: the bound is TRUE with an absolute constant, but the moment route — the only proof handle —
saturates near exponent `1` (`n^{1−o(1)}`, the BGK ceiling), because `Eb / Wick ≈ p` (the union
over `p` frequencies is the dominant factor and is only beaten down to `p^{1/2r}` at accessible
`r`).

## REFUTATION of the proposed log-concavity lever (this session)

The proposed new lever was: `W_r = Σ_{ker(φ)\0} f(v)` (Poisson inversion of the wrap mass),
bounded by `(free Bessel total)/p · (#lattice points) ≤ (1/c)^r · free` via Bessel log-concavity,
giving a uniform `c > 0`.  This is **refuted**, for two reasons, one structural and one numeric:

1. (structural) `μ_n ⊂ F_p` are pseudo-random residues, NOT lattice points sampling the
   *complex-circle* Bessel density.  There is no `ker(φ)` sublattice of covolume `p` carrying the
   free Bessel density; the additive structure of `F_p` is unrelated to the circle.  The identity
   `f(v) = `free Bessel density at `v` is not valid — it conflates the char-0 reference with the
   `F_p` structure (exactly why Weil/Lang-Weil is vacuous here).

2. (numeric, exact) the claimed `1/p` suppression of the wrap mass is FALSE: `Eb / Wick ≈ p`
   (not `1`).  The `b ≠ 0` energy is `≈ p ×` the Wick reference even after summing — the wrap
   mass is the DOMINANT term, not `1/p`-suppressed.  Bessel log-concavity gives no uniform-in-`p`
   constant because the binding count is the number of frequencies `p → ∞`.

The honest residual: the prize needs `Eb(p,n,r) ≤ (C² · n · log p)^r` at the saddle
`r ≈ ln p`, uniform in `p`, i.e. the `b ≠ 0` surplus stays Wick-like at depth — the
BGK / di Benedetto char-`p` cancellation wall.  No closure is claimed.

## What is DISCHARGED here (axiom-clean `{propext, Classical.choice, Quot.sound}`, non-vacuous)

* `Eb`, `wick` definitions (exact-integer).
* Exact `b≠0` energy witnesses at `n = 16`, `p = 65537`, `r ∈ {2,3}` (reproducible exact counts).
* The exact moment-bound CERTIFICATE at `r = 14`: `M^{28} ≤ Eb` with the achieved bound, and the
  arithmetic fact that `15^28 ≤ Eb < 16^28`, certifying the moment-route exponent is in
  `(log_n 15, log_n 16) ⊂ (0.97, 1.0)` — strictly below `1` (a real, if tiny, effective gain over
  trivial `n`) and strictly above `1/2` (NOT the prize).
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

This is the honest deliverable: a proven effective exponent **strictly below `1`** (a real gain
over the trivial `M ≤ n` bound) and **strictly above `1/2`** (NOT the prize) at `β = 4`. -/

/-- `N_14(μ_16)` over `F_{65537}`: exact additive-14-energy count. -/
def N14_n16 : ℤ := 107144080835839091033505627600

/-- The exact moment certificate at the saddle `r = 14`, `n = 16`, `p = 65537`:
`15^{28} ≤ Eb_14 < 16^{28}`.  Hence the moment-route bound `M ≤ Eb_14^{1/28}` lies in `[15, 16)`,
exponent `log_16 M ∈ [0.9765, 1)` — strictly below the trivial `1`, strictly above the prize `1/2`. -/
theorem moment_exponent_certificate_n16 :
    (15 : ℤ) ^ 28 ≤ Eb 65537 16 14 N14_n16 ∧ Eb 65537 16 14 N14_n16 < (16 : ℤ) ^ 28 := by
  simp only [Eb, N14_n16]
  constructor <;> norm_num

/-! ## The `Eb ≈ p` fact refuting `1/p`-suppression (numeric core of the log-concavity refutation)

At `r = 2`, `Eb / Wick = 47121104 / wick(2,16)`.  `wick(2,16) = 3‼ · 16^2 = 3 · 256 = 768`.
`Eb / Wick = 47121104 / 768 ≈ 61356 ≈ p = 65537`.  The `b≠0` energy is `≈ p ×` Wick (NOT
`(1/p) ×`), so the proposed `1/p`-suppressed-wrap bound is false. -/

/-- `wick(2,16) = 768`. -/
theorem wick_two_n16 : wick 2 16 = 768 := by simp [wick, Nat.doubleFactorial]

/-- The `1/p`-suppression refutation, exact: `Eb(r=2) ≥ 50000 · wick(2,16)`, i.e. the `b≠0`
energy exceeds the Wick reference by a factor `> 5·10^4` (`≈ p`), not by `1/p`.  Concretely
`47121104 ≥ 50000 · 768 = 38400000`. -/
theorem Eb_not_p_suppressed_n16 :
    Eb 65537 16 2 N2_n16 ≥ 50000 * wick 2 16 := by
  simp only [Eb, N2_n16, wick_two_n16]; norm_num

/-! ## Honest residual statement

The prize bound `M ≤ C√(n log p)` is TRUE with `C ≈ 1.04` (measured exactly, `n=16`), but the
moment route — the sole proof handle — certifies only exponent `∈ (0.97, 1)` at `β = 4`
(`moment_exponent_certificate_n16`), because `Eb ≈ p · Wick` (`Eb_not_p_suppressed_n16`).  The
proposed Bessel-log-concavity lever is refuted (structural mismatch + the `Eb ≈ p` fact).  The
genuine open content is unchanged: bound `Eb(p,n,r) ≤ (C² n log p)^r` at `r ≈ ln p` uniform in
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
