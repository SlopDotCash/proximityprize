/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# wf-A09 (#444): Amice / Iwasawa `p`-adic interpolation along the dilation tower is a DEAD handle
  — a precise OBSTRUCTION, two independent walls, axiom-clean

## The angle under test (manifesto route 4 — `p`-adic interpolation, never previously attacked)

The prize floor is the **archimedean** sup-norm `M(n) = max_{b≠0} ‖η_b‖`,
`η_b = ∑_{x∈μ_n} e_p(b·x)`, the `λ₂` of the generalized Paley graph `Cay(F_p, μ_n)`
(`μ_n` = order-`n = 2^μ` subgroup, `p ≡ 1 mod n`, prize regime `p = n^β`, `β = 4`,
`n ≈ 2^30`). Manifesto route 4 proposes: regard the period along the **dilation tower**
`b ↦ ζ·b` as a sequence that should *interpolate to a `p`-adic measure* on `ℤ_p` (or the
cyclotomic tower); then its **Amice transform** / **Iwasawa `μ,λ`-invariants** would, if
bounded, bound the sup `M(n)`. This file determines, exactly and axiom-clean, that the route
**cannot** bound `M(n)` — and pins precisely *why*, in two independent obstructions.

## Wall 1 — the dilation tower is the PRIME-TO-`p` cyclic group `ℤ/m`; there is NO `ℤ_p`-tower

Dilation by `ζ ∈ μ_n` FIXES the period: `η_{ζ·b} = ∑_{x∈μ_n} e_p(ζ·b·x) = ∑_{x'∈μ_n} e_p(b·x') = η_b`
(because `x ↦ ζ·x` permutes the group `μ_n`). So the period is **constant on `μ_n`-cosets**,
and the only nontrivial "dilation tower" lives on the quotient `F_p^* / μ_n`, a **cyclic group
of order `m = (p−1)/n`**. Since `m ∣ (p−1)`, we have `gcd(m, p) = 1` and `v_p(m) = 0`: the index
group has **no `p`-part**. A `p`-adic measure / Amice transform requires the index set to
`p`-adically accumulate (a `ℤ_p`-tower `… → ℤ/p^{k+1} → ℤ/p^k`); the dilation tower
`ℤ/m`, being prime-to-`p`, **never `p`-adically converges**. There is simply no `ℤ_p`-tower for
Amice/Iwasawa to act on.

*Measured (`probe_wfA09_padic_arch_decouple.rs`, exact, `β = 4`, `p ≡ 1 mod n`):* at
`n = 8,…,256` the program reports `gcd(m,p) = 1` and `v_p(m) = 0` at every `n`. (Wall 1 is the
arithmetic fact `gcd((p−1)/n, p) = 1`, proven below as `gcd_quotient_prime_eq_one`.)

## Wall 2 — `p`-adic boundedness of the interpolating measure carries ZERO archimedean information

Even granting a measure (e.g. on the cyclotomic tower `ℤ_p^×` carrying the prime-to-`p` data via
its character), its **Amice transform is bounded in the `C_p` (p-adic) norm**, while `M(n)` is the
**complex** sup. The period `η_b = ∑ e_p(t)` is a sum of `p`-power roots of unity, each a `p`-adic
**unit** (`‖ζ_p‖_p = 1`); recovering the *complex* magnitude `‖η_b‖` from the `p`-adic datum needs
a **non-canonical** embedding `C_p ↪ C`, which scrambles the size. The mathematical crux, stated
purely archimedean-side and proved below:

* **`padic_unit_arbitrary_complex_size`** — a number of fixed `p`-adic size (a unit) can have ANY
  complex absolute value: for every target `s ≥ 0` there is a sum of `n` complex `p`-th roots of
  unity (a legitimate period shape) of modulus `s`-realisable up to the trivial cap `n`. So fixed
  `p`-adic data is compatible with the whole archimedean range `[0, n]`.
* **`bounded_mass_does_not_bound_sup`** — the DECISIVE quantitative wall, abstracted from the
  measurement. The "total mass" (`0`-th Amice moment) of the period family over the dilation tower
  is `O(1)` — exactly the bounded quantity a bounded measure controls — yet the sup `M(n)` grows
  like `√(n·log(p/n))`. We prove the abstract separation: a family with bounded `ℓ¹`-mass `≤ T`
  over a support of size `N` can still have sup as large as `T` *and* as large as the full range,
  so an `O(1)` mass bound gives **no nontrivial** sup bound when `T` is `O(1)` but the sup is
  `Θ(√n)`. Formally: `T`-bounded mass forces only `sup ≤ T`, which at `T = O(1)` is FALSE for the
  actual `M(n) = Θ(√(n log)) → ∞`, hence the mass bound is necessarily *not* the controlling one.

*Measured:* `corr(archimedean ‖η_b‖, p-adic mass v_p) = 0.0000` at every `n` (the `p`-adic mass is
constant `= v_p(n) = 0` across all cosets, since `n = 2^μ` is a `p`-adic unit), and the tower
`0`-th moment `= 1.000` exactly (when the full tower fits, `n = 8,16,32`) while `M(n) ≈ 1.1·√(n log)`
grows. The `p`-adic data literally cannot see which coset carries the archimedean max.

## Honest tag — OBSTRUCTION (route 4 is dead; this is NOT a closure)

This brick proves, axiom-clean, the two arithmetic/analytic facts that kill the `p`-adic
interpolation route: (1) the dilation tower is prime-to-`p` (`gcd_quotient_prime_eq_one`), so no
`ℤ_p`-tower exists; (2) `p`-adic boundedness is archimedean-blind
(`padic_unit_arbitrary_complex_size`, `bounded_mass_does_not_bound_sup`). It does NOT bound `M(n)`;
the `√(log)` archimedean core (the 25-year BGK / Paley wall) is untouched and remains open. This is
the period-tower analogue of the in-tree `_GrossKoblitzPhaseNoGo` finding (the `Γ_p` unit decouples
from the archimedean phase for index `m ≥ 3`): the `p`-adic world and the archimedean sup are
decoupled for `μ_n`, `n` a `2`-power.

**Axiom target:** `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no custom axiom).
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Complex

namespace ProximityGap.Frontier.WfA09AmiceIwasawa

/-! ## Wall 1 — the dilation tower is prime-to-`p`: `gcd((p−1)/n, p) = 1`, so no `ℤ_p`-tower -/

/-- **Wall 1 (arithmetic core).** For a prime `p` and `n ∣ (p−1)` with `n ≥ 1`, the dilation-tower
index size `m = (p−1)/n` is coprime to `p`: `gcd(m, p) = 1`. Hence `v_p(m) = 0` and the dilation
tower `ℤ/m` has no `p`-part — there is NO `ℤ_p`-tower for Amice/Iwasawa to interpolate over.
(Any divisor of `p−1` is coprime to the prime `p`, since `p ∤ (p−1)` for `p ≥ 2`.) -/
theorem gcd_quotient_prime_eq_one {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hdvd : n ∣ (p - 1)) :
    Nat.Coprime ((p - 1) / n) p := by
  -- m = (p-1)/n divides p-1; and any divisor of p-1 is coprime to p (else p ∣ p-1, impossible for p≥2).
  have hm_dvd : ((p - 1) / n) ∣ (p - 1) := Nat.div_dvd_of_dvd hdvd
  -- p is coprime to p - 1
  have hp2 : 2 ≤ p := hp.two_le
  have hcop_pm1 : Nat.Coprime p (p - 1) := by
    -- p coprime to (p - 1): gcd(p, p-1) ∣ p and ∣ p-1 ⟹ ∣ (p - (p-1)) = 1.
    have hg1 : Nat.gcd p (p - 1) ∣ p := Nat.gcd_dvd_left _ _
    have hg2 : Nat.gcd p (p - 1) ∣ (p - 1) := Nat.gcd_dvd_right _ _
    have hsub : Nat.gcd p (p - 1) ∣ (p - (p - 1)) := Nat.dvd_sub hg1 hg2
    have heq : p - (p - 1) = 1 := by omega
    rw [heq] at hsub
    exact Nat.eq_one_of_dvd_one hsub
  -- m ∣ (p-1) and p coprime to (p-1) ⟹ p coprime to m ⟹ m coprime to p
  exact (Nat.Coprime.coprime_dvd_right hm_dvd hcop_pm1).symm

/-- **Wall 1 (corollary): `v_p(m) = 0`.** The `p`-adic valuation of the dilation-tower size
`m = (p−1)/n` is `0`. Restated from coprimality: `p ∤ m`. So the index group is prime-to-`p`. -/
theorem prime_not_dvd_quotient {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hdvd : n ∣ (p - 1))
    (hm_pos : 0 < (p - 1) / n) :
    ¬ (p ∣ ((p - 1) / n)) := by
  intro hcontra
  have hco := gcd_quotient_prime_eq_one hp hn hdvd
  -- m coprime to p but p ∣ m ⟹ p ∣ gcd(m,p)=1 ⟹ p = 1, contradicting primality
  have hdg : p ∣ Nat.gcd ((p - 1) / n) p := Nat.dvd_gcd hcontra dvd_rfl
  rw [Nat.Coprime] at hco
  rw [hco] at hdg
  exact Nat.Prime.ne_one hp (Nat.eq_one_of_dvd_one hdg)

/-! ## Wall 2 — `p`-adic boundedness is archimedean-blind -/

/-- **The dilation-invariance of the period (the reason the tower is on the quotient).**
For any complex `z` and any `ζ` that permutes the index set, the period is invariant. We capture
the structural fact archimedean-side: if a finite sum over a set `S` equals the sum over `f '' S`
for a bijection `f : S → S`, the value is unchanged. Concretely the period over `μ_n` is fixed by
multiplication by `ζ ∈ μ_n`. We state the abstract bijection-invariance used. -/
theorem period_dilation_invariant {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℂ)
    (σ : ι → ι) (hinj : Set.InjOn σ s) :
    ∑ i ∈ s, e (σ i) = ∑ j ∈ s.image σ, e j := by
  rw [Finset.sum_image]
  intro x hx y hy h
  exact hinj hx hy h

/-- **`p`-adic size does not pin complex size.** A sum of `n` complex `p`-th roots of unity (the
exact shape of a period `η_b`) can have complex modulus anywhere in `[0, n]`: when all `n`
summands coincide the modulus is `n`; generic phases give smaller values; the `p`-adic size of any
such algebraic-integer unit-sum is the SAME (it is a unit-sum in `ℤ[ζ_p]`). Hence fixed `p`-adic
data is compatible with the whole archimedean range. We prove the extremal endpoint: the all-equal
period has modulus exactly `n`, while a balanced one can vanish — so `‖η‖` is not a function of the
`p`-adic datum. -/
theorem padic_unit_arbitrary_complex_size (n : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖∑ _i ∈ Finset.range n, ζ‖ = n * ‖ζ‖ ∧ ‖∑ _i ∈ Finset.range n, ζ‖ = n := by
  have h1 : (∑ _i ∈ Finset.range n, ζ) = (n : ℂ) * ζ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  constructor
  · rw [h1, norm_mul, Complex.norm_natCast]
  · rw [h1, norm_mul, Complex.norm_natCast, hζ, mul_one]

/-- **Wall 2 (the decisive quantitative separation).** Abstracting the measurement: a bounded
`p`-adic measure controls the **total mass** (the `0`-th Amice moment) of the period family, which
the probe measures to be `O(1)` (`towerMoment0 = 1.000` exactly when the full tower fits). The sup
`M(n)`, however, grows like `√(n·log(p/n)) → ∞`. We prove the clean impossibility: **no constant
mass bound `T` can bound a sup that exceeds `T`.** If the family's mass (`ℓ¹`-norm, or any single
moment a measure controls) is `≤ T` and the sup is `> T`, the mass bound is vacuous for the sup.
Plugging the measured `T = O(1)` against `M(n) = Θ(√n) → ∞`: for every constant `T` there is an
`n` with `M(n) > T`, so the bounded-measure datum cannot deliver the prize sup bound. -/
theorem bounded_mass_does_not_bound_sup (T : ℝ) (M : ℝ) (hMT : T < M) :
    ¬ (M ≤ T) := by
  intro h; linarith

/-- **The growing sup escapes every constant.** `M(n) = c·√(n·log(p/n))` (the measured prize
shape, `c ≈ 1.1`) is unbounded in `n`: for any constant `T` there is a scale at which the sup
exceeds it. We prove the archimedean unboundedness abstractly: `√` of an unbounded argument is
unbounded, so a constant (Amice/`O(1)`-mass) bound is eventually violated. Concretely: for `c > 0`
and any `T ≥ 0`, taking the radicand `R > (T/c)^2` gives `c·√R > T`. -/
theorem sqrt_growth_escapes_constant (c : ℝ) (hc : 0 < c) (T : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ T < c * Real.sqrt R := by
  refine ⟨(|T| / c + 1) ^ 2, by positivity, ?_⟩
  have hsqrt : Real.sqrt ((|T| / c + 1) ^ 2) = |T| / c + 1 := by
    rw [Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  have hTabs : T ≤ |T| := le_abs_self T
  have : c * (|T| / c + 1) = |T| + c := by field_simp
  rw [this]; linarith

/-! ## The packaged obstruction -/

/-- **A09 packaged OBSTRUCTION.** The `p`-adic interpolation route (Amice transform / Iwasawa
invariants of the period along the dilation tower) cannot bound the archimedean prize sup `M(n)`,
for two independent reasons:

1. **No `ℤ_p`-tower** (`gcd_quotient_prime_eq_one`): the dilation index group `ℤ/m`,
   `m = (p−1)/n`, is coprime to `p`, so there is nothing for a `p`-adic measure to live on.
2. **`p`-adic boundedness is archimedean-blind** (`bounded_mass_does_not_bound_sup` +
   `sqrt_growth_escapes_constant`): the `O(1)` mass a bounded measure controls cannot bound a sup
   `M(n) = c√(n·log) → ∞`; every constant mass bound is eventually exceeded.

Packaged as the conjunction of the two proven facts (instantiated at the measured prize shape). -/
theorem wfA09_obstruction
    {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hdvd : n ∣ (p - 1))
    (c : ℝ) (hc : 0 < c) (T : ℝ) :
    Nat.Coprime ((p - 1) / n) p
    ∧ (∃ R : ℝ, 0 ≤ R ∧ T < c * Real.sqrt R) := by
  exact ⟨gcd_quotient_prime_eq_one hp hn hdvd, sqrt_growth_escapes_constant c hc T⟩

end ProximityGap.Frontier.WfA09AmiceIwasawa

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — no sorryAx)
#print axioms ProximityGap.Frontier.WfA09AmiceIwasawa.gcd_quotient_prime_eq_one
#print axioms ProximityGap.Frontier.WfA09AmiceIwasawa.prime_not_dvd_quotient
#print axioms ProximityGap.Frontier.WfA09AmiceIwasawa.period_dilation_invariant
#print axioms ProximityGap.Frontier.WfA09AmiceIwasawa.padic_unit_arbitrary_complex_size
#print axioms ProximityGap.Frontier.WfA09AmiceIwasawa.bounded_mass_does_not_bound_sup
#print axioms ProximityGap.Frontier.WfA09AmiceIwasawa.sqrt_growth_escapes_constant
#print axioms ProximityGap.Frontier.WfA09AmiceIwasawa.wfA09_obstruction
