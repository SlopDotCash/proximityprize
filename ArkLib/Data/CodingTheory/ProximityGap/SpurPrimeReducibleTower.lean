/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# `Φ_{2^m}` is REDUCIBLE mod `3` for ALL `m ≥ 3` — the uniform-in-`m` candidate-persistence of the
# spur prime `p = 3` (Issue #444)

The char-`p` energy splits `E_r = E_r^{(0)} + Spur_r(p)`, and a prime `p` is a *candidate bad prime*
at dyadic depth `m` only if `Φ_{2^m}` is **reducible** mod `p` (a necessary condition: some short
relation can vanish in an extension `F_{p^f}` only when `Φ_{2^m}` actually splits there). The concrete
witnesses (`SpurWeightThree`, `SpurPrimePersistTower`) show `p = 3` is bad at `m = 3, 4` by exhibiting a
shared factor at each depth. This file gives the **uniform-in-`m`** structural reason those factors
keep existing: `Φ_{2^m}` is reducible mod `3` for *every* `m ≥ 3`, via a single tower identity.

## The mechanism: the dyadic doubling identity lifts reducibility up the whole tower

Over ANY commutative ring, `Φ_{2^{m+1}} = X^{2^m} + 1 = (X^2)^{2^{m-1}} + 1 = Φ_{2^m}(X^2)` — i.e.

>   `cyclotomic (2^{m+1}) R = (cyclotomic (2^m) R).comp (X^2)`   (`m ≥ 1`).

So composition with `X²` carries any factorization one rung up the tower: if `g ∣ Φ_{2^m}` then
`g.comp(X²) ∣ Φ_{2^{m+1}}`, and `natDegree (g.comp X²) = 2·natDegree g`, so a non-unit stays a non-unit.
Starting from the `m = 3` base (`Φ_8 = (X²+X−1)(X²−X−1)` over `F_3`, `SpurWeightThree.phi8_factor_mod3`),
this **lifts to every `m ≥ 3` by induction**: `Φ_{2^m}` always has the non-unit divisor obtained by
iterating `X ↦ X²` on `X²+X−1`. Hence `Φ_{2^m}` is reducible mod `3` for all `m ≥ 3`.

Probe `probe_phi_reducible_mod3_uniform.py` (exact sympy, `m = 3..8`): `Φ_{2^m}` mod 3 splits into
exactly 2 irreducible factors, each of degree `ord_{2^m}(3) = 2^{m-2} = ½·deg` — the non-cyclicity of
`(ℤ/2^m)*` (`m ≥ 3`) makes `3` never a primitive root, so `Φ` never stays irreducible.
Probe `probe_phi_doubling_lift.py`: `Φ_{2^{m+1}} = Φ_{2^m}(X²)` and the `X²+X−1` lift divides `Φ_{2^m}`
at every `m = 3..7`.

## Honest scope

NOT a CORE bound, NOT a refutation, NOT full Spur-persistence. *Reducibility* of `Φ_{2^m}` mod 3 is
NECESSARY but not sufficient for a genuine `Spur` collision (one also needs a SHORT antipodal-free
relation among the factors — supplied at low `m` by the witness files). This file proves the necessary
condition holds uniformly in `m` (so `3` stays a CANDIDATE bad prime at every depth), via a clean
tower identity that is itself a reusable brick (`cyclotomic_two_pow_succ_eq_comp_sq`). It carries no
capacity / beyond-Johnson / cliff-at-`n/2` / `δ*→0` claim. `CORE M(μ_n) ≤ C·√(n·log(p/n))` OPEN.

Issue #444.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Polynomial

namespace ArkLib.ProximityGap.SpurPrimeReducible

local instance fact3 : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance fact5 : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance fact13 : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance fact17 : Fact (Nat.Prime 17) := ⟨by decide⟩
local instance fact37 : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance fact41 : Fact (Nat.Prime 41) := ⟨by decide⟩
local instance fact53 : Fact (Nat.Prime 53) := ⟨by decide⟩
local instance fact61 : Fact (Nat.Prime 61) := ⟨by decide⟩
local instance fact73 : Fact (Nat.Prime 73) := ⟨by decide⟩
local instance fact89 : Fact (Nat.Prime 89) := ⟨by decide⟩
local instance fact97 : Fact (Nat.Prime 97) := ⟨by decide⟩
local instance fact101 : Fact (Nat.Prime 101) := ⟨by decide⟩
local instance fact109 : Fact (Nat.Prime 109) := ⟨by decide⟩
local instance fact113 : Fact (Nat.Prime 113) := ⟨by decide⟩
local instance fact137 : Fact (Nat.Prime 137) := ⟨by decide⟩

/-- **`Φ_{2^m} = X^{2^{m−1}} + 1` over any commutative ring** (`m ≥ 1`). The `p = 2` prime-power
cyclotomic; pulled out as a reusable named form. -/
theorem cyclotomic_two_pow {R : Type*} [CommRing R] {m : ℕ} (hm : 1 ≤ m) :
    cyclotomic (2 ^ m) R = X ^ (2 ^ (m - 1)) + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hm1 : 1 + k - 1 = k := by omega
  rw [hm1]
  have h : (2 : ℕ) ^ (1 + k) = 2 ^ (k + 1) := by ring_nf
  rw [h, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  ring


/-- **Generic square-root-of-minus-one factorization of dyadic cyclotomic tower levels.**
If a commutative ring contains `ι` with `ι² = -1`, then every `Φ_{2^m}` (`m ≥ 2`) splits
into the two half-degree factors `X^{2^{m-2}} ± ι`. This packages the repeated explicit prime
rungs into one reusable closed form. -/
theorem cyclotomic_two_pow_factor_of_sq_eq_neg_one {R : Type*} [CommRing R] {m : ℕ}
    (hm : 2 ≤ m) {ι : R} (hι : ι * ι = -1) :
    cyclotomic (2 ^ m) R = (X ^ (2 ^ (m - 2)) + C ι) * (X ^ (2 ^ (m - 2)) - C ι) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow]
  rw [show (X ^ (2 ^ (m - 2)) + C ι) * (X ^ (2 ^ (m - 2)) - C ι) =
      (X ^ 2) ^ (2 ^ (m - 2)) + 1 by
    calc
      (X ^ (2 ^ (m - 2)) + C ι) * (X ^ (2 ^ (m - 2)) - C ι)
          = X ^ (2 ^ (m - 2) * 2) - (C ι) ^ 2 := by ring
      _ = X ^ (2 ^ (m - 2) * 2) - C (ι ^ 2) := by rw [map_pow]
      _ = X ^ (2 ^ (m - 2) * 2) + 1 := by
        rw [show ι ^ 2 = -1 by simpa [pow_two] using hι]
        rw [map_neg, map_one]
        ring
      _ = X ^ (2 * 2 ^ (m - 2)) + 1 := by
        congr 2
        ring
      _ = (X ^ 2) ^ (2 ^ (m - 2)) + 1 := by rw [pow_mul]]
  rw [pow_mul]

/-- **Generic reducibility from a square root of `-1`.** Over any field containing `ι` with `ι² = -1`,
the half-degree factorization above has two positive-degree factors for `m ≥ 3`, so `Φ_{2^m}` is not
irreducible. This abstracts the repeated explicit `p ≡ 1 mod 4` prime rungs into one reusable lemma. -/
theorem not_irreducible_cyclotomic_two_pow_of_sq_eq_neg_one {K : Type*} [Field K] {m : ℕ}
    (hm : 3 ≤ m) {ι : K} (hι : ι * ι = -1) :
    ¬ Irreducible (cyclotomic (2 ^ m) K) := by
  rw [cyclotomic_two_pow_factor_of_sq_eq_neg_one (by omega) hι]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + C ι, X ^ (2 ^ (m - 2)) - C ι, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + C ι : K[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + C ι : K[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - C ι : K[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - C ι : K[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega

/-- **THE DYADIC DOUBLING IDENTITY: `Φ_{2^{m+1}} = Φ_{2^m}(X²)` over any commutative ring** (`m ≥ 1`).
Both sides equal `X^{2^m} + 1`. This is the single lever that lifts factorizations up the dyadic tower. -/
theorem cyclotomic_two_pow_succ_eq_comp_sq {R : Type*} [CommRing R] {m : ℕ} (hm : 1 ≤ m) :
    cyclotomic (2 ^ (m + 1)) R = (cyclotomic (2 ^ m) R).comp (X ^ 2) := by
  rw [cyclotomic_two_pow (Nat.le_succ_of_le hm), cyclotomic_two_pow hm]
  simp only [add_comp, pow_comp, X_comp, one_comp]
  rw [← pow_mul]
  congr 2
  have h1 : m + 1 - 1 = (m - 1) + 1 := by omega
  rw [h1, pow_succ, mul_comm]

/-- `natDegree (X^2) = 2` over a nontrivial commutative ring. -/
theorem natDegree_X_sq {R : Type*} [CommRing R] [Nontrivial R] :
    (X ^ 2 : R[X]).natDegree = 2 := by
  simp [natDegree_X_pow]

/-- **Reducibility lifts through `comp (X²)`:** over a field, if `p` is NOT irreducible and has positive
degree, then `p.comp (X²)` is not irreducible either. The factorization `p = a*b` (both non-unit)
lifts to `p.comp(X²) = a.comp(X²) * b.comp(X²)` with both factors non-unit (their degrees double). -/
theorem not_irreducible_comp_sq_of_not_irreducible {K : Type*} [Field K] {p : K[X]}
    (hp : 0 < p.natDegree) (hred : ¬ Irreducible p) :
    ¬ Irreducible (p.comp (X ^ 2)) := by
  -- p is not a unit (positive degree) and not irreducible ⟹ p = a*b with a,b non-units (a, b ≠ 0).
  have hpu : ¬ IsUnit p := by
    intro hu
    rw [Polynomial.natDegree_eq_zero_of_isUnit hu] at hp
    exact absurd hp (lt_irrefl 0)
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  -- extract a non-trivial factorization from ¬Irreducible
  rw [irreducible_iff, not_and_or] at hred
  rcases hred with h | h
  · exact absurd hpu h
  · push Not at h
    obtain ⟨a, b, hab, hau, hbu⟩ := h
    -- a, b have positive degree (non-unit, nonzero since product is p ≠ 0)
    have ha0 : a ≠ 0 := by rintro rfl; simp [hab] at hp0
    have hb0 : b ≠ 0 := by rintro rfl; simp [hab] at hp0
    have hadeg : 0 < a.natDegree := by
      rcases Nat.eq_zero_or_pos a.natDegree with h0 | h0
      · exact absurd ((Polynomial.isUnit_iff_degree_eq_zero).2
          (by rw [Polynomial.degree_eq_natDegree ha0, h0]; rfl)) hau
      · exact h0
    have hbdeg : 0 < b.natDegree := by
      rcases Nat.eq_zero_or_pos b.natDegree with h0 | h0
      · exact absurd ((Polynomial.isUnit_iff_degree_eq_zero).2
          (by rw [Polynomial.degree_eq_natDegree hb0, h0]; rfl)) hbu
      · exact h0
    -- lift: p.comp(X²) = a.comp(X²) * b.comp(X²)
    rw [irreducible_iff, not_and_or]; right; push Not
    refine ⟨a.comp (X ^ 2), b.comp (X ^ 2), by rw [hab, mul_comp], ?_, ?_⟩
    · -- a.comp(X²) non-unit: its natDegree = 2*natDegree a > 0
      intro hu
      have : (a.comp (X ^ 2)).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      rw [natDegree_comp, natDegree_X_sq] at this
      omega
    · intro hu
      have : (b.comp (X ^ 2)).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      rw [natDegree_comp, natDegree_X_sq] at this
      omega

/-- `Φ_{2^m}` over `F_3` has positive degree for `m ≥ 1` (`natDegree = 2^{m-1} ≥ 1`). -/
theorem natDegree_cyclotomic_two_pow_pos {m : ℕ} (hm : 1 ≤ m) :
    0 < (cyclotomic (2 ^ m) (ZMod 3)).natDegree := by
  have _hm0 : 0 < m := by omega
  rw [Polynomial.natDegree_cyclotomic]
  have : 0 < Nat.totient (2 ^ m) := Nat.totient_pos.2 (by positivity)
  exact this

/-- **Base case: `Φ_8` is NOT irreducible over `F_3`** (`SpurWeightThree.phi8_factor_mod3`:
`X⁴+1 = (X²+X−1)(X²−X−1)`, both non-unit). -/
theorem not_irreducible_phi8_mod3 : ¬ Irreducible (cyclotomic (2 ^ 3) (ZMod 3)) := by
  rw [show cyclotomic (2 ^ 3) (ZMod 3) = X ^ 4 + 1 by
        rw [cyclotomic_two_pow (by norm_num)]; norm_num]
  rw [show (X ^ 4 + 1 : (ZMod 3)[X]) = (X ^ 2 + X - 1) * (X ^ 2 - X - 1) by
        have h3 : (3 : (ZMod 3)[X]) = 0 := by
          have : (3 : ZMod 3) = 0 := by decide
          calc (3 : (ZMod 3)[X]) = C (3 : ZMod 3) := by norm_cast
            _ = 0 := by rw [this]; exact map_zero C
        linear_combination (X ^ 2) * h3]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ 2 + X - 1, X ^ 2 - X - 1, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ 2 + X - 1 : (ZMod 3)[X]).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have h2 : (X ^ 2 + X - 1 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
    omega
  · intro hu
    have hd : (X ^ 2 - X - 1 : (ZMod 3)[X]).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have h2 : (X ^ 2 - X - 1 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
    omega

/-- **THE UNIFORM THEOREM: `Φ_{2^m}` is REDUCIBLE (not irreducible) mod `3` for ALL `m ≥ 3`.**
Induction from the `m = 3` base via the dyadic doubling identity
`Φ_{2^{m+1}} = Φ_{2^m}(X²)` (`cyclotomic_two_pow_succ_eq_comp_sq`) and the
`comp(X²)` reducibility lift (`not_irreducible_comp_sq_of_not_irreducible`).

So the spur prime `p = 3` stays a CANDIDATE bad prime at every dyadic depth `m ≥ 3` (the necessary
splitting condition for any in-extension short-relation vanishing holds uniformly). This is the
uniform-in-`m` structural reason behind the concrete `m = 3, 4` persistence witnesses
(`SpurWeightThree`, `SpurPrimePersistTower`). NOT full Spur-persistence (which also needs a SHORT
antipodal-free relation among the factors), and NOT a CORE bound. `CORE OPEN.` -/
theorem not_irreducible_cyclotomic_two_pow_mod3 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 3)) := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with hk | hk
    · -- k+1 = 3 (since 3 ≤ k+1 and k < 3 ⟹ k = 2)
      interval_cases k
      · omega
      · omega
      · exact not_irreducible_phi8_mod3
    · -- k ≥ 3: lift from Φ_{2^k}
      have hk1 : 1 ≤ k := by omega
      rw [cyclotomic_two_pow_succ_eq_comp_sq hk1]
      exact not_irreducible_comp_sq_of_not_irreducible
        (natDegree_cyclotomic_two_pow_pos hk1) (ih hk)

/-- **Explicit `F_5` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`2² = -1` in `F_5`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 2)(X^{2^{m-2}} - 2)`.
This gives a second uniform candidate-bad-prime tower (`p = 5`) without invoking the abstract
cyclotomic-order irreducibility criterion. -/
theorem cyclotomic_two_pow_mod5_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 5) =
      (X ^ (2 ^ (m - 2)) + 2) * (X ^ (2 ^ (m - 2)) - 2) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow, pow_mul]
  have h5 : (5 : (ZMod 5)[X]) = 0 := by
    have : (5 : ZMod 5) = 0 := by decide
    calc (5 : (ZMod 5)[X]) = C (5 : ZMod 5) := by norm_cast
      _ = 0 := by rw [this]; exact map_zero C
  linear_combination h5

/-- **Second uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_5` for every `m ≥ 3`.**
The two factors in `cyclotomic_two_pow_mod5_factor` both have positive degree, hence are non-units.
Honest scope: this is only the reducibility necessary condition for a char-`5` spur collision, not a
short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod5 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 5)) := by
  rw [cyclotomic_two_pow_mod5_factor (by omega)]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + 2, X ^ (2 ^ (m - 2)) - 2, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + 2 : (ZMod 5)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + 2 : (ZMod 5)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - 2 : (ZMod 5)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - 2 : (ZMod 5)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega

/-- **Explicit `F_13` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`5² = -1` in `F_13`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 5)(X^{2^{m-2}} - 5)`.
This is the next square-root-of-minus-one candidate-bad-prime tower after the `F_5` brick. -/
theorem cyclotomic_two_pow_mod13_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 13) =
      (X ^ (2 ^ (m - 2)) + 5) * (X ^ (2 ^ (m - 2)) - 5) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow, pow_mul]
  have h13 : (13 : (ZMod 13)[X]) = 0 := by
    have : (13 : ZMod 13) = 0 := by decide
    calc (13 : (ZMod 13)[X]) = C (13 : ZMod 13) := by norm_cast
      _ = 0 := by rw [this]; exact map_zero C
  linear_combination 2 * h13

/-- **Third explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_13` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod13_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod13 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 13)) := by
  rw [cyclotomic_two_pow_mod13_factor (by omega)]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + 5, X ^ (2 ^ (m - 2)) - 5, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + 5 : (ZMod 13)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + 5 : (ZMod 13)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - 5 : (ZMod 13)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - 5 : (ZMod 13)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega

/-- **Explicit `F_17` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`4² = -1` in `F_17`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 4)(X^{2^{m-2}} - 4)`.
This is the next square-root-of-minus-one candidate-bad-prime tower after the `F_13` brick. -/
theorem cyclotomic_two_pow_mod17_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 17) =
      (X ^ (2 ^ (m - 2)) + 4) * (X ^ (2 ^ (m - 2)) - 4) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow, pow_mul]
  have h17 : (17 : (ZMod 17)[X]) = 0 := by
    have : (17 : ZMod 17) = 0 := by decide
    calc (17 : (ZMod 17)[X]) = C (17 : ZMod 17) := by norm_cast
      _ = 0 := by rw [this]; exact map_zero C
  linear_combination h17

/-- **Fourth explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_17` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod17_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod17 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 17)) := by
  rw [cyclotomic_two_pow_mod17_factor (by omega)]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + 4, X ^ (2 ^ (m - 2)) - 4, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + 4 : (ZMod 17)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + 4 : (ZMod 17)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - 4 : (ZMod 17)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - 4 : (ZMod 17)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega

/-- **Explicit `F_29` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`12² = -1` in `F_29`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 12)(X^{2^{m-2}} - 12)`.
This extends the square-root-of-minus-one reducible tower past the `F_17` rung. -/
theorem cyclotomic_two_pow_mod29_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 29) =
      (X ^ (2 ^ (m - 2)) + 12) * (X ^ (2 ^ (m - 2)) - 12) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow, pow_mul]
  have h29 : (29 : (ZMod 29)[X]) = 0 := by
    have : (29 : ZMod 29) = 0 := by decide
    calc (29 : (ZMod 29)[X]) = C (29 : ZMod 29) := by norm_cast
      _ = 0 := by rw [this]; exact map_zero C
  linear_combination 5 * h29

/-- **Fifth explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_29` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod29_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod29 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 29)) := by
  haveI : Fact (Nat.Prime 29) := ⟨by decide⟩
  rw [cyclotomic_two_pow_mod29_factor (by omega)]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + 12, X ^ (2 ^ (m - 2)) - 12, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + 12 : (ZMod 29)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + 12 : (ZMod 29)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - 12 : (ZMod 29)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - 12 : (ZMod 29)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega

/-- **Explicit `F_37` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`6² = -1` in `F_37`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 6)(X^{2^{m-2}} - 6)`.
This extends the square-root-of-minus-one reducible tower past the `F_29` rung. -/
theorem cyclotomic_two_pow_mod37_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 37) =
      (X ^ (2 ^ (m - 2)) + 6) * (X ^ (2 ^ (m - 2)) - 6) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow, pow_mul]
  have h37 : (37 : (ZMod 37)[X]) = 0 := by
    have : (37 : ZMod 37) = 0 := by decide
    calc (37 : (ZMod 37)[X]) = C (37 : ZMod 37) := by norm_cast
      _ = 0 := by rw [this]; exact map_zero C
  linear_combination h37

/-- **Sixth explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_37` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod37_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod37 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 37)) := by
  rw [cyclotomic_two_pow_mod37_factor (by omega)]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + 6, X ^ (2 ^ (m - 2)) - 6, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + 6 : (ZMod 37)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + 6 : (ZMod 37)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - 6 : (ZMod 37)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - 6 : (ZMod 37)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega

/-- **Explicit `F_41` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`9² = -1` in `F_41`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 9)(X^{2^{m-2}} - 9)`.
This extends the square-root-of-minus-one reducible tower past the `F_37` rung. -/
theorem cyclotomic_two_pow_mod41_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 41) =
      (X ^ (2 ^ (m - 2)) + 9) * (X ^ (2 ^ (m - 2)) - 9) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow, pow_mul]
  have h41 : (41 : (ZMod 41)[X]) = 0 := by
    have : (41 : ZMod 41) = 0 := by decide
    calc (41 : (ZMod 41)[X]) = C (41 : ZMod 41) := by norm_cast
      _ = 0 := by rw [this]; exact map_zero C
  linear_combination 2 * h41

/-- **Seventh explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_41` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod41_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod41 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 41)) := by
  rw [cyclotomic_two_pow_mod41_factor (by omega)]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + 9, X ^ (2 ^ (m - 2)) - 9, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + 9 : (ZMod 41)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + 9 : (ZMod 41)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - 9 : (ZMod 41)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - 9 : (ZMod 41)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega

/-- **Explicit `F_53` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`23² = -1` in `F_53`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 23)(X^{2^{m-2}} - 23)`.
This extends the square-root-of-minus-one reducible tower past the `F_41` rung. -/
theorem cyclotomic_two_pow_mod53_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 53) =
      (X ^ (2 ^ (m - 2)) + 23) * (X ^ (2 ^ (m - 2)) - 23) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow, pow_mul]
  have h53 : (53 : (ZMod 53)[X]) = 0 := by
    have : (53 : ZMod 53) = 0 := by decide
    calc (53 : (ZMod 53)[X]) = C (53 : ZMod 53) := by norm_cast
      _ = 0 := by rw [this]; exact map_zero C
  linear_combination 10 * h53

/-- **Eighth explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_53` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod53_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod53 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 53)) := by
  rw [cyclotomic_two_pow_mod53_factor (by omega)]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + 23, X ^ (2 ^ (m - 2)) - 23, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + 23 : (ZMod 53)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + 23 : (ZMod 53)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - 23 : (ZMod 53)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - 23 : (ZMod 53)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega

/-- **Explicit `F_61` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`11² = -1` in `F_61`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 11)(X^{2^{m-2}} - 11)`.
This extends the square-root-of-minus-one reducible tower past the `F_53` rung. -/
theorem cyclotomic_two_pow_mod61_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 61) =
      (X ^ (2 ^ (m - 2)) + 11) * (X ^ (2 ^ (m - 2)) - 11) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow, pow_mul]
  have h61 : (61 : (ZMod 61)[X]) = 0 := by
    have : (61 : ZMod 61) = 0 := by decide
    calc (61 : (ZMod 61)[X]) = C (61 : ZMod 61) := by norm_cast
      _ = 0 := by rw [this]; exact map_zero C
  linear_combination 2 * h61

/-- **Ninth explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_61` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod61_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod61 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 61)) := by
  rw [cyclotomic_two_pow_mod61_factor (by omega)]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + 11, X ^ (2 ^ (m - 2)) - 11, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + 11 : (ZMod 61)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + 11 : (ZMod 61)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - 11 : (ZMod 61)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - 11 : (ZMod 61)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega

/-- **Explicit `F_73` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`27² = -1` in `F_73`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 27)(X^{2^{m-2}} - 27)`.
This extends the square-root-of-minus-one reducible tower past the `F_61` rung. -/
theorem cyclotomic_two_pow_mod73_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 73) =
      (X ^ (2 ^ (m - 2)) + 27) * (X ^ (2 ^ (m - 2)) - 27) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow, pow_mul]
  have h73 : (73 : (ZMod 73)[X]) = 0 := by
    have : (73 : ZMod 73) = 0 := by decide
    calc (73 : (ZMod 73)[X]) = C (73 : ZMod 73) := by norm_cast
      _ = 0 := by rw [this]; exact map_zero C
  linear_combination 10 * h73

/-- **Tenth explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_73` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod73_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod73 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 73)) := by
  rw [cyclotomic_two_pow_mod73_factor (by omega)]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + 27, X ^ (2 ^ (m - 2)) - 27, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + 27 : (ZMod 73)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + 27 : (ZMod 73)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - 27 : (ZMod 73)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - 27 : (ZMod 73)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega

/-- **Explicit `F_89` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`34² = -1` in `F_89`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 34)(X^{2^{m-2}} - 34)`.
This extends the square-root-of-minus-one reducible tower past the `F_73` rung. -/
theorem cyclotomic_two_pow_mod89_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 89) =
      (X ^ (2 ^ (m - 2)) + 34) * (X ^ (2 ^ (m - 2)) - 34) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow, pow_mul]
  have h89 : (89 : (ZMod 89)[X]) = 0 := by
    have : (89 : ZMod 89) = 0 := by decide
    calc (89 : (ZMod 89)[X]) = C (89 : ZMod 89) := by norm_cast
      _ = 0 := by rw [this]; exact map_zero C
  linear_combination 13 * h89

/-- **Eleventh explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_89` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod89_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod89 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 89)) := by
  rw [cyclotomic_two_pow_mod89_factor (by omega)]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + 34, X ^ (2 ^ (m - 2)) - 34, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + 34 : (ZMod 89)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + 34 : (ZMod 89)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - 34 : (ZMod 89)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - 34 : (ZMod 89)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega

/-- **Explicit `F_97` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`22² = -1` in `F_97`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 22)(X^{2^{m-2}} - 22)`.
This extends the square-root-of-minus-one reducible tower past the `F_89` rung. -/
theorem cyclotomic_two_pow_mod97_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 97) =
      (X ^ (2 ^ (m - 2)) + 22) * (X ^ (2 ^ (m - 2)) - 22) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow, pow_mul]
  have h97 : (97 : (ZMod 97)[X]) = 0 := by
    have : (97 : ZMod 97) = 0 := by decide
    calc (97 : (ZMod 97)[X]) = C (97 : ZMod 97) := by norm_cast
      _ = 0 := by rw [this]; exact map_zero C
  linear_combination 5 * h97

/-- **Twelfth explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_97` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod97_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod97 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 97)) := by
  rw [cyclotomic_two_pow_mod97_factor (by omega)]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + 22, X ^ (2 ^ (m - 2)) - 22, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + 22 : (ZMod 97)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + 22 : (ZMod 97)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - 22 : (ZMod 97)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - 22 : (ZMod 97)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega

/-- **Explicit `F_101` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`10² = -1` in `F_101`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 10)(X^{2^{m-2}} - 10)`.
This extends the square-root-of-minus-one reducible tower past the `F_97` rung. -/
theorem cyclotomic_two_pow_mod101_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 101) =
      (X ^ (2 ^ (m - 2)) + 10) * (X ^ (2 ^ (m - 2)) - 10) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow, pow_mul]
  have h101 : (101 : (ZMod 101)[X]) = 0 := by
    have : (101 : ZMod 101) = 0 := by decide
    calc (101 : (ZMod 101)[X]) = C (101 : ZMod 101) := by norm_cast
      _ = 0 := by rw [this]; exact map_zero C
  linear_combination h101

/-- **Thirteenth explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_101` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod101_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod101 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 101)) := by
  rw [cyclotomic_two_pow_mod101_factor (by omega)]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + 10, X ^ (2 ^ (m - 2)) - 10, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + 10 : (ZMod 101)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + 10 : (ZMod 101)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - 10 : (ZMod 101)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - 10 : (ZMod 101)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega


/-- **Explicit `F_109` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`33² = -1` in `F_109`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 33)(X^{2^{m-2}} - 33)`.
This extends the square-root-of-minus-one reducible tower past the `F_101` rung. -/
theorem cyclotomic_two_pow_mod109_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 109) =
      (X ^ (2 ^ (m - 2)) + 33) * (X ^ (2 ^ (m - 2)) - 33) := by
  rw [cyclotomic_two_pow (by omega)]
  have hpow : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    have h : m - 1 = (m - 2) + 1 := by omega
    rw [h, pow_succ, mul_comm]
  rw [hpow, pow_mul]
  have h109 : (109 : (ZMod 109)[X]) = 0 := by
    have : (109 : ZMod 109) = 0 := by decide
    calc (109 : (ZMod 109)[X]) = C (109 : ZMod 109) := by norm_cast
      _ = 0 := by rw [this]; exact map_zero C
  linear_combination 10 * h109

/-- **Fourteenth explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_109` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod109_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod109 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 109)) := by
  rw [cyclotomic_two_pow_mod109_factor (by omega)]
  rw [irreducible_iff, not_and_or]; right; push Not
  refine ⟨X ^ (2 ^ (m - 2)) + 33, X ^ (2 ^ (m - 2)) - 33, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) + 33 : (ZMod 109)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) + 33 : (ZMod 109)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega
  · intro hu
    have hd : (X ^ (2 ^ (m - 2)) - 33 : (ZMod 109)[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (X ^ (2 ^ (m - 2)) - 33 : (ZMod 109)[X]).natDegree = 2 ^ (m - 2) := by
      compute_degree!
    rw [hdeg] at hd
    have hpos : 0 < 2 ^ (m - 2) := by positivity
    omega

/-- **Explicit `F_113` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`15² = -1` in `F_113`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 15)(X^{2^{m-2}} - 15)`.
This extends the square-root-of-minus-one reducible tower past the `F_109` rung, reusing the generic
square-root-of-minus-one closed form. -/
theorem cyclotomic_two_pow_mod113_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 113) =
      (X ^ (2 ^ (m - 2)) + 15) * (X ^ (2 ^ (m - 2)) - 15) := by
  simpa using cyclotomic_two_pow_factor_of_sq_eq_neg_one (R := ZMod 113) hm
    (ι := (15 : ZMod 113)) (by decide)

/-- **Fifteenth explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_113` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod113_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod113 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 113)) := by
  simpa using not_irreducible_cyclotomic_two_pow_of_sq_eq_neg_one (K := ZMod 113) hm
    (ι := (15 : ZMod 113)) (by decide)

/-- **Explicit `F_137` half-degree factorization of every dyadic cyclotomic tower level.** For `m ≥ 2`,
`37² = -1` in `F_137`, so
`Φ_{2^m}(X) = X^{2^{m-1}} + 1 = (X^{2^{m-2}} + 37)(X^{2^{m-2}} - 37)`.
This extends the square-root-of-minus-one reducible tower past the `F_113` rung, reusing the generic
square-root-of-minus-one closed form. -/
theorem cyclotomic_two_pow_mod137_factor {m : ℕ} (hm : 2 ≤ m) :
    cyclotomic (2 ^ m) (ZMod 137) =
      (X ^ (2 ^ (m - 2)) + 37) * (X ^ (2 ^ (m - 2)) - 37) := by
  simpa using cyclotomic_two_pow_factor_of_sq_eq_neg_one (R := ZMod 137) hm
    (ι := (37 : ZMod 137)) (by decide)

/-- **Sixteenth explicit uniform candidate-bad-prime tower: `Φ_{2^m}` is reducible over `F_137` for every
`m ≥ 3`.** The two factors in `cyclotomic_two_pow_mod137_factor` both have positive degree. Honest scope:
necessary reducibility only, not a short-relation witness and not a CORE bound. -/
theorem not_irreducible_cyclotomic_two_pow_mod137 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 137)) := by
  simpa using not_irreducible_cyclotomic_two_pow_of_sq_eq_neg_one (K := ZMod 137) hm
    (ι := (37 : ZMod 137)) (by decide)

end ArkLib.ProximityGap.SpurPrimeReducible

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_factor_of_sq_eq_neg_one
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_of_sq_eq_neg_one
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_succ_eq_comp_sq
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_comp_sq_of_not_irreducible
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod3
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod5_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod5
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod13_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod13
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod17_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod17
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod29_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod29
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod37_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod37
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod41_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod41
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod53_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod53
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod61_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod61
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod73_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod73
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod89_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod89
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod97_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod97
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod101_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod101
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod109_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod109
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod113_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod113
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_mod137_factor
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod137
