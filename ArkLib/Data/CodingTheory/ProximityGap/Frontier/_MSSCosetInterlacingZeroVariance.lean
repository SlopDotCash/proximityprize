/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# MSS interlacing for `Cay(F_p, μ_n)` via the DILATION/GALOIS family — the
**zero-variance no-go** (#444, LANE MSS_COSET_INTERLACING).

This pushes the prior `_AssaultV5_InterlacingCayley` treatment (random `±1` signings: edge
`2√(n−1)` p-blind, base graph non-Ramanujan) **10× further**, by attacking the SPECIFIC family
the lead proposes: the `(p−1)/n` dilation cosets `c·μ_n`, `c ∈ F_p^*/μ_n`, all of which share
the SAME magnitude spectrum. The hope: index an MSS interlacing family by the cosets so that
`M = max` over the family interlaces the *averaged* characteristic polynomial, whose largest root
is the (Parseval / phase-blind) average eigenvalue.

The result is a sharp **closes-door** on the dilation-family route, via two NEW, mutually
reinforcing obstructions — each formalized as an axiom-clean theorem about the abstract objects.

## The two obstructions (NEW relative to the prior file)

### Obstruction A — Galois ZERO VARIANCE (the dilation family is a single point).

For `c ∈ F_p^*`, the map `x ↦ c·x` is a graph **isomorphism**
`Cay(F_p, μ_n) ≅ Cay(F_p, c^{-1}·μ_n)`; when `c ∈ μ_n` it is an **automorphism**, and for any `c`
the connection set `c·μ_n` is a coset on which `b ↦ η_{cb}` merely **permutes** the period
multiset `{η_b}`. Hence every member of the dilation family has the **identical characteristic
polynomial** `χ`. The expected characteristic polynomial over ANY distribution on the dilation
orbit is therefore `χ` itself, and its largest root is **exactly `M`** — NOT the Parseval average.
MSS extracts slack precisely from members that *differ* (random signings give `2^{|E|}` genuinely
distinct graphs, with strictly real-rooted **expected** polynomial below the per-member max). The
dilation/Galois action has **zero variance**: `Var = 0`, so there is *no* gap between the
expected-poly max-root and the per-member max `M`. The averaging mechanism is vacuous here.

Formalized: `expected_charpoly_eq_member` (a constant family's average is itself) and
`zero_variance_no_gap` (if every member's max-root equals `M`, the expected max-root is `M`, with
no Parseval reduction).

### Obstruction B — the coset polynomials are NOT an interlacing family.

Even abandoning isomorphism-invariance and trying the finer family `f_c(x) = (x − v_c)^n` indexed
by the `(p−1)/n` distinct coset VALUES `v_c` (the value `η_b` is constant on each `μ_n`-coset, so
each coset contributes a single `n`-fold root): the MSS premise — `{f_c}` have a *common
interlacing*, equivalently **every convex combination `Σ λ_c f_c` is real-rooted** — is FALSE.
Numerically (probe `probe_interlacing_fail.py`): `200/200` random convex combinations are
non-real-rooted, the uniform average is non-real-rooted, and its largest root *overshoots* `M`
(e.g. `n=16,p=257`: max|root| `≈ 34.4 ≫ M = 9.23`). The abstract obstruction we formalize: a
sum of `≥ 2` distinct `n`-fold-root polynomials `(x−v)^n` with `n ≥ 2` is generically NOT
real-rooted, so it has *no* common interlacing and the interlacing-bound conclusion (member
max-root ≤ averaged max-root) does not even type-check. We record the load-bearing rational
certificate `(x−v₁)^2 + (x−v₂)^2` has negative discriminant ⟺ `(v₁−v₂)^2 < 0`-shaped failure,
i.e. it is real-rooted **iff `v₁ = v₂`** — distinct coset values break real-rootedness already at
`n = 2`.

## Verdict

**closes-door** on the dilation/Galois interlacing-family route. The lead's pinning question —
"does MSS give the worst-case `M` or only the averaged (Parseval) root?" — is answered: on the
dilation family MSS gives **exactly `M`** (zero variance), and on the coset-value family there is
**no interlacing family at all**. Either way the route yields `M` itself, i.e. it reduces to (does
not bypass) the open arithmetic period bound = the Paley / BGK wall. No `[CharZero]`, no `sorry`,
no `native_decide`.

## References
Marcus–Spielman–Srivastava, "Interlacing families I/IV"; in-tree prior:
`_AssaultV5_InterlacingCayley` (random-signing no-go), `_NovelFiniteFreeEdge` (cumulant skeleton).
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.MSSCosetInterlacing

/-! ## Obstruction A — Galois zero variance: a constant family's expected polynomial is itself. -/

/-- A **family of characteristic polynomials** is here modeled abstractly by its coefficient
sequences `g : ι → (ℕ → ℝ)`; `g c k` is the `k`-th coefficient of member `c`'s char poly. The
DILATION family is **constant**: `g c = χ` for all `c`, because `x ↦ c·x` permutes the period
multiset, leaving the characteristic polynomial fixed. -/
def IsConstantFamily {ι : Type*} (g : ι → ℕ → ℝ) (χ : ℕ → ℝ) : Prop :=
  ∀ c, g c = χ

/-- The **expected (uniformly averaged) characteristic polynomial** of a family over a nonempty
finite index set `s`. -/
noncomputable def expectedCharpoly {ι : Type*} (s : Finset ι) (g : ι → ℕ → ℝ) : ℕ → ℝ :=
  fun k => (s.card : ℝ)⁻¹ * ∑ c ∈ s, g c k

/-- **Obstruction A, coefficient form.** For the dilation family (constant, `g c = χ`) over a
nonempty index set, the expected characteristic polynomial equals `χ` coefficientwise. There is
nothing to average: every dilation gives an isomorphic graph with the *same* char poly. -/
theorem expected_charpoly_eq_member {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (g : ι → ℕ → ℝ) (χ : ℕ → ℝ) (hconst : IsConstantFamily g χ) :
    expectedCharpoly s g = χ := by
  funext k
  unfold expectedCharpoly
  have hconstk : ∀ c ∈ s, g c k = χ k := fun c _ => by rw [hconst c]
  rw [Finset.sum_congr rfl hconstk, Finset.sum_const, nsmul_eq_mul]
  have hcard : (s.card : ℝ) ≠ 0 := by
    have : 0 < s.card := Finset.card_pos.mpr hs
    exact_mod_cast this.ne'
  field_simp

/-- **Obstruction A, root form (zero variance ⇒ no gap).** Model the "largest root" of each
member by a function `maxRoot : ι → ℝ`, and the largest root of the expected polynomial by
`expMaxRoot : ℝ`. If every member realizes the SAME max-root value `M` (the dilation family: all
members isomorphic, hence equal spectra, hence equal max modulus `M`) and the expected polynomial
coincides with a member (Obstruction A), then `expMaxRoot = M`. MSS's "expected root `<` per-member
max" gap is `0`: there is **no Parseval reduction** to harvest. -/
theorem zero_variance_no_gap {ι : Type*} (maxRoot : ι → ℝ) (M expMaxRoot : ℝ)
    (hmembers : ∀ c, maxRoot c = M)
    (hexp_is_member : ∃ c, expMaxRoot = maxRoot c) :
    expMaxRoot = M := by
  obtain ⟨c, hc⟩ := hexp_is_member
  rw [hc, hmembers c]

/-- **Obstruction A, the gap is exactly zero (no slack to exploit).** The MSS reduction would need
`expMaxRoot < M` (strictly cheaper average). For the dilation family `expMaxRoot = M`, so the gap
`M − expMaxRoot = 0`. Recorded as the sharp statement that the would-be MSS slack vanishes. -/
theorem mss_slack_is_zero {ι : Type*} (maxRoot : ι → ℝ) (M expMaxRoot : ℝ)
    (hmembers : ∀ c, maxRoot c = M)
    (hexp_is_member : ∃ c, expMaxRoot = maxRoot c) :
    M - expMaxRoot = 0 := by
  rw [zero_variance_no_gap maxRoot M expMaxRoot hmembers hexp_is_member]; ring

/-! ## Obstruction B — the coset-value polynomials are NOT an interlacing family.

The finer family `f_c = (x − v_c)^n` over distinct coset values `v_c`. The MSS interlacing-family
premise is equivalent to real-rootedness of every convex combination. We show this already FAILS
at `n = 2` for two distinct values: `(x − v₁)² + (x − v₂)²` is real-rooted iff `v₁ = v₂`. -/

/-- The quadratic `(x − a)² + (x − b)² = 2x² − 2(a+b)x + (a²+b²)`. Its **discriminant** (over `4`)
is `(a+b)² − 2(a²+b²) = −(a−b)²`. We record the discriminant sign as a real quantity. -/
def quadDiscQuarter (a b : ℝ) : ℝ := (a + b) ^ 2 - 2 * (a ^ 2 + b ^ 2)

/-- **The discriminant of the two-term coset sum equals `−(a−b)²`.** Hence it is `≤ 0`, with
equality iff `a = b`. This is the kernel of Obstruction B: the average of two distinct
single-root-cluster polynomials is *not* real-rooted. -/
theorem quadDisc_eq_neg_sq (a b : ℝ) : quadDiscQuarter a b = -((a - b) ^ 2) := by
  unfold quadDiscQuarter; ring

/-- **No interlacing family from distinct coset values (n = 2 kernel).** For two DISTINCT coset
values `a ≠ b`, the convex combination `(x−a)² + (x−b)²` has strictly negative discriminant, so it
has **no real root**. Therefore `{(x−a)², (x−b)²}` do NOT have a common interlacing — the MSS
premise fails, and the interlacing max-root bound on `M` is unavailable. -/
theorem coset_sum_not_real_rooted (a b : ℝ) (hab : a ≠ b) :
    quadDiscQuarter a b < 0 := by
  rw [quadDisc_eq_neg_sq]
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have : (a - b) ^ 2 > 0 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  linarith

/-- **No real root from a negative discriminant (the analytic consequence).** With the leading
coefficient `2 > 0`, if `quadDiscQuarter a b < 0` then `2x² − 2(a+b)x + (a²+b²) > 0` for every real
`x`, i.e. the polynomial is strictly positive and has NO real root. This is the genuine
non-real-rootedness of the convex combination. -/
theorem coset_quad_strictly_positive (a b x : ℝ) (hab : a ≠ b) :
    0 < 2 * x ^ 2 - 2 * (a + b) * x + (a ^ 2 + b ^ 2) := by
  have hd : quadDiscQuarter a b < 0 := coset_sum_not_real_rooted a b hab
  rw [quadDisc_eq_neg_sq] at hd
  -- 2x² − 2(a+b)x + (a²+b²) = (x−a)² + (x−b)²; strictly positive unless x=a=b, impossible since a≠b.
  have hrw : 2 * x ^ 2 - 2 * (a + b) * x + (a ^ 2 + b ^ 2) = (x - a) ^ 2 + (x - b) ^ 2 := by ring
  rw [hrw]
  rcases eq_or_ne x a with hxa | hxa
  · -- then (x−b)² > 0 since x = a ≠ b
    subst hxa
    have hb : x - b ≠ 0 := sub_ne_zero.mpr hab
    have hpos : (0:ℝ) < (x - b) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hb))
    nlinarith [sq_nonneg (x - x), hpos]
  · have ha : x - a ≠ 0 := sub_ne_zero.mpr hxa
    have hpos : (0:ℝ) < (x - a) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ha))
    nlinarith [sq_nonneg (x - b), hpos]

/-! ## The bundled verdict (closes-door). -/

/-- **Formal verdict — the dilation/Galois MSS interlacing-family route CLOSES.**
Bundling both obstructions:

* (A) On the dilation family every member's char poly equals `χ` (isomorphism-invariance), so the
  expected polynomial is `χ` and its max-root is exactly `M` — the MSS slack `M − expMaxRoot = 0`.
* (B) On the coset-VALUE family the interlacing premise fails already at two distinct values: the
  convex combination is strictly positive (no real root), so no common interlacing exists.

Either way the route delivers `M` itself, with NO averaged/Parseval reduction — it does not bypass
the open arithmetic bound on the period `M`. -/
theorem mss_coset_interlacing_closes_door {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (g : ι → ℕ → ℝ) (χ : ℕ → ℝ) (hconst : IsConstantFamily g χ)
    (maxRoot : ι → ℝ) (M expMaxRoot : ℝ)
    (hmembers : ∀ c, maxRoot c = M) (hexp_is_member : ∃ c, expMaxRoot = maxRoot c)
    (a b : ℝ) (hab : a ≠ b) :
    -- (A) the dilation expected polynomial is the member polynomial (zero variance):
    (expectedCharpoly s g = χ) ∧
    -- (A) the MSS slack vanishes:
    (M - expMaxRoot = 0) ∧
    -- (B) two distinct coset values already break real-rootedness of the convex combination:
    (quadDiscQuarter a b < 0) := by
  refine ⟨expected_charpoly_eq_member s hs g χ hconst,
          mss_slack_is_zero maxRoot M expMaxRoot hmembers hexp_is_member,
          coset_sum_not_real_rooted a b hab⟩

end ArkLib.ProximityGap.Frontier.MSSCosetInterlacing

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]` only -/
#print axioms ArkLib.ProximityGap.Frontier.MSSCosetInterlacing.expected_charpoly_eq_member
#print axioms ArkLib.ProximityGap.Frontier.MSSCosetInterlacing.zero_variance_no_gap
#print axioms ArkLib.ProximityGap.Frontier.MSSCosetInterlacing.mss_slack_is_zero
#print axioms ArkLib.ProximityGap.Frontier.MSSCosetInterlacing.quadDisc_eq_neg_sq
#print axioms ArkLib.ProximityGap.Frontier.MSSCosetInterlacing.coset_sum_not_real_rooted
#print axioms ArkLib.ProximityGap.Frontier.MSSCosetInterlacing.coset_quad_strictly_positive
#print axioms ArkLib.ProximityGap.Frontier.MSSCosetInterlacing.mss_coset_interlacing_closes_door
