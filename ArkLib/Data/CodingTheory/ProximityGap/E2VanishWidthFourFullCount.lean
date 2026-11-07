/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2VanishEnergy
import Mathlib.Tactic

/-!
# The two-antipodal stratum of the width-4 `e₂=0` locus [L13.6] (#407)

**Status (corrected 2026-10-28 audit, PG-234).** This file proves the *algebra* of the
two-antipodal-pair quadruples `{x,−x,a,−a}` and the `Nat` identity
`n(n−4)/4 + n/4 = n(n−3)/4`. It does **not** prove any cardinality theorem: no statement in this
file counts `e₂=0` four-subsets of `μ_n`. The conjectural count `n(n−3)/4` rests on the named
classification `WidthFourDyadicClassified`, and that classification is **false over finite fields
in general**: `not_widthFourDyadicClassified_zmod97` (below) is a kernel-checked counterexample
in `μ₃₂ ⊂ 𝔽₉₇` (a proper subgroup of index 3), where `S = {1, 8, 27, 55}` has `e₂(S) = 0` and no
antipodal pair. Exact enumeration of the 35,960 four-subsets of `μ₃₂ ⊂ 𝔽₉₇` gives 424 `e₂=0`
sets, 192 of them antipodal-pair-free, against the formula value 232. Characteristic-zero
vanishing-sum structure does not transfer to `𝔽_q` without an extra guard (e.g. a prime large
enough relative to the relevant cyclotomic norms); no such guarded count is proved here.

The in-tree `E2VanishWidthFourLaw` treats the **one-antipodal-pair** shape: a quadruple
`{x,−x,a,b}` with `a·b = x²`, `a+b ≠ 0`, all with `e₁ ≠ 0` (the genuine bad-scalar producers).
That is only PART of the `e₂=0` locus at width 4.

This file treats the **complementary shape** — the **two-antipodal-pair** quadruples. Together
with a classification hypothesis these two shapes would give the full width-4 count; without one,
the count below is a conjecture/probe readout, not a theorem.

## The cyclic-sieving readout (conjectural; NOT a theorem over finite fields)

Identify `μ_n` (`n = 2^μ`) with `ℤ/n` by exponents. *If* every width-4 `e₂=0` subset of `μ_n`
contains an antipodal pair (the hypothesis `WidthFourDyadicClassified`, false in general over
`𝔽_q`; see the status note above), then such a subset has one of two structural shapes:

* **Stratum A (one antipodal pair, `e₁ ≠ 0`):** `{x,−x,a,b}` with `a·b = x²`, `a+b ≠ 0`.
  `e₂ = a·b − x²` (in-tree `e2_antipodal_quadruple`); count `n(n−4)/4`.
* **Stratum B (two antipodal pairs, `e₁ = 0`):** `{x,−x,a,−a}` with `a² = −x²`.
  `e₂ = −x² − a²` (`e2_double_antipodal`, THIS FILE); count `n/4`.

The probe-level count (`probe_2antip.py`, enumeration `n = 8,16,32,64,128`; numerical evidence in
the probe's own setting only, not a theorem) is

> `#{S ⊆ μ_n : |S| = 4, e₂(S) = 0} = n(n−4)/4 + n/4 = n(n−3)/4`   (conjectural).

This equation is **false** for `μ₃₂ ⊂ 𝔽₉₇` (true count 424, formula 232), so it cannot hold for
every dyadic subgroup of every finite field.

| `n`  | stratum A `n(n−4)/4` | stratum B `n/4` | total `n(n−3)/4` |
|------|----------------------|-----------------|-------------------|
| 8    | 8                    | 2               | 10                |
| 16   | 48                   | 4               | 52                |
| 32   | 224                  | 8               | 232               |
| 64   | 960                  | 16              | 976               |

This file proves the **algebraic core** of stratum B — the `e₂` and `e₁` identities of a double
antipodal quadruple. The two shapes are *algebraically disjoint*: stratum A has `e₁ = a+b ≠ 0`,
stratum B has `e₁ = 0` (`e1_double_antipodal`), so they never overlap. Whether they *exhaust*
the width-4 `e₂=0` locus is exactly the hypothesis `WidthFourDyadicClassified`, which this file
refutes for `μ₃₂ ⊂ 𝔽₉₇`.

The shape identities are pure field algebra (`e₂ = (e₁² − p₂)/2` for the explicit 4-set),
q-independent, no character sum. The statement "at width 4 every `e₂=0` set is one of the two
antipodal shapes" is **not** q-independent: it fails in `μ₃₂ ⊂ 𝔽₉₇`.

## Honest scope

Proved here: the stratum-B identities, the stratum disjointness via `e₁`, the `Nat` identity
`n(n−4)/4 + n/4 = n(n−3)/4`, and the refutation `not_widthFourDyadicClassified_zmod97`. Not proved:
any cardinality statement for the width-4 `e₂=0` locus, in particular the formula `n(n−3)/4`.
Nothing here pins the δ* node `B = max|η_b|` either: the window interior needs width `w ≈ n/2`,
where the analogous count is super-linear / open (the `K(n)` orbit census; see
`E2DilationDirectCount` header).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- Reiner, Stanton, White. *The cyclic sieving phenomenon*. JCTA 108 (2004).
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.E2VanishWidthFourFullCount

open ArkLib.ProximityGap.E2VanishEnergy

variable {F : Type*} [Field F] [DecidableEq F]

/-- A **double antipodal quadruple** `{x,−x,a,−a}`: two genuine antipodal pairs, all four elements
distinct. The distinctness requirements are `x ≠ −x` (genuine first pair), `a ≠ −a` (genuine second
pair), and `a ∉ {x,−x}` (the two pairs are different). Note `−a ∉ {x,−x}` is then automatic
(`−a = x ⟹ a = −x`, `−a = −x ⟹ a = x`). -/
structure DoubleAntipodalQuadruple (x a : F) : Prop where
  /-- the first antipodal pair is genuine (`x ≠ −x`, forced by `x ≠ 0` in char `≠ 2`) -/
  hxnx : x ≠ -x
  /-- the second antipodal pair is genuine (`a ≠ −a`) -/
  hana : a ≠ -a
  /-- `a` is not `x` -/
  hax : a ≠ x
  /-- `a` is not `−x` -/
  hanx : a ≠ -x

/-- The underlying finset `{x, −x, a, −a}` of a double antipodal quadruple. -/
def dquad (x a : F) : Finset F := {x, -x, a, -a}

/-- `x ∉ {−x, a, −a}` (the first insert obligation). -/
private theorem x_notMem {x a : F} (h : DoubleAntipodalQuadruple x a) :
    x ∉ ({-x, a, -a} : Finset F) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨h.hxnx, fun hc => h.hax hc.symm, ?_⟩
  -- x = -a ⟹ a = -x, contradicting hanx
  intro hc
  exact h.hanx (by linear_combination hc)

/-- `−x ∉ {a, −a}` (the second insert obligation). -/
private theorem negx_notMem {x a : F} (h : DoubleAntipodalQuadruple x a) :
    (-x) ∉ ({a, -a} : Finset F) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨fun hc => h.hanx hc.symm, ?_⟩
  -- -x = -a ⟹ a = x, contradicting hax
  intro hc
  exact h.hax (by linear_combination hc)

/-- `a ∉ {−a}` (the third insert obligation). -/
private theorem a_notMem {x a : F} (h : DoubleAntipodalQuadruple x a) :
    a ∉ ({-a} : Finset F) := by
  simp only [Finset.mem_singleton]; exact h.hana

/-- A double antipodal quadruple has exactly 4 elements. -/
theorem dquad_card {x a : F} (h : DoubleAntipodalQuadruple x a) :
    (dquad x a).card = 4 := by
  unfold dquad
  rw [Finset.card_insert_of_notMem (x_notMem h), Finset.card_insert_of_notMem (negx_notMem h),
      Finset.card_insert_of_notMem (a_notMem h), Finset.card_singleton]

/-- **The double-antipodal `e₁` law.** Both antipodal pairs cancel, so `e₁({x,−x,a,−a}) = 0`. This
is the structural marker of stratum B: `e₁ = 0`, hence stratum B is DISJOINT from stratum A (whose
`e₁ = a+b ≠ 0`) and from the bad-scalar producers (`α = −1/e₁` undefined). -/
theorem e1_double_antipodal {x a : F} (h : DoubleAntipodalQuadruple x a) :
    e1 (dquad x a) = 0 := by
  classical
  unfold e1 dquad
  rw [Finset.sum_insert (x_notMem h), Finset.sum_insert (negx_notMem h),
      Finset.sum_insert (a_notMem h), Finset.sum_singleton]
  ring

/-- **The double-antipodal `p₂` law.** `p₂({x,−x,a,−a}) = 2x² + 2a²` (each antipodal pair
contributes `x² + (−x)² = 2x²`). -/
theorem p2_double_antipodal {x a : F} (h : DoubleAntipodalQuadruple x a) :
    p2 (dquad x a) = 2 * x ^ 2 + 2 * a ^ 2 := by
  classical
  unfold p2 dquad
  rw [Finset.sum_insert (x_notMem h), Finset.sum_insert (negx_notMem h),
      Finset.sum_insert (a_notMem h), Finset.sum_singleton]
  ring

/-- **The stratum-B `e₂` identity (key).** For a double antipodal quadruple `{x,−x,a,−a}` over a
field of characteristic `≠ 2`,
`e₂({x,−x,a,−a}) = −x² − a²`.

This is `e₂ = (e₁² − p₂)/2` with `e₁ = 0` and `p₂ = 2x² + 2a²`:
`(0 − (2x²+2a²))/2 = −x² − a²`. Both antipodal pairs contribute `−x²` resp. `−a²` to the pairwise-
product sum, and all cross terms cancel (`x·a + x·(−a) + (−x)·a + (−x)·(−a) = 0`). This is the
stratum-B analogue of the in-tree `e2_antipodal_quadruple` (`= a·b − x²`). -/
theorem e2_double_antipodal (h2 : (2 : F) ≠ 0) {x a : F} (h : DoubleAntipodalQuadruple x a) :
    e2 (dquad x a) = -x ^ 2 - a ^ 2 := by
  rw [e2_eq, e1_double_antipodal h, p2_double_antipodal h]
  rw [div_eq_iff h2]; ring

/-- **The stratum-B `e₂=0` characterization.** A double antipodal quadruple `{x,−x,a,−a}` has
`e₂ = 0` *iff* `a² = −x²` (equivalently `(a/x)² = −1`, so `a/x` is a primitive 4th root of unity,
existing over `μ_n` exactly when `4 ∣ n`, i.e. `a = ζ^{n/4}·x`):
`e₂({x,−x,a,−a}) = 0 ⟺ a² = −x²`.

This is the **codim-1 quadratic locus of stratum B**. Over `μ_n` with `x = ζ^p`, it pins
`a = ζ^{p + n/4}` (the unique square root of `−x²` up to the antipode `−a`); counting these
double-antipodal sets would give an `n/4` stratum-B contribution (that count is not formalized
here, and the width-4 locus need not consist of strata A and B only; see
`not_widthFourDyadicClassified_zmod97`). -/
theorem e2_zero_double_antipodal_iff (h2 : (2 : F) ≠ 0) {x a : F}
    (h : DoubleAntipodalQuadruple x a) :
    e2 (dquad x a) = 0 ↔ a ^ 2 = -x ^ 2 := by
  rw [e2_double_antipodal h2 h]
  constructor
  · intro he; linear_combination -he
  · intro he; linear_combination -he

/-- **Stratum B is `e₁ = 0`, never a bad-scalar witness.** A double antipodal quadruple is fully
negation-closed, so by `e1_double_antipodal` it has `e₁ = 0`; the bad-scalar criterion
`E2VanishEnergy.badScalar_of_energy` requires `e₁ ≠ 0`. Hence stratum B contributes to the `e₂=0`
COUNT but produces **no bad scalar** — it is the silent (`e₁ = 0`) half of the width-4 locus,
consistent with `E2VanishEnergy.no_badScalar_of_neg_closed`. -/
theorem double_antipodal_no_badScalar {x a : F} (h : DoubleAntipodalQuadruple x a) :
    ¬ (e1 (dquad x a) ^ 2 = p2 (dquad x a) ∧ e1 (dquad x a) ≠ 0) :=
  fun ⟨_, hne⟩ => hne (e1_double_antipodal h)

/-! ## The width-4 dichotomy: the two strata are algebraically disjoint

The disjointness of the two antipodal shapes is the `e₁`-value: stratum A has `e₁ = a+b ≠ 0`,
stratum B has `e₁ = 0`. This does **not** say every width-4 `e₂=0` set is in stratum A or B: over
`𝔽_q` there can be antipodal-pair-free `e₂=0` sets (`not_widthFourDyadicClassified_zmod97`), so
no count follows from disjointness alone. We record the disjointness as the abstract statement
that the two strata's `e₁`-values cannot coincide. -/

/-- **The two-strata disjointness (e₁ discriminator).** Stratum B (double antipodal) always has
`e₁ = 0`; any set with `e₁ ≠ 0` is therefore NOT a double antipodal quadruple. So strata A and B
do not overlap; whether they exhaust the width-4 `e₂=0` locus is a separate question (false in
general over `𝔽_q`, see `not_widthFourDyadicClassified_zmod97`). -/
theorem stratum_disjoint_via_e1 {x a : F} (h : DoubleAntipodalQuadruple x a)
    {S : Finset F} (hSeq : S = dquad x a) (hbad : e1 S ≠ 0) : False :=
  hbad (hSeq ▸ e1_double_antipodal h)

/-! ## The conjectural closed form `n(n−3)/4` (arithmetic only)

*If* the width-4 `e₂=0` locus over `μ_n` (`n = 2^μ`) were exactly the disjoint union of the two
strata with the advertised stratum counts, its size would be `n(n−4)/4 + n/4 = n(n−3)/4`. We prove
only the **arithmetic of the closed form** (`Nat`-level). No count theorem is proved: the
exhaustiveness hypothesis `WidthFourDyadicClassified` is false in general over finite fields
(`not_widthFourDyadicClassified_zmod97`), and the stratum counts themselves are not proved here.
In characteristic zero, the analogous statement is expected from the structure of vanishing sums
of `2`-power roots of unity, but that transfer is not formalized and needs a field guard. -/

/-- **The closed-form arithmetic (unconditional `Nat` identity).** For `4 ∣ n` (the dyadic domain
`n = 2^μ`, `μ ≥ 2`): `n(n−4)/4 + n/4 = n(n−3)/4`. Pure `Nat` arithmetic, fully proven. This is
**not** a count of `e₂=0` sets: it would equal the width-4 `e₂=0` count only under a (here
unproved, and over `𝔽_q` in general false) classification with stratum sizes `n(n−4)/4` and
`n/4`; see `not_widthFourDyadicClassified_zmod97`. -/
theorem widthFour_e2zero_count_arith {n : ℕ} (hn : 4 ∣ n) (hn4 : 4 ≤ n) :
    n * (n - 4) / 4 + n / 4 = n * (n - 3) / 4 := by
  obtain ⟨k, rfl⟩ := hn
  have hk : 1 ≤ k := by omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  -- n = 4(1+j); all subtractions are now nonnegative and reduce to addition.
  have hsub4 : 4 * (1 + j) - 4 = 4 * j := by omega
  have hsub3 : 4 * (1 + j) - 3 = 4 * j + 1 := by omega
  rw [hsub4, hsub3]
  -- LHS = 4(1+j)·4j/4 + 4(1+j)/4;  RHS = 4(1+j)·(4j+1)/4
  have hA : 4 * (1 + j) * (4 * j) / 4 = (1 + j) * (4 * j) := by
    rw [show 4 * (1 + j) * (4 * j) = 4 * ((1 + j) * (4 * j)) by ring,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  have hB : 4 * (1 + j) / 4 = 1 + j := by
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  have hC : 4 * (1 + j) * (4 * j + 1) / 4 = (1 + j) * (4 * j + 1) := by
    rw [show 4 * (1 + j) * (4 * j + 1) = 4 * ((1 + j) * (4 * j + 1)) by ring,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  rw [hA, hB, hC]
  ring

/-- **The width-4 antipodal-pair classification (named hypothesis; FALSE in general over
`𝔽_q`).** The predicate says: every width-4 subset of `μ_n` with `e₂ = 0` contains at least one
antipodal pair `{ζ, −ζ}`.

Over a finite field this is **not** automatic for dyadic `μ_n`:
`not_widthFourDyadicClassified_zmod97` refutes it for `μ₃₂ ⊂ 𝔽₉₇` with the set `{1, 8, 27, 55}`.
The earlier probe (`probe_noantip.py`: 0 exceptions for `n = 8,16,32` in the probe's setting) is
therefore not evidence for arbitrary fields. In characteristic zero the statement is the expected
consequence of the structure of vanishing sums of `2`-power roots of unity (the minimal vanishing
sums are antipodal pairs), and it can transfer to `𝔽_q` only under an additional guard (e.g. a
prime large enough that no spurious cyclotomic-norm divisibility occurs). Neither the
characteristic-zero statement nor a guarded transfer is proved here, and even with this
hypothesis no count theorem is stated in this file. -/
def WidthFourDyadicClassified (μ_n : Finset F) : Prop :=
  ∀ S ⊆ μ_n, S.card = 4 → e2 S = 0 →
    (∃ ζ ∈ S, ζ ≠ 0 ∧ -ζ ∈ S)

/-! ## Refutation of the classification over `𝔽₉₇` (PG-234)

`μ₃₂ ⊂ 𝔽₉₇` is a proper dyadic subgroup (index 3). The set `{1, 8, 27, 55}` lies in it, has
`e₂ = 2231 = 23·97 ≡ 0`, and contains no antipodal pair (the negatives `96, 89, 70, 42` are not
in the set). Hence `WidthFourDyadicClassified` fails there. -/

section Refutation

private theorem fact_prime_97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

attribute [local instance] fact_prime_97

/-- The antipodal-pair-free `e₂ = 0` four-set in `μ₃₂ ⊂ 𝔽₉₇`. -/
def widthFourCounter97 : Finset (ZMod 97) := {1, 8, 27, 55}

theorem widthFourCounter97_roots : ∀ x ∈ widthFourCounter97, x ^ 32 = 1 := by decide

theorem widthFourCounter97_card : widthFourCounter97.card = 4 := by decide

theorem widthFourCounter97_e2 : e2 widthFourCounter97 = 0 := by
  have h1 : e1 widthFourCounter97 = 91 := by decide
  have h2 : p2 widthFourCounter97 = 36 := by decide
  rw [e2_eq, h1, h2, show (91 : ZMod 97) ^ 2 - 36 = 0 by decide, zero_div]

theorem widthFourCounter97_no_antipode :
    ¬ ∃ x ∈ widthFourCounter97, x ≠ 0 ∧ -x ∈ widthFourCounter97 := by decide

/-- **`WidthFourDyadicClassified` is false for `μ₃₂ ⊂ 𝔽₉₇`.** Kernel-checked counterexample
`{1, 8, 27, 55}`; the hypothesis behind the conjectural count `n(n−3)/4` does not hold for every
dyadic subgroup of a finite field. -/
theorem not_widthFourDyadicClassified_zmod97 :
    ¬ WidthFourDyadicClassified (Polynomial.nthRootsFinset 32 (1 : ZMod 97)) := by
  intro h
  apply widthFourCounter97_no_antipode
  apply h widthFourCounter97
  · intro x hx
    rw [Polynomial.mem_nthRootsFinset (by decide : 0 < 32)]
    exact widthFourCounter97_roots x hx
  · exact widthFourCounter97_card
  · exact widthFourCounter97_e2

end Refutation

end ArkLib.ProximityGap.E2VanishWidthFourFullCount

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.dquad_card
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.e1_double_antipodal
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.p2_double_antipodal
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.e2_double_antipodal
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.e2_zero_double_antipodal_iff
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.double_antipodal_no_badScalar
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.stratum_disjoint_via_e1
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.widthFour_e2zero_count_arith
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.not_widthFourDyadicClassified_zmod97
