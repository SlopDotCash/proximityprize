/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2VanishEnergy
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal
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

In **characteristic zero** the classification does hold for every dyadic `μ_{2^k}`:
`widthFourDyadicClassified_charZero` (below) derives it from the in-tree Lam–Leung theorem
`LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero`. This proves the classification only;
it is not a cardinality statement.

The in-tree `E2VanishWidthFourLaw` treats the **one-antipodal-pair** shape: a quadruple
`{x,−x,a,b}` with `a·b = x²`, `a+b ≠ 0`, all with `e₁ ≠ 0` (the genuine bad-scalar producers).
That is only PART of the `e₂=0` locus at width 4.

This file treats the **complementary shape** — the **two-antipodal-pair** quadruples. Together
with the classification (proved here only in characteristic zero) and the two stratum counts (not
proved), these two shapes would give the full width-4 count; the count below is a
conjecture/probe readout, not a theorem.

## The cyclic-sieving readout (conjectural; NOT a theorem over finite fields)

Identify `μ_n` (`n = 2^μ`) with `ℤ/n` by exponents. *If* every width-4 `e₂=0` subset of `μ_n`
contains an antipodal pair (the hypothesis `WidthFourDyadicClassified`, false in general over
`𝔽_q` but true in characteristic zero; see the status note above), then such a subset has one of
two structural shapes:

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
refutes for `μ₃₂ ⊂ 𝔽₉₇` and proves for `μ_{2^k}` in characteristic zero.

The shape identities are pure field algebra (`e₂ = (e₁² − p₂)/2` for the explicit 4-set),
q-independent, no character sum. The statement "at width 4 every `e₂=0` set is one of the two
antipodal shapes" is **not** q-independent: it fails in `μ₃₂ ⊂ 𝔽₉₇`.

## Honest scope

Proved here: the stratum-B identities, the stratum disjointness via `e₁`, the `Nat` identity
`n(n−4)/4 + n/4 = n(n−3)/4`, the refutation `not_widthFourDyadicClassified_zmod97`, and the
characteristic-zero classification `widthFourDyadicClassified_charZero`. Not proved: any
cardinality statement for the width-4 `e₂=0` locus, in particular the formula `n(n−3)/4`, and
any guarded transfer of the classification to `𝔽_q`.
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
In characteristic zero the classification itself is proved (`widthFourDyadicClassified_charZero`),
but the stratum counts are still missing there, and any transfer to `𝔽_q` needs a field guard. -/

/-- **The closed-form arithmetic (unconditional `Nat` identity).** For `4 ∣ n` (the dyadic domain
`n = 2^μ`, `μ ≥ 2`): `n(n−4)/4 + n/4 = n(n−3)/4`. Pure `Nat` arithmetic, fully proven. This is
**not** a count of `e₂=0` sets: it would equal the width-4 `e₂=0` count only under the
classification (proved here in characteristic zero, false in general over `𝔽_q`; see
`not_widthFourDyadicClassified_zmod97`) together with the stratum sizes `n(n−4)/4` and `n/4`,
which are not proved. -/
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
therefore not evidence for arbitrary fields. In characteristic zero the statement holds for every
`μ_{2^k}` (`widthFourDyadicClassified_charZero`, from the structure of vanishing sums of `2`-power
roots of unity), and it can transfer to `𝔽_q` only under an additional guard (e.g. a prime large
enough that no spurious cyclotomic-norm divisibility occurs). A guarded transfer is not proved
here, and no count theorem is stated in this file. -/
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

/-! ## The classification in characteristic zero

In characteristic zero, Lam–Leung for `2`-power roots of unity
(`LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero`: a vanishing multiset sum of `2^k`-th
roots of unity is antipodally balanced) applies to the six pairwise products of an `e₂=0`
four-subset of `μ_{2^k}`. A case analysis on two balance witnesses then yields an antipodal pair
inside the set. The case analysis is the multiplicative analogue, with `h = −1`, of the
exponent-side `WindowTwoLayer.antipodal_pair_of_balanced` (`BalancedFourLaw`). -/

section CharZero

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

/-- **Antipodal pair from balanced pairwise products.** Let `a, b, c, d` be nonzero elements of a
field of characteristic zero with `b ≠ c`. If the multiset `{ab, ac, ad, bc, bd, cd}` of their
pairwise products is antipodally balanced (`count z = count (−z)` for every `z`), then two of
`a, b, c, d` are antipodal. -/
theorem antipodal_pair_of_balanced_products {a b c d : L}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hbc : b ≠ c)
    (hbal : ∀ z : L, ({a * b, a * c, a * d, b * c, b * d, c * d} : Multiset L).count z
      = ({a * b, a * c, a * d, b * c, b * d, c * d} : Multiset L).count (-z)) :
    a = -b ∨ a = -c ∨ a = -d ∨ b = -c ∨ b = -d ∨ c = -d := by
  set M : Multiset L := {a * b, a * c, a * d, b * c, b * d, c * d} with hM
  have hneg_mem : ∀ z ∈ M, -z ∈ M := by
    intro z hz
    have h1 : 0 < M.count z := Multiset.count_pos.mpr hz
    rw [hbal z] at h1
    exact Multiset.count_pos.mp h1
  have hne_self : ∀ z : L, z ≠ 0 → -z ≠ z := by
    intro z hz h
    have : (2 : L) * z = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h2 | h2
    · exact two_ne_zero h2
    · exact hz h2
  have k_ab := hneg_mem (a * b) (by rw [hM]; simp)
  have k_ac := hneg_mem (a * c) (by rw [hM]; simp)
  simp only [hM, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at k_ab k_ac
  by_contra hG
  simp only [not_or] at hG
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hG
  -- `x * (y + w) = 0` with `x ≠ 0` forces `y = -w`
  have cancel : ∀ x y w : L, x ≠ 0 → x * (y + w) = 0 → y = -w := by
    intro x y w hx h
    have := (mul_eq_zero.mp h).resolve_left hx
    linear_combination this
  rcases k_ab with h | h | h | h | h | hx1
  · exact hne_self _ (mul_ne_zero ha hb) h
  · exact h4 (cancel a b c ha (by linear_combination -h))
  · exact h5 (cancel a b d ha (by linear_combination -h))
  · exact h2 (cancel b a c hb (by linear_combination -h))
  · exact h3 (cancel b a d hb (by linear_combination -h))
  · rcases k_ac with h | h | h | h | h | hx2
    · exact h4 (cancel a b c ha (by linear_combination -h))
    · exact hne_self _ (mul_ne_zero ha hc) h
    · exact h6 (cancel a c d ha (by linear_combination -h))
    · exact h1 (cancel c a b hc (by linear_combination -h))
    · -- `-ac = bd` and `-ab = cd` give `d·(c - b)·(c + b) = 0`, so `b = -c`
      have e : d * ((c - b) * (c + b)) = 0 := by linear_combination b * h - c * hx1
      have hcb := (mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hd)).resolve_left
        (sub_ne_zero.mpr (Ne.symm hbc))
      exact h4 (by linear_combination hcb)
    · exact h3 (cancel c a d hc (by linear_combination -hx2))

/-- **`WidthFourDyadicClassified` holds for every dyadic `μ_{2^k}` in characteristic zero.** Every
four-subset `S ⊆ μ_{2^k}` with `e₂(S) = 0` contains an antipodal pair `{ζ, −ζ}`. Since `2 ≠ 0`,
`e₂(S) = 0` says that the six pairwise products, all `2^k`-th roots of unity, sum to zero;
Lam–Leung (`LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero`) makes that multiset
antipodally balanced, and `antipodal_pair_of_balanced_products` extracts the pair. This is the
characteristic-zero counterpart of `not_widthFourDyadicClassified_zmod97`; it says nothing about
`𝔽_q` and proves no count. -/
theorem widthFourDyadicClassified_charZero (k : ℕ) :
    WidthFourDyadicClassified (Polynomial.nthRootsFinset (2 ^ k) (1 : L)) := by
  intro S hS hcard he2
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hroot : ∀ w ∈ S, w ^ (2 ^ k) = 1 := fun w hw =>
    (Polynomial.mem_nthRootsFinset hpos (1 : L)).mp (hS hw)
  have hnz : ∀ w ∈ S, w ≠ 0 := by
    intro w hw h0
    have := hroot w hw
    rw [h0, zero_pow (Nat.pos_iff_ne_zero.mp hpos)] at this
    exact zero_ne_one this
  obtain ⟨a, t, hat, rfl, ht⟩ := Finset.card_eq_succ.mp hcard
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp ht
  have ha := hnz a (by simp)
  have hb := hnz b (by simp)
  have hc := hnz c (by simp)
  have hd := hnz d (by simp)
  -- `e₂ = 0` ⇒ the six pairwise products sum to zero
  have he1 : e1 (insert a {b, c, d}) = a + b + c + d := by
    unfold e1
    rw [Finset.sum_insert hat, Finset.sum_insert (by simp [hbc, hbd]),
      Finset.sum_insert (by simp [hcd]), Finset.sum_singleton]
    ring
  have hp2 : p2 (insert a {b, c, d}) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
    unfold p2
    rw [Finset.sum_insert hat, Finset.sum_insert (by simp [hbc, hbd]),
      Finset.sum_insert (by simp [hcd]), Finset.sum_singleton]
    ring
  rw [e2_eq, he1, hp2] at he2
  have hsum6 : a * b + a * c + a * d + b * c + b * d + c * d = 0 := by
    have h2 : (a + b + c + d) ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) = 0 := by
      rcases div_eq_zero_iff.mp he2 with h | h
      · exact h
      · exact absurd h two_ne_zero
    have : (2 : L) * (a * b + a * c + a * d + b * c + b * d + c * d) = 0 := by
      linear_combination h2
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  set M : Multiset L := {a * b, a * c, a * d, b * c, b * d, c * d} with hM
  have hMroot : ∀ z ∈ M, z ^ (2 ^ k) = 1 := by
    have hr : ∀ x ∈ ({a, b, c, d} : Finset L), x ^ (2 ^ k) = 1 := by
      intro x hx
      exact hroot x (by simpa using hx)
    have ra := hr a (by simp)
    have rb := hr b (by simp)
    have rc := hr c (by simp)
    have rd := hr d (by simp)
    intro z hz
    simp only [hM, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mul_pow, ra, rb, rc, rd]
  have hMsum : M.sum = 0 := by
    rw [hM]
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
    linear_combination hsum6
  have hbal := LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero hMroot hMsum
  rcases antipodal_pair_of_balanced_products ha hb hc hd hbc hbal with h | h | h | h | h | h
  · exact ⟨b, by simp, hb, by simp [← h]⟩
  · exact ⟨c, by simp, hc, by simp [← h]⟩
  · exact ⟨d, by simp, hd, by simp [← h]⟩
  · exact ⟨c, by simp, hc, by simp [← h]⟩
  · exact ⟨d, by simp, hd, by simp [← h]⟩
  · exact ⟨d, by simp, hd, by simp [← h]⟩

end CharZero

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
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.antipodal_pair_of_balanced_products
#print axioms ArkLib.ProximityGap.E2VanishWidthFourFullCount.widthFourDyadicClassified_charZero
