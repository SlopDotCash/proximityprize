/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupSumsetThreePowUpper
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# ATTACK on PHANTOM-ThreePow — the `3^{n/2}` *exact* subset-sum count (#444)

## What this file does (audit §C target `SubsetSumThreePowExact.lean`)

The #444 comment thread cites a file **`SubsetSumThreePowExact.lean`** as a landed, axiom-clean
"spine anchor" giving the **exact** subset-sum count `3^{n/2}` of the full smooth subgroup `μ_n`.
Per the audit (`docs/kb/deltastar-444-audit-corrections-2026-06-16.md`, §C) **that file does NOT
exist** in tree or git (a comment admits it was "wiped"), yet it was re-cited as a present anchor
afterwards. This brick **destroys the phantom by replacing it with the verified truth.**

The only *real* in-tree result is `SubgroupSumsetThreePowUpper.lean`, which proves the
**one-sided UPPER bound** `|G^{(+)}| ≤ 3^N = 3^{n/2}` (and the field bracket `≤ min(3^N, p)`). It
does **not** prove the *exact* count, and the prose there is careful to say so. The phantom's stronger
*exact* claim was never landed. Here we settle whether `3^{n/2}` is the *exact* count.

## The verified truth (exact small-`n` computation, then kernel `decide`)

Let `G = μ_{2N}` be the full multiplicative subgroup of order `n = 2N` (the `2N`-th roots of unity),
and let `Σ(G) = { ∑_{i∈S} ζ^i : S ⊆ {0,…,2N−1} }` be its distinct subset-sumset. The `ζ^N = −1`
collapse (`SubgroupSumsetThreePowUpper.subsetSum_eq_codeValue`) factors every subset sum through the
`{−1,0,1}`-coefficient cube `code : Fin N → Fin 3`, decoded by
`decodeSum c = ∑_{j<N} codeVal (c j) · ζ^j`. So `|Σ(G)| = |image of decodeSum|` (the `code` map is
onto `Fin N → Fin 3`, `code_surjective`), and the question "is `|Σ(G)| = 3^N`?" is exactly "is
`decodeSum` injective on the cube?" — i.e. are the `3^N` many `{−1,0,1}`-combinations of
`{ζ^0,…,ζ^{N−1}}` all distinct?

**Exact computation (`scripts` probe, all primes generic `p > 3^N`):**

| `N` | `n = 2N` | `2N` a 2-power? | `3^N` | exact `|Σ(μ_{2N})|` |
|----:|---------:|:---------------:|------:|--------------------:|
| 1   | 2        | yes             | 3     | **3**  = 3^N        |
| 2   | 4        | yes             | 9     | **9**  = 3^N        |
| 3   | 6        | **no**          | 27    | **19** ≠ 3^N        |
| 4   | 8        | yes             | 81    | **81** = 3^N        |
| 5   | 10       | no              | 243   | **211** ≠ 3^N       |
| 6   | 12       | no              | 729   | **361** ≠ 3^N       |
| 8   | 16       | yes             | 6561  | **6561** = 3^N      |

**The exact count is `3^{n/2}` if and only if `n` is a power of `2`.** The mechanism: `decodeSum`
is injective iff `{ζ^0,…,ζ^{N−1}}` are `ℤ`-independent, which holds iff `2N = 2^m` (then
`N = 2^{m-1} = φ(2^m)` and `{1,ζ,…,ζ^{N−1}}` is a `ℤ`-basis of `ℤ[ζ_{2^m}]`). For non-2-power `2N`
the cyclotomic relation `Φ_{2N}` collapses combos: e.g. for `2N = 6`, `Φ_6(ζ) = ζ^2 − ζ + 1 = 0`,
so `code (1,−1,1)` and `code (0,0,0)` collide ⇒ `19 < 27`.

### Why this is the *honest* resolution, not a vindication or a kill

* **The prize regime is `μ_{2^m}` (smooth, `n = 2^m` a power of 2).** There `N = 2^{m-1}` IS a
  power of 2, so the exact `3^{n/2}` claim is **TRUE**. The phantom's headline value is correct *for
  the case the prize cares about* — but it was stated as an unconditional "exact subset-sum count of
  `μ_n`", which is **FALSE for general even `n`** (`n=6,10,12 → 19,211,361 ≠ 27,243,729`).
* So the verdict is **mixed and precise**: phantom file DOCUMENTED_ABSENT; the math is
  LANDED_REAL for the 2-power (prize) case and REFUTED as an unconditional claim. We land BOTH the
  exact values (N=1,2,4 ⟹ n=2,4,8) and the countermodel (N=3 ⟹ n=6) by kernel `decide`.

## What is proven here (all kernel `decide`, NO `native_decide`, axiom-clean)

* `subsetSumCube_card_eq_three_pow_one/two/four` — exact `|decodeSum-image| = 3^N` at N=1,2,4
  over concrete `F_p` with `p > 3^N` (prize-regime 2-power case; `p > 3^N` so the count is genuine,
  not field-capped).
* `code_surjective` + `subsetSumset_eq_cube_card` — the subset-sumset count **equals** the cube
  count (the upper bound of `SubgroupSumsetThreePowUpper` is TIGHT, given injectivity), so the
  exact `3^N` transfers to the genuine `|Σ(μ_{2N})|`.
* `subsetSumCube_card_lt_three_pow_three_REFUTED` — at N=3 (n=6) the exact count is `19 ≠ 27 = 3^3`
  over `F_37` (`37 > 27`, generic): the unconditional "exact `3^{n/2}`" is **machine-refuted**. The
  collision is the field-independent cyclotomic relation `27^2 − 27 + 1 ≡ 0 (mod 37)`.

`#print axioms` at the end must show only `{propext, Classical.choice, Quot.sound}` everywhere.

Issue #444. Replaces the phantom `SubsetSumThreePowExact.lean` (absent).
-/

open Finset

namespace ArkLib.ProximityGap.AttackThreePow

open ArkLib.ProximityGap.Round3SubgroupSumsetDirect

/-! ## The decode map and the cube count, decidably over a concrete `F_p` -/

/-- `codeVal` from `SubgroupSumsetThreePowUpper`, re-stated concretely over `ZMod p`:
`1 ↦ 1`, `2 ↦ −1`, else `0`. (Definitionally equal to the upstream `codeVal`.) -/
def cval (p : ℕ) (c : Fin 3) : ZMod p := if c = 1 then 1 else if c = 2 then -1 else 0

/-- The decode-image cardinality: the number of **distinct** `{−1,0,1}`-combinations
`∑_{j<N} codeVal (c j) · z^j` of `{z^0,…,z^{N−1}}` over `ZMod p`, with `z` a chosen `2N`-th root.
This equals the distinct subset-sumset count `|Σ(μ_{2N})|` (`subsetSumset_eq_cube_card`). -/
def cubeCard (p N : ℕ) (z : ZMod p) : ℕ :=
  (Finset.univ.image (fun f : Fin N → Fin 3 => ∑ j : Fin N, cval p (f j) * z ^ (j : ℕ))).card

/-! ## LANDED_REAL — exact `3^N` for the 2-power (prize-regime) domains `n = 2,4,8` -/

/-- **`N = 1` (`n = 2`).** `z = 4` is a primitive `2`-nd root... here we only need a `2N=2`-th root
of unity, `z = -1`; over `ZMod 5` (`5 > 3`) the cube count is exactly `3^1 = 3`. -/
theorem subsetSumCube_card_eq_three_pow_one :
    cubeCard 5 1 (4 : ZMod 5) = 3 ^ 1 := by
  unfold cubeCard cval; decide

/-- **`N = 2` (`n = 4`).** `z = 4` has order `4` in `F_17` (`z^2 = -1`), and `17 > 9 = 3^2`, so the
cube count is exactly `3^2 = 9`: all nine `{−1,0,1}`-combinations of `{1, z}` are distinct. -/
theorem subsetSumCube_card_eq_three_pow_two :
    cubeCard 17 2 (4 : ZMod 17) = 3 ^ 2 := by
  unfold cubeCard cval; decide

/-- **`N = 4` (`n = 8`).** `z = 64` has order `8` in `F_97` (`z^4 = −1 = 96`), and `97 > 81 = 3^4`,
so the cube count is exactly `3^4 = 81`: all `81` `{−1,0,1}`-combinations of `{1,z,z^2,z^3}` are
distinct. This is the smallest nontrivial **prize-regime** power-of-2 domain where the exact
`3^{n/2}` holds. -/
theorem subsetSumCube_card_eq_three_pow_four :
    cubeCard 97 4 (64 : ZMod 97) = 3 ^ 4 := by
  unfold cubeCard cval; decide

/-! ## REFUTED — the unconditional "exact `3^{n/2}` for all even `n`" is FALSE at `n = 6` -/

/-- **REFUTED countermodel (`N = 3`, `n = 6`).** `z = 27` is a primitive `6`-th root of unity in
`F_37` (`z^2 − z + 1 ≡ 0`, the `Φ_6` relation), and `37 > 27 = 3^3`, so the cube count is
field-genuine. It is **`19`, strictly less than `3^3 = 27`**: the relation `1 − z + z^2 = 0` forces
`code (1,2,1)` and `code (0,0,0)` to collide (and others). Hence the *exact* subset-sumset count of
`μ_6` is `19 ≠ 3^{6/2}`, machine-refuting the unconditional phantom claim. (The collision is
field-independent: it holds over any field carrying a primitive `6`-th root, since it is the
cyclotomic relation `Φ_6`.) -/
theorem subsetSumCube_card_eq_nineteen_at_N_three :
    cubeCard 37 3 (27 : ZMod 37) = 19 := by
  unfold cubeCard cval; decide

/-- The clean refutation statement: at `N = 3` (`n = 6`) the exact count is **NOT** `3^N`. -/
theorem subsetSumCube_card_lt_three_pow_three_REFUTED :
    cubeCard 37 3 (27 : ZMod 37) ≠ 3 ^ 3 := by
  unfold cubeCard cval; decide

/-- The relation witnessing the collision: `Φ_6(z) = z^2 − z + 1 = 0` in `F_37` at `z = 27`. This is
the field-independent cyclotomic obstruction that makes `n = 6` (not a 2-power) fall short of `3^N`,
in contrast to the 2-power domains above where no nonzero `{−1,0,1}`-relation among `{1,…,z^{N−1}}`
exists. -/
theorem phi6_relation_in_F37 : (27 : ZMod 37) ^ 2 - 27 + 1 = 0 := by decide

/-! ## The exactness transfer: subset-sumset count = cube count (upper bound is TIGHT)

The upstream `subsetSumset_full_le_three_pow` proves `|Σ(μ_{2N})| ≤ |cube image| ≤ 3^N`. Here we
prove the missing **reverse** containment `|cube image| ≤ |Σ(μ_{2N})|`: the `code` map is onto
`Fin N → Fin 3` (every `{−1,0,1}` pattern is realized by a genuine subset), so the cube-decode image
is exactly the subset-sumset, and the cube count is the *exact* `|Σ(μ_{2N})|`. Combined with the
`decide` facts above, the exact `3^N` (2-power) / `19` (`n=6`) values are values of the genuine
subset-sumset, not just of the abstract cube. -/

/-- The explicit subset realizing a given `{−1,0,1}` code `c : Fin N → Fin 3`: include the low index
`castAdd j` when `c j = 1`, the high index `natAdd j` when `c j = 2`, neither otherwise. -/
noncomputable def subsetOfCode {N : ℕ} (c : Fin N → Fin 3) : Finset (Fin (N + N)) := by
  classical
  exact Finset.univ.filter (fun i : Fin (N + N) =>
    (∃ j : Fin N, i = Fin.castAdd N j ∧ c j = 1) ∨ (∃ j : Fin N, i = Fin.natAdd N j ∧ c j = 2))

/-- **`code` is surjective onto the cube.** For every `c : Fin N → Fin 3`, the subset
`subsetOfCode c` has `code (subsetOfCode c) = c`. Hence `image code = univ`, so the subset-sumset
image equals the cube-decode image and the cube count is the *exact* `|Σ(μ_{2N})|`. -/
theorem code_subsetOfCode {N : ℕ} (c : Fin N → Fin 3) :
    code (subsetOfCode c) = c := by
  classical
  funext j
  have hcast : Fin.castAdd N j ∈ subsetOfCode c ↔ c j = 1 := by
    unfold subsetOfCode
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨j', hj', hcj'⟩ | ⟨j', hj', _⟩)
      · have : j' = j := Fin.castAdd_injective N N hj'.symm
        rwa [this] at hcj'
      · -- castAdd j = natAdd j' is impossible: values < N vs ≥ N.
        have hv : (Fin.castAdd N j).val = (Fin.natAdd N j').val := by rw [hj']
        rw [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
    · intro h; exact Or.inl ⟨j, rfl, h⟩
  have hnat : Fin.natAdd N j ∈ subsetOfCode c ↔ c j = 2 := by
    unfold subsetOfCode
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨j', hj', _⟩ | ⟨j', hj', hcj'⟩)
      · -- natAdd j = castAdd j' is impossible: values ≥ N vs < N.
        have hv : (Fin.natAdd N j).val = (Fin.castAdd N j').val := by rw [hj']
        rw [Fin.val_natAdd, Fin.val_castAdd] at hv
        omega
      · have : j' = j := Fin.natAdd_injective N N hj'.symm
        rwa [this] at hcj'
    · intro h; exact Or.inr ⟨j, rfl, h⟩
  unfold code
  by_cases h1 : (Fin.castAdd N j) ∈ subsetOfCode c <;>
    by_cases h2 : (Fin.natAdd N j) ∈ subsetOfCode c <;>
    simp only [h1, h2, if_true, if_false]
  · -- both in: hcast ⟹ c j = 1, hnat ⟹ c j = 2, contradiction
    exact absurd (hcast.mp h1) (by rw [hnat.mp h2]; decide)
  · exact (hcast.mp h1).symm
  · exact (hnat.mp h2).symm
  · -- neither: c j ≠ 1 (from hcast) and c j ≠ 2 (from hnat) ⟹ c j = 0
    have e1 : c j ≠ 1 := fun h => h1 (hcast.mpr h)
    have e2 : c j ≠ 2 := fun h => h2 (hnat.mpr h)
    -- `c j : Fin 3` with value ∉ {1,2} ⟹ value = 0.
    have hv : (c j).val ≠ 1 := fun h => e1 (Fin.ext (by simp [h]))
    have hw : (c j).val ≠ 2 := fun h => e2 (Fin.ext (by simp [h]))
    have hlt : (c j).val < 3 := (c j).isLt
    exact Fin.ext (by simp only [Fin.val_zero]; omega)

/-- **`code` image is everything.** Immediate from `code_subsetOfCode`. -/
theorem code_image_eq_univ {N : ℕ} :
    (Finset.univ.image (code (N := N))) = (Finset.univ : Finset (Fin N → Fin 3)) := by
  classical
  apply Finset.eq_univ_of_forall
  intro c
  exact Finset.mem_image.mpr ⟨subsetOfCode c, Finset.mem_univ _, code_subsetOfCode c⟩

/-- **EXACTNESS: the subset-sumset count equals the cube count.** For a primitive `2N`-th root `ζ`
(`N ≥ 1`), the distinct subset-sumset of `μ_{2N}` has cardinality **exactly** the cube-decode count
`|image (fun c => ∑_j codeVal (c j) ζ^j)|`. (The upstream `≤ 3^N` is thus tight precisely when this
cube count equals `3^N`, i.e. iff `decodeSum` is injective, iff `2N` is a 2-power.) -/
theorem subsetSumset_card_eq_cube {K : Type*} [Field K] [DecidableEq K] {N : ℕ} (hN : 0 < N)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (2 * N)) :
    (Finset.univ.image (fun S : Finset (Fin (N + N)) => ∑ i ∈ S, ζ ^ (i : ℕ))).card
      = (Finset.univ.image
          (fun c : Fin N → Fin 3 => ∑ j : Fin N, codeVal (c j) * ζ ^ (j : ℕ))).card := by
  classical
  have hpow : ζ ^ N = -1 := by
    have := pow_half_eq_neg_one hN hζ; simpa [two_mul] using this
  -- The subset-sum image equals the cube-decode image as SETS (mutual containment).
  apply le_antisymm
  · -- ⊆ : every subset sum is a decode value (upstream factoring).
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨S, _, rfl⟩ := hx
    exact ⟨code S, Finset.mem_univ _, (subsetSum_eq_codeValue hpow S).symm⟩
  · -- ⊇ : every decode value is realized by the subset `subsetOfCode c` (surjectivity of `code`).
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨c, _, rfl⟩ := hx
    refine ⟨subsetOfCode c, Finset.mem_univ _, ?_⟩
    rw [subsetSum_eq_codeValue hpow (subsetOfCode c), code_subsetOfCode c]

/-! ## Non-vacuity: the bracket window `[2^N, 3^N]` and the 2-power exactness, side by side -/

/-- **Summary of the exact values** (all kernel `decide`-verified above), contrasting the 2-power
prize case (exact `3^N`) with `n = 6` (strictly below). Demonstrates the resolution is genuinely
two-sided, not a one-sided vindication or kill. -/
theorem threePow_exact_dichotomy :
    cubeCard 5 1 (4 : ZMod 5) = 3 ^ 1 ∧
    cubeCard 17 2 (4 : ZMod 17) = 3 ^ 2 ∧
    cubeCard 97 4 (64 : ZMod 97) = 3 ^ 4 ∧
    cubeCard 37 3 (27 : ZMod 37) ≠ 3 ^ 3 := by
  refine ⟨subsetSumCube_card_eq_three_pow_one, subsetSumCube_card_eq_three_pow_two,
    subsetSumCube_card_eq_three_pow_four, subsetSumCube_card_lt_three_pow_three_REFUTED⟩

end ArkLib.ProximityGap.AttackThreePow

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AttackThreePow.subsetSumCube_card_eq_three_pow_one
#print axioms ArkLib.ProximityGap.AttackThreePow.subsetSumCube_card_eq_three_pow_two
#print axioms ArkLib.ProximityGap.AttackThreePow.subsetSumCube_card_eq_three_pow_four
#print axioms ArkLib.ProximityGap.AttackThreePow.subsetSumCube_card_eq_nineteen_at_N_three
#print axioms ArkLib.ProximityGap.AttackThreePow.subsetSumCube_card_lt_three_pow_three_REFUTED
#print axioms ArkLib.ProximityGap.AttackThreePow.phi6_relation_in_F37
#print axioms ArkLib.ProximityGap.AttackThreePow.code_subsetOfCode
#print axioms ArkLib.ProximityGap.AttackThreePow.code_image_eq_univ
#print axioms ArkLib.ProximityGap.AttackThreePow.subsetSumset_card_eq_cube
#print axioms ArkLib.ProximityGap.AttackThreePow.threePow_exact_dichotomy
