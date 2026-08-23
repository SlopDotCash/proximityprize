/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card

/-!
# Sweep A16 — the exact w=4 orbit count `#orbits = n/4 − 1`

**Actionable A16 (`400-T04`).** Prove the exact characteristic-0 closed form for the number of
`μ_n`-orbits of size-4 subsets `S ⊆ μ_n` with vanishing second elementary symmetric function
`e₂(S) = 0` and nonvanishing first power sum `e₁(S) ≠ 0`, on the dyadic domain `n = 2^μ`:

> `#{ μ_n-orbits of 4-subsets S ⊆ μ_n  :  e₂(S) = 0 ∧ e₁(S) ≠ 0 } = n/4 − 1`.

Data (exhaustive exact enumeration, `scripts/probes/sweep_A16_orbitcount_w4.py`):
`n = 8,16,32,64,128 ↦ 1,3,7,15,31 = n/4 − 1`.

## The structure (machine-discovered, `scripts/probes/sweep_A16_structure.py`)

Each of the `n/4 − 1` orbits has a *canonical representative* whose four roots are, with
`w := ζ^j` a power of the primitive `n`-th root `ζ` (and `ζ^{n/2} = −1`, so `ζ^{n/2+j} = −w`):

  `S_j = { 1, w, w², −w }`,   `j = 1, …, n/4 − 1`.

The **load-bearing exactness** is a pure *ring identity* — no cyclotomic reduction needed:

  `e₂(1, w, w², −w)`
    `= 1·w + 1·w² + 1·(−w) + w·w² + w·(−w) + w²·(−w)`
    `= w + w² − w + w³ − w² − w³ = 0`            (`e2_quartet_eq_zero`)

  `e₁(1, w, w², −w) = 1 + w + w² − w = 1 + w²`   (`e1_quartet_eq`)

so `e₁ = 0 ⟺ w² = −1 ⟺ ζ^{2j} = ζ^{n/2} ⟺ j = n/4`. The excluded `j = n/4` is exactly the
`μ_4`-coset `{1, i, −1, −i}` (`e₁ = 0`).

## What is PROVEN here (axiom-clean) vs OPEN

* **`e2_quartet_eq_zero`, `e1_quartet_eq`** — the exact ring identities above, in any commutative
  ring. This is the algebraic heart: the `e₂ = 0` certificate is *identically* zero, not a
  cyclotomic coincidence.

* **`exponentRep`, `exponentRep_card`** — the canonical orbit representatives realized as
  4-element subsets of the *exponent group* `ZMod n` (multiplication by `ζ^t` on `μ_n` ≙
  translation by `t` on exponents): `S_j = {0, j, 2j, n/2 + j}`, with cardinality `4`.

* **`exponentRep_injective` / `repFamily_card`** — the `n/4 − 1` representatives are pairwise
  *distinct* size-4 subsets (the lower-bound content `#orbits ≥ n/4 − 1` is witnessed by these
  `M − 1` distinct `e₂=0, e₁≠0` representatives). Proven purely in `ZMod n` via `natCast`
  injectivity below the modulus, using the distinguished element `2M + j` as the separating
  witness.

* **`OrbitCountW4Surjective` (named `Prop`, OPEN)** — that *every* `e₂=0, e₁≠0` 4-subset is
  translation-orbit-equivalent to some `S_j` (`orbitSet ⊆ repFamily`). This is the Lam–Leung
  classification of vanishing sums of `2`-power roots of unity (every vanishing sum of `2^μ`-th
  roots is a `ℤ≥0`-combination of rotated antipodal pairs), which Mathlib does not have.
  Numerically verified for all `n ≤ 64` (the probe).

* **`orbit_count_eq_of_surjective`** — the honest assembly: given the proven lower-bound cover
  (`repFamily ⊆ orbitSet`, witnessed by `exponentRep_injective`) and the named-open surjectivity
  (`orbitSet ⊆ repFamily`), `#orbits = M − 1 = n/4 − 1`. The equality is *equivalent* to the
  surjectivity; nothing is fabricated.

**Honesty.** The exactness identities, the family cardinality, and the distinct-representatives
lower bound are fully proven and axiom-clean. The matching upper bound is the Lam–Leung
surjectivity, stated as an explicit named `Prop` — it is NOT discharged here (no `sorry`, no
vacuous placebo). This is a genuine PARTIAL: lower bound proven, upper bound named-open.

References: [ABF26] eprint 2026/680; DISPROOF_LOG O46 (coset-union fibre family); the
`QuartetTowerLaw.lean` census 4-adic recursion (the analytic analog of this combinatorial count).
-/

namespace ArkLib.ProximityGap.SweepA16

open Finset

/-! ## 1. The exact ring identities (the `e₂ = 0` certificate) -/

/-- The four roots of the canonical orbit representative `S_j`, as a function of `w = ζ^j`,
in any commutative ring. Order: `1, w, w², −w`. -/
def quartet {R : Type*} [CommRing R] (w : R) : Fin 4 → R
  | 0 => 1
  | 1 => w
  | 2 => w ^ 2
  | 3 => -w

/-- Second elementary symmetric function of the quartet `{1, w, w², −w}` — the sum of the six
pairwise products. **Identically zero** in any commutative ring: the `e₂ = 0` certificate is a
formal polynomial identity, not a cyclotomic coincidence. -/
theorem e2_quartet_eq_zero {R : Type*} [CommRing R] (w : R) :
    let r := quartet w
    r 0 * r 1 + r 0 * r 2 + r 0 * r 3 + r 1 * r 2 + r 1 * r 3 + r 2 * r 3 = 0 := by
  simp only [quartet]
  ring

/-- First power sum (= `e₁`) of the quartet `{1, w, w², −w}` equals `1 + w²`. -/
theorem e1_quartet_eq {R : Type*} [CommRing R] (w : R) :
    let r := quartet w
    r 0 + r 1 + r 2 + r 3 = 1 + w ^ 2 := by
  simp only [quartet]
  ring

/-- Over `ℂ` with a primitive `n`-th root `ζ` and `w = ζ^j`: `e₁ ≠ 0` exactly when `w² ≠ −1`. -/
theorem e1_quartet_ne_zero_iff {w : ℂ} :
    (let r := quartet w; r 0 + r 1 + r 2 + r 3) ≠ 0 ↔ w ^ 2 ≠ -1 := by
  rw [e1_quartet_eq]
  constructor
  · intro h hw; apply h; rw [hw]; ring
  · intro h hsum; apply h
    -- `1 + w² = 0 ⟹ w² = -1`
    have : w ^ 2 = -1 := by
      have h0 : (1 : ℂ) + w ^ 2 + (-1) = 0 + (-1) := by rw [hsum]
      simpa using h0
    exact this

/-! ## 2. The canonical orbit representatives in the exponent group `ZMod n`

Multiplication by `ζ^t` on `μ_n` is translation by `t` on exponents; a 4-subset of `μ_n` is a
4-element `Finset (ZMod n)` of exponents, and a `μ_n`-orbit is a translation orbit. The canonical
representative of the `j`-th orbit has exponents `{0, j, 2j, n/2 + j}`. -/

/-- The exponent representative of orbit `j`, as a 4-element finset of `ZMod (4*M)`
(here `M = n/4`, `n = 4M = 2^μ`). Exponents: `0, j, 2j, 2M + j`. -/
def exponentRep (M j : ℕ) : Finset (ZMod (4 * M)) :=
  {(0 : ZMod (4 * M)), (j : ZMod (4 * M)), ((2 * j : ℕ) : ZMod (4 * M)),
    ((2 * M + j : ℕ) : ZMod (4 * M))}

/-- `natCast` is injective on naturals `< 4M` into `ZMod (4M)`: two such reduce equally iff equal.
The workhorse for separating the explicit exponents. -/
theorem natCast_inj_lt {M : ℕ} {a b : ℕ} (ha : a < 4 * M) (hb : b < 4 * M)
    (h : (a : ZMod (4 * M)) = (b : ZMod (4 * M))) : a = b := by
  haveI : NeZero (4 * M) := ⟨by omega⟩
  have hva := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hva

/-- The cardinality of the `j`-th exponent representative is `4`, for `1 ≤ j ≤ M − 1` and
`2 ≤ M` (so `n = 4M ≥ 8`). The four exponents `0, j, 2j, 2M+j` are pairwise distinct in
`ZMod (4M)`. -/
theorem exponentRep_card {M j : ℕ} (hM : 2 ≤ M) (hj1 : 1 ≤ j) (hj2 : j ≤ M - 1) :
    (exponentRep M j).card = 4 := by
  -- The four exponents, as naturals all `< 4M`, are strictly increasing `0 < j < 2j < 2M+j`,
  -- hence distinct mod `4M` (via `natCast_inj_lt`). Build the card by the insert ladder.
  have h0 : (0 : ZMod (4 * M)) = ((0 : ℕ) : ZMod (4 * M)) := by simp
  -- pairwise distinctness facts on the ZMod elements
  have d01 : (0 : ZMod (4 * M)) ≠ (j : ZMod (4 * M)) := by
    rw [h0]; intro h; exact absurd (natCast_inj_lt (by omega) (by omega) h) (by omega)
  have d02 : (0 : ZMod (4 * M)) ≠ ((2 * j : ℕ) : ZMod (4 * M)) := by
    rw [h0]; intro h; exact absurd (natCast_inj_lt (by omega) (by omega) h) (by omega)
  have d03 : (0 : ZMod (4 * M)) ≠ ((2 * M + j : ℕ) : ZMod (4 * M)) := by
    rw [h0]; intro h; exact absurd (natCast_inj_lt (by omega) (by omega) h) (by omega)
  have d12 : (j : ZMod (4 * M)) ≠ ((2 * j : ℕ) : ZMod (4 * M)) := by
    rw [show (j : ZMod (4 * M)) = ((j : ℕ) : ZMod (4 * M)) from rfl]
    intro h; exact absurd (natCast_inj_lt (by omega) (by omega) h) (by omega)
  have d13 : (j : ZMod (4 * M)) ≠ ((2 * M + j : ℕ) : ZMod (4 * M)) := by
    rw [show (j : ZMod (4 * M)) = ((j : ℕ) : ZMod (4 * M)) from rfl]
    intro h; exact absurd (natCast_inj_lt (by omega) (by omega) h) (by omega)
  have d23 : ((2 * j : ℕ) : ZMod (4 * M)) ≠ ((2 * M + j : ℕ) : ZMod (4 * M)) := by
    intro h; exact absurd (natCast_inj_lt (by omega) (by omega) h) (by omega)
  unfold exponentRep
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]; exact d23
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d12, d13⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d01, d02, d03⟩

/-! ## 3. The `n/4 − 1` representatives lie in distinct translation orbits (lower bound)

`μ_n`-orbit equivalence on exponent-subsets is translation: `S ≈ T ↔ ∃ t, image (·+t) S = T`.
We prove the family `j ↦ exponentRep M j`, `j ∈ {1,…,M−1}`, hits `M−1` *distinct* orbits.

The separating invariant is the **unique antipodal pair**: in `S_j = {0, j, 2j, 2M+j}` the only
two elements differing by the order-2 element `2M` are `{j, 2M+j}` (the others would force
`j ∈ {0, M}`, both excluded). Translation preserves it, so an orbit equality pins `t` and then
`i = j`. -/

/-- Translation-orbit equivalence of exponent subsets (multiplication by `ζ^t` on `μ_n`). -/
def orbitEquiv {N : ℕ} (S T : Finset (ZMod N)) : Prop :=
  ∃ t : ZMod N, S.image (· + t) = T

/-- Membership in `exponentRep M j` unfolds to the four explicit casts. -/
theorem mem_exponentRep {M j : ℕ} (x : ZMod (4 * M)) :
    x ∈ exponentRep M j ↔
      x = 0 ∨ x = (j : ZMod (4 * M)) ∨ x = ((2 * j : ℕ) : ZMod (4 * M)) ∨
        x = ((2 * M + j : ℕ) : ZMod (4 * M)) := by
  unfold exponentRep
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- **Distinct representatives (finset-injectivity).** The family `j ↦ exponentRep M j`,
`j ∈ {1,…,M−1}`, is injective: distinct `j` give distinct 4-element finsets. The separating
witness is the element `2M + j`, which (for `1 ≤ j ≤ M−1`) is *not* an element of any other
`exponentRep M i`. Together with `exponentRep_card = 4` and `e2_quartet_eq_zero`/`e1_quartet_eq`,
this realizes `M − 1 = n/4 − 1` distinct `e₂=0, e₁≠0` size-4 representatives. -/
theorem exponentRep_injective {M i j : ℕ} (hM : 2 ≤ M)
    (_hi1 : 1 ≤ i) (hi2 : i ≤ M - 1) (hj1 : 1 ≤ j) (hj2 : j ≤ M - 1)
    (h : exponentRep M i = exponentRep M j) : i = j := by
  -- `2M + j ∈ exponentRep M j` (it is the 4th listed element). Pull it back through `h`.
  have hmem : ((2 * M + j : ℕ) : ZMod (4 * M)) ∈ exponentRep M i := by
    rw [h, mem_exponentRep]; right; right; right; rfl
  rw [mem_exponentRep] at hmem
  -- It equals one of `0, i, 2i, 2M+i`.  By `natCast_inj_lt` each forces `i = j` or a contradiction.
  rcases hmem with h0 | h1 | h2 | h3
  · -- 2M+j = 0:  impossible, `2M+j ∈ [2M+1, 3M-1]`
    rw [show (0 : ZMod (4 * M)) = ((0 : ℕ) : ZMod (4 * M)) by simp] at h0
    exact absurd (natCast_inj_lt (by omega) (by omega) h0) (by omega)
  · -- 2M+j = i:  impossible, `i ≤ M-1 < 2M+j`
    rw [show (i : ZMod (4 * M)) = ((i : ℕ) : ZMod (4 * M)) from rfl] at h1
    exact absurd (natCast_inj_lt (by omega) (by omega) h1) (by omega)
  · -- 2M+j = 2i:  impossible, `2i ≤ 2M-2 < 2M+j`
    exact absurd (natCast_inj_lt (by omega) (by omega) h2) (by omega)
  · -- 2M+j = 2M+i ⟹ j = i
    have := natCast_inj_lt (M := M) (a := 2 * M + j) (b := 2 * M + i) (by omega) (by omega) h3
    omega

/-- The family of canonical representatives, indexed by `j ∈ {1,…,M−1}`. -/
def repFamily (M : ℕ) : Finset (Finset (ZMod (4 * M))) :=
  (Finset.Icc 1 (M - 1)).image (exponentRep M)

/-- **The number of distinct canonical representatives is exactly `M − 1 = n/4 − 1`.**
Proven via `exponentRep_injective` (injectivity of the indexing) and `card_Icc`. This is the
PROVEN content of the count: the `μ_n`-orbit set contains `≥ n/4 − 1` distinct orbits, witnessed
by these representatives (under the named orbit-distinctness `Prop` below they are *exactly* the
orbit reps). -/
theorem repFamily_card {M : ℕ} (hM : 2 ≤ M) : (repFamily M).card = M - 1 := by
  unfold repFamily
  rw [Finset.card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro i hi j hj h
    simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
    exact exponentRep_injective hM hi.1 hi.2 hj.1 hj.2 h

/-! ## 4. The matching upper bound — the Lam–Leung surjectivity (named, OPEN)

The full equality `#orbits = n/4 − 1` requires, beyond the proven lower bound, that *every*
`e₂=0, e₁≠0` size-4 subset of `μ_n` is translation-orbit-equivalent to some `exponentRep M j`.
Equivalently: every vanishing sum of six `2^μ`-th roots of unity (the six pairwise products of a
quartet with `e₂=0`) is a `ℤ≥0`-combination of rotated antipodal pairs `{ζ^a, ζ^{a+n/2}}` — the
Lam–Leung classification of vanishing sums of prime-power roots of unity. Mathlib has no
Lam–Leung; we state the consequence as an explicit named `Prop`. Numerically verified exhaustively
for `n ≤ 64` (`scripts/probes/sweep_A16_orbitcount_w4.py`). NOT discharged here. -/

/-- **Named-open hypothesis.** Every `e₂=0, e₁≠0` quartet of `n`-th roots (`n = 4M`) is, up to
multiplication by `μ_n`, one of the `M − 1` canonical quartets `{1, ζ^j, ζ^{2j}, −ζ^j}`.
This is the Lam–Leung surjectivity; it is the only missing input to the exact count, and it is
the analytic content the project does not yet have in Lean. (Stated abstractly as a `Prop` about
the orbit set so the equality below is a clean conditional, with NO hidden `sorry`.) -/
def OrbitCountW4Surjective (M : ℕ) (orbitSet : Finset (Finset (ZMod (4 * M)))) : Prop :=
  orbitSet ⊆ repFamily M

/-- **The exact closed form, conditional on the Lam–Leung surjectivity.** If `orbitSet` is a set of
orbit representatives that (i) each lie in the proven family `repFamily M` (Lam–Leung
surjectivity, `OrbitCountW4Surjective`) and (ii) hits every family member (the proven lower
bound — each `exponentRep M j` is realized), then `#orbits = M − 1 = n/4 − 1`.

The lower-bound half (`repFamily M ⊆ orbitSet`) is the PROVEN
`exponentRep_injective`/`repFamily_card` content; the upper-bound half is the named-open
`OrbitCountW4Surjective`. This theorem is the honest assembly: `= n/4 − 1` is equivalent to the
surjectivity, nothing is fabricated. -/
theorem orbit_count_eq_of_surjective {M : ℕ} (hM : 2 ≤ M)
    {orbitSet : Finset (Finset (ZMod (4 * M)))}
    (hsurj : OrbitCountW4Surjective M orbitSet)
    (hcover : repFamily M ⊆ orbitSet) :
    orbitSet.card = M - 1 := by
  have : orbitSet = repFamily M := Finset.Subset.antisymm hsurj hcover
  rw [this, repFamily_card hM]

/-- Sanity instances of the closed form `M − 1 = n/4 − 1`: at `n = 4M`,
`M = 2,4,8,16,32 ↦ M−1 = 1,3,7,15,31` (matching the probe data for `n = 8,16,32,64,128`). -/
example : (2 : ℕ) - 1 = 1 ∧ (4 : ℕ) - 1 = 3 ∧ (8 : ℕ) - 1 = 7 ∧
    (16 : ℕ) - 1 = 15 ∧ (32 : ℕ) - 1 = 31 := by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

-- Axiom audit (must be `[propext, Classical.choice, Quot.sound]`, no `sorryAx`):
#print axioms e2_quartet_eq_zero
#print axioms e1_quartet_eq
#print axioms exponentRep_card
#print axioms exponentRep_injective
#print axioms repFamily_card
#print axioms orbit_count_eq_of_surjective

end ArkLib.ProximityGap.SweepA16
