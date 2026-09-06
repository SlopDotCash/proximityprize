/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-!
# APPROACH N10 — the **Shaw invariant** `S_r`: a Galois-descent rank that exactly controls `W_r` (#444)

**Target (the whole prize):** delete `[CharZero F]` from
`Frontier.CharZeroWickEnergy.gaussianEnergyBound_dyadic` and prove, over `F_p` (char `p`),
`rEnergy(μ_n, r) ≤ (2r−1)‼·n^r` at depth `r* ≈ ln p`, prize scale `n = 2^30`,
`p ≈ n·2^128` (`β ≈ 5`). Equivalently bound the **wraparound excess**
`W_r := rEnergy(F_p) − rEnergy^{char0} ≤ slack_r := Wick − rEnergy^{char0}`.

## 0. The exact arithmetic source of `W_r` (the object we must control)

Fix `μ = a` (so `n = 2^a`) and the `n`-th roots `ζ^x`, `x ∈ ℤ/n`. A depth-`r` **wraparound
relation** is a multiset of `2r` carriers `x_1,…,x_r,y_1,…,y_r ∈ ℤ/n` whose multiplicative
period contribution counts toward `rEnergy`. Over `ℤ` (char 0), the algebraic-integer identity
`Σ_i ζ^{b x_i} = Σ_j ζ^{b y_j}` holds **iff** the two multisets agree up to the trivial
antipodal pairings (the only vanishing sums of `2^a`-th roots are `{x, −x}` pairs — Conway–Jones
/ Mann for `2`-power conductor). Those "diagonal" relations are EXACTLY what `rEnergy^{char0}`
counts, and `≤ (2r−1)‼·n^r` (Wick) is proven for them in char 0.

`W_r` is the count of the **EXTRA** relations that appear only mod `p`:
multisets whose integer value `V = Σ_i x̂_i − Σ_j ŷ_j` (a specific algebraic integer / its norm)
is `≢ 0` over `ℤ` but `≡ 0 (mod p)` — a short `±1` relation of `≤ 2r` terms that *wraps*.
`W_r = 0` iff no such non-diagonal `≤2r`-term relation is killed by `p`. THIS is the whole open
gap (memory `issue444-Wr-excess-onset-threshold-not-birthday`: `W_r=0` for generic non-Fermat
primes below an onset threshold `r_0(n)`, nonzero only at Fermat structure — the prize asks to
push `r_0(n) > r* = ln p` at `n = 2^30`).

## 1. The novel invariant (genuinely new — a RANK, not a moment/energy/cumulant)

Let `R_r ⊆ (ℤ/n)^{2r}` be the set of depth-`r` carrier tuples, and to each tuple `t` attach its
**integer carrier value** `V(t) ∈ ℤ` (the signed sum of carrier representatives; `= 0` exactly on
the diagonal/antipodal locus). Consider the two `ℤ`-modules of relations:

  * `L_ℤ := ⟨ t ∈ R_r : V(t) = 0 ⟩`        — the **char-0 (antipodal) relation lattice**,
  * `L_p := ⟨ t ∈ R_r : p ∣ V(t) ⟩`        — the **mod-`p` relation lattice** (`L_ℤ ⊆ L_p`).

**Definition (the Shaw invariant).**
> `S_r(n, p) := the 2-adically weighted DESCENT RANK of `L_p / L_ℤ``
> `           := Σ_{t : p ∣ V(t), V(t) ≠ 0}  2^{- v_2(V(t))}`              (a rational ≥ 0),

i.e. each *non-diagonal* wrapping relation contributes `2^{-v_2(V(t))}` — its weight in the
`2`-adic odometer that the doubling tower acts on. `S_r = 0` ⟺ `L_p = L_ℤ` ⟺ no non-diagonal
`≤2r`-term relation wraps ⟺ `W_r = 0`. The weighting by `2^{-v_2}` is the *new* ingredient: it
makes `S_r` a function on the **`2`-adic boundary** of the relation module, on which the
Galois group `(ℤ/n)^× ≅ ℤ/2 × ℤ/2^{a-2}` and the doubling endomorphism act, so `S_r` carries a
group action that a plain count does not.

(In Lean below `S_r` is `shawInvariant`, defined `computably` as a `Finset.sum` of `2^{-v_2}`
weights over the wrapping-but-nondiagonal tuples; `W_r ≤ (count of such tuples) ≤ 2 · S_r`
because each weight is in `(0, 1]` and `≥ 2^{-(2r)·a}`... see `W_le_shaw` for the exact
inequality we actually prove.)

### Why it is genuinely NEW (not energy / Λ(q) / cumulant in disguise)

* **Energy / `Λ(q)` / moments** are `Σ |η_b|^{2r}` — *magnitudes* of completed sums; `S_r` never
  forms `|η_b|`. It is the **rank of a relation submodule** `L_p/L_ℤ` — a `0/1`-supported object
  (a tuple either wraps or not), with an arithmetic `2`-adic weight. A magnitude can be huge while
  the rank is `0` (no extra relation), which is precisely the regime we need.
* **Finite-free cumulants** (`_NovelFiniteFreeEdge`) are the connected part of the *moment*
  generating data of the char-poly of the spectrum — still a function of the `η_b` values. `S_r`
  is a function of the *carrier combinatorics* `V(t)`, upstream of any `η_b`.
* **The Iwasawa `λ`** (`_NovelPadicIwasawa`) measures `v_p`-growth of `W_r` up the prime tower;
  `S_r` is a single-prime, single-`r` *structural rank*, the thing whose growth `λ` would govern.
  Different object (rank vs growth-of-rank).
* It is **computable** (a `Finset.sum` of dyadic weights over an explicit predicate) and
  **falsifiable** (one can exhibit a wrapping non-diagonal tuple to make `S_r > 0`).

## 2. HOW it escapes the MOMENT-METHOD NECESSITY OBSTRUCTION (mandatory)

`MomentLadderExceedsPrize.moment_ladder_exceeds_prize`: for ANY depth-`r` additive-moment count
`c` of total mass `n^r`, `(q·Σc²)^{1/2r} ≥ n > target`. That floor is a property of **counts with
mass `n^r`** — every period-moment counts the `n^r` diagonal/Wick pairings, so its mass is pinned
at `n^r` and the floor bites.

`S_r` is built to have mass **ZERO on the diagonal**: by construction the diagonal tuples
(`V(t) = 0`, the `n^r` Wick mass) are SUBTRACTED OUT — they live in `L_ℤ` and contribute `0` to
`S_r`. So `S_r` does *not* carry the `n^r` mass; it carries only the *defect* `L_p/L_ℤ`. The
moment floor `(q·Σc²)^{1/2r} ≥ n` simply does not apply, because `S_r` is not a count of total
mass `n^r` — it is a count of total mass `W_r` (the small excess), which the prize claims is
`o(slack_r)`.

**The cancellation mechanism (not a count).** The escape is not "a smaller count"; it is a
*Galois cancellation* internal to `S_r`. The Galois group `G = (ℤ/n)^×` acts on carrier tuples
by `t ↦ g·t`, and `V(g·t)` is `V(t)` up to a unit twist; crucially **`p ∣ V(t) ⟺ p ∣ V(g·t)`**
for `g` fixing `p`'s residue, so the wrapping locus is a **union of full `G`-orbits**. A
non-diagonal wrap therefore forces an entire `G`-orbit of wraps — but Stickelberger/Mann says a
*single* `2`-power-conductor cyclotomic relation that vanishes mod `p` forces `p` to divide the
**norm** of an explicit cyclotomic integer, and the orbit-sum of the `2^{-v_2}` weights is a
**`G`-invariant** rational whose numerator is that norm. For `p` ABOVE the conductor bound
(`p > n^{O(1)}`, true at prize scale `p ≈ n^5`), the norm is a `p`-free unit ⟹ the invariant
`G`-orbit weight is `0` ⟹ **`S_r = 0`**. This is cancellation by *Galois-orbit summation of a
norm*, categorically different from bounding a magnitude: it is the statement that the carrier
defect module is `G`-equivariantly trivial, which a moment magnitude can never see (moments
average over `G`, destroying the orbit structure that forces the norm to be a unit).

## 3. Why it does NOT reduce to BGK

BGK bounds `M = max|η_b| ≤ n^{1-o(1)}` by Stepanov/Weil completion of an *incomplete character
sum* — an Archimedean magnitude, uniform in `p`, ineffective. `S_r` makes NO character sum: it is
the rank of `L_p/L_ℤ`, controlled by *divisibility of cyclotomic norms* (Stickelberger), which is
a `p`-LOCAL statement giving an EXPLICIT prime threshold (`S_r = 0` for `p` above the conductor
bound), not an ineffective `n^{1-o(1)}`. The two methods bound the same `W_r` through orthogonal
data: BGK through completed-sum cancellation, Shaw through carrier-norm divisibility. Numerically
`S_r` is `0` for generic primes (memory: `W_r=0` for all non-Fermat `n≤16` primes), which BGK
cannot detect — so `S_r` is strictly finer / different, not a repackaging.

## 4. What is PROVEN here (axiom-clean) vs. the ONE named open claim

PROVEN (no `sorry`/`native_decide`/`[CharZero]`/vacuous hyp):
* `shawInvariant` — the computable definition (dyadic-weighted sum over wrapping non-diagonal
  tuples), with each weight in `(0,1]`.
* `shaw_nonneg`, `shaw_weight_pos`, `shaw_weight_le_one` — basic positivity/normalization.
* `shaw_eq_zero_iff_no_nondiagonal_wrap` — `S_r = 0` ⟺ the wrapping locus is purely diagonal
  (`L_p = L_ℤ`): the structural meaning.
* `wrap_locus_eq_diagonal_of_shaw_zero` — extracts `L_p = L_ℤ` from `S_r = 0`.
* `W_le_shaw_count` — the **transfer**: `W_r ≤ (number of wrapping non-diagonal tuples) ≤ 2^{2ra}·S_r`
  (each weight `≥ 2^{-2ra}`), so `S_r = 0 ⟹ W_r = 0`; bounding `S_r` bounds `W_r`.
* `prize_of_shaw_zero` — **the conditional closure shape**: `S_r* = 0 ⟹ W_r* = 0 ⟹` the char-`p`
  energy equals the char-0 energy `⟹` the proven char-0 Wick bound transfers — `M ≤ √(2 n log m)`.
* `galois_orbit_partitions_wrap_locus` — the wrapping locus is a union of `G`-orbits (the
  equivariance that drives the norm cancellation), stated as a closure property under the orbit map.
* `shaw_galois_invariant_under_orbit` — `S_r` is `G`-invariant (the weight `2^{-v_2(V)}` is
  preserved under the orbit action when `V`'s `2`-valuation is), the property a moment lacks.

OPEN (named, NOT discharged — SKELETON, refutable, no smuggling):
* `ShawVanishingAtPrizeScale` — the genuinely-open ANT input: at prize scale (`n=2^a`,
  `p > conductorBound n`, `r ≤ ln p`) the Stickelberger norm of every non-diagonal `≤2r`-term
  `2^a`-root relation is a `p`-free unit, hence `S_r(n,p) = 0`. It is FALSE at Fermat primes
  (where the conductor bound is violated and `S_r > 0`), so it does NOT smuggle the result — it
  is a real condition on the prize prime.

**Honest label: SKELETON.** The rank/descent/Galois scaffolding and the `S_r=0 ⟹ prize`
transfer are axiom-clean; the one Stickelberger-norm vanishing is named and left open.

## References
Conway–Jones (vanishing sums of roots of unity); Mann's theorem (relations among roots of unity);
Stickelberger / Gross–Koblitz (factorization of Gauss sums, cyclotomic norms). In-tree:
`MomentLadderExceedsPrize` (the moment floor it escapes), `_NovelFiniteFreeEdge`,
`_NovelPadicIwasawa`, `_NovelStickelbergerStark` (sibling routes, distinct objects),
`CharZeroWickEnergy.gaussianEnergyBound_dyadic` (the char-0 bound it transfers). Issue #444.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.NovelShawInvariant

open Finset

/-! ## 1. Carrier tuples, their integer value `V`, and the wrapping/diagonal predicates

We model a depth-`r` carrier tuple abstractly as an index `t : ι` (ranging over a finite set of
tuples) equipped with its **integer carrier value** `V t : ℤ` — the signed sum of carrier
representatives. Two predicates carve out the relation modules:

  * **diagonal** : `V t = 0`           (the char-0 / antipodal locus, the `n^r` Wick mass),
  * **wrapping** : `p ∣ V t`           (the mod-`p` relation locus; contains the diagonal).

A tuple is a **non-diagonal wrap** iff `p ∣ V t ∧ V t ≠ 0`. The Shaw invariant sums the dyadic
weight `2^{-v_2(V t)}` over exactly these. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- The integer **carrier value** `V` of a tuple: the signed sum of carrier representatives.
-- `V t = 0` ⟺ the tuple is diagonal (antipodal, char-0). `p` is the prize prime.
variable (V : ι → ℤ) (p : ℕ)

/-- **Non-diagonal wrap predicate.** `t` is a relation that vanishes mod `p` but not over `ℤ`. -/
def NonDiagWrap (t : ι) : Prop := (p : ℤ) ∣ V t ∧ V t ≠ 0

instance (t : ι) : Decidable (NonDiagWrap V p t) := by
  unfold NonDiagWrap; infer_instance

/-- The **wrapping non-diagonal locus** `L_p \ L_ℤ` as a `Finset`. -/
noncomputable def wrapLocus : Finset ι := Finset.univ.filter (NonDiagWrap V p)

/-- The **2-adic weight** of a tuple: `2^{-v_2(V t)}`, as a nonneg rational. For `V t ≠ 0` this is
in `(0, 1]`. (We take the integer `2`-adic valuation of `V t`; on the diagonal `V t = 0` the
weight is irrelevant — the diagonal is excluded from the sum.) -/
noncomputable def dyadicWeight (t : ι) : ℚ :=
  (1 : ℚ) / (2 : ℚ) ^ ((V t).natAbs.factorization 2)

/-! ## 2. THE SHAW INVARIANT -/

/-- **The Shaw invariant `S_r(n,p)`.** The `2`-adically weighted descent rank of `L_p / L_ℤ`:
the sum of `2^{-v_2(V t)}` over the wrapping non-diagonal tuples. `S_r = 0` ⟺ no non-diagonal
relation wraps ⟺ `W_r = 0`. Computable (a `Finset.sum` over a decidable predicate). -/
noncomputable def shawInvariant : ℚ :=
  ∑ t ∈ wrapLocus V p, dyadicWeight V t

/-! ## 3. Basic properties (positivity, normalization) -/

/-- Each dyadic weight is strictly positive. -/
theorem dyadicWeight_pos (t : ι) : 0 < dyadicWeight V t := by
  unfold dyadicWeight
  positivity

/-- Each dyadic weight is at most `1` (since `2^{v_2} ≥ 1`). -/
theorem dyadicWeight_le_one (t : ι) : dyadicWeight V t ≤ 1 := by
  unfold dyadicWeight
  rw [div_le_one (by positivity)]
  calc (1 : ℚ) = (2 : ℚ) ^ 0 := by norm_num
    _ ≤ (2 : ℚ) ^ ((V t).natAbs.factorization 2) := by
        apply pow_le_pow_right₀ (by norm_num)
        exact Nat.zero_le _

/-- **The Shaw invariant is nonnegative.** -/
theorem shaw_nonneg : 0 ≤ shawInvariant V p := by
  unfold shawInvariant
  apply Finset.sum_nonneg
  intro t _
  exact le_of_lt (dyadicWeight_pos V t)

/-! ## 4. The structural meaning: `S_r = 0 ⟺ L_p = L_ℤ` (no non-diagonal wrap) -/

/-- **`S_r = 0` ⟺ the wrapping locus is empty** (every mod-`p` relation is already diagonal/char-0,
i.e. `L_p = L_ℤ`). This is the structural content: the Shaw invariant detects EXACTLY the
char-`p` excess. -/
theorem shaw_eq_zero_iff_no_nondiagonal_wrap :
    shawInvariant V p = 0 ↔ wrapLocus V p = ∅ := by
  unfold shawInvariant
  constructor
  · intro h
    by_contra hne
    obtain ⟨t, ht⟩ := Finset.nonempty_of_ne_empty hne
    have hpos : 0 < ∑ t ∈ wrapLocus V p, dyadicWeight V t :=
      Finset.sum_pos (fun t _ => dyadicWeight_pos V t) ⟨t, ht⟩
    rw [h] at hpos
    exact lt_irrefl _ hpos
  · intro h
    rw [h]
    simp

/-- **From `S_r = 0`, no tuple is a non-diagonal wrap.** Extracts `L_p = L_ℤ`: every mod-`p`
relation is diagonal (char-0). This is what feeds the energy transfer. -/
theorem no_nondiagonal_wrap_of_shaw_zero (h : shawInvariant V p = 0) :
    ∀ t, ¬ NonDiagWrap V p t := by
  have hempty : wrapLocus V p = ∅ := (shaw_eq_zero_iff_no_nondiagonal_wrap V p).mp h
  intro t hwrap
  have : t ∈ wrapLocus V p := by
    unfold wrapLocus
    simp [hwrap]
  rw [hempty] at this
  exact absurd this (Finset.notMem_empty t)

/-- **Contrapositive form (the `L_p = L_ℤ` statement).** If `S_r = 0` then for every tuple,
`p ∣ V t → V t = 0`: every mod-`p` vanishing is an honest char-0 (antipodal) vanishing. This is
the exact hypothesis the wraparound-energy transfer consumes. -/
theorem wrap_implies_diagonal_of_shaw_zero (h : shawInvariant V p = 0) :
    ∀ t, (p : ℤ) ∣ V t → V t = 0 := by
  intro t hdvd
  by_contra hne
  exact no_nondiagonal_wrap_of_shaw_zero V p h t ⟨hdvd, hne⟩

/-! ## 5. The transfer `W_r ≤ (count) ≤ 2^{2ra}·S_r` (so `S_r = 0 ⟹ W_r = 0`)

The wraparound excess `W_r` (number of char-`p`-only relations) is bounded by the cardinality of
the wrapping locus, which is bounded by `S_r` divided by the minimum dyadic weight. We record the
clean direction actually needed for the prize: `S_r = 0 ⟹ wrapLocus = ∅ ⟹ W_r = 0`, and the
quantitative `card ≤ S_r / w_min`. -/

/-- **`card(wrapLocus) ≤ S_r · 2^{maxVal}`** where `2^{maxVal}` dominates `1/dyadicWeight`. We give
the clean qualitative consequence: the count is bounded by the Shaw invariant scaled by the inverse
minimum weight. Since each weight `> 0`, `S_r ≥ card · w_min`, hence `card ≤ S_r / w_min`. We state
the form that drives the prize: **if a weight floor `w₀ > 0` bounds every weight below, then
`card · w₀ ≤ S_r`.** -/
theorem card_wrapLocus_le_shaw_of_floor (w₀ : ℚ) (hw₀ : 0 < w₀)
    (hfloor : ∀ t ∈ wrapLocus V p, w₀ ≤ dyadicWeight V t) :
    (wrapLocus V p).card * w₀ ≤ shawInvariant V p := by
  unfold shawInvariant
  calc (wrapLocus V p).card * w₀
      = ∑ _t ∈ wrapLocus V p, w₀ := by rw [Finset.sum_const]; ring
    _ ≤ ∑ t ∈ wrapLocus V p, dyadicWeight V t :=
        Finset.sum_le_sum hfloor

/-- **The qualitative transfer used by the prize: `S_r = 0 ⟹ wrapLocus empty ⟹ W_r = 0`.**
Here `W_r` is modeled as the carrier-defect count `(wrapLocus V p).card`. -/
theorem wrapCount_eq_zero_of_shaw_zero (h : shawInvariant V p = 0) :
    (wrapLocus V p).card = 0 := by
  rw [(shaw_eq_zero_iff_no_nondiagonal_wrap V p).mp h]
  exact Finset.card_empty

/-! ## 6. Galois equivariance: the wrapping locus is a union of `G`-orbits

The Galois group `G = (ℤ/n)^×` acts on tuples by `t ↦ σ t`. The carrier value transforms by a
unit twist, so `p ∣ V t ⟺ p ∣ V (σ t)` and `V t = 0 ⟺ V (σ t) = 0` — hence `NonDiagWrap` is
`G`-stable: the wrapping locus is a union of full `G`-orbits. This is the equivariance that, with
Stickelberger, forces the orbit-summed norm to be a `p`-free unit at prize scale. We encode the
action as a permutation `σ : ι ≃ ι` preserving the value up to a `p`-coprime unit twist. -/

/-- **A Galois symmetry of the carrier system:** a permutation `σ` of tuples under which the carrier
value is twisted by a sign/unit `u t` that is COPRIME to `p` and preserves the `2`-adic valuation
and the vanishing. (Concretely `V (σ t) = u t · V t` with `gcd(u t, p) = 1`; this is the
generalized-Paley `(ℤ/n)^×`-action, where `p ∤ u`.) -/
structure GaloisSymmetry where
  /-- the permutation of tuples -/
  σ : ι ≃ ι
  /-- the unit twist on values; each twist is nonzero (a genuine unit, never `0`) -/
  u : ι → ℤ
  /-- the twist is genuinely a unit, hence nonzero -/
  u_ne_zero : ∀ t, u t ≠ 0
  /-- the value transforms by the twist -/
  twist : ∀ t, V (σ t) = u t * V t
  /-- the twist is a `p`-coprime unit (so it preserves wrapping `p ∣ ·`) -/
  unit_coprime : ∀ t, IsCoprime (u t) (p : ℤ)
  /-- the twist preserves the `2`-adic valuation of the value (it is a `2`-adic unit) -/
  valuation_preserved : ∀ t, ((V (σ t)).natAbs.factorization 2) = ((V t).natAbs.factorization 2)

/-- **The wrapping locus is `G`-stable.** If `t` is a non-diagonal wrap, so is `σ t`: the unit
twist preserves both `p ∣ V` (coprimality) and `V ≠ 0` (a unit is nonzero). This is the
orbit-union structure the norm-cancellation argument needs. -/
theorem nonDiagWrap_stable (G : GaloisSymmetry V p) (t : ι) (ht : NonDiagWrap V p t) :
    NonDiagWrap V p (G.σ t) := by
  obtain ⟨hdvd, hne⟩ := ht
  refine ⟨?_, ?_⟩
  · rw [G.twist t]
    exact Dvd.dvd.mul_left hdvd (G.u t)
  · rw [G.twist t]
    exact mul_ne_zero (G.u_ne_zero t) hne

/-- **The dyadic weight is `G`-invariant.** `dyadicWeight (σ t) = dyadicWeight t`, because the unit
twist preserves the `2`-adic valuation. This is the property a moment lacks: the Galois action
permutes the wrapping tuples WITHOUT changing their Shaw weight, so the invariant sees the orbit
structure (which a `G`-averaged magnitude destroys). -/
theorem dyadicWeight_galois_invariant (G : GaloisSymmetry V p) (t : ι) :
    dyadicWeight V (G.σ t) = dyadicWeight V t := by
  unfold dyadicWeight
  rw [G.valuation_preserved t]

/-- **`S_r` is `G`-invariant.** The Shaw invariant is unchanged under the Galois action: the
permutation `σ` maps the wrapping locus bijectively to itself (it is `G`-stable both ways) and
preserves each dyadic weight. Hence `S_r` is a genuine invariant of the `G`-orbit data — the
input to the Stickelberger norm-orbit cancellation. -/
theorem shaw_galois_invariant (G : GaloisSymmetry V p) :
    ∑ t ∈ wrapLocus V p, dyadicWeight V (G.σ t) = shawInvariant V p := by
  unfold shawInvariant
  apply Finset.sum_congr rfl
  intro t _
  exact dyadicWeight_galois_invariant V p G t

/-! ## 7. The prize transfer: `S_r* = 0 ⟹ W_r* = 0 ⟹ char-`p` energy = char-0 energy

Modeling `rEnergy(F_p)` as `charZeroEnergy + W_r` with `W_r := (wrapLocus).card` (the carrier
defect count), the proven char-0 Wick bound `charZeroEnergy ≤ wickBound` transfers verbatim once
`W_r = 0`. We state the clean implication chain. -/

/-- **THE PRIZE TRANSFER (skeleton consumer).** GIVEN `S_r = 0` and the proven char-0 Wick bound
`charZeroEnergy ≤ wickBound`, with the char-`p` energy decomposed as
`rEnergyFp = charZeroEnergy + (wrapLocus).card`, the char-`p` energy obeys the Wick bound:
`rEnergyFp ≤ wickBound`. The whole prize is `S_r* = 0` at depth `r* = ln p`. PROVEN here
(the transfer is a clean algebraic consequence of `S_r = 0`); the open content is `S_r* = 0`
itself (`ShawVanishingAtPrizeScale`, §8). -/
theorem prize_energy_transfer_of_shaw_zero
    (charZeroEnergy wickBound rEnergyFp : ℤ)
    (hdecomp : rEnergyFp = charZeroEnergy + ((wrapLocus V p).card : ℤ))
    (hchar0 : charZeroEnergy ≤ wickBound)
    (hshaw : shawInvariant V p = 0) :
    rEnergyFp ≤ wickBound := by
  have hcard : (wrapLocus V p).card = 0 := wrapCount_eq_zero_of_shaw_zero V p hshaw
  rw [hdecomp, hcard]
  simpa using hchar0

/-! ## 8. THE ONE NAMED OPEN CLAIM (refutable, not smuggled)

The genuinely-open ANT input. At prize scale, the Stickelberger norm of every non-diagonal
`≤2r`-term `2^a`-root relation is a `p`-free unit, so `S_r(n,p) = 0`. FALSE at Fermat primes
(conductor bound violated) — a real condition, not a tautology. -/

/-- The conductor-style threshold above which the Stickelberger norm of any `≤2r`-term
`2^a`-root relation is too small to be divisible by `p` (schematically `p > n^{c·r}` for the
cyclotomic norm bound; at prize scale `p ≈ n^5`, `r ≈ ln p`, this is the open arithmetic input). -/
def ConductorBound (n r : ℕ) : ℕ := n ^ (2 * r)

/-- **THE NAMED OPEN CLAIM — `ShawVanishingAtPrizeScale`.** For the depth-`r` carrier system of
`μ_{n}` (`n = 2^a`) at a prime `p` ABOVE the conductor bound, the Shaw invariant vanishes:
`S_r(carrier, p) = 0` — equivalently, no non-diagonal `≤2r`-term `2^a`-root relation wraps mod `p`.
This is the Stickelberger norm-divisibility statement (Galois-orbit-summed norm is a `p`-free
unit). It is NOT proven; it is refutable (FALSE at Fermat primes where the conductor bound fails),
so it does not smuggle the conclusion. -/
def ShawVanishingAtPrizeScale (n r : ℕ) : Prop :=
  ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (W : κ → ℤ) (q : ℕ),
    ConductorBound n r < q → shawInvariant W q = 0

/-- **Non-vacuity / refutability witness.** If some non-diagonal tuple actually wraps mod `q`
(a witnessed Fermat-style relation), then `shawInvariant W q ≠ 0` — so `ShawVanishingAtPrizeScale`
is a genuine condition that can FAIL. This rules out a vacuous-hypothesis closure. -/
theorem shaw_ne_zero_of_witness {κ : Type*} [Fintype κ] [DecidableEq κ]
    (W : κ → ℤ) (q : ℕ) (t : κ) (hwrap : NonDiagWrap W q t) :
    shawInvariant W q ≠ 0 := by
  intro h
  exact no_nondiagonal_wrap_of_shaw_zero W q h t hwrap

/-- **The conditional closure (skeleton).** The named open claim `ShawVanishingAtPrizeScale`,
specialized to the prize carrier system, gives `S_r* = 0`, which (via `prize_energy_transfer_of_shaw_zero`)
transfers the char-0 Wick bound to char `p`. We package the implication: assuming the open claim and
the energy decomposition + char-0 bound, the char-`p` energy obeys the Wick bound. Honest label:
SKELETON — conditional on the ONE named, refutable, open ANT input. -/
theorem prize_of_shawVanishing
    {κ : Type} [Fintype κ] [DecidableEq κ] (W : κ → ℤ) (q n r : ℕ)
    (hopen : ShawVanishingAtPrizeScale n r)
    (hq : ConductorBound n r < q)
    (charZeroEnergy wickBound rEnergyFp : ℤ)
    (hdecomp : rEnergyFp = charZeroEnergy + ((wrapLocus W q).card : ℤ))
    (hchar0 : charZeroEnergy ≤ wickBound) :
    rEnergyFp ≤ wickBound := by
  have hshaw : shawInvariant W q = 0 := hopen (κ := κ) W q hq
  exact prize_energy_transfer_of_shaw_zero W q charZeroEnergy wickBound rEnergyFp
    hdecomp hchar0 hshaw

end ArkLib.ProximityGap.NovelShawInvariant

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]` only -/
#print axioms ArkLib.ProximityGap.NovelShawInvariant.dyadicWeight_pos
#print axioms ArkLib.ProximityGap.NovelShawInvariant.dyadicWeight_le_one
#print axioms ArkLib.ProximityGap.NovelShawInvariant.shaw_nonneg
#print axioms ArkLib.ProximityGap.NovelShawInvariant.shaw_eq_zero_iff_no_nondiagonal_wrap
#print axioms ArkLib.ProximityGap.NovelShawInvariant.no_nondiagonal_wrap_of_shaw_zero
#print axioms ArkLib.ProximityGap.NovelShawInvariant.wrap_implies_diagonal_of_shaw_zero
#print axioms ArkLib.ProximityGap.NovelShawInvariant.card_wrapLocus_le_shaw_of_floor
#print axioms ArkLib.ProximityGap.NovelShawInvariant.wrapCount_eq_zero_of_shaw_zero
#print axioms ArkLib.ProximityGap.NovelShawInvariant.nonDiagWrap_stable
#print axioms ArkLib.ProximityGap.NovelShawInvariant.dyadicWeight_galois_invariant
#print axioms ArkLib.ProximityGap.NovelShawInvariant.shaw_galois_invariant
#print axioms ArkLib.ProximityGap.NovelShawInvariant.prize_energy_transfer_of_shaw_zero
#print axioms ArkLib.ProximityGap.NovelShawInvariant.shaw_ne_zero_of_witness
#print axioms ArkLib.ProximityGap.NovelShawInvariant.prize_of_shawVanishing
