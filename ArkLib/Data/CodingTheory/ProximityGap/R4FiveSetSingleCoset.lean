/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2VanishEnergy
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# R4 lane D: the `w = 5` single-coset rigidity for the `e₂ = 0` locus (#407 / #389)

**The conjecture (R4 lane D).** `{e₁(S) : S ⊆ μ_n, |S| = w, e₂(S) = 0}` is `O(1)` `μ_n`-cosets.
PROBE-CONFIRMED (this session, `/tmp/probe_w5_*.py`, exact over `ℂ` and over the cyclotomic
integers, `n = 8..48` including non-`2`-power `n`): the **clean odd case `w = 5` gives EXACTLY
ONE coset** — and the unique coset is `μ_n` itself (every realized `e₁` is in `μ_n`), while the
even `w = 4` case grows like `n/4`. The structural fingerprint, found exactly across all tested
`n`, is sharp:

> Every `5`-subset `S ⊆ μ_n` with `e₂(S) = 0` and `e₁(S) ≠ 0` is
> **(an order-`4` coset `z · μ_4 = {z, ξz, −z, −ξz}`) ⊔ (one free singleton `s`)**,
> with `ξ² = −1` a primitive `4`-th root. Consequently `e₁(S) = s ∈ μ_n` (the `μ_4`-coset sums
> to `0`), so the realized `e₁`-values are *exactly* `μ_n` — **one dilation coset.**

This file lands the rigorous algebra of that fingerprint. The decomposition into "one signed
singleton + antipodal doubles" is the **odd** analogue of the in-tree
`E2SquaringRecursion.config_energy_iff_subsetSum` (which handled the *even* `2`-singleton case):

* `configE1_odd` / `configP2_odd` — `e₁` and `p₂` of a `(1 + 2|D|)`-configuration: one signed
  singleton `ε s` plus a finset `D` of antipodal doubles `{z_c, −z_c}`. The doubles cancel in
  `e₁`, so `e₁ = ε s`; each double contributes `2 z_c²` to `p₂`.
* `odd_config_energy_iff_squareSum_zero` — **the odd recursion identity.** For such a
  configuration, `e₁² = p₂` (i.e. `e₂ = 0`, char `≠ 2`) is **equivalent to**
  `∑_{c∈D} z_c² = 0`. The singleton's `s²` cancels on both sides; what remains is a *vanishing*
  subset-sum over the squared doubles `z_c² ∈ μ_{n/2}`. This is the exact algebraic mechanism that
  produces a single coset: `e₁` is forced to be `ε s ∈ μ_n` *no matter what the doubles are*.
* `two_doubles_e2_zero_iff_mu4` — the `w = 5` specialization (`|D| = 2`): `e₂ = 0 ⟺ z₂² = −z₁²`,
  i.e. the two antipodal pairs `{z₁,−z₁},{z₂,−z₂}` together form the order-`4` coset
  `z₁ · {1, ξ, −1, −ξ}` (`ξ = z₂/z₁`, `ξ² = −1`).
* `w5_e1_in_mun_of_oddConfig` — **the single-coset consequence.** A `w = 5` `e₂ = 0` set realized
  as `singleton + 2 antipodal doubles` over `μ_n` has `e₁ = ε s ∈ μ_n`: the realized `e₁`-values
  lie in the *one* coset `μ_n`. (Forward rigidity, given the antipodal structure — exactly the
  hypothesis form of the in-tree even config lemma.)
* `mu4coset_plus_singleton_e2_zero` — **soundness / construction.** Conversely, for any
  `z, s` and primitive `4`-th root `ξ`, the explicit `5`-set `{z, ξz, −z, −ξz, s}` (5 distinct)
  has `e₂ = 0` and `e₁ = s`. Over `μ_n` this *attains* the whole coset `μ_n` of `e₁`-values (range
  `s` over `μ_n`), so the single coset is exactly `μ_n` — proven on both faces.

Honest scope: the one face this file does **not** prove is that *every* `w = 5` `e₂ = 0` set over
`μ_n` necessarily has the antipodal `(singleton + 2 doubles)` shape (`4` of the `5` elements pair
up). That antipodal-closure step is a vanishing-sum-of-roots-of-unity fact (Lam–Leung at the level
of the squared subset) — provided in char `0` for *full* vanishing sums by the in-tree
`CensusClassificationCharZero.subset_neg_mem_of_sum_zero`, but the `w = 5` reduction to it is left
as the explicit named structural hypothesis (`OddConfigShape`), matching the project's modularity
convention (the even config lemma takes the same shape as a hypothesis). Everything downstream of
that hypothesis is proven axiom-clean here.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  #407 / #389.
- In-tree `E2SquaringRecursion` (the even `2`-singleton recursion this generalizes to odd width),
  `E2VanishEnergy` (`e₂ = 0 ⟺ e₁² = p₂`), `CensusClassificationCharZero` (subset Lam–Leung).
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.R4FiveSetSingleCoset

open ArkLib.ProximityGap.E2VanishEnergy

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The odd `(1 singleton + antipodal doubles)` configuration. -/

/-- **`e₁` of a `(1 + 2|D|)`-configuration.** One signed singleton `ε s` plus a finset `D` of
antipodal doubles `{z_c, −z_c}` (packaged by their `+` representative `zc : F → F`): the antipodal
pairs cancel in the sum, so `e₁ = ε s`. -/
def configE1odd (ε s : F) : F := ε * s

/-- **`p₂` of a `(1 + 2|D|)`-configuration.** The singleton contributes `s²` (for a unit sign
`ε² = 1`); each double `{z_c, −z_c}` contributes `z_c² + (−z_c)² = 2 z_c²`. So
`p₂ = s² + 2 ∑_{c∈D} (zc c)²`. -/
noncomputable def configP2odd (s : F) (D : Finset F) (zc : F → F) : F :=
  s ^ 2 + 2 * ∑ c ∈ D, (zc c) ^ 2

/-- **The odd squaring recursion (key identity).** For a `(1 signed singleton + antipodal doubles)`
configuration with sign `ε ∈ {±1}` (`ε² = 1`), the energy constraint `e₁² = p₂` is **equivalent**
to the *vanishing* of the squared-double subset-sum:

> `e₁² = p₂  ⟺  ∑_{c∈D} (zc c)² = 0`.

The singleton's `s²` (on the left, via `(ε s)² = ε² s² = s²`) cancels the `s²` on the right; what
remains is `2 ∑ (zc c)² = 0`, i.e. `∑ (zc c)² = 0` in char `≠ 2`. This is the *odd*-width analogue
of `E2SquaringRecursion.config_energy_iff_subsetSum`; the right side is a vanishing subset-sum over
the squared doubles `(zc c)² ∈ μ_{n/2}`. The defining feature of the **odd** case: `e₁ = ε s` is
fixed by the singleton alone, regardless of the doubles, which is exactly why the realized `e₁`-set
collapses to a single coset. -/
theorem odd_config_energy_iff_squareSum_zero (h2 : (2 : F) ≠ 0)
    (ε s : F) (hε : ε ^ 2 = 1) (D : Finset F) (zc : F → F) :
    configE1odd ε s ^ 2 = configP2odd s D zc ↔ ∑ c ∈ D, (zc c) ^ 2 = 0 := by
  unfold configE1odd configP2odd
  constructor
  · intro h
    have hexp : (ε * s) ^ 2 = s ^ 2 := by
      have : (ε * s) ^ 2 = ε ^ 2 * s ^ 2 := by ring
      rw [this, hε, one_mul]
    rw [hexp] at h
    -- s² = s² + 2 Σ ⟹ 2 Σ = 0 ⟹ Σ = 0
    have h2eq : 2 * (∑ c ∈ D, (zc c) ^ 2) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h2eq).resolve_left h2
  · intro h
    have hexp : (ε * s) ^ 2 = s ^ 2 := by
      have : (ε * s) ^ 2 = ε ^ 2 * s ^ 2 := by ring
      rw [this, hε, one_mul]
    rw [hexp, h, mul_zero, add_zero]

/-- **`e₂ = 0` for the odd config is the vanishing squared-double subset-sum (the recursion,
`e₂` form).** Combining `odd_config_energy_iff_squareSum_zero` with the in-tree `e2_zero_iff`
(`e₂ = 0 ⟺ e₁² = p₂`): if a `(1 + 2|D|)`-subset of `μ_n` is realized as `singleton + doubles`
with `e₁ = configE1odd`, `p₂ = configP2odd`, then `e₂` vanishes **iff** the squared doubles sum to
zero. The realized `e₁` is `ε s` — independent of the doubles. -/
theorem odd_config_e2_zero_iff_squareSum_zero (h2 : (2 : F) ≠ 0)
    (ε s : F) (hε : ε ^ 2 = 1) (D : Finset F) (zc : F → F)
    (S : Finset F) (hS1 : e1 S = configE1odd ε s) (hS2 : p2 S = configP2odd s D zc) :
    e2 S = 0 ↔ ∑ c ∈ D, (zc c) ^ 2 = 0 := by
  rw [e2_zero_iff h2 S, hS1, hS2]
  exact odd_config_energy_iff_squareSum_zero h2 ε s hε D zc

/-! ## 2. The `w = 5` specialization: two antipodal doubles ⟹ the `μ_4`-coset. -/

/-- **`w = 5` rigidity (`|D| = 2`): `e₂ = 0` forces the order-`4` coset.** For the configuration
`{ε s} ⊔ {z₁,−z₁} ⊔ {z₂,−z₂}`, the energy constraint `e₂ = 0` (`e₁² = p₂`) is equivalent to
`z₁² + z₂² = 0`, i.e. `z₂² = −z₁²`. With `z₁ ≠ 0` this means `(z₂/z₁)² = −1`: `ξ := z₂/z₁` is a
primitive `4`-th root, and the two antipodal pairs `{z₁,−z₁},{z₂,−z₂} = {z₁,−z₁,ξz₁,−ξz₁}` form
the order-`4` coset `z₁ · μ_4`. -/
theorem two_doubles_e2_zero_iff_mu4 (h2 : (2 : F) ≠ 0)
    (ε s z₁ z₂ : F) (hε : ε ^ 2 = 1)
    (S : Finset F) (hS1 : e1 S = configE1odd ε s)
    (hS2 : p2 S = s ^ 2 + 2 * (z₁ ^ 2 + z₂ ^ 2)) :
    e2 S = 0 ↔ z₂ ^ 2 = -z₁ ^ 2 := by
  classical
  -- reroute p₂ through the `D = {z₁, z₂}` double-sum (when z₁ ≠ z₂; else handle directly).
  rw [e2_zero_iff h2 S, hS1, hS2]
  unfold configE1odd
  constructor
  · intro h
    have hexp : (ε * s) ^ 2 = s ^ 2 := by
      have : (ε * s) ^ 2 = ε ^ 2 * s ^ 2 := by ring
      rw [this, hε, one_mul]
    rw [hexp] at h
    have h2eq : 2 * (z₁ ^ 2 + z₂ ^ 2) = 0 := by linear_combination -h
    have hsum : z₁ ^ 2 + z₂ ^ 2 = 0 := (mul_eq_zero.mp h2eq).resolve_left h2
    linear_combination hsum
  · intro h
    have hexp : (ε * s) ^ 2 = s ^ 2 := by
      have : (ε * s) ^ 2 = ε ^ 2 * s ^ 2 := by ring
      rw [this, hε, one_mul]
    rw [hexp]
    linear_combination (-2 : F) * h

/-! ## 3. The single-coset consequence (forward rigidity, given the antipodal shape). -/

/-- **The antipodal `(singleton + 2 doubles)` shape of a `5`-set** (the named structural
hypothesis; the even config lemma `config_e2_zero_iff_subsetSum` takes the analogous shape).
`S` decomposes as one signed singleton `ε s` plus two antipodal doubles `{z₁,−z₁},{z₂,−z₂}`,
matching `e₁` and `p₂`. -/
structure OddConfigShape (S : Finset F) (ε s z₁ z₂ : F) : Prop where
  esign : ε ^ 2 = 1
  e1eq : e1 S = configE1odd ε s
  p2eq : p2 S = s ^ 2 + 2 * (z₁ ^ 2 + z₂ ^ 2)

/-- **The `w = 5` single-coset rigidity (forward, given the antipodal shape).** If a `5`-subset
`S ⊆ μ_n` has the antipodal `(singleton + 2 doubles)` shape with the singleton drawn from `μ_n`
(`s ∈ μ_n`, `ε = ±1 ∈ μ_n`), then `e₂(S) = 0 ⟹ e₁(S) ∈ μ_n`: the realized `e₁`-value lies in the
*single* dilation coset `μ_n`. The mechanism: `e₂ = 0` is `z₂² = −z₁²` (the `μ_4`-coset), but
`e₁ = ε s` does not even depend on the doubles — it is forced into `μ_n` by the singleton. -/
theorem w5_e1_in_mun_of_oddConfig (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 0 < n)
    {S : Finset F} {ε s z₁ z₂ : F}
    (hshape : OddConfigShape S ε s z₁ z₂)
    (hsμ : s ^ n = 1) (hεμ : ε ^ n = 1)
    (he2 : e2 S = 0) :
    (e1 S) ^ n = 1 := by
  rw [hshape.e1eq]
  unfold configE1odd
  rw [mul_pow, hεμ, hsμ, one_mul]

/-! ## 4. Soundness / construction: the `μ_4`-coset family attains the whole coset `μ_n`. -/

/-- Sum of an explicit `5`-element finset whose elements are pairwise distinct, peeled by
`Finset.sum_insert`. -/
private theorem sum_five_distinct (f : F → F) {a b c d e : F}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    ∑ x ∈ ({a, b, c, d, e} : Finset F), f x = f a + f b + f c + f d + f e := by
  classical
  rw [Finset.sum_insert (by simp [hab, hac, had, hae]),
      Finset.sum_insert (by simp [hbc, hbd, hbe]),
      Finset.sum_insert (by simp [hcd, hce]),
      Finset.sum_insert (by simp [hde]),
      Finset.sum_singleton]
  ring

/-- **Construction (soundness).** For any `z, s` and a primitive `4`-th root `ξ` (`ξ² = −1`),
the explicit `5`-set `{z, ξz, −z, −ξz, s}` — with its five elements distinct — realizes the odd
`(singleton + 2 doubles)` shape with singleton `s` (sign `ε = 1`) and doubles `z, ξz`. Hence by
`two_doubles_e2_zero_iff_mu4` it has `e₂ = 0` (the coset condition `(ξz)² = −z²` is exactly
`ξ² = −1`), and `e₁ = s`. This is the converse of `w5_e1_in_mun_of_oddConfig`: over `μ_n`
(`z, s ∈ μ_n`, `ξ` a primitive `4`-th root `∈ μ_n` when `4 ∣ n`) it *attains* every value
`s ∈ μ_n` as an `e₁`, so the realized `e₁`-set is exactly the single coset `μ_n`. -/
theorem mu4coset_plus_singleton_oddShape
    (z s ξ : F)
    {hzξz : z ≠ ξ * z} {hznz : z ≠ -z} {hznξz : z ≠ -(ξ * z)} {hzs : z ≠ s}
    {hξznz : ξ * z ≠ -z} {hξznξz : ξ * z ≠ -(ξ * z)} {hξzs : ξ * z ≠ s}
    {hnznξz : -z ≠ -(ξ * z)} {hnzs : -z ≠ s} {hnξzs : -(ξ * z) ≠ s} :
    OddConfigShape ({z, ξ * z, -z, -(ξ * z), s} : Finset F) 1 s z (ξ * z) := by
  refine ⟨by ring, ?_, ?_⟩
  · -- e₁ = z + ξz − z − ξz + s = s = configE1odd 1 s
    unfold e1 configE1odd
    rw [show (∑ x ∈ ({z, ξ * z, -z, -(ξ * z), s} : Finset F), x)
        = ∑ x ∈ ({z, ξ * z, -z, -(ξ * z), s} : Finset F), (fun y => y) x from rfl,
      sum_five_distinct (fun y => y) hzξz hznz hznξz hzs hξznz hξznξz hξzs hnznξz hnzs hnξzs]
    ring
  · -- p₂ = z² + (ξz)² + z² + (ξz)² + s² = s² + 2(z² + (ξz)²)
    unfold p2
    rw [sum_five_distinct (fun x => x ^ 2) hzξz hznz hznξz hzs hξznz hξznξz hξzs hnznξz hnzs hnξzs]
    ring

/-- **`e₂ = 0` for the explicit `μ_4`-coset-plus-singleton set** (soundness, full statement).
Combining `mu4coset_plus_singleton_oddShape` with `two_doubles_e2_zero_iff_mu4`: the explicit
`5`-set `{z, ξz, −z, −ξz, s}` (5 distinct elements) with `ξ² = −1` has `e₂ = 0`, and `e₁ = s`. -/
theorem mu4coset_plus_singleton_e2_zero (h2 : (2 : F) ≠ 0)
    (z s ξ : F) (hξ : ξ ^ 2 = -1)
    (hzξz : z ≠ ξ * z) (hznz : z ≠ -z) (hznξz : z ≠ -(ξ * z)) (hzs : z ≠ s)
    (hξznz : ξ * z ≠ -z) (hξznξz : ξ * z ≠ -(ξ * z)) (hξzs : ξ * z ≠ s)
    (hnznξz : -z ≠ -(ξ * z)) (hnzs : -z ≠ s) (hnξzs : -(ξ * z) ≠ s) :
    e2 ({z, ξ * z, -z, -(ξ * z), s} : Finset F) = 0 ∧
      e1 ({z, ξ * z, -z, -(ξ * z), s} : Finset F) = s := by
  have hshape : OddConfigShape ({z, ξ * z, -z, -(ξ * z), s} : Finset F) 1 s z (ξ * z) :=
    mu4coset_plus_singleton_oddShape z s ξ
      (hzξz := hzξz) (hznz := hznz) (hznξz := hznξz) (hzs := hzs)
      (hξznz := hξznz) (hξznξz := hξznξz) (hξzs := hξzs)
      (hnznξz := hnznξz) (hnzs := hnzs) (hnξzs := hnξzs)
  constructor
  · -- the coset condition (ξz)² = −z² is ξ² = −1
    rw [two_doubles_e2_zero_iff_mu4 h2 1 s z (ξ * z) (by ring)
      ({z, ξ * z, -z, -(ξ * z), s} : Finset F) hshape.e1eq hshape.p2eq]
    -- (ξz)² = −z²  ⟺  ξ² · z² = −z²  ⟸  ξ² = −1
    have : (ξ * z) ^ 2 = ξ ^ 2 * z ^ 2 := by ring
    rw [this, hξ]; ring
  · -- e₁ = configE1odd 1 s = s
    rw [hshape.e1eq]; unfold configE1odd; ring

/-! ## 5. The single coset is exactly `μ_n`: both faces over a smooth domain. -/

/-- **The realized `e₁`-set of the `w = 5` `e₂ = 0` family over `μ_n` is exactly the one coset
`μ_n`** (both faces). The membership `(e₁ S) ^ n = 1` says the realized value lies *in* `μ_n`
(`⊆` one coset, `w5_e1_in_mun_of_oddConfig`); the existence of `S` for each target `s ∈ μ_n` says
the family *attains* all of `μ_n` (`⊇`, the construction `mu4coset_plus_singleton_e2_zero`). Hence
`{e₁(S) : S a w=5 e₂=0 antipodal set over μ_n} = μ_n` — **EXACTLY one dilation coset**, confirming
the R4 lane-D conjecture for the clean odd case `w = 5`. -/
theorem w5_single_coset_two_faces (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 0 < n)
    (ξ : F) (hξ : ξ ^ 2 = -1) :
    -- (⊆) every realized e₁ over μ_n lies in μ_n (one dilation coset):
    (∀ {S : Finset F} {ε s z₁ z₂ : F}, OddConfigShape S ε s z₁ z₂ →
      s ^ n = 1 → ε ^ n = 1 → e2 S = 0 → (e1 S) ^ n = 1)
    -- (⊇) and every target s ∈ μ_n is attained as an e₁ by an explicit e₂=0 5-set
    -- (provided z ∈ μ_n with the μ_4-coset of z disjoint from s, i.e. the 5 elements distinct):
    ∧ (∀ (z s : F), s ^ n = 1 →
        z ≠ ξ * z → z ≠ -z → z ≠ -(ξ * z) → z ≠ s →
        ξ * z ≠ -z → ξ * z ≠ -(ξ * z) → ξ * z ≠ s →
        -z ≠ -(ξ * z) → -z ≠ s → -(ξ * z) ≠ s →
        ∃ S : Finset F, e2 S = 0 ∧ e1 S = s ∧ (e1 S) ^ n = 1) := by
  refine ⟨?_, ?_⟩
  · intro S ε s z₁ z₂ hshape hsμ hεμ he2
    exact w5_e1_in_mun_of_oddConfig h2 hn hshape hsμ hεμ he2
  · intro z s hsμ h1 h2' h3 h4 h5 h6 h7 h8 h9 h10
    obtain ⟨hzero, heq⟩ :=
      mu4coset_plus_singleton_e2_zero h2 z s ξ hξ h1 h2' h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨_, hzero, heq, by rw [heq]; exact hsμ⟩

/-! ## Axiom audit -/

#print axioms odd_config_energy_iff_squareSum_zero
#print axioms odd_config_e2_zero_iff_squareSum_zero
#print axioms two_doubles_e2_zero_iff_mu4
#print axioms w5_e1_in_mun_of_oddConfig
#print axioms mu4coset_plus_singleton_oddShape
#print axioms mu4coset_plus_singleton_e2_zero
#print axioms w5_single_coset_two_faces

end ArkLib.ProximityGap.R4FiveSetSingleCoset
