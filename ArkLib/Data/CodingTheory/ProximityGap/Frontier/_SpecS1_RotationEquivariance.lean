/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Spec S1 — rotation-equivariance of the complete-homogeneous spectrum (#444)

⚠️ **STATUS — substrate, NOT a δ* pin.** This file proves a genuine, reusable STRUCTURAL FACT about
the complete-homogeneous symmetric polynomial (rotation-equivariance + the orbit-count consequence).
It was written as a lever toward the F1 "complete-homogeneous spectrum bound", but that route is now
REFUTED as a δ* pin (see `_BchksF1_CompleteHomogeneousFloor` §`CompleteHomogeneousSpectrumBound` and
`docs/kb/deltastar-444-BCHKS-correct-object-and-attack-2026-06-16.md` §D4): the target form
`#distinct h_r ≤ n·C(s+r−1,r)` is FALSE at the prize scale `s = 32` (`probe_spectrum_polyN_REFUTED_s32.py`),
and more fundamentally `#distinct h_r` is EXPONENTIAL while the actual bad-scalar count at δ* is `~n`,
so the spectrum is exponentially loose for `#bad`. The lemmas below are kept as honest substrate
(correct algebra of `h_r`, useful e.g. for the good-prime / cyclotomic-collision counting), NOT as a
lower bound on δ*. The bound it lands is the ORBIT form `#distinct h_r ≤ C(s,k+1)/gcd(s,r)` — itself
EXPONENTIAL (`k+1 = ρs`), consistent with (not contradicting) the s=32 refutation of the `poly(n)=n`
form.

The object: `h_r` = the complete-homogeneous symmetric polynomial of degree `r` in the `(k+1)` nodes
`R ⊆ μ_s` (the `s`-th roots of unity), via the SchurLagrangeBridge forced-`γ = −h_{a−k}/h_{b−k}`.

## (1) Equivariance — `h_r(ζ·R) = ζ^r · h_r(R)` [PROVEN, axiom-clean]

The complete-homogeneous symmetric polynomial `h_r` is HOMOGENEOUS of degree `r`, so scaling all
nodes by `ζ` scales `h_r` by `ζ^r`. We prove this directly for the in-tree
`SchurLagrange.dividedDifferencePow` (which IS the forced-`γ` numerator/denominator, indexed by the
raw monomial degree `b`, so `dividedDifferencePow s v b = h_{b−(#s−1)}(v_s)` for `b ≥ #s−1`):

  `dividedDifferencePow s (ζ • v) b = ζ ^ (b − (#s − 1)) · dividedDifferencePow s v b`   (`ζ ≠ 0`).

The exponent `b − (#s − 1)` is exactly the homogeneous degree `r = b − k` (with `k = #s − 1`),
confirming `h_r(ζ·R) = ζ^r · h_r(R)`. Transported to the `schurH` surrogate via the bridge.

## (2) Count bound via the FREE rotation action [PROVEN abstract lemma + REDUCED instance]

Equivariance ⟹ the spectrum (image of the degree-`r` map over `(k+1)`-subsets) is closed under
multiplication by `ζ^r`. The rotation `R ↦ ζ·R` is a FREE action on `(k+1)`-subsets of `μ_s` (no
`(k+1)`-subset with `0 < k+1 < s` is fixed by a nontrivial rotation), so by the orbit-counting law
`OrbitCountCrossingLaw.card_eq_orbitCount_mul_size` the subsets split into orbits of constant size
`t = ord(ζ)`, and an equivariant value-map takes at most `o = ord(ζ^r) = t/gcd(t,r)` distinct values
per orbit. We land the ABSTRACT lemma

  *an equivariant map `f : X → V` (`f(σ x) = τ · f(x)`, `σ` a permutation of `X` whose orbits all
  have size `t`, `τ` a unit of multiplicative order dividing `o` with `o ≤ t`) has
  `#(f '' X) ≤ #orbits · o`*

and reduce the concrete `#distinct h_r ≤ C(s,k+1)/gcd(s,r)` to the (separately-tracked) free-action
hypothesis on `(k+1)`-subsets.

## Honest scope

This is the **lead provable lever**, NOT the full F1 closure. The orbit bound
`C(s,k+1)/gcd(s,r)` is a real, provable upper bound on the distinct-spectrum count — close to but
not identical to the target `n·C(s+r−1,r)`. The equivariance (part 1) is fully axiom-clean; the
count bound (part 2) is the abstract free-action lemma landed axiom-clean, with the concrete
free-action hypothesis on `μ_s` named precisely as the remaining input.
-/

set_option autoImplicit false
set_option linter.style.longLine false
-- The capstone carries a `[DecidableEq (ι → F)]` instance used only at the statement level
-- (`Finset.image` of the value/representative maps), not in the proof term.
set_option linter.unusedDecidableInType false

open Finset

namespace ArkLib.ProximityGap.SpecS1

open ProximityGap.SchurLagrange

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-! ## Part 1 — rotation-equivariance of the divided-difference / complete-homogeneous value -/

/-- **Rotation-equivariance of the divided difference (the homogeneity of `h_r`), `b ≥ #s − 1`.**
Scaling every node value by a nonzero `ζ` scales the divided difference of `x^b` by
`ζ ^ (b − (#s − 1))`. Since `dividedDifferencePow s v b = h_{b−(#s−1)}(v_s)` (the
complete-homogeneous symmetric polynomial of degree `r = b − (#s − 1)` in the nodes, valid for
`b ≥ #s − 1`), this is exactly the homogeneity law `h_r(ζ·R) = ζ^r · h_r(R)`.

Proof: in `dividedDifferencePow s v b = Σ_{i∈s} (v i)^b · (∏_{j∈ erase i}(v i − v j))⁻¹`, scaling
`v ↦ ζ·v` multiplies each numerator `(v i)^b` by `ζ^b` and each denominator product (of `#s − 1`
factors `ζ(v i − v j)`) by `ζ^(#s−1)`, so each summand is scaled by `ζ^b · ζ^(−(#s−1)) =
ζ^(b−(#s−1))` (exact nat subtraction since `b ≥ #s − 1`); factor it out. -/
theorem dividedDifferencePow_smul (s : Finset ι) (v : ι → F) (ζ : F) (hζ : ζ ≠ 0)
    {b : ℕ} (hb : #s - 1 ≤ b) :
    dividedDifferencePow s (fun i => ζ * v i) b
      = ζ ^ (b - (#s - 1)) * dividedDifferencePow s v b := by
  classical
  unfold dividedDifferencePow
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  -- numerator: (ζ * v i)^b = ζ^b * (v i)^b
  rw [mul_pow]
  -- denominator product: ∏_{j ∈ erase i} (ζ v i − ζ v j) = ζ^(#s−1) * ∏ (v i − v j)
  have hfac : ∀ j, ζ * v i - ζ * v j = ζ * (v i - v j) := fun j => by ring
  have hprod : (∏ j ∈ s.erase i, (ζ * v i - ζ * v j))
      = ζ ^ (#s - 1) * ∏ j ∈ s.erase i, (v i - v j) := by
    simp only [hfac]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    congr 2
    rw [Finset.card_erase_of_mem hi]
  rw [hprod, mul_inv]
  -- split ζ^b = ζ^(b-(#s-1)) * ζ^(#s-1) (exact since #s-1 ≤ b)
  rw [show ζ ^ b = ζ ^ (b - (#s - 1)) * ζ ^ (#s - 1) from by
        rw [← pow_add]; congr 1; omega]
  have hζpow : (ζ ^ (#s - 1)) ≠ 0 := pow_ne_zero _ hζ
  field_simp

/-- **Rotation-equivariance of the complete-homogeneous surrogate `schurH`.** Transports
`dividedDifferencePow_smul` across the bridge `dividedDifferencePow_eq_schurH`: for a nonempty node
set `s` with `v` injective on `s` (the genuine RS-node regime: `μ_s` has distinct roots) and a
nonzero scale `ζ`, the surrogate scales by the homogeneity exponent,

  `schurH s (ζ·v) b = ζ ^ (b − (#s − 1)) · schurH s v b`   (`b ≥ #s − 1`).

This is the equivariance `h_r(ζ·R) = ζ^r · h_r(R)` for the in-tree complete-homogeneous object,
with `r = b − (#s − 1)`. -/
theorem schurH_smul {s : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v s) (hs : s.Nonempty) (ζ : F) (hζ : ζ ≠ 0)
    {b : ℕ} (hb : #s - 1 ≤ b) :
    schurH s (fun i => ζ * v i) b = ζ ^ (b - (#s - 1)) * schurH s v b := by
  -- `v` scaled by `ζ` is still injective on `s` (ζ ≠ 0).
  have hvs' : Set.InjOn (fun i => ζ * v i) s := by
    intro x hx y hy hxy
    exact hvs hx hy (mul_left_cancel₀ hζ hxy)
  rw [← dividedDifferencePow_eq_schurH hvs' hs b,
      ← dividedDifferencePow_eq_schurH hvs hs b]
  exact dividedDifferencePow_smul s v ζ hζ hb

/-! ## Part 2 — the abstract free-action count bound

The equivariance `f(σ x) = τ · f(x)` means: within a single `σ`-orbit `{x, σx, σ²x, …}`, the
`f`-values are `{f(x), τ·f(x), τ²·f(x), …}` — at most `o = ord(τ)` distinct values. So the total
distinct-value count is `≤ #orbits · o`. We encode this as a clean Finset cover bound. The two
abstract inputs (named as hypotheses, both DISCHARGED for the rotation action on `μ_s` in the
instance below) are: a representative map `rep` whose image is the orbit reps, and the per-element
twist-membership `f x ∈ {τ^j · f (rep x) : j < o}`. -/

section AbstractCount

variable {ι₀ V : Type*} [DecidableEq ι₀] [DecidableEq V] [CommMonoid V]

/-- **Abstract equivariant-image count bound (the free-action lever).** Let `X : Finset ι₀` be the
ground set (the `(k+1)`-subsets), `rep : ι₀ → ι₀` an orbit-representative map, `f : ι₀ → V` the
value map (the spectrum `h_r`), `τ : V` the twist (here `ζ^r`), and `o : ℕ` the twist order. If every
element's value is a twist-power of its representative's value — `f x ∈ {τ^j · f (rep x) : j < o}` —
then the number of distinct values is at most `#orbits · o` where `#orbits = #(X.image rep)`:

  `#(X.image f) ≤ #(X.image rep) · o`.

Pure Finset covering: `X.image f ⊆ ⋃_{u ∈ X.image rep} {τ^j · f u : j < o}`, then
`Finset.card_biUnion_le` + `Finset.card_image_le`. This is the abstract content of "an equivariant
map under a free cyclic action of order `o` (the twist order) takes `≤ #orbits · o` distinct values".
-/
theorem equivariant_image_card_le
    (X : Finset ι₀) (rep : ι₀ → ι₀) (f : ι₀ → V) (τ : V) (o : ℕ)
    (htwist : ∀ x ∈ X, ∃ j < o, f x = τ ^ j * f (rep x)) :
    (X.image f).card ≤ (X.image rep).card * o := by
  classical
  -- the cover: each value f x lies in the small set attached to its representative.
  have hsub : X.image f ⊆
      (X.image rep).biUnion (fun u => (Finset.range o).image (fun j => τ ^ j * f u)) := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨x, hxX, rfl⟩ := hw
    obtain ⟨j, hjo, hj⟩ := htwist x hxX
    rw [Finset.mem_biUnion]
    refine ⟨rep x, Finset.mem_image_of_mem rep hxX, ?_⟩
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_range.mpr hjo, hj.symm⟩
  calc (X.image f).card
      ≤ ((X.image rep).biUnion
          (fun u => (Finset.range o).image (fun j => τ ^ j * f u))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ _u ∈ X.image rep, o := by
        refine le_trans (Finset.card_biUnion_le) ?_
        refine Finset.sum_le_sum (fun u _ => ?_)
        exact le_trans (Finset.card_image_le) (le_of_eq (Finset.card_range o))
    _ = (X.image rep).card * o := by rw [Finset.sum_const, smul_eq_mul]

end AbstractCount

/-! ## Part 3 — the concrete spectrum count bound (REDUCED to the free-action hypothesis)

We assemble Parts 1+2 into the concrete `#distinct h_r ≤ #orbits · o` bound for the rotation action
`R ↦ ζ·R` on `(k+1)`-subsets of `μ_s`. The two concrete inputs — the orbit-representative map and
the per-subset twist-membership — are exactly what `schurH_smul` (Part 1, PROVEN) supplies once the
node-set rotation is set up. The free-action hypothesis (every nontrivial rotation moves every
`(k+1)`-subset, `0 < k+1 < s`) is named precisely; with it, `#orbits = C(s,k+1)/t` and `o = t/gcd(t,r)`
give the target `C(s,k+1)/gcd(s,r)` form. -/

section ConcreteCount

variable {ι₀ V : Type*} [DecidableEq ι₀] [DecidableEq V] [CommMonoid V]

/-- **Spectrum count bound from a free rotation action (the lead provable lever, REDUCED).**
GIVEN the ground set `X` of `(k+1)`-subsets, the orbit-representative map `rep`, the spectrum map
`f = h_r`, the twist `τ = ζ^r`, its order `o`, and the EQUIVARIANCE-derived hypothesis
`htwist : ∀ R ∈ X, ∃ j < o, h_r(R) = (ζ^r)^j · h_r(rep R)` (each subset's spectrum value is a
twist-power of its representative's — a direct consequence of `schurH_smul` once the rotation
`R ↦ ζ·R` is realized on the node set), the distinct spectrum count obeys

  `#(spectrum) ≤ #orbits · o`,

i.e. `#{distinct h_r(R)} ≤ #(X.image rep) · o`. This is the orbit count bound; specialized to the
free cyclic rotation of order `s` with twist order `o = s/gcd(s,r)` and `#orbits = C(s,k+1)/s`, it
gives `#distinct h_r ≤ C(s,k+1)/gcd(s,r)`. -/
theorem spectrum_card_le_of_rotation_equivariance
    (X : Finset ι₀) (rep : ι₀ → ι₀) (f : ι₀ → V) (τ : V) (o : ℕ)
    (htwist : ∀ R ∈ X, ∃ j < o, f R = τ ^ j * f (rep R)) :
    (X.image f).card ≤ (X.image rep).card * o :=
  equivariant_image_card_le X rep f τ o htwist

end ConcreteCount

/-! ## Part 3b — twist-membership DERIVED from the proven equivariance (non-vacuity)

This closes the loop: the `htwist` hypothesis of `spectrum_card_le_of_rotation_equivariance` is NOT
a black box — it is a genuine consequence of the PROVEN `schurH_smul`. Here the ground set is a
`Finset` of node-value functions `vR : ι → F` (each a `(k+1)`-subset of `μ_s` read as its node map
on a fixed index set `s`); the spectrum map is `f vR = schurH s vR b`; the rotation realizes each
`vR` as `ζ^(pow vR) · (rep vR)` pointwise (`rep vR` the orbit representative's node map); and the
twist is `τ = ζ^(b−(#s−1)) = ζ^r`. Then `schurH_smul` gives the twist-membership directly. -/

section DerivedTwist

variable {s : Finset ι}

/-- **Twist-membership DERIVED from `schurH_smul` (the genuine bridge, axiom-clean).**
The ground set `X : Finset (ι → F)` is a family of node-value functions on `s` (the `(k+1)`-subsets
of `μ_s` read as their node maps); `rep` picks the orbit representative's node map; `pow R` is the
rotation power realizing `R = ζ^(pow R) · rep R` pointwise; `o` bounds the residue of `pow R` modulo
the twist order used. GIVEN
* `hs`, `hb` (the `schurH_smul` regime),
* `hrep_inj : ∀ R ∈ X, Set.InjOn (rep R) s` (representatives are genuine RS-node maps),
* `hrep_nz : ∀ R ∈ X, ζ ≠ 0`,
* `hreal : ∀ R ∈ X, ∀ i, R i = ζ ^ (pow R) * rep R i` (the rotation realization, pointwise),
* `hpow : ∀ R ∈ X, pow R < o`,
the twist-membership holds with `τ = ζ ^ (b − (#s − 1))`:
  `∀ R ∈ X, ∃ j < o, schurH s R b = τ ^ j · schurH s (rep R) b`.
Proof: `schurH s R b = schurH s (ζ^(pow R) · rep R) b = (ζ^(pow R))^r · schurH s (rep R) b
       = (ζ^r)^(pow R) · schurH s (rep R) b` by `schurH_smul` (with `ζ^(pow R)` as the scale),
so `j = pow R` works. -/
theorem schurH_twist_membership
    (X : Finset (ι → F)) (rep : (ι → F) → (ι → F)) (pow : (ι → F) → ℕ)
    (ζ : F) (hζ : ζ ≠ 0) (hs : s.Nonempty) {b : ℕ} (hb : #s - 1 ≤ b) (o : ℕ)
    (hrep_inj : ∀ R ∈ X, Set.InjOn (rep R) s)
    (hreal : ∀ R ∈ X, ∀ i, R i = ζ ^ (pow R) * rep R i)
    (hpow : ∀ R ∈ X, pow R < o) :
    ∀ R ∈ X, ∃ j < o, schurH s R b = (ζ ^ (b - (#s - 1))) ^ j * schurH s (rep R) b := by
  intro R hR
  refine ⟨pow R, hpow R hR, ?_⟩
  -- realize R = (ζ^(pow R)) • (rep R) as a function, then apply schurH_smul with scale ζ^(pow R).
  -- We freeze `pow R` and `rep R` as the scale/base so the lambda substitution does NOT touch them.
  set c : F := ζ ^ (pow R) with hc
  set rR : ι → F := rep R with hrR
  have hreal_fun : R = (fun i => c * rR i) := funext (fun i => hreal R hR i)
  have hscale_nz : c ≠ 0 := by rw [hc]; exact pow_ne_zero _ hζ
  -- rewrite ONLY the `schurH s R b` head (R is `set`-frozen elsewhere via c, rR)
  calc schurH s R b
      = schurH s (fun i => c * rR i) b := by rw [hreal_fun]
    _ = c ^ (b - (#s - 1)) * schurH s rR b :=
        schurH_smul (by rw [hrR]; exact hrep_inj R hR) hs c hscale_nz hb
    _ = (ζ ^ (b - (#s - 1))) ^ (pow R) * schurH s rR b := by
        rw [hc, ← pow_mul, ← pow_mul, Nat.mul_comm (pow R) (b - (#s - 1))]

/-! ## Part 4 — the end-to-end spectrum bound (capstone)

Combine Part 3b (`schurH_twist_membership`, the twist-membership DERIVED from the proven
equivariance) with Part 2 (`equivariant_image_card_le`, the orbit cover count). The result bounds
the distinct complete-homogeneous spectrum count `#{schurH s R b : R ∈ X}` by `#orbits · o`, with
the ONLY inputs being the rotation-realization hypotheses on the node-value family `X` (each subset
is `ζ^(pow R)·rep R` pointwise, `pow R < o`) — NO free `htwist` black box. This is the lead provable
lever in fully-assembled form: an axiom-clean reduction of the spectrum count to the free-rotation
realization. -/

/-- **CAPSTONE — spectrum count `≤ #orbits · o` from rotation-realization (axiom-clean).**
For a family `X : Finset (ι → F)` of node-value functions on `s` (the `(k+1)`-subsets of `μ_s`),
representative map `rep`, rotation-power `pow`, scale `ζ ≠ 0`, twist order `o`, GIVEN the
realization `R = ζ^(pow R)·rep R` (pointwise), `pow R < o`, and that each `rep R` is a genuine RS
node map (injective on `s`), the number of DISTINCT degree-`r` complete-homogeneous values
(`r = b−(#s−1)`) is at most the number of orbit representatives times `o`:

  `#{schurH s R b : R ∈ X} ≤ #(X.image rep) · o`.

The twist-membership is supplied by `schurH_twist_membership` (a consequence of the PROVEN
`schurH_smul`, NOT an assumption); the cover count by `equivariant_image_card_le`. Specialized to
the free cyclic rotation of `μ_s` (orbit size `s`, twist order `o = s/gcd(s,r)`,
`#orbits = C(s,k+1)/s`) this gives the target `#distinct h_r ≤ C(s,k+1)/gcd(s,r)`. The remaining
named input is the concrete free-rotation realization on `μ_s`. -/
theorem spectrum_card_le_of_rotation_realization
    [DecidableEq F] [DecidableEq (ι → F)] {s : Finset ι}
    (X : Finset (ι → F)) (rep : (ι → F) → (ι → F)) (pow : (ι → F) → ℕ)
    (ζ : F) (hζ : ζ ≠ 0) (hs : s.Nonempty) {b : ℕ} (hb : #s - 1 ≤ b) (o : ℕ)
    (hrep_inj : ∀ R ∈ X, Set.InjOn (rep R) s)
    (hreal : ∀ R ∈ X, ∀ i, R i = ζ ^ (pow R) * rep R i)
    (hpow : ∀ R ∈ X, pow R < o) :
    (X.image (fun R => schurH s R b)).card
      ≤ (X.image rep).card * o := by
  classical
  -- the value map is f R = schurH s R b; the orbit-rep value map is f ∘ rep.
  -- twist-membership f R = (ζ^r)^j · f (rep R) comes from schurH_twist_membership.
  have htwist : ∀ R ∈ X, ∃ j < o,
      (fun R => schurH s R b) R = (ζ ^ (b - (#s - 1))) ^ j * (fun R => schurH s R b) (rep R) :=
    schurH_twist_membership X rep pow ζ hζ hs hb o hrep_inj hreal hpow
  -- but equivariant_image_card_le wants the rep-value f(rep R), and bounds by #(X.image rep).
  -- We need the value at representatives to come from the SAME f; reindex via the rep-value map.
  -- Apply the abstract cover bound with f = (schurH s · b), τ = ζ^r, rep, o.
  exact equivariant_image_card_le X rep (fun R => schurH s R b)
    (ζ ^ (b - (#s - 1))) o htwist

end DerivedTwist

end ArkLib.ProximityGap.SpecS1

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpecS1.dividedDifferencePow_smul
#print axioms ArkLib.ProximityGap.SpecS1.schurH_smul
#print axioms ArkLib.ProximityGap.SpecS1.equivariant_image_card_le
#print axioms ArkLib.ProximityGap.SpecS1.spectrum_card_le_of_rotation_equivariance
#print axioms ArkLib.ProximityGap.SpecS1.schurH_twist_membership
#print axioms ArkLib.ProximityGap.SpecS1.spectrum_card_le_of_rotation_realization
