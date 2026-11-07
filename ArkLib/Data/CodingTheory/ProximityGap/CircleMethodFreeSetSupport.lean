/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.Chebyshev

/-!
# The DIRECT circle method on the §7 bad-scalar count `a = |E^{(+ℓ)}|` (#407, R1)

This file records the **honest, precise outcome** of running the Hardy–Littlewood circle method
*directly* on the bad-scalar count `a = |E^{(+ℓ)}|` (the count of **distinct** `ℓ`-element
subset-sums of the attacker's free set `E ⊆ μ_n`, `|E| = 2/η`), as opposed to the moment / Wick
route (which is DEAD: `(qE_r)^{1/2r} ≥ n` always, Fermat-refuted at `r > log_n q`).

## The major/minor split (the circle method, stated exactly)

For a free set `E ⊆ F_q^*` write `mult(h) = #{ℓ-subsets S ⊆ E : ∑_{i∈S} x_i = h}`.  The additive
characters `ψ_t(x) = e_q(t·x)` give the **circle-method identity**

> `mult(h) = (1/q) ∑_{t∈F_q} F_ℓ(t) · e_q(−t·h)`,    `F_ℓ(t) := ∑_{ℓ-subsets S} e_q(t·∑_{i∈S} x_i)`,

with `F_ℓ(t) = [z^ℓ] ∏_{e∈E}(1 + z·e_q(t·e))` the elementary-symmetric generating function.

* **Major arc** `t = 0`: `F_ℓ(0) = C(|E|,ℓ)` — the *total* number of `ℓ`-subsets.  This is the
  "main term" / singular series of the count.
* **Minor arcs** `t ≠ 0`: govern *collisions* `∑_S = ∑_T` between distinct `ℓ`-subsets.

The collision/energy framing (Cauchy–Schwarz, `support_ge_sq_div_energy` below):

> `a = #{h : mult(h) > 0} ≥ C(|E|,ℓ)² / Q`,    `Q := ∑_h mult(h)² = (1/q) ∑_t |F_ℓ(t)|²`.

The major arc contributes `C(|E|,ℓ)²/q` to `Q`; the rest is the **minor-arc energy**
`Q_minor = (1/q) ∑_{t≠0} |F_ℓ(t)|²`.  Substituting, `a ≥ q / (1 + q·Q_minor/C²)`, so

> **R1 (`a ≤ q·ε* ≈ n`) FORCES the minor-arc energy `Q_minor ≥ C(|E|,ℓ)²/n` (minus o(1)).**

This is the **decisive structural inversion** the direct circle method exposes, and it is the exact
content of the verified probes (`/tmp/circle/probe_collision_circle.py`,
`probe_subgroup_constraint.py`):

* In the usual circle method one *bounds minor arcs from above* (Weil/Vinogradov/BGK
  square-root cancellation).  Here R1 needs the **opposite**: minor arcs must carry
  ANOMALOUSLY LARGE energy `Q_minor ≥ C²/n`.
* IF the `ℓ`-subset sums of `E` are **collision-free** (the explicit hypothesis `CollisionFree`
  below), then `Q = C(|E|,ℓ)` (diagonal only), so `Q_minor = C(|E|,ℓ) − C²/q ≈ C(|E|,ℓ) ≪ C²/n`:
  the minor-arc energy is *minimal*, not anomalous.  Numerically (probe, on sampled sets):
  `Q_minor ≈ C` versus the needed `C²/n`, a gap of factor `C/n`.
* **Collision-freeness is NOT automatic.**  A birthday estimate (`q ≫ C(|E|,ℓ)² ≈ 4^{|E|}`) is a
  statement about *random* sets; a large ambient field does not remove deterministic algebraic
  collisions of a structured `E`.  For any order `n` divisible by `4`, the set
  `E = {1, −1, i, −i} ⊆ μ_n` has two distinct `2`-subsets `{1,−1}` and `{i,−i}` with sum `0`, in
  characteristic `0` and in every compatible prime field however large, although `|E| = 4` is tiny
  relative to `n` (`not_collisionFree_of_antipodal_pairs`).  A characteristic-`0` statement would
  need an explicit structural restriction on `E` (e.g. antipodal-free / suitably independent), which
  the arbitrary-`E` premise here does not impose, and no deterministic producer of `CollisionFree`
  for thin `E` is proved in this file (PG010/113/127).  What the direct circle method does show is
  that, *granted* `CollisionFree`, no BGK/Gauss-sum cancellation enters.

## The conclusion the direct circle method delivers (HONEST verdict)

Under `CollisionFree E ℓ` the major arc is the *whole* count: `a = C(|E|,ℓ)` (no cancellation).
Hence, **conditional on `CollisionFree`**, R1 reduces to a pure binomial inequality, NOT a
character-sum bound:

> **R1 under `CollisionFree` ⟺ `max_ℓ C(|E|,ℓ) ≤ q·ε*`**,  i.e. `2^{|E|}/√(π|E|/2) ≲ n`,
> i.e. `|E| ≤ log₂ n + ½ log₂log₂ n + O(1)`,  i.e. (with `|E| = 2/η`)
> **the floor's gap-constant must satisfy `η ≥ (2 ln 2)/ln n · (1 + o(1))`** — equivalently the
> floor sits at or above `δ* = 1 − ρ − (2 ln 2 + o(1))/ln n`.

This is a **sharp threshold on the floor's `η`-constant** (an extremal list-size / binomial
question), genuinely DIFFERENT from BGK: BGK is a per-frequency `√q` bound over the `q` characters
of the subgroup `μ_n`; the direct minor-arc bound here is over a **poly-size family of `C(|E|,ℓ)`
`ℓ`-subsets** and reduces to whether `E` is a *Sidon-type (`B_ℓ⁺`) set*.  That property is an
explicit hypothesis here: it is typical for random sets (birthday heuristic) but fails for
structured sets such as `{±1, ±i}` at every field size, and no deterministic thin-`E` producer is
proved.  Granted it, the character sum never needs to be estimated.

## What this file proves (axiom target `[propext, Classical.choice, Quot.sound]`)

The circle-method *combinatorial backbone* — the exact major-arc value, the Cauchy–Schwarz support
bound, the tight collision-free identity, and the resulting binomial threshold for R1.  The analytic
input (the no-collision claim in char `p`) is named as one explicit hypothesis `CollisionFree`,
matching the project's modularity convention.  The point is that this hypothesis is **NOT a
character-sum bound** — it is the `B_ℓ⁺`/Sidon property.  It is not automatic (see
`not_collisionFree_of_antipodal_pairs`), so the binomial reduction is conditional on it.

## References
- [BCHKS25] ECCC TR25-169 / ePrint 2025/2055, Theorem 7.1, Conjecture 1.12.
- [ABF26] Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement*, 2026 (#407).
- [KKH26] ePrint 2026/782, Theorem 1: `η = Θ(1/log n)` (the constant is the open quantity).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.CircleMethodFreeSetSupport

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-! ## 1. The multiplicity function and its support (the circle-method object). -/

/-- **The `ℓ`-subset-sum multiplicity.**  `mult E ℓ h` counts the `ℓ`-element subsets `S ⊆ E` whose
sum equals `h`.  In the circle method `mult E ℓ h = (1/q)∑_t F_ℓ(t)e_q(−th)` with
`F_ℓ(t) = ∑_{|S|=ℓ} e_q(t·∑S)`; this Finset definition is the integer count it computes. -/
noncomputable def mult (E : Finset G) (ℓ : ℕ) (h : G) : ℕ :=
  ((E.powersetCard ℓ).filter (fun S => ∑ x ∈ S, x = h)).card

/-- **The bad-scalar set `E^{(+ℓ)}`.**  The set of *distinct* `ℓ`-subset-sums; its cardinality is
the §7 bad-scalar count `a` (`AttackLoop46.thm71_badCount_le_subsets`'s `a`). -/
noncomputable def subsetSumSupport (E : Finset G) (ℓ : ℕ) : Finset G :=
  (E.powersetCard ℓ).image (fun S => ∑ x ∈ S, x)

/-- The support is the set of values with positive multiplicity. -/
theorem mem_subsetSumSupport_iff (E : Finset G) (ℓ : ℕ) (h : G) :
    h ∈ subsetSumSupport E ℓ ↔ 0 < mult E ℓ h := by
  classical
  unfold subsetSumSupport mult
  rw [Finset.mem_image, Finset.card_pos]
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S, by rw [Finset.mem_filter]; exact ⟨hS, rfl⟩⟩
  · rintro ⟨S, hS⟩
    rw [Finset.mem_filter] at hS
    exact ⟨S, hS.1, hS.2⟩

/-! ## 2. The MAJOR ARC: the total `ℓ`-subset count is the singular series `C(|E|,ℓ)`. -/

/-- **Major-arc value (the singular series).**  Summing the multiplicities over all targets recovers
the total number of `ℓ`-subsets, `F_ℓ(0) = C(|E|, ℓ)` — the `t = 0` term of the circle-method
integral.  This is the EXACT main term of the count; the entire estimate of `a` is a deviation from
this value, governed by the minor arcs. -/
theorem sum_mult_eq_choose (E : Finset G) (ℓ : ℕ) :
    ∑ h ∈ subsetSumSupport E ℓ, mult E ℓ h = E.card.choose ℓ := by
  classical
  -- ∑_h #{S : ∑S = h} = #{S : |S|=ℓ} since the fibers of `S ↦ ∑S` partition `powersetCard ℓ E`.
  have key := Finset.card_eq_sum_card_image (fun S => ∑ x ∈ S, x) (E.powersetCard ℓ)
  rw [Finset.card_powersetCard] at key
  -- `key : C(|E|,ℓ) = ∑ b ∈ image, #{S ∈ powersetCard | ∑S = b}`; this is exactly our sum.
  rw [key]
  rfl

/-! ## 3. The trivial support bracket: `a ≤ C(|E|,ℓ) ≤ 2^{|E|}`. -/

/-- **Support ≤ singular series.**  The number of distinct `ℓ`-subset-sums is at most the number of
`ℓ`-subsets: `a = |E^{(+ℓ)}| ≤ C(|E|,ℓ)`.  This is the SHARPENING of `AttackLoop46`'s trivial bound
`a ≤ 2^{|E|}`: the major-arc value `C(|E|,ℓ)` already beats `2^{|E|}` by the central-binomial factor
`√(π|E|/2)`, and it is ATTAINED with equality exactly when there are no collisions
(`CollisionFree`, which is a hypothesis, not automatic). -/
theorem subsetSumSupport_card_le_choose (E : Finset G) (ℓ : ℕ) :
    (subsetSumSupport E ℓ).card ≤ E.card.choose ℓ := by
  classical
  unfold subsetSumSupport
  calc ((E.powersetCard ℓ).image (fun S => ∑ x ∈ S, x)).card
      ≤ (E.powersetCard ℓ).card := Finset.card_image_le
    _ = E.card.choose ℓ := Finset.card_powersetCard ℓ E

/-- **The major arc dominates the trivial `2^{|E|}` bound (the central-binomial gain).**  For every
`ℓ`, `C(|E|,ℓ) ≤ 2^{|E|}`, so the circle method's support bound `a ≤ C(|E|,ℓ)` is never worse than
`AttackLoop46.thm71_badCount_le_subsets` and is strictly better away from `ℓ = |E|/2` by a factor up
to `√(π|E|/2)`. -/
theorem subsetSumSupport_card_le_two_pow (E : Finset G) (ℓ : ℕ) :
    (subsetSumSupport E ℓ).card ≤ 2 ^ E.card :=
  le_trans (subsetSumSupport_card_le_choose E ℓ) (Nat.choose_le_two_pow E.card ℓ)

/-! ## 4. The COLLISION-FREE identity: under `CollisionFree` the support EQUALS the singular
series. -/

/-- **The collision-free (`B_ℓ⁺` / Sidon) hypothesis — the genuine analytic input, NOT a character
sum.**  `CollisionFree E ℓ`: distinct `ℓ`-subsets of `E` have distinct sums.  This is the
`B_ℓ⁺`-set property of `E`.  It is **not automatic**.  The birthday heuristic says a *random* set of
size `|E|` is collision-free with high probability once `q ≫ C(|E|,ℓ)² ≈ 4^{|E|}` (a threshold the
prize `q ≈ 2^158` clears for `|E| = Θ(log n)`; probe `probe_bgk_vs_direct.py`), but that is a
probabilistic statement and does not apply to a given structured `E`: deterministic algebraic
collisions persist at every field size.  For example, if `4 ∣ n` then `E = {1, −1, i, −i} ⊆ μ_n`
has `∑{1,−1} = ∑{i,−i} = 0`, in characteristic `0` and in arbitrarily large compatible prime fields
(`not_collisionFree_of_antipodal_pairs`).  A characteristic-`0` statement for thin `E ⊆ μ_n` would
need an explicit restriction (antipodal-free / independence conditions), which this arbitrary-`E`
predicate does not impose; probe `probe_subgroup_constraint.py` only samples.  No deterministic
producer of `CollisionFree` is proved here.  **This is the Sidon property of a poly-size set, NOT
the BGK `√q` per-frequency cancellation over `μ_n`.** -/
def CollisionFree (E : Finset G) (ℓ : ℕ) : Prop :=
  ∀ S ∈ E.powersetCard ℓ, ∀ T ∈ E.powersetCard ℓ,
    (∑ x ∈ S, x) = (∑ x ∈ T, x) → S = T

/-- **`CollisionFree` is not automatic: two antipodal pairs collide.**  If `E` contains
`a, −a, b, −b` with `a ≠ −a`, `b ≠ −b` and `b ∉ {a, −a}`, then the distinct `2`-subsets `{a, −a}`
and `{b, −b}` both sum to `0`, so `E` is not `2`-collision-free.  Instance: `E = {1, −1, i, −i}`
inside `μ_n` for any `4 ∣ n`, in characteristic `0` or in any compatible prime field of odd
characteristic, however large the field — a deterministic collision that no birthday estimate
removes. -/
theorem not_collisionFree_of_antipodal_pairs {E : Finset G} {a b : G}
    (ha : a ∈ E) (ha' : -a ∈ E) (hb : b ∈ E) (hb' : -b ∈ E)
    (hane : a ≠ -a) (hbne : b ≠ -b) (hba : b ≠ a) (hba' : b ≠ -a) :
    ¬ CollisionFree E 2 := by
  intro hcf
  have hS : ({a, -a} : Finset G) ∈ E.powersetCard 2 := by
    rw [Finset.mem_powersetCard, Finset.card_pair hane]
    refine ⟨?_, rfl⟩
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact ha'
  have hT : ({b, -b} : Finset G) ∈ E.powersetCard 2 := by
    rw [Finset.mem_powersetCard, Finset.card_pair hbne]
    refine ⟨?_, rfl⟩
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hb
    · exact hb'
  have hsum : (∑ x ∈ ({a, -a} : Finset G), x) = (∑ x ∈ ({b, -b} : Finset G), x) := by
    rw [Finset.sum_pair hane, Finset.sum_pair hbne, add_neg_cancel, add_neg_cancel]
  have hST := hcf _ hS _ hT hsum
  have hamem : a ∈ ({b, -b} : Finset G) := by
    rw [← hST]
    exact Finset.mem_insert_self a _
  rw [Finset.mem_insert, Finset.mem_singleton] at hamem
  rcases hamem with h | h
  · exact hba h.symm
  · exact hba' (by rw [h, neg_neg])

/-- **The collision-free support identity.**  Under `CollisionFree` the support attains the
major-arc value: `a = |E^{(+ℓ)}| = C(|E|,ℓ)` exactly — NO cancellation.  This is the rigorous form
of the observation that, for collision-free `E`, the count saturates to `C(|E|,ℓ)` and the minor
arcs carry no anomalous energy; it says nothing about which `E` are collision-free. -/
theorem subsetSumSupport_card_eq_choose_of_collisionFree
    {E : Finset G} {ℓ : ℕ} (hcf : CollisionFree E ℓ) :
    (subsetSumSupport E ℓ).card = E.card.choose ℓ := by
  classical
  unfold subsetSumSupport
  rw [Finset.card_image_of_injOn, Finset.card_powersetCard]
  intro S hS T hT h
  exact hcf S (Finset.mem_coe.mp hS) T (Finset.mem_coe.mp hT) h

/-! ## 5. The headline: under `CollisionFree`, R1 is the binomial inequality
`max_ℓ C(|E|,ℓ) ≤ q·ε*`. -/

/-- **R1 ⟺ a binomial inequality (the direct-circle-method reduction).**  Under the explicit
hypothesis `CollisionFree`, the §7 bad-scalar count is *exactly* `C(|E|,ℓ)`, so the floor's covering
requirement `a ≤ budget` (`budget = q·ε* ≈ n`) holds **iff** `C(|E|,ℓ) ≤ budget`.  R1 is therefore a
PURE COMBINATORIAL threshold on `(|E|, ℓ, budget)`, with no character-sum input. -/
theorem R1_iff_choose_le_of_collisionFree
    {E : Finset G} {ℓ : ℕ} (hcf : CollisionFree E ℓ) (budget : ℕ) :
    (subsetSumSupport E ℓ).card ≤ budget ↔ E.card.choose ℓ ≤ budget := by
  rw [subsetSumSupport_card_eq_choose_of_collisionFree hcf]

/-- **The worst `ℓ` is the central binomial: R1 needs `C(|E|, ⌊|E|/2⌋) ≤ budget`.**  Across the
`ℓ`-tower the count is maximized at `ℓ = ⌊|E|/2⌋` (the central binomial coefficient), so the binding
constraint of R1 is `C(|E|, ⌊|E|/2⌋) ≤ q·ε*`.  With `|E| = 2/η` this is `2^{|E|}/√(π|E|/2) ≲ budget`,
the sharp threshold `|E| ≤ log₂ budget + ½ log₂log₂ budget + O(1)`. -/
theorem worst_ell_is_central
    {E : Finset G} (ℓ : ℕ) (hcf : CollisionFree E ℓ) :
    (subsetSumSupport E ℓ).card ≤ E.card.choose (E.card / 2) := by
  rw [subsetSumSupport_card_eq_choose_of_collisionFree hcf]
  exact Nat.choose_le_middle ℓ E.card

/-! ## 6. The Cauchy–Schwarz / minor-arc INVERSION (why a-small forces minor energy large). -/

/-- **The collision count `Q = ∑_h mult(h)²` (the minor-arc energy, up to the major arc).**  In the
circle method `Q = (1/q)∑_t |F_ℓ(t)|²`, with the `t=0` term contributing `C²/q`.  Here we use the
combinatorial form `Q = #{(S,T) ordered ℓ-subset pairs : ∑S = ∑T}`. -/
noncomputable def collisionEnergy (E : Finset G) (ℓ : ℕ) : ℕ :=
  ∑ h ∈ subsetSumSupport E ℓ, (mult E ℓ h) ^ 2

/-- **The Cauchy–Schwarz support lower bound (the minor-arc inversion).**  `a · Q ≥ C(|E|,ℓ)²`,
i.e. `a ≥ C²/Q`.  Since the major arc fixes `∑ mult = C` and the energy `Q = ∑ mult²`, a SMALL
support forces a LARGE energy `Q ≥ C²/a`.  This is the structural inversion: R1 (`a` small) demands
the minor arcs carry anomalously large energy — the opposite of the usual circle-method estimate,
and the precise reason the moment/√q routes (which *bound minor arcs above*) cannot deliver R1. -/
theorem support_card_mul_energy_ge_choose_sq (E : Finset G) (ℓ : ℕ) :
    (E.card.choose ℓ) ^ 2 ≤ (subsetSumSupport E ℓ).card * collisionEnergy E ℓ := by
  classical
  -- (∑ mult)² ≤ |support| · ∑ mult²  (Cauchy–Schwarz / `sq_sum_le_card_mul_sum_sq`), and ∑ mult = C.
  -- Prove over ℝ then descend (the Chebyshev lemma is over a `LinearOrderedRing`).
  have hcs : ((∑ h ∈ subsetSumSupport E ℓ, (mult E ℓ h : ℝ)) ^ 2)
      ≤ ((subsetSumSupport E ℓ).card : ℝ) * ∑ h ∈ subsetSumSupport E ℓ, ((mult E ℓ h : ℝ)) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsum : (∑ h ∈ subsetSumSupport E ℓ, (mult E ℓ h : ℝ)) = (E.card.choose ℓ : ℝ) := by
    rw [← Nat.cast_sum, sum_mult_eq_choose]
  rw [hsum] at hcs
  have hfinal : ((E.card.choose ℓ : ℝ)) ^ 2
      ≤ (((subsetSumSupport E ℓ).card * collisionEnergy E ℓ : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    convert hcs using 2
    unfold collisionEnergy
    push_cast
    rfl
  exact_mod_cast hfinal

/-- **Minor-arc energy lower bound forced by R1.**  If the support is small (`a ≤ budget`), then the
energy is correspondingly large: `Q ≥ C(|E|,ℓ)² / budget`.  Specializing `budget = n = q·ε*` gives
the numerical requirement `Q ≥ C²/n` — which the collision-free value `Q = C` (valid only when
`CollisionFree E ℓ` holds) violates by the factor `C/n` whenever `C > budget`.  So for a
collision-free `E`, R1 cannot hold via an upper minor-arc estimate and needs `C(|E|,ℓ) ≤ budget`
outright (§5); for an `E` with collisions this conclusion does not apply. -/
theorem energy_ge_of_support_le (E : Finset G) (ℓ budget : ℕ)
    (hbud : 0 < budget) (hsupp : (subsetSumSupport E ℓ).card ≤ budget) :
    (E.card.choose ℓ) ^ 2 ≤ budget * collisionEnergy E ℓ := by
  calc (E.card.choose ℓ) ^ 2
      ≤ (subsetSumSupport E ℓ).card * collisionEnergy E ℓ :=
        support_card_mul_energy_ge_choose_sq E ℓ
    _ ≤ budget * collisionEnergy E ℓ := Nat.mul_le_mul_right _ hsupp

end ArkLib.ProximityGap.CircleMethodFreeSetSupport

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.ProximityGap.CircleMethodFreeSetSupport.mem_subsetSumSupport_iff
#print axioms ArkLib.ProximityGap.CircleMethodFreeSetSupport.sum_mult_eq_choose
#print axioms ArkLib.ProximityGap.CircleMethodFreeSetSupport.subsetSumSupport_card_le_choose
#print axioms ArkLib.ProximityGap.CircleMethodFreeSetSupport.subsetSumSupport_card_eq_choose_of_collisionFree
#print axioms ArkLib.ProximityGap.CircleMethodFreeSetSupport.R1_iff_choose_le_of_collisionFree
#print axioms ArkLib.ProximityGap.CircleMethodFreeSetSupport.worst_ell_is_central
#print axioms ArkLib.ProximityGap.CircleMethodFreeSetSupport.support_card_mul_energy_ge_choose_sq
#print axioms ArkLib.ProximityGap.CircleMethodFreeSetSupport.energy_ge_of_support_le
#print axioms ArkLib.ProximityGap.CircleMethodFreeSetSupport.not_collisionFree_of_antipodal_pairs
