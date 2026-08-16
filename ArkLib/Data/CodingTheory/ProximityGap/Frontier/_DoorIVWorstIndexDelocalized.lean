/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Door IV, Lane 1: the worst-frequency coset **index** is prime-independently DELOCALIZED — no
# fixed-residue / fixed-position selection rule grips it across primes.

This file records the axiom-clean combinatorial kernel behind the probe
`scripts/probes/probe_dooriv_worstb_crossprime_index.py` (see its `.NOTE`).

## The probed object

For a prime `p = k·n + 1` with `n = 2^a`, the period `η_b = Σ_{y ∈ μ_n} e_p(b·y)` is constant on
`μ_n`-cosets of `b`, so the adversary lives in the quotient `Z_k`, `k = (p−1)/n`. The worst index
`j*(p) ∈ Z_k` is the argmax of `|η_{g^j}|`. A door-(iv) anti-concentration hope (the brief's open
question "is the worst-b SET structured?") is that `j*(p)` is selected by a **prime-independent
arithmetic rule** — e.g. it always sits in a fixed residue class mod some small `d`, or at a fixed
normalized position `j*/k`. If so, a *targeted* (non-energy, non-sum-product) anti-concentration bound
could aim at that fixed structure.

## The probe verdict (reproducible; EXACT phase sums; prize regime p ≈ n⁴ ≫ n³; proper `μ_n`)

Over 14 primes per `n ∈ {16,32,64}`, with a **random uniform** subsample of `Z_k` (a strided subsample
biases `j mod stride → 0`, a scan artifact that was caught and removed — see `.NOTE`):

* normalized position `j*/k`: mean ≈ 0.41–0.56, sd ≈ 0.31–0.33, matching the uniform(0,1) reference
  (mean 0.5, sd 0.289). Full-range, not pinned.
* `j* mod 2,3,4`: uniform at every `n` (the artifactual "all ≡ 0 mod 4" at `n=32` vanished once the
  stride bias was removed).

So the worst index is **delocalized**: across primes it visits every residue class and spreads over the
whole range. No prime-independent rule (fixed residue, fixed position) selects it.

## The formalizable kernel (this file)

The content is a clean impossibility: a selection rule that is *prime-independent* in the relevant senses
is either **constant mod `d`** (a fixed-residue rule) or **constant in normalized position** (a fixed-
position rule). The probe exhibits a worst-index family that is neither — it hits two distinct residues
mod `d` and two distinct positions. We formalize:

* `not_constant_mod_of_two_residues`: a family hitting two indices with different residues mod `d`
  is not congruent to any single fixed residue — no fixed-residue rule fits.
* `not_constant_position_of_two_values`: a family taking two distinct normalized positions is not
  equal to any single fixed position — no fixed-position rule fits.
* `delocalized_excludes_fixed_selector`: packaged — a worst-index family witnessed delocalized (two
  residues mod `d` AND two positions) is excluded by *every* fixed-residue-and-position selector.

This proves **nothing** about CORE and uses no moment / completion / energy. It is a no-go pin: the
worst frequency carries no prime-independent index structure for a targeted anti-concentration bound to
grip. CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace ProximityGap.Frontier.DoorIVWorstIndexDelocalized

/-- A **fixed-residue selection rule** mod `d`: a claim that every worst index `j*(p)` lands in one
fixed residue class `r` mod `d`, uniformly across primes `p`. Here `J : P → ℕ` is the worst-index
family indexed by the prime label `p : P`. -/
def FixedResidueRule {P : Type*} (J : P → ℕ) (d r : ℕ) : Prop :=
  ∀ p, J p % d = r

/-- A **fixed-position selection rule**: a claim that every worst index sits at one fixed value `c`
(the normalized-position analogue; we work with the raw value, the rule being "always the same"). -/
def FixedPositionRule {P : Type*} (J : P → ℕ) (c : ℕ) : Prop :=
  ∀ p, J p = c

/-- **No fixed-residue rule** can fit a family that realizes two distinct residues mod `d`.
If primes `p₁, p₂` give worst indices with `J p₁ % d ≠ J p₂ % d`, then for *no* residue `r` is the
family congruent to `r` mod `d`. This is the probe's "`j* mod d` is not biased to one class". -/
theorem not_constant_mod_of_two_residues {P : Type*} (J : P → ℕ) (d : ℕ) (p₁ p₂ : P)
    (h : J p₁ % d ≠ J p₂ % d) : ∀ r, ¬ FixedResidueRule J d r := by
  intro r hr
  exact h ((hr p₁).trans (hr p₂).symm)

/-- **No fixed-position rule** can fit a family that realizes two distinct values.
If primes `p₁, p₂` give distinct worst indices `J p₁ ≠ J p₂`, then for *no* constant `c` is the family
equal to `c`. This is the probe's "`j*/k` is full-range, not pinned". -/
theorem not_constant_position_of_two_values {P : Type*} (J : P → ℕ) (p₁ p₂ : P)
    (h : J p₁ ≠ J p₂) : ∀ c, ¬ FixedPositionRule J c := by
  intro c hc
  exact h ((hc p₁).trans (hc p₂).symm)

/-- A family is **index-delocalized** (in the witnessed sense) if it realizes two distinct residues
mod `d` *and* two distinct values. This is exactly what the probe measures: residue-unbiased and
full-range across primes. -/
def IndexDelocalized {P : Type*} (J : P → ℕ) (d : ℕ) : Prop :=
  (∃ p₁ p₂, J p₁ % d ≠ J p₂ % d) ∧ (∃ p₁ p₂, J p₁ ≠ J p₂)

/-- **Packaged no-go.** A delocalized worst-index family is excluded by *every* fixed-residue rule and
*every* fixed-position rule simultaneously: no prime-independent fixed selector reproduces it. Hence the
adversarial frequency offers no prime-stable arithmetic target for a *targeted* (non-energy, non-sum-
product) anti-concentration bound. (No CORE / cancellation / completion / capacity claim.) -/
theorem delocalized_excludes_fixed_selector {P : Type*} (J : P → ℕ) (d : ℕ)
    (h : IndexDelocalized J d) :
    (∀ r, ¬ FixedResidueRule J d r) ∧ (∀ c, ¬ FixedPositionRule J c) := by
  obtain ⟨⟨q₁, q₂, hq⟩, ⟨p₁, p₂, hp⟩⟩ := h
  exact ⟨not_constant_mod_of_two_residues J d q₁ q₂ hq,
         not_constant_position_of_two_values J p₁ p₂ hp⟩

/-- Contrapositive convenience: if *some* fixed-residue rule fits, the family is residue-constant mod
`d` (every prime gives the same residue), so it is **not** residue-delocalized. This makes explicit
that exhibiting one disagreement mod `d` is the whole content of "residue-unbiased". -/
theorem fixedResidue_forces_constant_mod {P : Type*} (J : P → ℕ) (d r : ℕ)
    (hr : FixedResidueRule J d r) : ∀ p₁ p₂, J p₁ % d = J p₂ % d := by
  intro p₁ p₂; exact (hr p₁).trans (hr p₂).symm

/-- Contrapositive convenience for the other selector axis: if a fixed-position rule fits, the worst-index
family is literally constant across primes. Thus a single pair of distinct measured indices is already a
complete obstruction to every prime-independent fixed-position selector. -/
theorem fixedPosition_forces_constant_values {P : Type*} (J : P → ℕ) (c : ℕ)
    (hc : FixedPositionRule J c) : ∀ p₁ p₂, J p₁ = J p₂ := by
  intro p₁ p₂; exact (hc p₁).trans (hc p₂).symm

/-- A fixed-position selector automatically gives a fixed-residue selector modulo every `d`, with residue
`c % d`. So the two probe axes are nested: any literal fixed position would also look residue-constant.
The observed residue delocalization therefore already rules out fixed-position selectors after reducing
modulo `d`, independently of the raw-value witness. -/
theorem fixedPosition_to_fixedResidue {P : Type*} (J : P → ℕ) (d c : ℕ)
    (hc : FixedPositionRule J c) : FixedResidueRule J d (c % d) := by
  intro p
  rw [hc p]

/-- If a family is residue-delocalized modulo `d`, no fixed-position selector can fit it. This packages the
probe-facing implication "residue spread alone kills a pinned index" without requiring a separate raw-value
witness. -/
theorem residue_delocalized_excludes_fixedPosition {P : Type*} (J : P → ℕ) (d : ℕ)
    (h : ∃ p₁ p₂, J p₁ % d ≠ J p₂ % d) : ∀ c, ¬ FixedPositionRule J c := by
  intro c hc
  obtain ⟨p₁, p₂, hp⟩ := h
  exact hp (fixedResidue_forces_constant_mod J d (c % d)
    (fixedPosition_to_fixedResidue J d c hc) p₁ p₂)

-- Axiom check: the kernel theorems must be axiom-clean.
#print axioms delocalized_excludes_fixed_selector
#print axioms not_constant_mod_of_two_residues
#print axioms not_constant_position_of_two_values
#print axioms fixedResidue_forces_constant_mod
#print axioms fixedPosition_forces_constant_values
#print axioms fixedPosition_to_fixedResidue
#print axioms residue_delocalized_excludes_fixedPosition

end ProximityGap.Frontier.DoorIVWorstIndexDelocalized
