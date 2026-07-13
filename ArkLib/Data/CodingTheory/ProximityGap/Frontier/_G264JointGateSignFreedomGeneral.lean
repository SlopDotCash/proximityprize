/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G263JointRankSignFreedom

/-!
# G264: general joint-gate sign-freedom — the G263 no-go is r-uniform, not a fixed-depth island

G263 certified, at the single minimal cell `m = 5`, that the joint two-rank centered covariance
gate is sign-free: four explicit nonnegative-integer kernels realize all four sign quadrants of
`(Cov₅ W, Cov₆ W)`, and the structural cause is that the two centered per-class functionals are
linearly independent (a nonzero `2×2` minor). That file leaves the *general* mechanism asserted in
prose but proved only by four hand-picked witnesses at one cell.

This file proves the mechanism as a **theorem for every cell and every rank pair**. For an
arbitrary cyclic length `m`, arbitrary integer weight profiles whose centered functionals `f, g`
are zero-sum (the DC-subtraction property, `sum_centeredFunctional_eq_zero`), and *any* pair of
coordinates `i, j` at which the minor `D = f i · g j − f j · g i` is nonzero, the nonnegative
integer cone realizes **all four open sign quadrants** of `(⟨W, f⟩, ⟨W, g⟩)`.

The witness is closed-form. For a target sign pair `(s, t) ∈ {±1}²` set

```text
a = s · g j − t · f j,   b = t · f i − s · g i,   W = c • 1 + a • e i + b • e j
```

with `c` a large enough nonnegative constant to keep every entry `≥ 0`. Because `f` and `g` are
zero-sum, the constant offset contributes nothing (`covPairing` is offset-invariant), and Cramer's
identity gives **exactly**

```text
⟨W, f⟩ = a · f i + b · f j = s · D,      ⟨W, g⟩ = a · g i + b · g j = t · D.
```

Hence `sign ⟨W, f⟩ = s · sign D` and `sign ⟨W, g⟩ = t · sign D`, so ranging `(s, t)` over `{±1}²`
hits all four sign quadrants regardless of the sign of `D`. No `decide`, no fixed cell, no rank
restriction: whenever two centered rank functionals are independent — which G64 forces for the two
live sponsor ranks at prize depth — the joint gate carries no cross-rank sign-forcing leverage.

Two corollaries recover the landed G263 cell (`m = 5`, minor `15`) from the general theorem, tying
the r-uniform statement back to the certified minimal countermodel.

Scope (honest): route no-go, r-uniform strengthening of G263, not a sponsor-prime estimate and not
prize closure. The surviving admissible route is unchanged: a genuinely row-labelled sponsor
Jacobi/cyclotomic covariance proved directly against the row label at each rank.
-/

namespace ArkLib.ProximityGap.Frontier.G264JointGateSignFreedomGeneral

open Finset

variable {N : ℕ}

/-- The centered pairing on `Fin N`: `⟨W, f⟩ = ∑ x, W x · f x`. This is the abstract shape of the
DC-subtracted covariance `centeredCov W R = ⟨W, centeredFunctional R⟩` from G263. -/
def covPairing (W f : Fin N → ℤ) : ℤ := ∑ x, W x * f x

/-- Constant-offset invariance against a zero-sum functional: adding `c` to every kernel entry does
not change the pairing when `∑ f = 0`. This is the general form of G263's `centeredCov_add_const`
and the reason total-mass / principal-frequency inflation carries zero gate information. -/
theorem covPairing_add_const (W f : Fin N → ℤ) (c : ℤ) (hf : ∑ x, f x = 0) :
    covPairing (fun x => W x + c) f = covPairing W f := by
  unfold covPairing
  have : ∑ x, (W x + c) * f x = (∑ x, W x * f x) + c * ∑ x, f x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [this, hf, mul_zero, add_zero]

/-- The single-support indicator `e_i` (integer-valued), the atom of a nonnegative kernel. -/
def indicator (i : Fin N) : Fin N → ℤ := fun x => if x = i then 1 else 0

@[simp] theorem covPairing_indicator (i : Fin N) (f : Fin N → ℤ) :
    covPairing (indicator i) f = f i := by
  unfold covPairing indicator
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The two-coordinate integer kernel `a • e_i + b • e_j` (before the nonnegativity offset). -/
def twoAtom (i j : Fin N) (a b : ℤ) : Fin N → ℤ := fun x => a * indicator i x + b * indicator j x

/-- Pairing of the two-atom kernel is the linear combination `a · f i + b · f j`. -/
theorem covPairing_twoAtom (i j : Fin N) (a b : ℤ) (f : Fin N → ℤ) :
    covPairing (twoAtom i j a b) f = a * f i + b * f j := by
  unfold covPairing twoAtom
  have hsplit : ∀ x, (a * indicator i x + b * indicator j x) * f x
      = a * (indicator i x * f x) + b * (indicator j x * f x) := fun x => by ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hi : ∑ x, indicator i x * f x = f i := by
    have := covPairing_indicator i f; unfold covPairing at this; exact this
  have hj : ∑ x, indicator j x * f x = f j := by
    have := covPairing_indicator j f; unfold covPairing at this; exact this
  rw [hi, hj]

/-- **Cramer witness identity.** With `a = s·g j − t·f j`, `b = t·f i − s·g i`, the two-atom kernel
pairs to exactly `s · D` against `f` and `t · D` against `g`, where `D = f i · g j − f j · g i`.
Pure algebra, no `decide`. -/
theorem cramer_pairings (i j : Fin N) (f g : Fin N → ℤ) (s t : ℤ) :
    covPairing (twoAtom i j (s * g j - t * f j) (t * f i - s * g i)) f
        = s * (f i * g j - f j * g i)
    ∧ covPairing (twoAtom i j (s * g j - t * f j) (t * f i - s * g i)) g
        = t * (f i * g j - f j * g i) := by
  rw [covPairing_twoAtom, covPairing_twoAtom]
  constructor <;> ring

/-- **General joint-gate sign-freedom.** Let `f g : Fin N → ℤ` be *zero-sum* (centered) functionals
whose minor `D = f i · g j − f j · g i` at some coordinate pair `i ≠ j` is nonzero. Then for every
sign pair `(s, t) ∈ {±1}²` there is a **nonnegative-integer** kernel `W` with
`⟨W, f⟩ = s · D` and `⟨W, g⟩ = t · D`. Consequently, choosing `(s, t)` appropriately for each of
the four sign quadrants, the nonnegative-integer cone realizes every joint sign pattern
`(sign ⟨W, f⟩, sign ⟨W, g⟩)`: the joint two-rank centered gate is sign-free at *every* cell and
*every* rank pair for which the two centered functionals are independent. -/
theorem joint_gate_sign_free_of_minor
    {i j : Fin N} (hij : i ≠ j) (f g : Fin N → ℤ)
    (hf : ∑ x, f x = 0) (hg : ∑ x, g x = 0)
    (s t : ℤ) :
    ∃ W : Fin N → ℤ, (∀ x, 0 ≤ W x)
      ∧ covPairing W f = s * (f i * g j - f j * g i)
      ∧ covPairing W g = t * (f i * g j - f j * g i) := by
  set a : ℤ := s * g j - t * f j with ha
  set b : ℤ := t * f i - s * g i with hb
  -- offset that makes every entry of the two-atom kernel nonnegative
  set c : ℤ := max 0 (max (-a) (-b)) with hc
  have hc0 : 0 ≤ c := le_max_left _ _
  have hca : 0 ≤ a + c := by
    have : -a ≤ c := le_trans (le_max_left _ _) (le_max_right 0 _); linarith
  have hcb : 0 ≤ b + c := by
    have : -b ≤ c := le_trans (le_max_right _ _) (le_max_right 0 _); linarith
  refine ⟨fun x => twoAtom i j a b x + c, ?_, ?_, ?_⟩
  · -- nonnegativity: the base is `a` at i, `b` at j, `0` elsewhere; offset by `c ≥ 0`
    intro x
    unfold twoAtom indicator
    by_cases hxi : x = i
    · subst hxi; by_cases hxj : x = j
      · exact absurd hxj hij
      · simp only [if_neg hxj]; simpa using hca
    · by_cases hxj : x = j
      · subst hxj; simp only [if_neg hxi]; simpa using hcb
      · simp only [if_neg hxi, if_neg hxj]; simpa using hc0
  · rw [covPairing_add_const _ f c hf, (cramer_pairings i j f g s t).1]
  · rw [covPairing_add_const _ g c hg, (cramer_pairings i j f g s t).2]

/-- **All four joint sign quadrants are realized by nonnegative-integer kernels.** For the two sign
choices `s₀ = sign D`, and each `(ε₁, ε₂) ∈ {±1}²`, the kernel built from `(s, t) = (ε₁ s₀, ε₂ s₀)`
pairs to `(ε₁ |D|, ε₂ |D|)`, hence is strictly positive/negative exactly as `ε₁, ε₂` dictate
(`hD` guarantees `|D| > 0`, so each quadrant is genuinely open). The conclusion exposes **both**
strict directions — `0 < ⟨W,f⟩ ↔ ε₁ = 1` and `⟨W,f⟩ < 0 ↔ ε₁ = -1` (likewise for `g`) — so a
downstream consumer gets genuine strict positivity/negativity, not mere non-positivity. Thus the
nonnegative cone meets all four open quadrants of `(⟨W,f⟩, ⟨W,g⟩)` and the joint gate is
sign-free. -/
theorem joint_gate_all_quadrants
    {i j : Fin N} (hij : i ≠ j) (f g : Fin N → ℤ)
    (hf : ∑ x, f x = 0) (hg : ∑ x, g x = 0)
    (hD : f i * g j - f j * g i ≠ 0) :
    ∀ ε₁ ε₂ : ℤ, (ε₁ = 1 ∨ ε₁ = -1) → (ε₂ = 1 ∨ ε₂ = -1) →
      ∃ W : Fin N → ℤ, (∀ x, 0 ≤ W x)
        -- strict, both-sided sign control: each open quadrant is genuinely realized
        ∧ (0 < covPairing W f ↔ ε₁ = 1) ∧ (covPairing W f < 0 ↔ ε₁ = -1)
        ∧ (0 < covPairing W g ↔ ε₂ = 1) ∧ (covPairing W g < 0 ↔ ε₂ = -1) := by
  intro ε₁ ε₂ hε₁ hε₂
  -- normalise the sign so that `s₀ · D = |D| > 0`
  set D : ℤ := f i * g j - f j * g i with hDdef
  set s₀ : ℤ := if 0 < D then 1 else -1 with hs0
  have hpos : 0 < s₀ * D := by
    rcases lt_trichotomy 0 D with hDpos | hDzero | hDneg
    · have : s₀ = 1 := by simp [hs0, hDpos]
      rw [this, one_mul]; exact hDpos
    · exact absurd hDzero.symm hD
    · have : s₀ = -1 := by simp [hs0, not_lt.mpr (le_of_lt hDneg)]
      rw [this]; nlinarith
  obtain ⟨W, hW0, hWf, hWg⟩ :=
    joint_gate_sign_free_of_minor hij f g hf hg (ε₁ * s₀) (ε₂ * s₀)
  -- `⟨W,f⟩ = ε₁ · (s₀ D)` with `s₀ D > 0`, hence strictly positive iff `ε₁ = 1`
  -- and strictly negative iff `ε₁ = -1` (the two `±1` cases are exhaustive)
  have hWf' : covPairing W f = ε₁ * (s₀ * D) := by rw [hWf]; ring
  have hWg' : covPairing W g = ε₂ * (s₀ * D) := by rw [hWg]; ring
  refine ⟨W, hW0, ?_, ?_, ?_, ?_⟩
  · rw [hWf']; rcases hε₁ with h | h <;> subst h <;> constructor <;> intro <;> nlinarith
  · rw [hWf']; rcases hε₁ with h | h <;> subst h <;> constructor <;> intro <;> nlinarith
  · rw [hWg']; rcases hε₂ with h | h <;> subst h <;> constructor <;> intro <;> nlinarith
  · rw [hWg']; rcases hε₂ with h | h <;> subst h <;> constructor <;> intro <;> nlinarith

/-! ## Recovering the landed G263 cell from the general theorem

The general theorem, instantiated at G263's exact minimal cell (`m = 5`, centered functionals
`f₅ = (-4,1,-4,1,6)`, `f₆ = (1,-4,6,-4,1)`, minor `D = 15` at coordinates `0, 1`), reproduces the
four-quadrant sign-freedom that G263 certified by hand. This ties the r-uniform statement back to
the certified countermodel. -/

open ArkLib.ProximityGap.Frontier.G263JointRankSignFreedom in
/-- The G263 centered functionals are zero-sum — the hypothesis the general theorem needs. -/
theorem g263_functionals_zero_sum :
    (∑ x, centeredFunctional R5 x = 0) ∧ (∑ x, centeredFunctional R6 x = 0) :=
  ⟨sum_centeredFunctional_eq_zero R5, sum_centeredFunctional_eq_zero R6⟩

open ArkLib.ProximityGap.Frontier.G263JointRankSignFreedom in
/-- Instantiating the general sign-freedom at the G263 cell: for every `(s, t)` a
nonnegative-integer kernel realizes `(s·15, t·15)`, recovering all four quadrants from the general
mechanism rather than from hand-picked witnesses. -/
theorem g263_recovered_from_general (s t : ℤ) :
    ∃ W : Fin 5 → ℤ, (∀ x, 0 ≤ W x)
      ∧ covPairing W (centeredFunctional R5) = s * 15
      ∧ covPairing W (centeredFunctional R6) = t * 15 := by
  have hminor :
      centeredFunctional R5 (0 : Fin 5) * centeredFunctional R6 (1 : Fin 5)
        - centeredFunctional R5 (1 : Fin 5) * centeredFunctional R6 (0 : Fin 5) = 15 :=
    centeredFunctionals_independent
  obtain ⟨W, hW0, hWf, hWg⟩ :=
    joint_gate_sign_free_of_minor (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide)
      (centeredFunctional R5) (centeredFunctional R6)
      (sum_centeredFunctional_eq_zero R5) (sum_centeredFunctional_eq_zero R6) s t
  rw [hminor] at hWf hWg
  exact ⟨W, hW0, hWf, hWg⟩

/-- Route status marker: G264 is an r-uniform strengthening of the G263 no-go, not prize closure. -/
def isPrizeClosure : Bool := false

theorem not_prizeClosure : isPrizeClosure = false := rfl

end ArkLib.ProximityGap.Frontier.G264JointGateSignFreedomGeneral
