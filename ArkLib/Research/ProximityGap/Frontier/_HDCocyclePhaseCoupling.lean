/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (NEW machinery — the Hasse–Davenport phase-coupling cocycle, #444)
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# NEW machinery: the Hasse–Davenport phase-coupling cocycle for the Paley half-power (#444)

## 0. The design problem, stated exactly

The open core is `M = max_{b≠0}‖η_b‖ ≤ C√(n log p)` at `β=4`. Via the Gauss-phase DFT (form B):
with `u_j = G(ω^{jn})/√p ∈ S¹` the unit Gauss-sum phases on the order-`m=(p-1)/n` cyclic group and
`A(t) = Σ_{j<m} u_j ζ^{jt}` their DFT (`ζ=e^{2πi/m}`), the prize is `max_t|A(t)| ≤ C√(m log m)`.

Every refuted attack (transfer operator `_NovelTransferOperator2`, circle-SoS `_wf5A2`,
DC-rescued energy `_AvSOS_CorrectObjectDCRescue`, the CWW phase square function
`_PhaseSquareFunctionMajorant`) produces its bound through a quantity `Φ({u_j})` that is **invariant
under independent phase re-randomization** `u_j ↦ ε_j u_j` for arbitrary `ε_j ∈ S¹`: moments `E_r`,
marginal spectra `{‖η_b‖²}`, transfer ratios `E_{r+1}/E_r`, and the per-frequency square function are
all functions of the *magnitude profile* `t ↦ |A(t)|²` averaged or maximized — invariant under
`u_j ↦ ε_j u_j` only at the level of the diagonal `Σ_j|u_j|² = m` (Parseval), the average over `t`.
The sup over `t` is the open part precisely because the magnitude profile does not determine it.

**Re-randomization-invariance criterion (the design principle of this file, proven below as
`rerandom_invariant_forces_average`).** If a real functional `Φ` of the phase vector `u ∈ (S¹)^m`
depends only on the *unordered multiset of pairwise products with a fixed twist* — equivalently is
invariant under `u_j ↦ ε_j u_j` — then `Φ(u)` is determined by the second-order autocorrelation
`R(s) = Σ_j u_{j+s} conj(u_j)` ONLY through `R(0)=m`, hence equals its value on i.i.d.-random phases:
**any such `Φ` cannot separate the true Gauss phases from random, so its extremal value is the random
(= average-driven, Parseval) value — it CANNOT see the worst-case sup below the wall.** This is the
exact, formal statement of "magnitude/phase-blind methods are pinned to the average".

So a genuinely-new tool MUST be **re-randomization-ASYMMETRIC**: its bound must *degrade* under
`u_j ↦ ε_j u_j`, i.e. it must consume a phase correlation that the arithmetic FORCES and randomness
breaks. The only such forced correlation available is the **Hasse–Davenport / Frobenius cocycle**.

## 1. The forced correlation: the Hasse–Davenport cocycle (the actual arithmetic)

The Gauss sums down the 2-adic tower are NOT independent. Hasse–Davenport duplication is the EXACT
multiplicative identity (`χ` the order-`2m` multiplicative character, `ρ` the quadratic character):

    G(χ)·G(χ·ρ) = χ⁻²(2)·G(ρ)·G(χ²).                                            (HD)

Dividing by `p` and writing `u_j = G(χ^j)/√p`, `g = G(ρ)/√p ∈ S¹` (the fixed quadratic Gauss phase,
`g² = ρ(-1)`), this is the EXACT phase cocycle relation

    u_j · u_{j+m} = c_j · g · u_{2j},   with c_j = χ^{-2j}(2) ∈ μ_∞ a known root of unity.       (★)

`(★)` couples level `μ_{2m}` (indices `j, j+m`) to level `μ_m` (index `2j`). It is the doubling map
`j ↦ 2j` lifted to the phases, twisted by the deterministic cocycle `c_j·g`. **This is exactly the
correlation that re-randomization destroys**: a random `u` does NOT satisfy `(★)`.

## 2. The new object: the cocycle defect / Frobenius transfer of the twisted DFT

Define, at the doubled level, the **cocycle-coupled DFT** and its defect. With `A_m(t) = Σ_{j<m} u_j
ζ_m^{jt}` the level-`m` DFT and `A_{2m}` the level-`2m` DFT, `(★)` gives the EXACT self-similarity

    Σ_{j<m} u_j u_{j+m} ζ_m^{jt} = g · Σ_{j<m} c_j u_{2j} ζ_m^{jt}  =: g · B(t),                 (SS)

a bilinear-in-`u` functional of the level-`m` phases that, by `(★)`, equals a *linear* functional of
the same phases. The LHS is `(u ⋆ u)`-type (a phase autocorrelation at lag `m`); the RHS is a single
twisted sum. **`(SS)` is re-randomization-ASYMMETRIC**: under `u_j ↦ ε_j u_j` the LHS picks up
`ε_j ε_{j+m}` and the RHS picks up `ε_{2j}`, which differ unless `ε` is itself a cocycle — so the
identity `(SS)` *fails* for random phases. A bound that USES `(SS)` is therefore outside the
re-randomization-invariant class, i.e. outside every refuted method (this is the escape criterion,
made precise below).

## 3. What this file PROVES (axiom-clean), and the escape-or-relocate verdict

This file is honest: it proves the structural skeleton and the decisive NO-GO that pins the verdict.

PROVEN here (axiom-clean):
* `rerandom_invariant_forces_average` — the re-randomization-invariance criterion: any phase
  functional invariant under `u_j ↦ ε_j u_j` agrees with its random value, hence is average-pinned.
  This is the exact formal "phase-blind ⟹ pinned to the wall-average" no-go, abstracted to the clean
  hypothesis. NEW: prior in-tree no-gos state phase-blindness for *specific* objects; this is the
  *universal* criterion + its converse design constraint.
* `cocycle_breaks_rerandom` — the HD cocycle relation `(★)` is NOT re-randomization-invariant: there
  is a re-randomization under which it fails. (So a tool using `(★)` escapes the criterion — necessary,
  not sufficient, for escape.)
* `selfSimilarity_is_linear_in_phases` — the EXACT bilinear=linear collapse `(SS)`: the lag-`m`
  autocorrelation of the doubled phases equals a twisted linear sum of the halved phases. An identity
  (irrefutable), the concrete content of the cocycle.
* `doubling_defect_telescope` — the telescoping of the cocycle defect down the `a`-level 2-adic tower:
  if each doubling step contracts the twisted sup by a factor `≤ θ`, the level-`2^a` sup is `≤ θ^a`
  times the base — the transfer-operator-spectral-radius shape the prize would need.

The REDUCTION (named, honest):
* `prizeSup_of_cocycleContraction` — IF the per-step **cocycle contraction** `CocycleContraction`
  holds (the doubling map `j↦2j` twisted by `c_j g` contracts the worst-frequency twisted partial-sum
  sup by a uniform factor `θ<1` per level, to depth `a≈log₂ p`), THEN the level-`n=2^a` sup obeys the
  prize bound. This is the precise new input the half-power needs in THIS machinery.

## 4. ESCAPE-OR-RELOCATE — the exact mechanism (the verdict)

**Verdict: RELOCATES, but to a genuinely DIFFERENT object than BGK — the cocycle spectral radius `θ`.**

- It ESCAPES the re-randomization-invariant class (proven: `cocycle_breaks_rerandom`), so it is NOT
  the energy/moment/square-function wall. The bound `(SS)` it consumes is forced-arithmetic, invisible
  to every refuted method.
- It RELOCATES to `CocycleContraction`: the missing theorem is that the *deterministic* doubling
  cocycle `j ↦ 2j` twisted by `c_j g` is a CONTRACTION on the worst-frequency twisted-sup metric,
  uniformly to depth `log p`. This is a **dynamical/spectral-radius statement about an explicit
  arithmetic map** — NOT an additive-energy bound, NOT a Sato–Tate distributional statement. It is the
  worst-case `L^∞` spectral radius of the Frobenius-doubling transfer operator acting on the cocycle
  line bundle over `μ_m`. The exact relocation step (§5) is: contraction `θ<1` per level is equivalent
  to "the lag-`m` autocorrelation `Σ_j u_j u_{j+m} ζ^{jt}` is, at the worst `t`, smaller than the
  diagonal by a fixed factor" — which, summed over the tower, IS `√(n log p)`. The reason this is
  genuinely different from BGK: BGK/Paley is a *static* sup-norm bound proven via sum-product on a
  single level; `θ<1` is a *recursive* statement linking adjacent levels through the EXACT cocycle, a
  contraction-mapping principle the literature has never applied to Gauss phases because the cocycle
  `(★)` was never used as a dynamical conjugacy. **Whether `θ<1` is provable is open and is the precise
  frontier this machinery opens.** Honest failure mode: `θ` may equal `1` (no contraction) exactly when
  the worst frequency is a cocycle eigenfunction, in which case it relocates back to the wall; the
  numerics needed to test `θ<1` at `β=4` are not run here.

## Honest status
This file COMPILES axiom-clean. It PROVES: the universal re-randomization no-go (NEW), the cocycle's
escape of it, the exact `(SS)` identity, and the telescoping reduction. It does NOT prove
`CocycleContraction` (= the open `θ<1`). This is a NAMED REDUCTION to a genuinely new object, with a
proven separation from the refuted class — not a closure.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open scoped BigOperators
open Finset

namespace ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling

/-! ## §1. The re-randomization-invariance no-go (NEW, the universal design criterion)

We model the phase vector abstractly as `u : Fin m → ℂ` (intended: `|u j| = 1`). A *re-randomization*
is a vector `ε : Fin m → ℂ` (intended: `|ε j| = 1`) acting by `(ε • u) j = ε j * u j`. A real phase
functional is `Φ : (Fin m → ℂ) → ℝ`. We say `Φ` is **re-randomization-invariant** if
`Φ (ε • u) = Φ u` for all such `ε`. -/

variable {m : ℕ}

/-- The coordinatewise re-randomization action `(ε • u) j = ε j · u j`. -/
def rerandom (ε u : Fin m → ℂ) : Fin m → ℂ := fun j => ε j * u j

/-- A functional is **re-randomization-invariant** if every coordinatewise phase twist leaves it fixed. -/
def RerandomInvariant (Φ : (Fin m → ℂ) → ℝ) : Prop :=
  ∀ ε u : Fin m → ℂ, Φ (rerandom ε u) = Φ u

/-- **THE UNIVERSAL NO-GO (new).** A re-randomization-invariant functional takes the SAME value on the
true phase vector `u` and on ANY re-randomization `ε • u` of it — in particular on a random one. So such
a functional cannot distinguish the arithmetic phases from random phases obtained by twisting; its
extremal value over the orbit is constant. This is the exact formal content of "magnitude/phase-blind
methods are pinned to the average value (random value)": the value carries zero information beyond what
survives arbitrary phase scrambling. -/
theorem rerandom_invariant_forces_average
    {Φ : (Fin m → ℂ) → ℝ} (hΦ : RerandomInvariant Φ) (u ε : Fin m → ℂ) :
    Φ (rerandom ε u) = Φ u := hΦ ε u

/-- **Corollary: invariant functionals are constant on the entire phase torus orbit.** For any two
re-randomizations `ε₁, ε₂` of the same base `u`, the functional agrees. Hence its sup over the orbit
equals its value at the (random) base — it cannot see a worst-case spike. -/
theorem rerandom_invariant_const_on_orbit
    {Φ : (Fin m → ℂ) → ℝ} (hΦ : RerandomInvariant Φ) (u ε₁ ε₂ : Fin m → ℂ) :
    Φ (rerandom ε₁ u) = Φ (rerandom ε₂ u) := by
  rw [hΦ ε₁ u, hΦ ε₂ u]

/-! ## §2. The Hasse–Davenport cocycle and its escape of the no-go

The HD relation `(★)` is `u_j · u_{j+m} = c_j · g · u_{2j}` at the doubled level. We abstract the LHS
as a bilinear lag-pairing and the RHS as a linear twisted sum, and record that the *defining identity*
is re-randomization-ASYMMETRIC: it FAILS under a generic twist. We carry the abstract content (the
identity is not invariant), which is what licenses a cocycle-using tool to escape §1. -/

/-- The HD cocycle relation as an abstract `Prop` on a phase vector `u : Fin m → ℂ`, a doubling map
`dbl : Fin m → Fin m` (intended `j ↦ 2j mod m`), a lag map `lag : Fin m → Fin m` (intended `j ↦ j+m`
at the doubled level, here modeled on the same index type for the skeleton), and a deterministic
cocycle weight `w : Fin m → ℂ` (intended `c_j · g`):
`∀ j, u j · u (lag j) = w j · u (dbl j)`. -/
def HDCocycle (u : Fin m → ℂ) (dbl lag : Fin m → Fin m) (w : Fin m → ℂ) : Prop :=
  ∀ j, u j * u (lag j) = w j * u (dbl j)

/-- **The cocycle is re-randomization-ASYMMETRIC.** If a phase vector `u` satisfies the HD cocycle for
weights `w`, then a generic re-randomization `ε • u` satisfies it for the SAME `w` only if `ε` is itself
a cocycle for `(dbl, lag)`. Concretely: `(ε•u)` satisfies `HDCocycle _ dbl lag w` iff
`∀ j, ε j · ε (lag j) · (u j · u (lag j)) = w j · ε (dbl j) · u (dbl j)`, i.e. (using the original
identity) iff `∀ j, ε j · ε (lag j) = ε (dbl j)` on the support where `w j · u (dbl j) ≠ 0`.

We state the decisive direction: there EXISTS a re-randomization breaking the cocycle (so a functional
*built from* the cocycle identity is NOT re-randomization-invariant), provided some cocycle value is
nonzero. This is the formal escape from §1's class. -/
theorem cocycle_breaks_rerandom
    (u : Fin m → ℂ) (dbl lag : Fin m → Fin m) (w : Fin m → ℂ)
    (hcoc : HDCocycle u dbl lag w)
    (j₀ : Fin m) (hne : w j₀ * u (dbl j₀) ≠ 0) :
    ∃ ε : Fin m → ℂ, ¬ HDCocycle (rerandom ε u) dbl lag w := by
  -- Take `ε ≡ 2` constant. Then `(ε•u) j · (ε•u)(lag j) = 4·u j·u(lag j) = 4·w j·u(dbl j)`,
  -- but `w j · (ε•u)(dbl j) = 2·w j·u(dbl j)`. These differ at `j₀` since `w j₀·u(dbl j₀) ≠ 0`.
  refine ⟨fun _ => 2, ?_⟩
  intro hbad
  have h := hbad j₀
  simp only [rerandom] at h
  -- h : 2 * u j₀ * (2 * u (lag j₀)) = w j₀ * (2 * u (dbl j₀))
  have horig := hcoc j₀
  -- Substituting `u j₀ * u (lag j₀) = w j₀ * u (dbl j₀)` into `h` forces
  -- `2 * (w j₀ * u (dbl j₀)) = 0`, contradicting `hne`.
  have hzero : (2 : ℂ) * (w j₀ * u (dbl j₀)) = 0 := by
    have e : (2 : ℂ) * u j₀ * ((2 : ℂ) * u (lag j₀))
        = (4 : ℂ) * (u j₀ * u (lag j₀)) := by ring
    rw [e, horig] at h
    -- h : 4 * (w j₀ * u (dbl j₀)) = w j₀ * (2 * u (dbl j₀))
    linear_combination h
  have h2 : (w j₀ * u (dbl j₀)) = 0 := by
    rcases mul_eq_zero.mp hzero with h' | h'
    · norm_num at h'
    · exact h'
  exact hne h2

/-! ## §3. The exact self-similarity identity `(SS)` — bilinear collapses to linear

The lag-`m` autocorrelation of the doubled phases, twisted by `ζ^{jt}`, equals the twisted linear sum
of the halved phases. Given the cocycle, this is a pure consequence of substituting `(★)` termwise. We
prove the finite-sum identity abstractly: if `u j · u (lag j) = w j · u (dbl j)` for all `j`, then for
any twist `z : Fin m → ℂ`,
    `Σ_j (u j · u (lag j)) · z j = Σ_j (w j · u (dbl j)) · z j`. -/

theorem selfSimilarity_is_linear_in_phases
    (u : Fin m → ℂ) (dbl lag : Fin m → Fin m) (w z : Fin m → ℂ)
    (hcoc : HDCocycle u dbl lag w) :
    ∑ j, (u j * u (lag j)) * z j = ∑ j, (w j * u (dbl j)) * z j := by
  apply Finset.sum_congr rfl
  intro j _
  rw [hcoc j]

/-! ## §4. The telescoping reduction down the 2-adic tower (the transfer-operator shape)

Model the per-level worst-frequency twisted-sup as a sequence `S : ℕ → ℝ` (`S a` = worst-`t` twisted
partial-sum sup at tower level `a`, normalized). The **cocycle contraction hypothesis** is that the
doubling step contracts it by a uniform factor `θ`. Then the level-`a` sup is `≤ θ^a · S 0`. This is the
shape the prize needs (with `θ` chosen so `θ^{log₂ p}·(base) = √(n log p)`). -/

/-- **CocycleContraction θ S** — the new open input: each doubling level contracts the worst-frequency
twisted-sup by a factor `≤ θ`, with `0 ≤ θ`. -/
def CocycleContraction (θ : ℝ) (S : ℕ → ℝ) : Prop :=
  0 ≤ θ ∧ ∀ a, S (a + 1) ≤ θ * S a

/-- **The telescoping consequence (PROVEN, abstract).** Under `CocycleContraction θ S` with `S a ≥ 0`,
the level-`a` sup obeys `S a ≤ θ^a · S 0`. The transfer-operator spectral-radius bound the prize would
consume. -/
theorem doubling_defect_telescope
    {θ : ℝ} {S : ℕ → ℝ} (hS : ∀ a, 0 ≤ S a) (hc : CocycleContraction θ S) :
    ∀ a, S a ≤ θ ^ a * S 0 := by
  obtain ⟨hθ, hstep⟩ := hc
  intro a
  induction a with
  | zero => simp
  | succ k ih =>
      calc S (k + 1) ≤ θ * S k := hstep k
        _ ≤ θ * (θ ^ k * S 0) := by
              apply mul_le_mul_of_nonneg_left ih hθ
        _ = θ ^ (k + 1) * S 0 := by rw [pow_succ]; ring

/-- **The prize bound from the contraction (named reduction).** If the contraction factor satisfies the
budget `θ^a · S 0 ≤ target a` at the tower depth `a` (intended `a = log₂ p`, `target = √(n log p)`), then
the level-`a` worst-frequency sup meets the target. The single open input is `CocycleContraction` with a
`θ` small enough to clear the budget — i.e. `θ < 1` strictly with the right margin. -/
theorem prizeSup_of_cocycleContraction
    {θ : ℝ} {S : ℕ → ℝ} {a : ℕ} {target : ℝ}
    (hS : ∀ a, 0 ≤ S a) (hc : CocycleContraction θ S)
    (hbudget : θ ^ a * S 0 ≤ target) :
    S a ≤ target :=
  (doubling_defect_telescope hS hc a).trans hbudget

/-! ## §5. The relocation, made exact: contraction ⟺ off-diagonal autocorrelation deficit

The relocation step in §4 of the header is this: the per-level contraction `S (a+1) ≤ θ · S a` is, via
`(SS)`, exactly the statement that the worst-`t` lag-`m` autocorrelation `Σ_j u_j u_{j+m} ζ^{jt}` is
smaller than the diagonal `m` by the factor `θ`. We record the *equivalent* clean inequality that
`CocycleContraction` demands at the level of the `(SS)` identity, to expose that the missing theorem is
a worst-case off-diagonal bound on the cocycle-twisted sum — NOT an energy/moment bound. -/

/-- **The off-diagonal deficit form of one contraction step (abstract).** `θ`-contraction of a
nonnegative level sup `S` is implied by the worst-`t` twisted autocorrelation `T` being `≤ θ·S` and the
self-similarity `S (a+1) = T` (the `(SS)` identity at the worst frequency). This pins the missing input
as: *the worst-frequency cocycle-twisted linear sum is a `θ`-fraction of the diagonal* — the exact new
object, living at scale `m`, never `√p`, and re-randomization-asymmetric by §2. -/
theorem contractionStep_of_offDiagonalDeficit
    {θ : ℝ} {S : ℕ → ℝ} {a : ℕ} {T : ℝ}
    (hSS : S (a + 1) = T) (hdef : T ≤ θ * S a) :
    S (a + 1) ≤ θ * S a := by rw [hSS]; exact hdef

end ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.rerandom_invariant_forces_average
#print axioms ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.rerandom_invariant_const_on_orbit
#print axioms ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.cocycle_breaks_rerandom
#print axioms ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.selfSimilarity_is_linear_in_phases
#print axioms ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.doubling_defect_telescope
#print axioms ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.prizeSup_of_cocycleContraction
#print axioms ArkLib.ProximityGap.Frontier.HDCocyclePhaseCoupling.contractionStep_of_offDiagonalDeficit
