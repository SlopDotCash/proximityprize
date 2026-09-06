/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import Research.ProximityPrize.Frontier._SYZ42Realizability

/-!
# SW1-F1 — the F1 Prop `UniformSylvesterInjective` is refuted, and the refutation
# survives every hypothesis repair confined to the triple (the coset family)

## Target

Face F1 of the rate-`1/2` strip route (one-question map §3, dossier v4 §3.2): the named Prop
`SYZ40.UniformSylvesterInjective K n k`, carried as the field
`SYZ42.StripMasterHypothesis''.uniformSylvester` and consumed by the conditional δ* bracket
`SYZ46.deltaStar_bracket_of_strip_master_hypothesis` at `(ZMod P, 2^30, 2^29)`.  Its stated
open content is the Hilbert–Burch near-balance `ι ≤ 1` of the μ-basis of a band-realizable
balanced pairwise-coprime triple `(W_AB, W_AC, W_BC)` over `μ_n`.

## Result (classification: **refutation / no-go**, with machine countermodels)

1. **Literal refutation (§1).**  `UniformSylvesterInjective K n k` quantifies over *all*
   `WAB WAC WBC : K[X]` of the stated degrees — no coprimality, no `μ_n`-rootedness, no band
   realizability.  With `WAC = WBC` and cofactors `rAC = rBC = 1` the divisibility
   `WAB ∣ WAC·1 − WBC·1 = 0` is trivial, so `SylvesterInjective` fails.  Hence
   `¬ UniformSylvesterInjective K (2k) k` for **every** field `K` and every `k ≥ 1`
   (`not_uniformSylvesterInjective`), `StripMasterHypothesis'' K V (2k) k` is **uninhabited**
   (`stripMasterHypothesis''_false`), in particular at the production parameters
   `(ZMod P, 2^30, 2^29)` (`stripMasterHypothesis''_false_production`).  The SYZ46 bracket is
   therefore a theorem with an unsatisfiable hypothesis; and the first conjunct of the
   `strip_theorem_of_master_hypothesis''` conclusion is itself false
   (`strip_conclusion_false`), so the assembly cannot be repaired by weakening the hypothesis
   while keeping that conclusion.

2. **Robust refutation — the coset family (§2).**  The literal hole (missing coprimality) is
   a formalization bug.  The substantive question is whether the *intended* Prop — restricted to
   pairwise-coprime, squarefree, `μ_n`-rooted triples on a band-realizable interior profile — is
   true.  It is not.  Take `n = 4d`, the subgroup `μ_d ⊂ μ_{4d}` and three of its four cosets as
   the pairwise-exclusive regions, with the triple region `T` inside the fourth coset.  The
   vanishing polynomials are the **binomials** `X^d − c_j` with `c_j^4 = 1` pairwise distinct,
   and for *any* three constants
   `(X^d − c₀)(c₁ − c₂) − (X^d − c₁)(c₀ − c₂) + (X^d − c₂)(c₀ − c₁) = 0`
   is a polynomial identity (`binomial_syzygy`): a nonzero **constant** syzygy, product-degree
   `d`, in the in-budget window `k − 1 − m = d − 1 − t ≥ 0` whenever `t ≤ d − 1`.  The packaged
   theorem `coset_family_refutes_F1` proves, for every field `K`, every `d`, and every
   `t` with `2d + 1 ≤ 3t` and `t + 1 ≤ d` (so `d ≥ 4`):
   pairwise coprime ∧ separable (squarefree) ∧ each divides `X^{4d} − 1` (all roots in `μ_{4d}`)
   ∧ degree profile `(d,d,d)` with triple `t` ∧ `Realizable d d d t (2d)` (SYZ50 polytope, rate
   `1/2`) ∧ `BalancedInterior d d d` (SYZ48) ∧ G172 interior cores `2n+1 ≤ 3s`
   **∧ `¬ SylvesterInjective`** at the SYZ38 window.  The family is **`p`-uniform** (a polynomial
   identity in the roots, not a small-field accident) and **`n`-scalable**: at the production
   shape `d = 2^28`, `n = 2^30`, `k = 2^29`, `t = 2^28 − 1` every condition holds
   (`coset_family_production`), over every `𝔽_p` with `p ≡ 1 (mod 2^30)` (which contains three
   distinct fourth roots of unity).  In μ-basis language the family is floor-attained,
   `δ₁ = d`, `ι = ⌊d/2⌋ ≥ 2` (`coset_imbalance_ge_two`): the near-balance `ι ≤ 1` is **false**
   on band-realizable balanced interior triples at every `n = 4d`, `d ≥ 4`.

   This is the explicit, closed-form member of the "persistent cyclotomic `ι = 2` witnesses"
   that SYZ53's sweep observed numerically (21 at `μ₁₄`, 216 at `μ₁₆`, stable for all large
   `p`); it identifies the persistence mechanism (binomial/coset structure ⇒ polynomial identity)
   and lifts it to a machine-checked theorem at production shape.

3. **Target-statement correction (§3, pure `ℕ`).**  Independently of 1–2, the near-balance
   target as phrased in the one-question map — `ι ≤ 1`, i.e. gap `δ₂ − δ₁ ≤ 2` at even `S` and
   `∈ {1, 3}` at odd `S` — is **insufficient** for `SylvesterInjective` on the realizable
   polytope boundary `S = 2·budget + 3` (odd): there `δ₁ ≥ budget + 1` forces gap `≤ 1`.  Exact
   law: `budget + 1 ≤ δ₁ ↔ gap + 2·budget + 2 ≤ S` (`out_of_budget_iff_gap`); the uniformly
   sufficient target is `gap ≤ 2` in **both** parities
   (`gap_le_two_suffices`), which is exactly `ι ≤ 1 ∧ (ι = 1 → S even)` — G172/SYZ44's original
   phrasing, which SYZ53/68/69 silently weakened (`gap_le_two_iff`).  Countermodel at a
   realizable balanced-interior profile: `(5,5,5), t = 1, k = 8`, `(δ₁,δ₂) = (6,9)`, `ι = 1`,
   `δ₁ = budget` (`imbalance_le_one_insufficient`).

## What is NOT claimed

Nothing here touches the production δ* verdict: the coset family refutes the **sufficient
condition** (F1 as a Prop about the triple), not the strip count bound.  SYZ53's sweep is
evidence that constant-syzygy configurations are stack-harmless at large `p` (bad count at the
generic floor); the companion probe `scripts/probes/sw1_f1_middle_slot_lift.py` runs the same
exact lift test on this family and on the SYZ71 `(6,6,6)` linear-slot occupant.  What this file
establishes is that the strip route **cannot** be closed through `UniformSylvesterInjective` as
formalized, nor through any repair that only constrains the triple `(W_AB, W_AC, W_BC)`: a
working F1 must be a *stack-aware* statement.  `UniformSylvesterInjective`, the strip bracket's
hypothesis, and production δ* remain exactly where they were: the first two are now known
unsatisfiable / vacuous, δ* is OPEN / ON-BGK.

All declarations axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no
`native_decide`, no new axiom.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SW1F1

open Polynomial
open ArkLib.ProximityGap

/-! ## 1. Literal refutation: the Prop has no coprimality hypothesis -/

section Literal

variable {K : Type*} [Field K]

/-- **`SylvesterInjective` fails whenever the two carrying slots coincide.**  With `WAC = WBC`
the cofactors `rAC = rBC = 1` give `WAC·1 − WBC·1 = 0`, divisible by anything, yet nonzero.
The SYZ38 predicate contains no coprimality clause that would exclude this. -/
theorem not_sylvesterInjective_of_eq (WAB WAC : K[X]) (bAC bBC : ℕ) :
    ¬ SYZ38.SylvesterInjective WAB WAC WAC bAC bBC := by
  intro h
  have h1 := h 1 1 (fun _ => by simp) (fun _ => by simp) (by simp)
  exact one_ne_zero h1.1

end Literal

/-- **`UniformSylvesterInjective K (2k) k` is false for every field and every `k ≥ 1`.**
Instantiate the universal statement at `mAB = k`, `mAC = mBC = k − 1`, `t = 0`,
`WAB = X^k`, `WAC = WBC = X^{k−1}`: all side conditions hold (`0 < k`, `k − 1 < 2k − 1`,
degrees exact) and the window is `(0, 0)`, which admits the constant cofactors of
`not_sylvesterInjective_of_eq`. -/
theorem not_uniformSylvesterInjective (K : Type*) [Field K] (k : ℕ) (hk : 1 ≤ k) :
    ¬ SYZ40.UniformSylvesterInjective K (2 * k) k := by
  intro h
  have hX : (Polynomial.X : K[X]) ^ k ≠ 0 := pow_ne_zero _ X_ne_zero
  have hS := h (Polynomial.X ^ k) (Polynomial.X ^ (k - 1)) (Polynomial.X ^ (k - 1)) k (k - 1) (k - 1) 0 rfl (by omega) (by omega)
    (by simp) (by simp) (by simp) hX
  exact not_sylvesterInjective_of_eq _ _ _ _ hS

/-- **The strip master hypothesis is uninhabited** for every field, every syndrome space, and
every `k ≥ 1`: its `uniformSylvester` field is the refuted Prop. -/
theorem stripMasterHypothesis''_false (K : Type*) [Field K]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (k : ℕ) (hk : 1 ≤ k) :
    ¬ SYZ42.StripMasterHypothesis'' K V (2 * k) k :=
  fun H => not_uniformSylvesterInjective K k hk H.uniformSylvester

/-- **At the production parameters** `(ZMod P, n = 2^30, k = 2^29)` the hypothesis of
`SYZ46.deltaStar_bracket_of_strip_master_hypothesis` is unsatisfiable: that bracket is vacuous. -/
theorem stripMasterHypothesis''_false_production (P : ℕ) [Fact (Nat.Prime P)]
    (V : Type*) [AddCommGroup V] [Module (ZMod P) V] [FiniteDimensional (ZMod P) V] :
    ¬ SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29) := by
  have h := stripMasterHypothesis''_false (ZMod P) V (2 ^ 29) (by norm_num)
  have e : (2 : ℕ) * 2 ^ 29 = 2 ^ 30 := by norm_num
  rw [e] at h
  exact h

/-- **The assembled conclusion is itself false.**  The first conjunct of
`SYZ42.strip_theorem_of_master_hypothesis''` — every in-budget syzygy of every degree-profile
triple vanishes — fails at `WAB = X^k`, `WAC = WBC = X^{k−1}`, `(rAB, rAC, rBC) = (0, 1, 1)`.
So the assembly is vacuous, not merely conditional: no weakening of the hypothesis can rescue
it while this conclusion is kept. -/
theorem strip_conclusion_false (K : Type*) [Field K] (k : ℕ) (hk : 1 ≤ k) :
    ¬ (∀ (WAB WAC WBC rAB rAC rBC : K[X]) (mAB mAC mBC t : ℕ),
      t < mAB → k - 1 < mAB + mAC - t →
      WAB.natDegree = mAB - t → WAC.natDegree = mAC - t → WBC.natDegree = mBC - t → WAB ≠ 0 →
      WAB * rAB - WAC * rAC + WBC * rBC = 0 →
      (rAC ≠ 0 → rAC.natDegree ≤ k - 1 - mAC) → (rBC ≠ 0 → rBC.natDegree ≤ k - 1 - mBC) →
      rAB = 0 ∧ rAC = 0 ∧ rBC = 0) := by
  intro h
  have hX : (Polynomial.X : K[X]) ^ k ≠ 0 := pow_ne_zero _ X_ne_zero
  have hc := h (Polynomial.X ^ k) (Polynomial.X ^ (k - 1)) (Polynomial.X ^ (k - 1)) 0 1 1 k (k - 1) (k - 1) 0 (by omega) (by omega)
    (by simp) (by simp) (by simp) hX (by ring) (fun _ => by simp) (fun _ => by simp)
  exact one_ne_zero hc.2.1

/-! ## 2. The coset family: a `p`-uniform, `n`-scalable countermodel that survives every
hypothesis repair confined to the triple -/

section Coset

variable {K : Type*} [Field K]

/-- **The binomial identity.**  For any three constants,
`(X^d − c₀)(c₁ − c₂) − (X^d − c₁)(c₀ − c₂) + (X^d − c₂)(c₀ − c₁) = 0`.  This is a constant
syzygy of the three binomials — the vanishing polynomials of three cosets of `μ_d` in `μ_{4d}`
when `c_j` are distinct fourth roots of unity. -/
theorem binomial_syzygy (d : ℕ) (c₀ c₁ c₂ : K) :
    (Polynomial.X ^ d - C c₀) * C (c₁ - c₂) - (Polynomial.X ^ d - C c₁) * C (c₀ - c₂) + (Polynomial.X ^ d - C c₂) * C (c₀ - c₁)
      = 0 := by
  simp only [C_sub]; ring

/-- The SYZ38 divisibility (†) for the binomial triple, exhibited with its quotient. -/
theorem binomial_dvd (d : ℕ) (c₀ c₁ c₂ : K) :
    (Polynomial.X ^ d - C c₀) ∣ ((Polynomial.X ^ d - C c₁) * C (c₀ - c₂) - (Polynomial.X ^ d - C c₂) * C (c₀ - c₁)) :=
  ⟨C (c₁ - c₂), by simp only [C_sub]; ring⟩

/-- **`SylvesterInjective` fails on the binomial triple at every window.**  The constant
cofactors `(C (c₀ − c₂), C (c₀ − c₁))` have degree `0`, hence are in-budget for any
`bAC, bBC`, and `rAC ≠ 0` as soon as `c₀ ≠ c₂`. -/
theorem not_sylvesterInjective_binomial (d : ℕ) (c₀ c₁ c₂ : K) (h02 : c₀ ≠ c₂)
    (bAC bBC : ℕ) :
    ¬ SYZ38.SylvesterInjective (Polynomial.X ^ d - C c₀) (Polynomial.X ^ d - C c₁) (Polynomial.X ^ d - C c₂) bAC bBC := by
  intro h
  have hS := h (C (c₀ - c₂)) (C (c₀ - c₁)) (fun _ => by simp) (fun _ => by simp)
    (binomial_dvd d c₀ c₁ c₂)
  exact h02 (sub_eq_zero.mp (C_eq_zero.mp hS.1))

/-- **Distinct binomials are coprime**: `(b − a)⁻¹·((X^d − a) − (X^d − b)) = 1`. -/
theorem isCoprime_binomial (d : ℕ) {a b : K} (hab : a ≠ b) :
    IsCoprime (Polynomial.X ^ d - C a) (Polynomial.X ^ d - C b) := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  refine ⟨C (b - a)⁻¹, -C (b - a)⁻¹, ?_⟩
  have h1 : C (b - a)⁻¹ * (Polynomial.X ^ d - C a) + -C (b - a)⁻¹ * (Polynomial.X ^ d - C b)
      = C ((b - a)⁻¹ * (b - a)) := by
    simp only [C_mul, C_sub]; ring
  rw [h1, inv_mul_cancel₀ hne, C_1]

/-- **All roots in `μ_{dm}`**: if `c^m = 1` then `X^d − c ∣ X^{dm} − 1`. -/
theorem binomial_dvd_X_pow_sub_one (d m : ℕ) {c : K} (hc : c ^ m = 1) :
    (Polynomial.X ^ d - C c) ∣ (Polynomial.X ^ (d * m) - 1) := by
  have h := sub_dvd_pow_sub_pow (Polynomial.X ^ d : K[X]) (C c) m
  rwa [← pow_mul, ← C_pow, hc, C_1] at h

/-- A root of unity is nonzero. -/
theorem ne_zero_of_pow_eq_one {c : K} {m : ℕ} (hm : m ≠ 0) (hc : c ^ m = 1) : c ≠ 0 := by
  rintro rfl
  rw [zero_pow hm] at hc
  exact zero_ne_one hc

/-- **`UniformSylvesterInjective` is refuted through a pairwise-coprime `μ_n`-rooted triple**
(not only through the degenerate `WAC = WBC`): the binomial triple sits at
`mAB = mAC = mBC = d + t`, any `t`, on `n = 4d`, `k = 2d`. -/
theorem not_uniformSylvesterInjective_of_binomial (d t : ℕ) (hd : 1 ≤ d)
    (c₀ c₁ c₂ : K) (h02 : c₀ ≠ c₂) :
    ¬ SYZ40.UniformSylvesterInjective K (2 * (2 * d)) (2 * d) := by
  intro h
  have hS := h (Polynomial.X ^ d - C c₀) (Polynomial.X ^ d - C c₁) (Polynomial.X ^ d - C c₂) (d + t) (d + t) (d + t) t rfl
    (by omega) (by omega)
    (by rw [natDegree_X_pow_sub_C]; omega) (by rw [natDegree_X_pow_sub_C]; omega)
    (by rw [natDegree_X_pow_sub_C]; omega)
    (X_pow_sub_C_ne_zero (by omega) _)
  exact not_sylvesterInjective_binomial d c₀ c₁ c₂ h02 _ _ hS

end Coset

/-! ### The band polytope, restated (SYZ50 / SYZ48 / G172 oleans are not built in this
checkout; definitions copied verbatim, cited). -/

/-- Verbatim `SYZ50.Realizable`: band-realizable at rate `1/2` — reduced degrees `(a,b,c)`,
triple region `t`, half-length `k` (`n = 2k`): nonempty regions, domain disjointness
`a+b+c+t ≤ 2k`, SYZ37 budget cap `max + 1 + t ≤ k`, G172 interior slack
`2k + 1 ≤ a+b+c+2t`. -/
def Realizable (a b c t k : ℕ) : Prop :=
  1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧
  a + b + c + t ≤ 2 * k ∧
  max a (max b c) + 1 + t ≤ k ∧
  2 * k + 1 ≤ a + b + c + 2 * t

/-- Verbatim `SYZ48.BalancedInterior`: the SYZ47 floor is blind, `max + 1 < ⌊S/2⌋`. -/
def BalancedInterior (a b c : ℕ) : Prop :=
  max a (max b c) + 1 < (a + b + c) / 2

/-- G172 interior band on three cores of size `s` inside `[n]`: `2n + 1 ≤ 3s`. -/
def InteriorCores (n s : ℕ) : Prop := 2 * n + 1 ≤ 3 * s

/-- Verbatim `SYZ45.imbalance`: `ι = ⌊(a+b+c)/2⌋ − δ₁`. -/
def imbalance (a b c δ₁ : ℕ) : ℕ := (a + b + c) / 2 - δ₁

/-- **The coset profile is band-realizable, balanced-interior, and interior-core** at
`n = 4d`, `k = 2d`, for `2d + 1 ≤ 3t ≤ 3(d − 1)` (which forces `d ≥ 4`).  Cores have size
`s = 2d + t`. -/
theorem coset_profile_realizable (d t : ℕ) (h1 : 2 * d + 1 ≤ 3 * t) (h2 : t + 1 ≤ d) :
    Realizable d d d t (2 * d) ∧ BalancedInterior d d d ∧ InteriorCores (4 * d) (2 * d + t) := by
  unfold Realizable BalancedInterior InteriorCores; omega

/-- The admissible `t`-range is nonempty exactly for `d ≥ 4`. -/
theorem coset_profile_exists_t_iff (d : ℕ) :
    (∃ t, 2 * d + 1 ≤ 3 * t ∧ t + 1 ≤ d) ↔ 4 ≤ d := by
  constructor
  · rintro ⟨t, h1, h2⟩; omega
  · intro h; exact ⟨d - 1, by omega, by omega⟩

/-- **Floor-attained ⇒ `ι = ⌊d/2⌋ ≥ 2`.**  The constant syzygy has product-degree `d`, so the
minimal generator degree satisfies `δ₁ ≤ d` and the imbalance is `≥ ⌊3d/2⌋ − d = ⌊d/2⌋ ≥ 2`
for `d ≥ 4`: near-balance `ι ≤ 1` fails on the whole family. -/
theorem coset_imbalance_ge_two (d δ₁ : ℕ) (hd : 4 ≤ d) (hδ : δ₁ ≤ d) :
    2 ≤ imbalance d d d δ₁ := by
  unfold imbalance; omega

section Packaged

variable {K : Type*} [Field K]

/-- **The packaged countermodel.**  For every field `K`, every `d`, every admissible `t`, and
any three pairwise-distinct fourth roots of unity `c₀ c₁ c₂ ∈ K` (with `(d : K) ≠ 0` for
separability), the binomial triple `(X^d − c₀, X^d − c₁, X^d − c₂)` satisfies **every**
hypothesis one could add to repair `UniformSylvesterInjective` on the triple alone —
pairwise coprime, squarefree, all roots in `μ_{4d}`, exact band degree profile `(d,d,d)` with
triple region `t`, band-realizable at rate `1/2`, balanced-interior, interior cores — and
**still** violates `SylvesterInjective` at the SYZ38 window `k − 1 − m = d − 1 − t`. -/
theorem coset_family_refutes_F1 (d t : ℕ) (h1 : 2 * d + 1 ≤ 3 * t) (h2 : t + 1 ≤ d)
    (c₀ c₁ c₂ : K) (hc₀ : c₀ ^ 4 = 1) (hc₁ : c₁ ^ 4 = 1) (hc₂ : c₂ ^ 4 = 1)
    (h01 : c₀ ≠ c₁) (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂) (hchar : (d : K) ≠ 0) :
    IsCoprime (Polynomial.X ^ d - C c₀) (Polynomial.X ^ d - C c₁) ∧
    IsCoprime (Polynomial.X ^ d - C c₀) (Polynomial.X ^ d - C c₂) ∧
    IsCoprime (Polynomial.X ^ d - C c₁) (Polynomial.X ^ d - C c₂) ∧
    (Polynomial.X ^ d - C c₀).Separable ∧ (Polynomial.X ^ d - C c₁).Separable ∧ (Polynomial.X ^ d - C c₂).Separable ∧
    (Polynomial.X ^ d - C c₀) ∣ (Polynomial.X ^ (4 * d) - 1) ∧
    (Polynomial.X ^ d - C c₁) ∣ (Polynomial.X ^ (4 * d) - 1) ∧
    (Polynomial.X ^ d - C c₂) ∣ (Polynomial.X ^ (4 * d) - 1) ∧
    (Polynomial.X ^ d - C c₀).natDegree = (d + t) - t ∧
    (Polynomial.X ^ d - C c₁).natDegree = (d + t) - t ∧
    (Polynomial.X ^ d - C c₂).natDegree = (d + t) - t ∧
    Realizable d d d t (2 * d) ∧ BalancedInterior d d d ∧ InteriorCores (4 * d) (2 * d + t) ∧
    ¬ SYZ38.SylvesterInjective (Polynomial.X ^ d - C c₀) (Polynomial.X ^ d - C c₁) (Polynomial.X ^ d - C c₂)
        (2 * d - 1 - (d + t)) (2 * d - 1 - (d + t)) := by
  have h4d : 4 * d = d * 4 := by ring
  obtain ⟨hR, hB, hI⟩ := coset_profile_realizable d t h1 h2
  refine ⟨isCoprime_binomial d h01, isCoprime_binomial d h02, isCoprime_binomial d h12,
    separable_X_pow_sub_C c₀ hchar (ne_zero_of_pow_eq_one (by norm_num) hc₀),
    separable_X_pow_sub_C c₁ hchar (ne_zero_of_pow_eq_one (by norm_num) hc₁),
    separable_X_pow_sub_C c₂ hchar (ne_zero_of_pow_eq_one (by norm_num) hc₂),
    h4d ▸ binomial_dvd_X_pow_sub_one d 4 hc₀,
    h4d ▸ binomial_dvd_X_pow_sub_one d 4 hc₁,
    h4d ▸ binomial_dvd_X_pow_sub_one d 4 hc₂,
    by rw [natDegree_X_pow_sub_C]; omega,
    by rw [natDegree_X_pow_sub_C]; omega,
    by rw [natDegree_X_pow_sub_C]; omega,
    hR, hB, hI,
    not_sylvesterInjective_binomial d c₀ c₁ c₂ h02 _ _⟩

/-- **Production shape.**  `d = 2^28`, `n = 4d = 2^30`, `k = 2d = 2^29`, `t = 2^28 − 1`:
the coset profile is band-realizable, balanced-interior and interior-core at the prize
parameters, and over any field with three distinct fourth roots of unity and `(2^28 : K) ≠ 0`
(every `𝔽_p`, `p ≡ 1 (mod 2^30)`) the binomial triple refutes `SylvesterInjective` there. -/
theorem coset_family_production (c₀ c₁ c₂ : K) (hc₀ : c₀ ^ 4 = 1) (hc₁ : c₁ ^ 4 = 1)
    (hc₂ : c₂ ^ 4 = 1) (h01 : c₀ ≠ c₁) (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂)
    (hchar : ((2 ^ 28 : ℕ) : K) ≠ 0) :
    Realizable (2 ^ 28) (2 ^ 28) (2 ^ 28) (2 ^ 28 - 1) (2 ^ 29) ∧
    BalancedInterior (2 ^ 28) (2 ^ 28) (2 ^ 28) ∧
    InteriorCores (2 ^ 30) (2 * 2 ^ 28 + (2 ^ 28 - 1)) ∧
    ¬ SYZ38.SylvesterInjective (Polynomial.X ^ (2 ^ 28) - C c₀) (Polynomial.X ^ (2 ^ 28) - C c₁)
        (Polynomial.X ^ (2 ^ 28) - C c₂) (2 ^ 29 - 1 - (2 ^ 28 + (2 ^ 28 - 1)))
        (2 ^ 29 - 1 - (2 ^ 28 + (2 ^ 28 - 1))) ∧
    ¬ SYZ40.UniformSylvesterInjective K (2 ^ 30) (2 ^ 29) := by
  have h1 : 2 * 2 ^ 28 + 1 ≤ 3 * (2 ^ 28 - 1) := by norm_num
  have h2 : (2 ^ 28 - 1) + 1 ≤ 2 ^ 28 := by norm_num
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hR, hB, hI, hS⟩ :=
    coset_family_refutes_F1 (K := K) (2 ^ 28) (2 ^ 28 - 1) h1 h2 c₀ c₁ c₂ hc₀ hc₁ hc₂
      h01 h02 h12 hchar
  have e1 : (2 : ℕ) * 2 ^ 28 = 2 ^ 29 := by norm_num
  have e2 : (4 : ℕ) * 2 ^ 28 = 2 ^ 30 := by norm_num
  have e3 : (2 : ℕ) * (2 * 2 ^ 28) = 2 ^ 30 := by norm_num
  refine ⟨(congrArg (fun x => Realizable (2 ^ 28) (2 ^ 28) (2 ^ 28) (2 ^ 28 - 1) x) e1).mp hR,
    hB,
    (congrArg (fun x => InteriorCores x (2 * 2 ^ 28 + (2 ^ 28 - 1))) e2).mp hI,
    (congrArg (fun x => ¬ SYZ38.SylvesterInjective (Polynomial.X ^ (2 ^ 28) - C c₀)
      (Polynomial.X ^ (2 ^ 28) - C c₁) (Polynomial.X ^ (2 ^ 28) - C c₂)
      (x - 1 - (2 ^ 28 + (2 ^ 28 - 1))) (x - 1 - (2 ^ 28 + (2 ^ 28 - 1)))) e1).mp hS,
    ?_⟩
  have hU := not_uniformSylvesterInjective_of_binomial (K := K) (2 ^ 28) (2 ^ 28 - 1)
    (by norm_num) c₀ c₁ c₂ h02
  rw [e3, e1] at hU
  exact hU

end Packaged

/-! ## 3. Target-statement correction: `ι ≤ 1` is not the right near-balance target -/

/-- **Exact out-of-budget law.**  Under the degree-sum law `δ₁ + δ₂ = S` with `δ₁ ≤ δ₂`, the
minimal generator is strictly out of budget iff the generator gap is at most the realizability
slack plus one: `budget + 1 ≤ δ₁ ↔ (δ₂ − δ₁) + 2·budget + 2 ≤ S`. -/
theorem out_of_budget_iff_gap (S δ₁ δ₂ budget : ℕ) (hsum : δ₁ + δ₂ = S) (hle : δ₁ ≤ δ₂) :
    budget + 1 ≤ δ₁ ↔ (δ₂ - δ₁) + 2 * budget + 2 ≤ S := by
  omega

/-- **`gap ≤ 2` suffices uniformly** on the realizable polytope (`2·budget + 3 ≤ S`, G172). -/
theorem gap_le_two_suffices (S δ₁ δ₂ budget : ℕ) (hsum : δ₁ + δ₂ = S) (hle : δ₁ ≤ δ₂)
    (hslack : 2 * budget + 3 ≤ S) (hgap : δ₂ - δ₁ ≤ 2) :
    budget + 1 ≤ δ₁ := by
  omega

/-- **`gap ≤ 2` in both parities is exactly `ι ≤ 1 ∧ (ι = 1 → S even)`** — the G172/SYZ44
phrasing.  The odd-`S` reading `gap ∈ {1, 3}` of SYZ53/68/69 admits `gap = 3`, `ι = 1`. -/
theorem gap_le_two_iff (S δ₁ δ₂ : ℕ) (hsum : δ₁ + δ₂ = S) (hle : δ₁ ≤ δ₂) :
    δ₂ - δ₁ ≤ 2 ↔ (S / 2 - δ₁ ≤ 1 ∧ (S / 2 - δ₁ = 1 → S % 2 = 0)) := by
  omega

/-- **`ι ≤ 1` alone is insufficient on the polytope boundary.**  At the realizable
balanced-interior profile `(5,5,5), t = 1, k = 8` (budget `6`, `S = 15 = 2·6 + 3`), the
generator pair `(δ₁, δ₂) = (6, 9)` has `ι = 1` and gap `3` (odd-`S` "admitted") yet
`δ₁ = budget`: an in-budget syzygy, `SylvesterInjective` fails. -/
theorem imbalance_le_one_insufficient :
    ∃ a b c t k δ₁ δ₂ : ℕ,
      Realizable a b c t k ∧ BalancedInterior a b c ∧
      δ₁ + δ₂ = a + b + c ∧ δ₁ ≤ δ₂ ∧ max a (max b c) ≤ δ₁ ∧
      imbalance a b c δ₁ ≤ 1 ∧ (a + b + c) % 2 = 1 ∧ δ₂ - δ₁ = 3 ∧
      δ₁ ≤ k - 1 - t :=
  ⟨5, 5, 5, 1, 8, 6, 9, by unfold Realizable; omega, by unfold BalancedInterior; omega,
    rfl, by omega, by omega, by unfold imbalance; omega, rfl, rfl, by omega⟩

/-- **The boundary is realizable at every `k ≥ 5`**: `(budget, budget, 3), t = k − 1 − budget`
with `budget = k − 1 − t ≥ 3`, `S = 2·budget + 3`. -/
theorem boundary_realizable (k : ℕ) (hk : 5 ≤ k) :
    ∃ a b c t, Realizable a b c t k ∧ a + b + c = 2 * (k - 1 - t) + 3 :=
  ⟨k - 2, k - 2, 3, 1, by unfold Realizable; omega, by omega⟩

end ArkLib.ProximityGap.SW1F1

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SW1F1.not_sylvesterInjective_of_eq
#print axioms ArkLib.ProximityGap.SW1F1.not_uniformSylvesterInjective
#print axioms ArkLib.ProximityGap.SW1F1.stripMasterHypothesis''_false
#print axioms ArkLib.ProximityGap.SW1F1.stripMasterHypothesis''_false_production
#print axioms ArkLib.ProximityGap.SW1F1.strip_conclusion_false
#print axioms ArkLib.ProximityGap.SW1F1.binomial_syzygy
#print axioms ArkLib.ProximityGap.SW1F1.binomial_dvd
#print axioms ArkLib.ProximityGap.SW1F1.not_sylvesterInjective_binomial
#print axioms ArkLib.ProximityGap.SW1F1.isCoprime_binomial
#print axioms ArkLib.ProximityGap.SW1F1.binomial_dvd_X_pow_sub_one
#print axioms ArkLib.ProximityGap.SW1F1.ne_zero_of_pow_eq_one
#print axioms ArkLib.ProximityGap.SW1F1.not_uniformSylvesterInjective_of_binomial
#print axioms ArkLib.ProximityGap.SW1F1.coset_profile_realizable
#print axioms ArkLib.ProximityGap.SW1F1.coset_profile_exists_t_iff
#print axioms ArkLib.ProximityGap.SW1F1.coset_imbalance_ge_two
#print axioms ArkLib.ProximityGap.SW1F1.coset_family_refutes_F1
#print axioms ArkLib.ProximityGap.SW1F1.coset_family_production
#print axioms ArkLib.ProximityGap.SW1F1.out_of_budget_iff_gap
#print axioms ArkLib.ProximityGap.SW1F1.gap_le_two_suffices
#print axioms ArkLib.ProximityGap.SW1F1.gap_le_two_iff
#print axioms ArkLib.ProximityGap.SW1F1.imbalance_le_one_insufficient
#print axioms ArkLib.ProximityGap.SW1F1.boundary_realizable
