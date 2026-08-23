/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Analysis.Complex.ExponentialBounds
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase

/-!
# R341: CAZAC `√(m log m)` claim ⟺ subgroup-coset square-root cancellation (exact transfer)

Session 2026-07-09 (#466), companion to `_R339GaussPhaseMellinTwist` (the Mellin identity
and the PAPR Prop) and `_R340GaussPhaseAutocorr` (the lag-side identity).  This brick
records the round's verified result: the **exact Gauss-inversion identity in solved form**
and the **two-sided equivalence** between the Gauss-phase CAZAC claim and the classical
subgroup-coset exponential-sum problem — with the open direction left as a named `Prop`.

## Dictionary (paper ↔ this file)

Paper notation: `p` prime, `χₘ` of exact order `m ∣ p−1`, `u_j = g(χₘ^j)/√p` the normalized
Gauss phases, `H = ker χₘ = (F_p^*)^m` the index-`m` subgroup (`|H| = h = (p−1)/m`), and
`S_a = ∑_{x∈aH} e_p(x)` the coset sum.  Here (over any finite field `F`, `q = |F|`):
`d = h = |H|` (the subgroup is `torsion F d = {y : y^d = 1}`), `t = (q−1)/d = m` (the number
of Mellin frequencies), `χ` has full order `q−1` (so `χ^d` has exact order `m` and plays
`χₘ`), `eta ψ (torsion F d) b = S_b`, and

  `mellinSum χ ψ d b = ∑_{j=1}^{m−1} g(χₘ^j)·χₘ(b)^{−j} = √p · ∑_{j=1}^{m−1} u_j τ^{−j}`

at the frequency `τ = χₘ(b) ∈ μ_m` (every `τ ∈ μ_m` arises this way: `χₘ` is surjective onto
`μ_m` with fibers the `m` cosets of `H`, so quantifying over `b ≠ 0` covers all frequencies).

## PROVEN here (machine-checked, general finite field, axiom-clean)

* `mellinSum_eq_coset` — **the boxed identity** `∑_{j=1}^{m−1} g(χₘ^j)·χₘ(b)^{−j} = m·S_b + 1`.
  The `+1` is exact, not `O(1)`: it is `−g(χₘ^0)` where `g(χₘ^0) = ∑_{x≠0} e_p(x) = −1`
  (trivial-character convention: the `j = 0` summand of the completion is
  `gaussSum 1 (mulShift ψ b) = −1`, `SubgroupGaussSumWorstCase.gaussSum_one_mulShift`).
  Numerically verified to `≤ 5×10⁻¹³` at `(p,m) ∈ {(13,4),(29,7),(31,30),(31,2)}` for all
  `a ∈ F_p^*`, and to `~10⁻¹²` up to `(3329,64)` (R339 `papr_check.py`).
* `norm_mellinSum_le_coset`, `mul_norm_eta_le_mellinSum` — the **exact two-sided transfer**
  `‖M_b‖ ≤ m·‖S_b‖ + 1` and `m·‖S_b‖ ≤ ‖M_b‖ + 1`: at each individual `b` the phase sum and
  the coset sum are the same number under the affine map `z ↦ m·z + 1`, so the `m` phase sums
  (over `τ ∈ μ_m`) and the `m` coset sums (over the cosets of `H`) are the same list; a
  refutation family for one side transfers verbatim to the other.
* `cosetCancellation_of_mellinCAZAC` (`C ↦ C`) and `mellinCAZAC_of_cosetCancellation`
  (`C ↦ C+1`) — the **equivalence at the named-Prop level**, uniform in `(F, d, b)`; and
  `uniform_mellinCAZAC_iff_uniform_cosetCancellation` — the absolute-constant form: a single
  `C` works for the CAZAC claim on all `(F, d)` **iff** a single `C` works for the coset
  bound on all `(F, d)`.  (The `+1`-slack bookkeeping: the coset Prop carries the exact
  additive `1` of the identity; absorption into `C+1` uses `√(q·t·log t) ≥ 2` for `t ≥ 2`,
  and the `t = 1` edge is degenerate — empty phase sum vs `|S_b| = 1` — handled exactly.)
* `norm_mellinSum_le_weil` — `‖M_b‖ ≤ (m−1)·√q`: under the identity, **Weil is exactly the
  trivial term-count bound on the phase sum** (each `‖g(χₘ^j)‖ = √q` is the substrate's
  `norm_gaussSum_eq_sqrt`); it is the mirror of `mul_norm_eta_torsion_le` and shows no
  classical algebraic-geometry input gives any cancellation in the Mellin sum.
* `norm_eta_le_card_torsion` — `‖S_b‖ ≤ h`: the absolute coset cap, which makes the claim
  trivially true for `h = |H| = O(C²·log q)` (i.e. `m ≳ q/log q`, the provably-SAFE regime
  of the 2026-07-09 numerics where the ratio `R → 0`).

## NAMED OPEN (do not discharge — this IS open-core face 3)

* `SubgroupCosetSqrtCancellation F d C` — square-root cancellation `m·|S_b| ≤ C√(q·m·log m)+1`
  (equivalently `|S_b| ≲ √(|H|·log m)`) over EVERY coset of EVERY multiplicative subgroup,
  uniformly in `q`, in the index `m`, and in the coset.  By the equivalence proven here it is
  interchangeable with `MellinCAZACBound F d C`, whose body unfolds to *exactly* the statement
  of `R339GaussPhaseMellinTwist.GaussPhasePAPRBound F d C` (restated locally per lane hygiene —
  frontier files do not import frontier oleans; an `Iff.rfl` weld is available to any consumer
  importing both).  Status: nontrivial exactly in the window `log q ≲ |H| ≲ q/log q` and open
  throughout it, in BOTH directions — this is Paley-graph / Montgomery-conjecture / BGK
  territory; best interior results (BGK `|H| ≥ q^ε` power-saving, Heath-Brown–Konyagin /
  Konyagin / Shkredov `q^{1/4}|H|^{3/8}`-type) are far from `√(|H| log m)`, and even the
  `a = 1` pure-subgroup case is open.  Numerics (2026-07-09, verifier-audited): the literal
  uniform-constant form is heading to failure at extreme-value rate `~√(log p)/log log p`
  along a *conditional* aligned family `m ~ c·log p/log log p` (cap `(m−1)` approached, never
  attained — e.g. `4p = L² + 27M²`, `M ≠ 0` forces `|T(1)| < 2` at `m = 3`; alignment
  unconditional only per fixed `m = 3,4` via Heath-Brown–Patterson equidistribution); but a
  matched random CAZAC model fails the same way (medians match the null to 4 digits), so this
  is NOT evidence against Paley/BGK pseudorandomness, and a random-matching corrected claim
  needs a multiplicative extreme-value factor, not an additive `log p`.  Strongest
  unconditional single point: `p = 246241`, `m = 456`, `|S_a|/√(h·ln m) = 2.947`.
  Respects DISPROOF_LOG `[I027]`: nothing here bounds `L^∞` by an `L⁴`/merit-factor datum.

Issue #466, round 341, LANE B (open-core face 3).
Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar

namespace ArkLib.ProximityGap.R341CAZACCosetEquivalence

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The (unnormalized) Mellin/CAZAC phase sum at frequency `χ^d(b)`:
`mellinSum χ ψ d b = ∑_{j=1}^{t−1} (χ^{dj})⁻¹(b) · τ(χ^{dj}, ψ)` with `t = (q−1)/d`.
Dividing by `√q` gives the normalized CAZAC sum `∑_{j=1}^{m−1} u_j χₘ(b)^{−j}`. -/
noncomputable def mellinSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (d : ℕ) (b : F) : ℂ :=
  ∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
    (χ ^ (d * j))⁻¹ b * gaussSum (χ ^ (d * j)) ψ

/-- Extracting a nonzero shift from a Gauss sum as a multiplicative twist
(self-contained copy of the R339/R340 lemma, kept local so this lane iterates on the
fast path without a frontier-to-frontier olean). -/
theorem gaussSum_mulShift_twist (χ' : MulChar F ℂ) (ψ : AddChar F ℂ) {b : F}
    (hb : b ≠ 0) :
    gaussSum χ' (AddChar.mulShift ψ b) = χ'⁻¹ b * gaussSum χ' ψ := by
  have hu : IsUnit b := isUnit_iff_ne_zero.mpr hb
  have h := gaussSum_mulShift χ' ψ hu.unit
  rw [IsUnit.unit_spec] at h
  have hne : χ' b ≠ 0 := by
    intro h0
    have hn := norm_mulChar_apply_unit χ' hb
    rw [h0, norm_zero] at hn
    norm_num at hn
  have hinv : χ'⁻¹ b * χ' b = 1 := by
    rw [MulChar.inv_apply_eq_inv' χ' b, inv_mul_cancel₀ hne]
  calc gaussSum χ' (AddChar.mulShift ψ b)
      = (χ'⁻¹ b * χ' b) * gaussSum χ' (AddChar.mulShift ψ b) := by rw [hinv, one_mul]
    _ = χ'⁻¹ b * (χ' b * gaussSum χ' (AddChar.mulShift ψ b)) := by ring
    _ = χ'⁻¹ b * gaussSum χ' ψ := by rw [h]

/-- **THE BOXED IDENTITY** (solved form of the completion/Mellin identity):

  `∑_{j=1}^{m−1} g(χₘ^j)·χₘ(b)^{−j} = m·S_b + 1`,

i.e. `mellinSum χ ψ d b = t·η_b + 1` with `t = (q−1)/d` and `η_b = ∑_{y∈torsion} ψ(by)`
the coset sum over `b·H`.  The `+1` is exact: it is `−gaussSum 1 (mulShift ψ b) = −(−1)`. -/
theorem mellinSum_eq_coset {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    mellinSum χ ψ d b
      = (((Fintype.card F - 1) / d : ℕ) : ℂ) * eta ψ (torsion F d) b + 1 := by
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have ht0 : 0 < (Fintype.card F - 1) / d := Nat.div_pos (Nat.le_of_dvd hq1 hd) hd0
  have hcomp := completion_identity hd hd0 hord ψ b
  have hsplit : ∑ j ∈ Finset.range ((Fintype.card F - 1) / d),
        gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)
      = gaussSum (χ ^ (d * 0)) (AddChar.mulShift ψ b)
        + ∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
            gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b) :=
    (Finset.add_sum_erase _ _ (Finset.mem_range.mpr ht0)).symm
  have hzero : gaussSum (χ ^ (d * 0)) (AddChar.mulShift ψ b) = -1 := by
    rw [mul_zero, pow_zero]
    exact gaussSum_one_mulShift hψ hb
  have hlin : (((Fintype.card F - 1) / d : ℕ) : ℂ) * eta ψ (torsion F d) b
      = -1 + mellinSum χ ψ d b := by
    rw [hcomp, hsplit, hzero]
    congr 1
    unfold mellinSum
    exact Finset.sum_congr rfl fun j _ => gaussSum_mulShift_twist (χ ^ (d * j)) ψ hb
  rw [hlin]
  ring

/-- Transfer, phase ≤ coset direction: `‖M_b‖ ≤ m·‖S_b‖ + 1` (exact additive loss `1`). -/
theorem norm_mellinSum_le_coset {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    ‖mellinSum χ ψ d b‖
      ≤ (((Fintype.card F - 1) / d : ℕ) : ℝ) * ‖eta ψ (torsion F d) b‖ + 1 := by
  rw [mellinSum_eq_coset hd hd0 hord hψ hb]
  calc ‖(((Fintype.card F - 1) / d : ℕ) : ℂ) * eta ψ (torsion F d) b + 1‖
      ≤ ‖(((Fintype.card F - 1) / d : ℕ) : ℂ) * eta ψ (torsion F d) b‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
    _ = (((Fintype.card F - 1) / d : ℕ) : ℝ) * ‖eta ψ (torsion F d) b‖ + 1 := by
        rw [norm_mul, Complex.norm_natCast, norm_one]

/-- Transfer, coset ≤ phase direction: `m·‖S_b‖ ≤ ‖M_b‖ + 1` (exact additive loss `1`).
Together with `norm_mellinSum_le_coset`: at each `b` the two quantities are the same
number under `z ↦ m·z + 1`, so refutation families transfer verbatim both ways. -/
theorem mul_norm_eta_le_mellinSum {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    (((Fintype.card F - 1) / d : ℕ) : ℝ) * ‖eta ψ (torsion F d) b‖
      ≤ ‖mellinSum χ ψ d b‖ + 1 := by
  have hres : (((Fintype.card F - 1) / d : ℕ) : ℂ) * eta ψ (torsion F d) b
      = mellinSum χ ψ d b - 1 := by
    rw [mellinSum_eq_coset hd hd0 hord hψ hb]
    ring
  calc (((Fintype.card F - 1) / d : ℕ) : ℝ) * ‖eta ψ (torsion F d) b‖
      = ‖(((Fintype.card F - 1) / d : ℕ) : ℂ) * eta ψ (torsion F d) b‖ := by
        rw [norm_mul, Complex.norm_natCast]
    _ = ‖mellinSum χ ψ d b - 1‖ := by rw [hres]
    _ ≤ ‖mellinSum χ ψ d b‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = ‖mellinSum χ ψ d b‖ + 1 := by rw [norm_one]

/-- **Weil is the trivial phase bound**: `‖M_b‖ ≤ (m−1)·√q` by term counting, since every
nontrivial Gauss phase has modulus exactly `√q`.  Under the identity this is precisely the
substrate's Weil-trivial coset bound `mul_norm_eta_torsion_le` — no classical
algebraic-geometry input yields any cancellation in the Mellin sum. -/
theorem norm_mellinSum_le_weil {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    ‖mellinSum χ ψ d b‖
      ≤ (((Fintype.card F - 1) / d - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F) := by
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have ht0 : 0 < (Fintype.card F - 1) / d := Nat.div_pos (Nat.le_of_dvd hq1 hd) hd0
  have htd : (Fintype.card F - 1) / d * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  unfold mellinSum
  calc ‖∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
          (χ ^ (d * j))⁻¹ b * gaussSum (χ ^ (d * j)) ψ‖
      ≤ ∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
          ‖(χ ^ (d * j))⁻¹ b * gaussSum (χ ^ (d * j)) ψ‖ := norm_sum_le _ _
    _ = ∑ _j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
          Real.sqrt (Fintype.card F) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
        have hjt : j < (Fintype.card F - 1) / d :=
          Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
        have hχ' : χ ^ (d * j) ≠ 1 := by
          refine chi_pow_ne_one hord ?_ ?_
          · exact Nat.mul_pos hd0 (Nat.pos_of_ne_zero hj0)
          · calc d * j < d * ((Fintype.card F - 1) / d) :=
                (Nat.mul_lt_mul_left hd0).mpr hjt
              _ = Fintype.card F - 1 := by rw [mul_comm]; exact htd
        rw [norm_mul, norm_mulChar_apply_unit ((χ ^ (d * j))⁻¹) hb, one_mul,
          norm_gaussSum_eq_sqrt hχ' hψ]
    _ = (((Fintype.card F - 1) / d - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_range.mpr ht0),
          Finset.card_range, nsmul_eq_mul]

/-- The absolute coset cap `‖S_b‖ ≤ |H| = d` (term counting on the coset side): makes the
claim trivially true in the `|H| = O(log q)` regime, i.e. `m ≳ q/log q` — the provably-SAFE
zone of the 2026-07-09 numerics. -/
theorem norm_eta_le_card_torsion {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    (ψ : AddChar F ℂ) (b : F) :
    ‖eta ψ (torsion F d) b‖ ≤ (d : ℝ) := by
  have heta : eta ψ (torsion F d) b = ∑ y ∈ torsion F d, ψ (b * y) := rfl
  rw [heta]
  calc ‖∑ y ∈ torsion F d, ψ (b * y)‖
      ≤ ∑ y ∈ torsion F d, ‖ψ (b * y)‖ := norm_sum_le _ _
    _ = ∑ _y ∈ torsion F d, (1 : ℝ) :=
        Finset.sum_congr rfl fun y _ => AddChar.norm_apply ψ (b * y)
    _ = ((torsion F d).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (d : ℝ) := by rw [card_torsion hd hd0]

/-! ## The two named Props and the equivalence -/

/-- **The CAZAC/PAPR claim at constant `C`** (NAMED OPEN): every Mellin frequency of the
Gauss-phase vector is at random-phase scale, `‖M_b‖ ≤ C·√(q·t·log t)`; dividing by `√q`
this is `|∑_{j=1}^{m−1} u_j τ^{−j}| ≤ C·√(m log m)` for every `τ ∈ μ_m`.  The body unfolds
to exactly `R339GaussPhaseMellinTwist.GaussPhasePAPRBound F d C` (local restatement; no
frontier-to-frontier import). -/
def MellinCAZACBound (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) (C : ℝ) : Prop :=
  ∀ (χ : MulChar F ℂ), orderOf χ = Fintype.card F - 1 →
  ∀ (ψ : AddChar F ℂ), ψ.IsPrimitive → ∀ b : F, b ≠ 0 →
    ‖mellinSum χ ψ d b‖
      ≤ C * Real.sqrt (Fintype.card F * (((Fintype.card F - 1) / d : ℕ))
          * Real.log (((Fintype.card F - 1) / d : ℕ)))

/-- **Square-root cancellation over multiplicative-subgroup cosets at constant `C`**
(NAMED OPEN — the arithmetic face): `m·|S_b| ≤ C·√(q·m·log m) + 1`, equivalently
`|S_b| ≤ C·√((q/m)·log m) + 1/m` — square-root cancellation `|S_b| ≲ √(|H|·log m)` on EVERY
coset of EVERY multiplicative subgroup, uniformly in `q`, the index `m`, and the coset.
Nontrivial exactly for `log q ≲ |H| ≲ q/log q` and open throughout that window in both
directions (Paley/Montgomery/BGK territory); the `+1` is the exact edge term of
`mellinSum_eq_coset`. -/
def SubgroupCosetSqrtCancellation (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) (C : ℝ) : Prop :=
  ∀ (ψ : AddChar F ℂ), ψ.IsPrimitive → ∀ b : F, b ≠ 0 →
    (((Fintype.card F - 1) / d : ℕ) : ℝ) * ‖eta ψ (torsion F d) b‖
      ≤ C * Real.sqrt (Fintype.card F * (((Fintype.card F - 1) / d : ℕ))
          * Real.log (((Fintype.card F - 1) / d : ℕ))) + 1

/-- **Equivalence, direction A (`C ↦ C`)**: the CAZAC claim implies coset square-root
cancellation at the SAME constant (the full-order character needed to run the identity
always exists: `MulChar.exists_mulChar_orderOf_eq_card_units`). -/
theorem cosetCancellation_of_mellinCAZAC {d : ℕ} (hd : d ∣ Fintype.card F - 1)
    (hd0 : 0 < d) {C : ℝ} (h : MellinCAZACBound F d C) :
    SubgroupCosetSqrtCancellation F d C := by
  intro ψ hψ b hb
  have hcardu : (Fintype.card Fˣ : ℕ) ≠ 0 := Fintype.card_ne_zero
  obtain ⟨χ, hχord⟩ := MulChar.exists_mulChar_orderOf_eq_card_units F
    (Complex.isPrimitiveRoot_exp (Fintype.card Fˣ) hcardu)
  have hord : orderOf χ = Fintype.card F - 1 := by
    rw [hχord, Fintype.card_units]
  have htrans := mul_norm_eta_le_mellinSum hd hd0 hord hψ hb
  have hbound := h χ hord ψ hψ b hb
  linarith [htrans, hbound]

/-- **Equivalence, direction B (`C ↦ C+1`)**: coset square-root cancellation implies the
CAZAC claim with constant `C+1` (the additive `1` of the identity is absorbed via
`√(q·t·log t) ≥ 2` for `t ≥ 2`; the `t = 1` edge is exact — the phase sum is empty). -/
theorem mellinCAZAC_of_cosetCancellation {d : ℕ} (hd : d ∣ Fintype.card F - 1)
    (hd0 : 0 < d) {C : ℝ} (h : SubgroupCosetSqrtCancellation F d C) :
    MellinCAZACBound F d (C + 1) := by
  intro χ hord ψ hψ b hb
  by_cases ht1 : (Fintype.card F - 1) / d = 1
  · have hM : mellinSum χ ψ d b = 0 := by
      unfold mellinSum
      rw [ht1, Finset.range_one, Finset.erase_singleton, Finset.sum_empty]
    rw [hM, norm_zero, ht1, Nat.cast_one, Real.log_one, mul_zero, Real.sqrt_zero,
      mul_zero]
  · have hq1 : 0 < Fintype.card F - 1 := by
      have := Fintype.one_lt_card (α := F)
      omega
    have ht0 : 0 < (Fintype.card F - 1) / d := Nat.div_pos (Nat.le_of_dvd hq1 hd) hd0
    have ht2 : 2 ≤ (Fintype.card F - 1) / d := by omega
    have htd : (Fintype.card F - 1) / d * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
    have h2 : 2 ≤ Fintype.card F - 1 := by
      calc 2 = 2 * 1 := by norm_num
        _ ≤ (Fintype.card F - 1) / d * d := Nat.mul_le_mul ht2 hd0
        _ = Fintype.card F - 1 := htd
    have hq3 : 3 ≤ Fintype.card F := by omega
    have hqR : (3 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hq3
    have htR : (2 : ℝ) ≤ (((Fintype.card F - 1) / d : ℕ) : ℝ) := by exact_mod_cast ht2
    have hlogmono : Real.log 2 ≤ Real.log (((Fintype.card F - 1) / d : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) htR
    have hl2 := Real.log_two_gt_d9
    have hqt : (6 : ℝ)
        ≤ (Fintype.card F : ℝ) * (((Fintype.card F - 1) / d : ℕ) : ℝ) := by
      calc (6 : ℝ) = 3 * 2 := by norm_num
        _ ≤ (Fintype.card F : ℝ) * (((Fintype.card F - 1) / d : ℕ) : ℝ) :=
            mul_le_mul hqR htR (by norm_num) (by positivity)
    have h4 : (4 : ℝ) ≤ (Fintype.card F : ℝ) * (((Fintype.card F - 1) / d : ℕ) : ℝ)
        * Real.log (((Fintype.card F - 1) / d : ℕ) : ℝ) := by
      calc (4 : ℝ) ≤ 6 * 0.6931471803 := by norm_num
        _ ≤ 6 * Real.log 2 := by linarith [hl2]
        _ ≤ ((Fintype.card F : ℝ) * (((Fintype.card F - 1) / d : ℕ) : ℝ)) * Real.log 2 :=
            mul_le_mul_of_nonneg_right hqt (by linarith [hl2])
        _ ≤ (Fintype.card F : ℝ) * (((Fintype.card F - 1) / d : ℕ) : ℝ)
            * Real.log (((Fintype.card F - 1) / d : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hlogmono (by positivity)
    have hsqrt2 : (2 : ℝ) ≤ Real.sqrt (Fintype.card F * (((Fintype.card F - 1) / d : ℕ))
        * Real.log (((Fintype.card F - 1) / d : ℕ))) := by
      calc (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt (Fintype.card F * (((Fintype.card F - 1) / d : ℕ))
            * Real.log (((Fintype.card F - 1) / d : ℕ))) :=
            Real.sqrt_le_sqrt (by nlinarith [h4])
    have htrans := norm_mellinSum_le_coset hd hd0 hord hψ hb
    have hcoset := h ψ hψ b hb
    have hexpand : (C + 1) * Real.sqrt (Fintype.card F * (((Fintype.card F - 1) / d : ℕ))
          * Real.log (((Fintype.card F - 1) / d : ℕ)))
        = C * Real.sqrt (Fintype.card F * (((Fintype.card F - 1) / d : ℕ))
          * Real.log (((Fintype.card F - 1) / d : ℕ)))
          + Real.sqrt (Fintype.card F * (((Fintype.card F - 1) / d : ℕ))
          * Real.log (((Fintype.card F - 1) / d : ℕ))) := by ring
    linarith [htrans, hcoset, hsqrt2, hexpand.le, hexpand.ge]

/-- **The uniform-constant equivalence** (the absolute-constant phrasing of the claim):
one absolute `C` makes the CAZAC `√(m log m)` bound hold on all finite fields and all
subgroup sizes iff one absolute `C` makes the coset square-root-cancellation bound hold on
all of them.  A refutation family (growing ratio) on either side kills both. -/
theorem uniform_mellinCAZAC_iff_uniform_cosetCancellation :
    (∃ C : ℝ, ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ),
        d ∣ Fintype.card K - 1 → 0 < d → MellinCAZACBound K d C)
      ↔ (∃ C : ℝ, ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ),
        d ∣ Fintype.card K - 1 → 0 < d → SubgroupCosetSqrtCancellation K d C) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro K _ _ _ d hd hd0
    exact cosetCancellation_of_mellinCAZAC hd hd0 (hC K d hd hd0)
  · rintro ⟨C, hC⟩
    refine ⟨C + 1, ?_⟩
    intro K _ _ _ d hd hd0
    exact mellinCAZAC_of_cosetCancellation hd hd0 (hC K d hd hd0)

end ArkLib.ProximityGap.R341CAZACCosetEquivalence

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.R341CAZACCosetEquivalence.gaussSum_mulShift_twist
#print axioms ArkLib.ProximityGap.R341CAZACCosetEquivalence.mellinSum_eq_coset
#print axioms ArkLib.ProximityGap.R341CAZACCosetEquivalence.norm_mellinSum_le_coset
#print axioms ArkLib.ProximityGap.R341CAZACCosetEquivalence.mul_norm_eta_le_mellinSum
#print axioms ArkLib.ProximityGap.R341CAZACCosetEquivalence.norm_mellinSum_le_weil
#print axioms ArkLib.ProximityGap.R341CAZACCosetEquivalence.norm_eta_le_card_torsion
#print axioms ArkLib.ProximityGap.R341CAZACCosetEquivalence.cosetCancellation_of_mellinCAZAC
#print axioms ArkLib.ProximityGap.R341CAZACCosetEquivalence.mellinCAZAC_of_cosetCancellation
#print axioms ArkLib.ProximityGap.R341CAZACCosetEquivalence.uniform_mellinCAZAC_iff_uniform_cosetCancellation
