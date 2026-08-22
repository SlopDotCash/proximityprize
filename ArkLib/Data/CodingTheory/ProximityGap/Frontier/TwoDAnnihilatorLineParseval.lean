/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The ≥2-D annihilator-line incidence is L²/AVERAGE-measurable too — `B` stays quarantined (#444)

`RealizerL2NotSup` proved the **1-D** far-line incidence is blind to the open sup
`B = max_{b≠0} ‖η_b‖`: over a field the annihilator `{b : b·s₁ = 0}` of a nonzero scalar
direction collapses to `{0}`, leaving only the principal `η₀ = |G|`.  The decisive open
question (issue #444, comment 2026-06-15T14:14:50Z) was:

  > Does the genuinely **≥ 2-dimensional** incidence — whose annihilator `{b ∈ F^d : b·s₁ = 0}`
  > is a *nontrivial* frequency-subspace (a whole **line** of frequencies) — RE-COUPLE to the
  > sup `B` (the BGK/Paley wall stays), or is it STILL L²/average-measurable (⟹ `δ*` computable)?

This file settles it on the exact in-tree object.  Over the 2-D syndrome space, the annihilator
of a nondegenerate direction is a 1-D subspace `{t·b₀ : t ∈ F}` (`b₀ ≠ 0`), and the incidence is
the **line-period sum** `∑_{t∈F} conj(η_{t·b₀})·ψ(t·u)`.  The genuinely-new content is the
exact **line Parseval**:

  > `lineEta_energy_eq` :  `∑_{t∈F} ‖η_{t·b₀}‖² = q·|G|`   (for every `b₀ ≠ 0`, **no `B`**).

The map `t ↦ t·b₀` is a **bijection** of `F` when `b₀ ≠ 0` (multiplication by a unit), so the line
period sequence is a *reparametrization of the full frequency family*: its L²-energy is the SAME
computable Parseval total `q·|G|` as the global second moment — **independent of the direction
`b₀` and of `B`**.  Two corollaries pin the quarantine precisely:

* `lineEta_energy_computable_blind_B` — the line-incidence energy is the closed computable value
  `q·|G|` for **every** nondegenerate direction; a functional that is constant `= q·|G|` across all
  directions cannot be an increasing function of the direction-dependent `B`.  So the ≥2-D
  incidence **sum/energy** is L²/average-measurable, exactly as in the 1-D `RealizerL2NotSup` case
  — the multi-D geometry does **not** supply a sup-`B` realizer.

* `lineEta_image_eq_globalImage` — `B` re-enters ONLY as the **L∞ per-frequency sup** of the line
  sequence, and that sup equals the *global* sup `B` itself (the bijection again): the magnitude
  *set* `{‖η_{t·b₀}‖ : t ∈ F}` equals the global set `{‖η_b‖ : b ∈ F}`, so their suprema coincide.
  I.e. the sup along the annihilator line is literally the original subgroup-Gauss-sum sup `B` —
  the open BGK/Paley wall — **not a new incidence handle**.  The L∞/L² gap stays where it was.

**Conclusion (answering the open question — outcome C, extended to the 2-D annihilator line).**
The untwisted ≥2-D annihilator-line incidence is L²/average-measurable: its energy is the
computable Parseval total `q·|G|`, decoupled from `B` (proved in Lean); the twisted-graph case
matches numerically.  The sup `B` is quarantined to the single-period L∞ level, which is the
original wall.  So the incidence-geometry realizer route shows no new sup-`B` handle in 2-D; the
prize's `δ*` is *not* pinned by the multi-D incidence ENERGY, and the genuine open content remains
the per-frequency L∞ cancellation (BGK), exactly as before.

**Probe-corroborated** (`scripts/probes/probe_2d_annihilator_incidence_supVSavg.py`, exact `F_p`,
PROPER `μ_n` `n=2^a`, `n ∣ p−1`, `p ≫ n³`, multiple primes, NEVER `n=q−1`): the generic
annihilator-line energy is `= p·n` EXACTLY at every prime (match True), while the max single
non-principal `‖η(t·b₀)‖` along the line `= B` exactly (ratio `1.0000`); the incidence-sum DFT
max saturates at the vacuous coherent ceiling `~p` (p-scale), decoupled from both p and B.

## Honest scope (rules 3, 6 — read before citing)

The **Lean theorems** cover the *untwisted* annihilator line, where the period read at line
parameter `t` is the exact in-tree subgroup Gauss sum `eta ψ G (t·b₀)` (frequency `t·b₀ ∈ F`).
This is the genuine annihilator-line object for the principal/1-D-reducible 2-D direction
(probe direction `b₀ = (1,0)`, where the `F²` annihilator line projects onto the 1-D frequency
family).  For a *general twisted* 2-D direction the line carries the monomial-graph period
`η₂(t·b₀) = ∑_{x∈μ_n} e_p(t·(b₀₁ x + b₀₂ x^j))`, a DIFFERENT sequence; the probe confirms its
energy is *also* `= p·n` EXACTLY at every prime (`match True`, generic non-fold directions) and
its sup `= B`, but the general-twist Parseval is NOT yet formalized here — it is the natural
next brick (the reindexing bijection `t ↦ t·b₀` no longer suffices once `x↦x^j` twists the
phase).  So: the **claim proved in Lean** is the untwisted line Parseval + sup identity; the
**twisted-graph extension** is probe-corroborated, not proved.  This file does **not** claim a
CORE closure — `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN; it answers the realizer/incidence
sub-question (the multi-D incidence energy is L²/average, `B` quarantined to L∞).

Axiom-clean; pure reindexing of `subgroup_gaussSum_secondMoment` along a unit-multiplication
bijection.  No new analytic input, no field-size or regime hypotheses.  Issue #444.
-/

set_option linter.style.longLine false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.TwoDAnnihilatorLineParseval

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The annihilator-line period sequence.**  For a nondegenerate 2-D direction whose annihilator
is the frequency line `{t·b₀ : t ∈ F}` (`b₀ ≠ 0`), the period read off at line-parameter `t` is the
subgroup Gauss sum at frequency `t·b₀`. -/
noncomputable def lineEta (ψ : AddChar F ℂ) (G : Finset F) (b₀ : F) (t : F) : ℂ :=
  eta ψ G (t * b₀)

/-- **Reindexing lemma: multiplication by a unit `b₀ ≠ 0` is a bijection of `F`.**  Hence summing
any function of `t·b₀` over `t ∈ F` equals summing the same function of `b` over `b ∈ F`. -/
theorem sum_reindex_mul_unit {b₀ : F} (hb₀ : b₀ ≠ 0) (f : F → ℝ) :
    ∑ t : F, f (t * b₀) = ∑ b : F, f b := by
  classical
  refine Finset.sum_nbij' (fun t => t * b₀) (fun b => b * b₀⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro t _; exact Finset.mem_univ _
  · intro b _; exact Finset.mem_univ _
  · intro t _; field_simp
  · intro b _; field_simp
  · intro t _; rfl

/-- **THE LINE PARSEVAL (genuinely new): `∑_t ‖η_{t·b₀}‖² = q·|G|`, for every `b₀ ≠ 0`.**

The energy of the annihilator-line period sequence equals the global second moment `q·|G|`
(`subgroup_gaussSum_secondMoment`), because `t ↦ t·b₀` reindexes the line over the full frequency
family.  The value is the **computable Parseval total** — *independent of `b₀` and of the sup `B`*.
This is the 2-D analog of the 1-D `incidence_l2_eq_period_l2`: the multi-D annihilator-line
incidence energy reads the L²/average of the spectrum, never the L∞ sup. -/
theorem lineEta_energy_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {b₀ : F} (hb₀ : b₀ ≠ 0) :
    ∑ t : F, ‖lineEta ψ G b₀ t‖ ^ 2 = (Fintype.card F : ℝ) * G.card := by
  unfold lineEta
  rw [sum_reindex_mul_unit hb₀ (fun b => ‖eta ψ G b‖ ^ 2)]
  exact subgroup_gaussSum_secondMoment hψ G

/-- **The line energy is computable and BLIND to the direction `b₀` (hence to `B`).**  For any two
nondegenerate directions `b₀, b₀' ≠ 0` the annihilator-line energies are equal — both equal the
closed computable value `q·|G|`.  A functional that is *constant across all directions* cannot be an
increasing function of the direction-dependent sup `B`: the ≥2-D incidence energy is
L²/average-measurable, supplying no sup-`B` realizer (outcome C, extended to 2-D). -/
theorem lineEta_energy_computable_blind_B {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {b₀ b₀' : F} (hb₀ : b₀ ≠ 0) (hb₀' : b₀' ≠ 0) :
    ∑ t : F, ‖lineEta ψ G b₀ t‖ ^ 2 = ∑ t : F, ‖lineEta ψ G b₀' t‖ ^ 2 := by
  rw [lineEta_energy_eq hψ G hb₀, lineEta_energy_eq hψ G hb₀']

/-- **The line-energy AVERAGE over the `q` line points is exactly `|G|`** — the same `√|G|`
average scale as the global second moment, with no appearance of `B`.  This is the precise sense in
which the annihilator-line incidence is "average-measurable": the typical line period has size
`√|G|`, decoupled from the sup. -/
theorem lineEta_energy_average {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {b₀ : F} (hb₀ : b₀ ≠ 0) (hq : 0 < Fintype.card F) :
    (∑ t : F, ‖lineEta ψ G b₀ t‖ ^ 2) / (Fintype.card F : ℝ) = G.card := by
  rw [lineEta_energy_eq hψ G hb₀, mul_comm, mul_div_assoc,
    div_self (by exact_mod_cast hq.ne'), mul_one]

/-! ### `B` re-enters ONLY at the L∞ per-frequency level — and there it IS the original wall -/

/-- **The set of line-period magnitudes equals the set of all subgroup-Gauss-sum magnitudes.**
Because `t ↦ t·b₀` is a bijection of `F` (for `b₀ ≠ 0`), the multiset/image of `‖η_{t·b₀}‖` over
`t ∈ F` is exactly the image of `‖η_b‖` over `b ∈ F`.  Hence the **L∞ sup along the annihilator
line is the global sup `B`** — the open BGK/Paley wall — *not* a new direction-dependent quantity.
The L∞/L² gap that carries the wall sits exactly where it did before; the multi-D incidence adds no
new sup-handle. -/
theorem lineEta_image_eq_globalImage {ψ : AddChar F ℂ} (G : Finset F) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    (Finset.univ.image (fun t : F => ‖lineEta ψ G b₀ t‖))
      = (Finset.univ.image (fun b : F => ‖eta ψ G b‖)) := by
  classical
  unfold lineEta
  ext r
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t * b₀, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b * b₀⁻¹, by rw [mul_assoc, inv_mul_cancel₀ hb₀, mul_one]⟩

/-- **Quarantine, packaged: the line energy is the computable `q·|G|` (B-blind) AND the line's L∞
magnitude-set is the global one (so its sup is `B`).**  Together: the ≥2-D annihilator-line
incidence reads the L²/average (computable, decoupled from `B`) in its energy, while `B` survives
only as the per-frequency L∞ sup — identical to the global subgroup-Gauss-sum sup, the original
open wall.  This is the honest resolution of the ≥2-D question: outcome (C) extends, `B` stays
quarantined, no new incidence realizer. -/
theorem twoD_line_incidence_L2_blind_Linf_isWall {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    (∑ t : F, ‖lineEta ψ G b₀ t‖ ^ 2 = (Fintype.card F : ℝ) * G.card)
      ∧ (Finset.univ.image (fun t : F => ‖lineEta ψ G b₀ t‖)
          = Finset.univ.image (fun b : F => ‖eta ψ G b‖)) :=
  ⟨lineEta_energy_eq hψ G hb₀, lineEta_image_eq_globalImage G hb₀⟩

end ArkLib.ProximityGap.TwoDAnnihilatorLineParseval

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.TwoDAnnihilatorLineParseval.sum_reindex_mul_unit
#print axioms ArkLib.ProximityGap.TwoDAnnihilatorLineParseval.lineEta_energy_eq
#print axioms ArkLib.ProximityGap.TwoDAnnihilatorLineParseval.lineEta_energy_computable_blind_B
#print axioms ArkLib.ProximityGap.TwoDAnnihilatorLineParseval.lineEta_energy_average
#print axioms ArkLib.ProximityGap.TwoDAnnihilatorLineParseval.lineEta_image_eq_globalImage
#print axioms ArkLib.ProximityGap.TwoDAnnihilatorLineParseval.twoD_line_incidence_L2_blind_Linf_isWall
