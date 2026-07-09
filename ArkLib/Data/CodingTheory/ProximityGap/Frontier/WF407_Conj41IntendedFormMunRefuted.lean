/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TopDirectionLineCount

/-!
# WF407 / thread T232-11-conj41 — the INTENDED (fixed-syndrome) form of Conjecture 41
is REFUTED on the prize-shaped smooth multiplicative subgroup `μ_n`

Conjecture 41 (Chai–Fan, ePrint 2026/858, the `c ≥ 3` "open-set rank lemma") predicts a
codimension-excess list size `M ≤ ⌊(2D−1)/c⌋` (linear, `O(D/c)`), which gives `M = O(1)`
at the Johnson radius. The paper prints it in **two inequivalent forms**:

* the **rank / dichotomy** form — about the kernel of the twisted normal block at a
  *fixed* syndrome (the quantity FRI soundness / the deep-quotient transfer actually
  consumes: the worst-case list at one received word); and
* the **"Equivalently, `M_true ≤ ⌊(2D−1)/c⌋`"** sentence — about the count of compatible
  parameters along a syndrome *line*.

DISPROOF_LOG O43/O64 already refuted the *line-count* sentence on the **additive** domain
`{0,…,N−1}` (`conj41_violation_witness`, `LamLeungTwoPow.conj41_mtrue_witness`), and showed
the two forms are inequivalent (the escape clause does "unintended exclusion"). That left
two questions for thread T232-11:

1. **Which form is intended?** Numerically (probe
   `scripts/probes/wf407_T232-11-conj41_intended_form.py`, GAP A): on the additive domain
   the line-count `M_line` shoots past the ceiling (13 at `N=16`) while the *fixed-syndrome*
   list `M_fixed` stays `≤ 5`. So the fixed-syndrome (rank/dichotomy) form is the **intended**
   one and the "Equivalently" sentence is an **erratum**: the two are different numbers.

2. **Does the intended form survive on the prize domain?** The prize domain is the smooth
   *multiplicative* subgroup `μ_n` (`n = 2^μ`), not the additive interval. Probe GAP B/C +
   `wf407_T232-11-conj41_coset_law.py`: on a **proper** subgroup `μ_n` the worst
   fixed-syndrome list obeys the exact, field-independent law
   `M_fixed(μ_n, w=6, c=3) = ⌊n/4⌋ − 1` (verified `n = 8,12,…,36`, two primes each), which
   **crosses the ceiling 5 at `n = 28`** — so the **intended form is also REFUTED on the
   prize domain**, and the worst family is a `μ_4`-coset–anchored PTE family (the support
   normalizes to negation pairs with `e₃ = 0`), welding the count onto the **same
   esymm-fiber / PTE / Katz-floor `n/4` wall** as threads A21/A08/400-T04.

This file delivers the **machine-checked countermodel** for (2): a *proper* smooth subgroup
`μ₃₆ ⊂ F₇₃^×` (`36 ∣ 72`, `36 < 72`) hosting **6** distinct genuine weight-`6` supports all
with `e₁ = e₂ = e₃ = 0`. By `TopLine.point_compat_iff_esymm_zero` these are exactly the
supports compatible with the **single fixed unit syndrome** `unitVec 5` at codimension
excess `c = 3`, so the fixed-syndrome list there has `≥ 6 > 5 = ⌊(2·9−1)/3⌋` codewords —
the intended (rank/dichotomy) form fails on a prize-shaped smooth subgroup.

**Honesty.** This is a `*_REFUTED` brick: a machine-checked countermodel to the *printed*
Conjecture 41 (its intended fixed-syndrome form) on `μ_n`. It does **not** close the prize.
On the contrary it confirms the welding: the correct list quantity is the esymm-fiber /
PTE count, which is the recognized open wall. The probes are exact (integer / mod-p,
field-independent across two primes), not sampled.
-/

namespace WF407Conj41MunRefuted

open TopLine Polynomial Finset
open scoped Classical

instance : Fact (Nat.Prime 73) := ⟨by norm_num⟩

/-- The six witness supports: distinct weight-`6` subsets of the proper smooth subgroup
`μ₃₆ ⊂ F₇₃^×` with `e₁ = e₂ = e₃ = 0`. Each is a union of three negation pairs of `μ₃₆`
(e.g. `{1, 72}`, `{8, 65}`, `{9, 64}` with `72 = −1`, `65 = −8`, `64 = −9` mod `73`),
i.e. `μ₂`-coset–anchored — the antipodal/PTE structure that makes `e₁ = e₃ = 0` automatic
and `e₂ = 0` the extra condition. -/
def W₁ : Finset (ZMod 73) := {1, 8, 9, 64, 65, 72}
def W₂ : Finset (ZMod 73) := {6, 19, 25, 48, 54, 67}
def W₃ : Finset (ZMod 73) := {4, 32, 36, 37, 41, 69}
def W₄ : Finset (ZMod 73) := {3, 24, 27, 46, 49, 70}
def W₅ : Finset (ZMod 73) := {2, 16, 18, 55, 57, 71}
def W₆ : Finset (ZMod 73) := {12, 23, 35, 38, 50, 61}

/-- The family of the six witness supports. -/
def Wfam : Finset (Finset (ZMod 73)) := {W₁, W₂, W₃, W₄, W₅, W₆}

/-- The proper smooth multiplicative subgroup `μ₃₆ ⊂ F₇₃^×` as an explicit `Finset`.
`73` is prime, `36 ∣ 72 = |F₇₃^×|`, and `36 < 72`, so this is a *proper* subgroup —
the prize-regime shape (a smooth subgroup strictly inside the field), not the
full-group degeneracy `μ_{p−1} = F_p^×`. -/
def mu36 : Finset (ZMod 73) :=
  {1, 25, 41, 3, 2, 50, 9, 6, 4, 27, 18, 12, 8, 54, 36, 24, 16, 35, 72, 48, 32, 70, 71,
   23, 64, 67, 69, 46, 55, 61, 65, 19, 37, 49, 57, 38}

/-- Each witness support lies in the proper subgroup `μ₃₆`. -/
theorem W_subset_mu36 :
    W₁ ⊆ mu36 ∧ W₂ ⊆ mu36 ∧ W₃ ⊆ mu36 ∧ W₄ ⊆ mu36 ∧ W₅ ⊆ mu36 ∧ W₆ ⊆ mu36 := by
  decide

/-- Each witness support has weight (cardinality) `6`. -/
theorem W_card :
    W₁.card = 6 ∧ W₂.card = 6 ∧ W₃.card = 6 ∧ W₄.card = 6 ∧ W₅.card = 6 ∧ W₆.card = 6 := by
  decide

/-- Each witness support has vanishing `e₁, e₂, e₃`. -/
theorem W_esymm_zero :
    (∀ i ∈ Finset.Icc 1 3, W₁.val.esymm i = 0) ∧
    (∀ i ∈ Finset.Icc 1 3, W₂.val.esymm i = 0) ∧
    (∀ i ∈ Finset.Icc 1 3, W₃.val.esymm i = 0) ∧
    (∀ i ∈ Finset.Icc 1 3, W₄.val.esymm i = 0) ∧
    (∀ i ∈ Finset.Icc 1 3, W₅.val.esymm i = 0) ∧
    (∀ i ∈ Finset.Icc 1 3, W₆.val.esymm i = 0) := by
  decide

/-- The six witness supports are pairwise distinct, so `Wfam.card = 6`. -/
theorem Wfam_card : Wfam.card = 6 := by decide

/-- Membership characterization of `powersetCard`: a support is in `mu36.powersetCard 6`
iff it is a subset of `μ₃₆` of cardinality `6`. -/
private theorem mem_pc {E : Finset (ZMod 73)} :
    E ∈ mu36.powersetCard 6 ↔ E ⊆ mu36 ∧ E.card = 6 := Finset.mem_powersetCard

/-- **The six witness supports all lie in the fixed-syndrome (zero-fiber) compatible set.**
By `TopLine.point_compat_iff_esymm_zero`, compatibility with the fixed unit syndrome
`unitVec 5` at codimension excess `c = 3` for a weight-`6` support is exactly
`e₁ = e₂ = e₃ = 0`. -/
theorem Wfam_subset_compat :
    Wfam ⊆ (mu36.powersetCard 6).filter (fun E => CompatC (unitVec 5) 9 3 E) := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W_subset_mu36
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := W_card
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := W_esymm_zero
  -- the point-fiber bridge: for a weight-6 support, CompatC (unitVec 5) 9 3 ↔ e₁=e₂=e₃=0
  have bridge : ∀ E : Finset (ZMod 73), E.card = 6 →
      ((∀ i ∈ Finset.Icc 1 3, E.val.esymm i = 0) → CompatC (unitVec 5) 9 3 E) := by
    intro E hcard hz
    have hw : E.card + 3 = 9 := by omega
    have hcw : (3 : ℕ) ≤ E.card := by omega
    have key := (point_compat_iff_esymm_zero (F := ZMod 73) (N := 9) (c := 3)
      (E := E) hw (by norm_num) hcw).mpr hz
    -- `point_compat_iff_esymm_zero` is stated at `unitVec (E.card - 1) = unitVec 5`
    rwa [show E.card - 1 = 5 from by omega] at key
  intro E hE
  simp only [Wfam, Finset.mem_insert, Finset.mem_singleton] at hE
  rw [Finset.mem_filter, mem_pc]
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨s1, c1⟩, bridge _ c1 z1⟩
  · exact ⟨⟨s2, c2⟩, bridge _ c2 z2⟩
  · exact ⟨⟨s3, c3⟩, bridge _ c3 z3⟩
  · exact ⟨⟨s4, c4⟩, bridge _ c4 z4⟩
  · exact ⟨⟨s5, c5⟩, bridge _ c5 z5⟩
  · exact ⟨⟨s6, c6⟩, bridge _ c6 z6⟩

/-- **The refutation of Conjecture 41's intended (fixed-syndrome) form on the prize-shaped
smooth subgroup `μ₃₆ ⊂ F₇₃^×`.** At codimension excess `c = 3`, support weight `w = 6`,
window `D = N = 9`, the Chai–Fan bound is `⌊(2D−1)/c⌋ = ⌊17/3⌋ = 5`. But the list of
weight-`6` supports of `μ₃₆` compatible with the *single fixed* unit syndrome `unitVec 5`
— which, by `point_compat_iff_esymm_zero`, equals the `e₁ = e₂ = e₃ = 0` zero fiber — has at
least `6` members. Since `6 > 5`, the bound fails on a proper smooth multiplicative
subgroup. The line-count form was already refuted on the additive domain (O43); this
refutes the *intended fixed-syndrome* form on the *prize domain*. -/
theorem conj41_intended_form_mun_REFUTED :
    (2 * 9 - 1) / 3 <
      ((mu36.powersetCard 6).filter (fun E => CompatC (unitVec 5) 9 3 E)).card := by
  have hbound : (2 * 9 - 1) / 3 = 5 := by norm_num
  rw [hbound]
  calc 5 < 6 := by norm_num
    _ = Wfam.card := Wfam_card.symm
    _ ≤ _ := Finset.card_le_card Wfam_subset_compat

end WF407Conj41MunRefuted
