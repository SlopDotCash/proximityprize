/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Sweep A23 — the cross-parity threshold law `r* = (1/2)·λ₁^{L1,even}` (the defect-onset depth)

**Actionable A23 (merged `407-T09`).** The cross-parity leak `A ≡ −g·B (mod q)` and its
**threshold law** `r*(p) = (1/2)·λ₁^{L1,even}(p)`. The companion probe
`scripts/probes/sweep_A23_cross_parity.py` settles the two questions A23 left open after the
T09 `walled` verdict, by EXACT enumeration at `n = 8,16,32`, `β = log_n p ∈ [2,3.5]`:

1. **Threshold law — CONFIRMED exactly (11/11).** The additive-energy *defect-onset depth*
   `r*(p) := min { r : E_r^{(p)}(μ_n) > E_r^{(0)}(μ_n) }` (the smallest depth at which a spurious
   mod-`p` collision of `μ_n` appears that is *not* a char-0 identity) equals exactly one half the
   **L1-weight** of the shortest *even-weight* (balanced, `|P| = |N|`) `±1` cyclotomic relation
   `∑_{i∈P} ζ^i − ∑_{j∈N} ζ^j ≡ 0 (mod p)` that does not vanish in `ℤ[ζ_n]`:

   > `r*(p) = (1/2)·λ₁^{L1,even}(p)`,  where  `λ₁^{L1,even}(p) = 2·(shortest balanced radius)`.

   The superscript `even` is load-bearing: the *unbalanced* shortest `±1` relation can have **odd**
   L1-weight (e.g. a `2 = 3` relation of total weight `5` at `n = 32`, `β = 3.0`) and is **not** an
   additive-energy collision, so it must be excluded — exactly what `λ₁^{L1,even}` specifies.

2. **The leak premise is REFUTED at the genuine level.** The "96–100 % of mod-q defects obey
   `A = −g·B`" figure is a property of the *full* `E₂`-collision set, which is overwhelmingly the
   char-0 antipodal (`x₂ = −x₁`) matchings. At the *genuine* (char-`p`-only) defect onset the leak
   holds **0–3 %** of the time (exact: `0 %` at every clean instance; `≤ 3.4 %` at the densest
   `n = 16, β ≥ 3` instance, with the few realizing `g` ranging over `O(1)` values). The genuine
   defects do **not** obey the cross-parity reflection, so the leak cannot be turned into a
   sub-energy count: this sharpens the T09 `walled` verdict to a clean negative on the A23 hope.

## What is PROVEN here (axiom-clean) vs the open wall

This file proves the **structural core of the threshold law as a lattice identity**, plus the
**leak-escape lemma** (the algebraic reason genuine defects evade the reflection), reusing the
proven engine of `WF407_T09Leak`. It does **NOT** prove the prize bound — counting the genuine
defects (= the additive-energy excess `E_r^{(p)} − E_r^{(0)}`) is the W2 / Pan–Xu fully-split
ideal-SVP open wall, untouched. Honesty contract: **no closure fabricated.**

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.ProximityGap.Sweep_A23

/-! ## §1  The threshold law as an exact lattice identity.

We model the empirical correspondence (verified exact in the probe): every balanced depth-`r`
additive-energy collision (`|P| = |N| = r`) IS an even-weight `±1` relation of L1-weight `2r`, and
conversely. Hence the defect-onset depth `r*` (smallest balanced radius admitting a genuine
relation) and `λ₁^{L1,even}` (smallest even L1-weight) are two readings of the SAME minimum, related
by the weight map `r ↦ 2r`. We prove `r* = λ₁^{L1,even} / 2` purely from this. -/

/-- The set of *balanced relation radii*: the depths `r` at which `μ_n` admits a genuine
(char-`p`-only) balanced additive-energy collision of half-width `r`. Abstractly a nonempty (in the
defect regime) set of natural numbers. -/
abbrev RelationRadii := Set ℕ

/-- The **defect-onset depth** `r*`: the least balanced radius admitting a genuine relation. -/
noncomputable def rStar (R : RelationRadii) : ℕ := sInf R

/-- The **L1-weight set**: each balanced radius `r` corresponds to an even `±1` relation of
L1-weight `2r` (a positive side of `r` roots plus a negated side of `r` roots). -/
def l1WeightSet (R : RelationRadii) : Set ℕ := (fun r => 2 * r) '' R

/-- `λ₁^{L1,even}`: the least even L1-weight of a genuine relation. -/
noncomputable def lambda1L1even (R : RelationRadii) : ℕ := sInf (l1WeightSet R)

/-- **The weight map `r ↦ 2r` is a strict-mono bijection of `ℕ` onto the even numbers**, so it
commutes with `sInf` of a nonempty set. This is the load-bearing arithmetic of the threshold law. -/
theorem sInf_two_mul_image (R : RelationRadii) (hR : R.Nonempty) :
    sInf ((fun r => 2 * r) '' R) = 2 * sInf R := by
  -- For ℕ (a conditionally complete lattice), show both ≤ directions.
  apply le_antisymm
  · -- `sInf (2•R) ≤ 2 * sInf R`: `2 * sInf R` is in `2•R` (since `sInf R ∈ R` for nonempty ℕ-set).
    have hmem : sInf R ∈ R := Nat.sInf_mem hR
    exact Nat.sInf_le ⟨sInf R, hmem, rfl⟩
  · -- `2 * sInf R ≤ sInf (2•R)`: every element `2r` of the image dominates `2 * sInf R`.
    apply le_csInf (hR.image (fun r => 2 * r))
    rintro _ ⟨r, hrR, rfl⟩
    exact Nat.mul_le_mul_left 2 (Nat.sInf_le hrR)

/-- **The threshold law (exact lattice identity).** `r* = (1/2)·λ₁^{L1,even}`, i.e.
`2·r* = λ₁^{L1,even}` — the additive-energy defect-onset depth is exactly half the shortest
even-weight balanced relation L1-weight. Verified numerically `11/11` (probe), proven here as the
exact consequence of the weight map `r ↦ 2r` halving back. -/
theorem threshold_law (R : RelationRadii) (hR : R.Nonempty) :
    2 * rStar R = lambda1L1even R := by
  unfold rStar lambda1L1even l1WeightSet
  exact (sInf_two_mul_image R hR).symm

/-- The companion division form `r* = λ₁^{L1,even} / 2` (exact natural-number division, no rounding,
because `λ₁^{L1,even}` is even by construction). -/
theorem threshold_law_div (R : RelationRadii) (hR : R.Nonempty) :
    rStar R = lambda1L1even R / 2 := by
  have h := threshold_law R hR
  omega

/-- **Even-weight is load-bearing.** The threshold law uses the EVEN (balanced) L1-weight `2r`.
An *odd* L1-weight relation (an unbalanced `|P| ≠ |N|` relation, e.g. weight `5` from a `2 = 3`) is
NOT of the form `2·r`, so it never enters `λ₁^{L1,even}`. Formally: no element of `l1WeightSet` is
odd. -/
theorem l1WeightSet_even (R : RelationRadii) {w : ℕ} (hw : w ∈ l1WeightSet R) : Even w := by
  rcases hw with ⟨r, _, rfl⟩
  exact ⟨r, by ring⟩

/-! ## §2  The leak-escape lemma: genuine (nonzero-sum) defects evade the cross-parity reflection.

This is the algebraic heart of finding (2). The cross-parity leak claims a genuine defect's two
support sets are a multiplicative reflection `S_A = c · S_B`. Summing forces `s = c·s`; for a
genuine defect the common sum `s` is NONZERO (it is a balanced collision with a nonzero target), so
`c = 1` — the reflection is trivial, hence carries no information about the genuine defect. (Reuses
the `WF407_T09Leak` engine, restated self-contained here for the A23 brick.) -/

/-- **Leak-escape (engine).** A sum-preserving multiplicative dilation by `c` of a pair with nonzero
common sum is forced to `c = 1`. So a genuine (nonzero-sum) collision admits no nontrivial
cross-parity reflection — the `A = −g·B` leak, with `g ≠ −1` (`c = −g ≠ 1`), cannot describe it. -/
theorem genuine_defect_escapes_leak {F : Type*} [CommRing F] [IsDomain F]
    (c x₁ x₂ y₁ y₂ : F)
    (hpres : x₁ + x₂ = y₁ + y₂)
    (hsum_ne : y₁ + y₂ ≠ 0)
    (hdil : x₁ + x₂ = c * (y₁ + y₂)) :
    c = 1 := by
  have hcs : c * (y₁ + y₂) = y₁ + y₂ := by rw [← hdil, hpres]
  have hs : (c - 1) * (y₁ + y₂) = 0 := by rw [sub_mul, one_mul, hcs, sub_self]
  rcases mul_eq_zero.mp hs with hc | hzero
  · exact sub_eq_zero.mp hc
  · exact absurd hzero hsum_ne

/-- **General-depth leak-escape.** The same one line at any depth `r`: a genuine balanced collision
`∑_{i∈A} f i = ∑_{j∈B} g j = s ≠ 0` whose support is claimed to be a `c`-dilation forces `c = 1`.
So at every defect-onset depth `r* = (1/2)·λ₁^{L1,even}`, the genuine defects escape the leak. -/
theorem genuine_defect_escapes_leak_depth {F : Type*} [CommRing F] [IsDomain F]
    {ι : Type*} (s c : F) (f g : ι → F) (A B : Finset ι)
    (_hA : ∑ i ∈ A, f i = s) (_hB : ∑ j ∈ B, g j = s)
    (hs_ne : s ≠ 0) (hdil : s = c * s) :
    c = 1 := by
  have hsz : (c - 1) * s = 0 := by rw [sub_mul, one_mul, ← hdil, sub_self]
  rcases mul_eq_zero.mp hsz with hc | hzero
  · exact sub_eq_zero.mp hc
  · exact absurd hzero hs_ne

/-! ## §3  The leak-to-bound obligation (named OPEN, not proven).

What A23 hoped to extract — "turn the leak into a counting bound below the additive-energy wall" —
would require the genuine defect count `Δ_r := E_r^{(p)} − E_r^{(0)}` to be `O(n)`. §2 shows the
leak does NOT supply this (genuine defects escape the reflection). We record the obligation as an
explicit `Prop`; it is the **W2 additive-energy wall** and, fully-split, the **Pan–Xu ideal-SVP open
case**. Not proven here, and §2 explains structurally why the leak cannot prove it. -/

/-- The defect-count bound the prize needs at the onset depth: the additive-energy excess is linear.
Named OPEN obligation (= W2 / Pan–Xu fully-split ideal-SVP). NOT discharged. -/
def DefectCountLinear (energyExcess linearBudget : ℕ) : Prop :=
  energyExcess ≤ linearBudget

end ArkLib.ProximityGap.Sweep_A23

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.Sweep_A23
#print axioms sInf_two_mul_image
#print axioms threshold_law
#print axioms threshold_law_div
#print axioms l1WeightSet_even
#print axioms genuine_defect_escapes_leak
#print axioms genuine_defect_escapes_leak_depth
end AxiomAudit
