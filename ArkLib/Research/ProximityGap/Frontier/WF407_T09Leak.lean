/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Tactic.LinearCombination

/-!
# WF407 thread T09-leak — the cross-parity reflection leak is sum-zero (antipodal) only

**Thread.** #407 T09-leak: "96–100% of all mod-q defects obey ONE structured relation
`A ≡ −g·B mod q`" (the *cross-parity leak*); the fully-split `N(𝔮)=p` case is the Pan–Xu
ideal-SVP open gap; the leak "was never turned into a bound".

**What this file proves (axiom-clean), and what it pins down.**

The leak, made precise at the additive-energy depth `r = 2` (the cleanest layer): an `E₂`
*collision* of `μ_n ⊂ F_q^×` is an equality of two-element sums `x₁ + x₂ = y₁ + y₂` with the two
pairs distinct. The probes (`scripts/probes/wf407_T09-leak_*.py`) measured that **in the prize
regime (`p ≫ n²`), 100 % of these collisions are a multiplicative reflection**
`{x₁, x₂} = c · {y₁, y₂}` (a torus-normalizer image), with `c = −g ∈ μ_n` — this *is* the
`A ≡ −g·B` leak. The probes then found the structural collapse:

* the reflection holds for **exactly** the *antipodal / sum-zero* collisions (`x₂ = −x₁`,
  `y₂ = −y₁`), which are the char-0 Lam–Leung matchings — **not** genuine spurious mod-`p`
  defects (genuine defects realize the reflection 0 % of the time, measured);
* the **count** of the genuinely-spurious part is exactly the char-`p` additive-energy excess
  `E₂^{(p)} − E₂^{(0)}` (verified exactly: `wf407_T09-leak_count_identity.py`).

The rigorous *engine* behind "100 % reflection ⟹ sum-zero" is one line of algebra, formalized
here in full generality (`sum_preserving_dilation_forces_zero`): **a multiplicative dilation by
`c ≠ 1` that preserves a sum forces that sum to be `0`.** Summing the setwise identity
`{x₁, x₂} = c · {y₁, y₂}` gives `x₁ + x₂ = c·(y₁ + y₂)`, i.e. `s = c·s`, so `(c − 1)·s = 0`,
hence `c = 1` or `s = 0`. Consequently the cross-parity reflection leak with `c ≠ 1` **certifies
the sum-zero antipodal structure** — it carries no information about the nonzero-sum genuine
defects, and therefore cannot be turned into a count of them below the additive-energy wall.

**Verdict (honesty contract).** This is a `walled` result: the leak reduces to / re-expresses the
char-`p` additive-energy excess `E₂^{(p)} − E₂^{(0)}` (wall **W2**, the √n additive-energy loss),
and in the fully-split `N(𝔭)=p` case the count of short genuine defects is the **Pan–Xu ideal-SVP
open gap**. The reflection-engine lemma below is the *clean true* part: it proves the leak's
100 %-reflection feature is purely the antipodal char-0 symmetry. NO bound on the genuine defect
count is claimed.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.ProximityGap.WF407.T09Leak

/-! ## §1  The reflection engine: a sum-preserving dilation by `c ≠ 1` forces the sum to be `0`. -/

/-- **The cross-parity reflection engine (two-term form).** In any integral domain `F`, if a
multiplicative dilation by `c` carries the pair sum `y₁ + y₂` to the pair sum `x₁ + x₂` while
preserving the value (`x₁ + x₂ = y₁ + y₂`), and the two summed pairs are related by the dilation
(`x₁ + x₂ = c·(y₁ + y₂)`), then either `c = 1` or the common sum `y₁ + y₂` is `0`.

This is the algebraic heart of the measured "100 % of `E₂` collisions are a `c = −g` reflection":
a genuine (nonzero-sum) collision cannot be a nontrivial dilation, so the reflection leak with
`c ≠ 1` is exactly the antipodal `y₁ + y₂ = 0` (Lam–Leung char-0) structure. -/
theorem sum_preserving_dilation_forces_zero {F : Type*} [CommRing F] [IsDomain F]
    (c x₁ x₂ y₁ y₂ : F)
    (hpres : x₁ + x₂ = y₁ + y₂)
    (hdil : x₁ + x₂ = c * (y₁ + y₂)) :
    c = 1 ∨ y₁ + y₂ = 0 := by
  -- `s = c·s` ⟹ `(c − 1)·s = 0` ⟹ `c = 1 ∨ s = 0`.
  have hcs : c * (y₁ + y₂) = y₁ + y₂ := by rw [← hdil, hpres]
  have hs : (c - 1) * (y₁ + y₂) = 0 := by
    rw [sub_mul, one_mul, hcs, sub_self]
  rcases mul_eq_zero.mp hs with hc | hzero
  · left; exact sub_eq_zero.mp hc
  · right; exact hzero

/-- **General-`k` reflection engine.** The same one-line argument for a `k`-term sum: if a sum
over a finite index set is preserved and is the `c`-dilation of another preserved sum, then
`c = 1` or the sum is `0`. (`E_r` collisions are `r`-term sums; the leak at every depth `r`
collapses to the antipodal structure for `c ≠ 1`.) -/
theorem sum_preserving_dilation_forces_zero_sum {F : Type*} [CommRing F] [IsDomain F]
    {ι : Type*} (s : F) (c : F) (f g : ι → F) (A B : Finset ι)
    (hA : ∑ i ∈ A, f i = s) (hB : ∑ i ∈ B, g i = s)
    (hdil : s = c * s) :
    c = 1 ∨ s = 0 := by
  have hs : (c - 1) * s = 0 := by
    rw [sub_mul, one_mul, ← hdil, sub_self]
  rcases mul_eq_zero.mp hs with hc | hzero
  · left; exact sub_eq_zero.mp hc
  · right; exact hzero

/-! ## §2  The leak as a named *open* obligation (the part that is NOT proven). -/

/-- **The cross-parity leak count (named OPEN obligation).** The genuine (nonzero-sum) spurious
`E₂` defect count of `μ_n ⊆ F_q^×` is, by definition, the char-`p` additive-energy excess
`E₂^{(p)} − E₂^{(0)}`. The thread's hope — "turn the leak into a bound" — is the statement that
this excess is `O(n)` (so that the worst Gauss period stays at the floor). We record it as an
explicit `Prop`; it is the **W2 additive-energy wall** and, in the fully-split `N(𝔭)=p` case, the
**Pan–Xu ideal-SVP open gap**. It is *not* proven here; the reflection engine of §1 shows the
leak's structure cannot supply it (the leak is the antipodal char-0 part, disjoint from the
genuine excess). -/
def CrossParityLeakBound (energyExcess linearBudget : ℕ) : Prop :=
  energyExcess ≤ linearBudget

/-- The reflection engine specialized to the leak hypothesis, packaged: for any genuine `E₂`
collision that is *claimed* to be a `c ≠ 1` reflection, the common sum is forced to `0` — i.e.
the collision is antipodal (char-0), contradicting genuineness. Formally: a nonzero-sum collision
admits no nontrivial sum-preserving dilation. -/
theorem genuine_collision_not_reflection {F : Type*} [CommRing F] [IsDomain F]
    (c x₁ x₂ y₁ y₂ : F)
    (hpres : x₁ + x₂ = y₁ + y₂)
    (hsum_ne : y₁ + y₂ ≠ 0)
    (hdil : x₁ + x₂ = c * (y₁ + y₂)) :
    c = 1 := by
  rcases sum_preserving_dilation_forces_zero c x₁ x₂ y₁ y₂ hpres hdil with h | h
  · exact h
  · exact absurd h hsum_ne

end ArkLib.ProximityGap.WF407.T09Leak

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.WF407.T09Leak
#print axioms sum_preserving_dilation_forces_zero
#print axioms sum_preserving_dilation_forces_zero_sum
#print axioms genuine_collision_not_reflection
end AxiomAudit
