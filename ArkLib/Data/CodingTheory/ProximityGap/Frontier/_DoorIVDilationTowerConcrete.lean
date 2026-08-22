/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDilationTowerSaturates

/-!
# Door-(iv) Lane-3: the CONCRETE dilation tower on `worstPeriod` (#444)

`_DoorIVDilationDescentRecursion` proved the single step
`worstPeriod ψ (H ∪ g·H) ≤ 2 · worstPeriod ψ H`, and `_DoorIVDilationTowerSaturates` proved the
ABSTRACT iteration `M a ≤ 2^a · M 0` for any sequence with `M (k+1) ≤ 2 · M k`.  This file BRIDGES the
two: instantiating the abstract iteration on the ACTUAL prize object `worstPeriod` along a user-supplied
descending dyadic chain of subgroups, so the prose "iterate the recursion down the tower" is realized on
the concrete `worstPeriod` sequence, not just an abstract `M : ℕ → ℝ`.

Given a descending chain `G : ℕ → Finset F` where each level is the index-2 dilate of the next
(`G k = G (k+1) ∪ (coset rep g k) · G (k+1)`, with `g k ≠ 0` and the two halves disjoint), the
single-step recursion gives `M (G k) ≤ 2 · M (G (k+1))` at every level, hence by the abstract tower
`M (G 0) ≤ 2^a · M (G a)`.

This is the honest concrete form of the saving-free dyadic descent: bounding the worst period of the top
subgroup `G 0` by iterating the trivial factor-`2` recursion down `a` levels gives only `2^a · M (G a)`,
which (with the base `G a` of `O(1)` worst period) is the trivial `M ≤ n` ceiling — no √-saving, on the
real object.  Pure Lane-3 constraint lock; no CORE / cancellation / completion / moment /
anti-concentration / capacity claim.  CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.I031DilationOrbitReduction (nonzeroFreqs mem_nonzeroFreqs)
open ProximityGap.Frontier.ConcreteMomentAssembly (worstPeriod worstPeriod_nonneg)
open ArkLib.ProximityGap.Frontier.DoorIVDilationDescentRecursion

namespace ArkLib.ProximityGap.Frontier.DoorIVDilationTowerConcrete

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The concrete per-level descent on `worstPeriod`, packaged for a descending dyadic chain.  If level
`k` of the chain is the index-2 dilate of level `k+1` (`G k = G (k+1) ∪ (g k)·G (k+1)`, `g k ≠ 0`,
halves disjoint), then `M (G k) ≤ 2 · M (G (k+1))` for every `k`. -/
theorem worstPeriodChain_step {ψ : AddChar F ℂ} (hne : (nonzeroFreqs F).Nonempty)
    (G : ℕ → Finset F) (g : ℕ → F) (hg : ∀ k, g k ≠ 0)
    (hdisj : ∀ k, Disjoint (G (k + 1)) ((G (k + 1)).image (fun y => g k * y)))
    (hchain : ∀ k, G k = G (k + 1) ∪ (G (k + 1)).image (fun y => g k * y)) :
    ∀ k, worstPeriod ψ (G k) hne ≤ 2 * worstPeriod ψ (G (k + 1)) hne := by
  intro k
  have hstep := worstPeriod_union_le_two_mul_worstPeriod (ψ := ψ)
    (G (k + 1)) hne (hg k) (hdisj k)
  rw [hchain k]
  exact hstep

/-- **★ The concrete dilation tower on `worstPeriod`.**  Iterating the single dilation step down a
descending dyadic chain of `a` levels bounds the top worst period by `2^a` times the bottom:
`M (G 0) ≤ 2^a · M (G a)`.  This realizes the prose "iterate the recursion `log₂ n` times" on the actual
prize object. -/
theorem worstPeriodChain_le_two_pow {ψ : AddChar F ℂ} (hne : (nonzeroFreqs F).Nonempty)
    (G : ℕ → Finset F) (g : ℕ → F) (hg : ∀ k, g k ≠ 0)
    (hdisj : ∀ k, Disjoint (G (k + 1)) ((G (k + 1)).image (fun y => g k * y)))
    (hchain : ∀ k, G k = G (k + 1) ∪ (G (k + 1)).image (fun y => g k * y)) :
    ∀ a, worstPeriod ψ (G 0) hne ≤ 2 ^ a * worstPeriod ψ (G a) hne := by
  -- run the abstract tower on M k := worstPeriod ψ (G k) hne, but the abstract lemma is stated against
  -- M 0; here M a is the BOTTOM, so we apply the abstract descent on the truncated suffix sequence.
  have hstep := worstPeriodChain_step (ψ := ψ) hne G g hg hdisj hchain
  intro a
  induction a with
  | zero => simp
  | succ n ih =>
    calc worstPeriod ψ (G 0) hne
        ≤ 2 ^ n * worstPeriod ψ (G n) hne := ih
      _ ≤ 2 ^ n * (2 * worstPeriod ψ (G (n + 1)) hne) := by
            apply mul_le_mul_of_nonneg_left (hstep n)
            positivity
      _ = 2 ^ (n + 1) * worstPeriod ψ (G (n + 1)) hne := by ring

/-- **Concrete saturation of the trivial ceiling.**  If in addition the bottom subgroup `G a` of the
chain has worst period `≤ 1` (e.g. a singleton tail), the concrete tower bound is `M (G 0) ≤ 2^a`, the
trivial ceiling reproduced with NO √-saving on the real object. -/
theorem worstPeriodChain_saturates_trivial {ψ : AddChar F ℂ} (hne : (nonzeroFreqs F).Nonempty)
    (G : ℕ → Finset F) (g : ℕ → F) (hg : ∀ k, g k ≠ 0)
    (hdisj : ∀ k, Disjoint (G (k + 1)) ((G (k + 1)).image (fun y => g k * y)))
    (hchain : ∀ k, G k = G (k + 1) ∪ (G (k + 1)).image (fun y => g k * y))
    {a : ℕ} (hbase : worstPeriod ψ (G a) hne ≤ 1) :
    worstPeriod ψ (G 0) hne ≤ 2 ^ a := by
  have h := worstPeriodChain_le_two_pow (ψ := ψ) hne G g hg hdisj hchain a
  have hpow : (0 : ℝ) ≤ 2 ^ a := by positivity
  calc worstPeriod ψ (G 0) hne ≤ 2 ^ a * worstPeriod ψ (G a) hne := h
    _ ≤ 2 ^ a * 1 := by exact mul_le_mul_of_nonneg_left hbase hpow
    _ = 2 ^ a := by ring

end ArkLib.ProximityGap.Frontier.DoorIVDilationTowerConcrete
