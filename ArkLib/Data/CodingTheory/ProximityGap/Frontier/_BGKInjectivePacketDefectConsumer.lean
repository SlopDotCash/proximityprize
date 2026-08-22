/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Signed packet consumers for the depth-seven injective defect

After the repeated-coordinate sector is absorbed, the production depth-seven ledger leaves the
single centered injective target

`q * W_inj - N_inj <= 126871 * q * n^7`.

A positive completion-multiplicity estimate cannot see the subtraction by the injective source
mass `N_inj`.  This file gives a dependency-free interface that retains it.  A canonical primitive
leaf partitions the wraparound configurations into completion fibers; arbitrary nonnegative DC
credits of total mass `N_inj` then give the exact identity

`sum_leaf (q * completionMultiplicity leaf - credit leaf) = q * W_inj - N_inj`.

The main consumer permits a **signed coboundary transfer** between leaves.  Thus a difficult leaf
may borrow budget from its paired/projective neighbor through a potential `P`; the terms
`P(d) - P(sigma d)` telescope exactly.  It is enough to prove the pointwise leaf inequality

`q * mult(d) - credit(d) <= boundary(d) + P(d) - P(sigma d)`

with total boundary at most `126871*q*n^7`.

This socket is useful only when `P` is constrained by packet geometry.  With an arbitrary
potential it is not new cancellation: on each permutation cycle its existence is equivalent to
the corresponding cycle-sum bound.  The two-leaf equivalence below formalizes the smallest
nontrivial case and prevents the coboundary notation from disguising the original global target.

Two diagnostics delimit this route.  Conjugating a complex phase, or multiplying it by a unit
phase, preserves squared energy, so the obvious phase pairing replicates rather than cancels the
Fourier energy.  An inverse lemma says that failure of any proposed leaf envelope forces a
specific heavy leaf.  The analytic leaf inequality itself remains open.

The companion exact census `probe_g153_packet_completion.py` found canonical completion fibers of
size `7242` at `(n,p)=(16,97)` and `486` at `(16,193)`, and as many as `44` primitive leaves in one
configuration.  Hence neither a tiny uniform fiber cap nor bounded leaf multiplicity is a valid
general mechanism.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1024

open Finset BigOperators
open scoped ComplexConjugate

namespace ArkLib.ProximityGap.Frontier.BGKInjectivePacketDefectConsumer

/-! ## Canonical completion fibers and exact DC centering -/

variable {Packet Config : Type*} [DecidableEq Packet] [DecidableEq Config]

/-- Number of configurations assigned to one canonical primitive packet/leaf. -/
def completionMultiplicity (configs : Finset Config) (owner : Config -> Packet)
    (d : Packet) : Nat :=
  (configs.filter fun c => owner c = d).card

/-- Canonical leaves partition the configuration set exactly. -/
theorem sum_completionMultiplicity_eq_card (configs : Finset Config)
    (packets : Finset Packet) (owner : Config -> Packet)
    (howner : ∀ c ∈ configs, owner c ∈ packets) :
    (∑ d ∈ packets, completionMultiplicity configs owner d) = configs.card := by
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := configs) (t := packets) (f := owner) howner
  simpa [completionMultiplicity] using hpart.symm

/-- Total DC source mass allocated to primitive leaves. -/
def totalCredit (packets : Finset Packet) (credit : Packet -> Nat) : Nat :=
  ∑ d ∈ packets, credit d

/-- Local signed completion defect after assigning a share of the injective DC source. -/
def centeredPacketDefect (configs : Finset Config) (owner : Config -> Packet)
    (q : Nat) (credit : Packet -> Nat) (d : Packet) : Int :=
  ((q * completionMultiplicity configs owner d : Nat) : Int) - (credit d : Int)

/-- **Exact signed completion identity.**  No positivity or completion cap is used. -/
theorem sum_centeredPacketDefect_eq (configs : Finset Config)
    (packets : Finset Packet) (owner : Config -> Packet)
    (howner : ∀ c ∈ configs, owner c ∈ packets)
    (q : Nat) (credit : Packet -> Nat) :
    (∑ d ∈ packets, centeredPacketDefect configs owner q credit d) =
      ((q * configs.card : Nat) : Int) - (totalCredit packets credit : Int) := by
  unfold centeredPacketDefect totalCredit
  rw [Finset.sum_sub_distrib]
  simp only [Nat.cast_mul, Nat.cast_sum]
  have hsum :
      (∑ d ∈ packets, (completionMultiplicity configs owner d : Int)) =
        (configs.card : Int) := by
    exact_mod_cast sum_completionMultiplicity_eq_card configs packets owner howner
  rw [<- Finset.mul_sum, hsum]

/-- The production injective coefficient left after the repeated-sector allocation `138`. -/
def injectiveCoefficient : Nat := 126871

/-- The exact unnormalized production-scale injective allowance. -/
def injectiveAllowance (q n : Nat) : Int :=
  (injectiveCoefficient : Int) * ((q * n ^ 7 : Nat) : Int)

/-- **Direct leaf consumer.**  Local signed defects and local slack sum to the exact remaining
injective allowance.  This is the lossless replacement for a positive completion cap. -/
theorem injective_defect_le_of_leaf_slack
    (configs : Finset Config) (packets : Finset Packet) (owner : Config -> Packet)
    (howner : ∀ c ∈ configs, owner c ∈ packets)
    (q n source : Nat) (credit : Packet -> Nat) (slack : Packet -> Int)
    (hcredit : totalCredit packets credit = source)
    (hlocal : ∀ d ∈ packets,
      centeredPacketDefect configs owner q credit d <= slack d)
    (hslack : (∑ d ∈ packets, slack d) <= injectiveAllowance q n) :
    ((q * configs.card : Nat) : Int) - (source : Int) <= injectiveAllowance q n := by
  have hsum :
      (∑ d ∈ packets, centeredPacketDefect configs owner q credit d) <=
        ∑ d ∈ packets, slack d :=
    Finset.sum_le_sum fun d hd => hlocal d hd
  rw [sum_centeredPacketDefect_eq configs packets owner howner, hcredit] at hsum
  exact hsum.trans hslack

/-! ## Subattack 1: signed completion telescoping -/

/-- A coboundary over a finite permutation has total mass zero. -/
theorem sum_coboundary_eq_zero {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    (sigma : Equiv.Perm Leaf) (potential : Leaf -> Int) :
    ∑ d, (potential d - potential (sigma d)) = 0 := by
  rw [Finset.sum_sub_distrib, Equiv.sum_comp sigma potential]
  simp

/-- **Signed telescoping packet/leaf hypothesis.**  Completion fibers may be very nonuniform.
It is enough that their centered defects have a pointwise majorant by a small boundary term plus
a coboundary transfer along a leaf permutation.  The transfer cancels exactly in the global sum. -/
theorem injective_defect_le_of_leaf_coboundary
    {Leaf Config : Type*} [Fintype Leaf] [DecidableEq Leaf] [DecidableEq Config]
    (configs : Finset Config) (owner : Config -> Leaf)
    (q n source : Nat) (credit : Leaf -> Nat)
    (boundary potential : Leaf -> Int) (sigma : Equiv.Perm Leaf)
    (hcredit : totalCredit (Finset.univ : Finset Leaf) credit = source)
    (hleaf : forall d : Leaf,
      centeredPacketDefect configs owner q credit d <=
        boundary d + potential d - potential (sigma d))
    (hboundary : (∑ d, boundary d) <= injectiveAllowance q n) :
    ((q * configs.card : Nat) : Int) - (source : Int) <= injectiveAllowance q n := by
  apply injective_defect_le_of_leaf_slack configs Finset.univ owner
      (fun c _ => Finset.mem_univ (owner c)) q n source credit
      (fun d => boundary d + potential d - potential (sigma d)) hcredit
  · intro d _
    exact hleaf d
  · rw [show (∑ d, (boundary d + potential d - potential (sigma d))) =
        (∑ d, boundary d) + ∑ d, (potential d - potential (sigma d)) by
      simp only [sub_eq_add_neg, Finset.sum_add_distrib]
      abel]
    rw [sum_coboundary_eq_zero]
    simpa using hboundary

/-- **Coboundary honesty check on one two-cycle.**  If the potential is completely arbitrary,
the two local transfer inequalities exist exactly when the original two-leaf sum inequality is
already true.  For a general permutation the analogous statement holds cycle by cycle.  Any
analytic use of the preceding consumer must therefore construct a constrained, local, or
projectively natural potential rather than choose one after seeing the full defect. -/
theorem two_leaf_coboundary_exists_iff_global_bound
    (d0 d1 b0 b1 : Int) :
    d0 + d1 <= b0 + b1 ↔
      ∃ p0 p1 : Int,
        d0 <= b0 + p0 - p1 ∧ d1 <= b1 + p1 - p0 := by
  constructor
  · intro h
    refine ⟨d0 - b0, 0, ?_, ?_⟩ <;> linarith
  · rintro ⟨p0, p1, h0, h1⟩
    linarith

/-! ## Subattack 2: phase pairing and its squared-energy obstruction -/

/-- Pairwise cancellation along an involution is sufficient before taking absolute squares. -/
theorem sum_le_of_involution_pair_bound {Leaf : Type*} [Fintype Leaf]
    [DecidableEq Leaf]
    (sigma : Equiv.Perm Leaf) (_hinvolution : forall d, sigma (sigma d) = d)
    (defect boundary : Leaf -> Int)
    (hpair : forall d, defect d + defect (sigma d) <=
      boundary d + boundary (sigma d)) :
    (∑ d, defect d) <= ∑ d, boundary d := by
  have hsum := Finset.sum_le_sum fun d (_hd : d ∈ (Finset.univ : Finset Leaf)) => hpair d
  simp only [Finset.sum_add_distrib] at hsum
  rw [Equiv.sum_comp sigma defect, Equiv.sum_comp sigma boundary] at hsum
  linarith

/-- Conjugate phases do not cancel after passing to squared energy. -/
theorem conjugate_pair_energy_no_cancellation (z : Complex) :
    Complex.normSq z + Complex.normSq (star z) = 2 * Complex.normSq z := by
  change Complex.normSq z + Complex.normSq (conj z) = 2 * Complex.normSq z
  rw [Complex.normSq_conj]
  ring

/-- Multiplication by a unit phase preserves squared energy.  Thus a projective orbit on which the
transform changes only by unit phases merely repeats the same nonnegative contribution. -/
theorem unit_phase_energy_invariant (u z : Complex) (hu : Complex.normSq u = 1) :
    Complex.normSq (u * z) = Complex.normSq z := by
  rw [Complex.normSq_mul, hu, one_mul]

/-- An invariant projective orbit contributes its cardinality times one energy; there is no
within-orbit signed saving left after squaring. -/
theorem sum_invariant_energy_eq_card_mul {Freq : Type*} [DecidableEq Freq]
    (orbit : Finset Freq) (energy : Freq -> Real) (base : Freq)
    (hinvariant : ∀ b ∈ orbit, energy b = energy base) :
    (∑ b ∈ orbit, energy b) = orbit.card * energy base := by
  calc
    (∑ b ∈ orbit, energy b) = ∑ _b ∈ orbit, energy base :=
      Finset.sum_congr rfl fun b hb => hinvariant b hb
    _ = orbit.card * energy base := by simp

/-! ## Subattack 3: inverse/heavy-leaf diagnostics -/

/-- If a proposed uniform leaf envelope is too small globally, a specific leaf violates it. -/
theorem exists_heavy_leaf_of_sum_gt_card_mul {Leaf : Type*} [DecidableEq Leaf]
    (leaves : Finset Leaf) (defect : Leaf -> Int) (cap : Int)
    (hfail : (leaves.card : Int) * cap < ∑ d ∈ leaves, defect d) :
    ∃ d ∈ leaves, cap < defect d := by
  by_contra h
  push Not at h
  have hsum : (∑ d ∈ leaves, defect d) <= ∑ _d ∈ leaves, cap :=
    Finset.sum_le_sum fun d hd => h d hd
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  linarith

/-- Coboundary inverse theorem: if the global boundary is exceeded, some primitive leaf violates
the signed local transfer inequality. -/
theorem exists_leaf_violating_coboundary_of_sum_gt
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    (sigma : Equiv.Perm Leaf) (defect boundary potential : Leaf -> Int)
    (hfail : (∑ d, boundary d) < ∑ d, defect d) :
    ∃ d : Leaf,
      boundary d + potential d - potential (sigma d) < defect d := by
  by_contra h
  push Not at h
  have hsum := Finset.sum_le_sum
    (fun d (_hd : d ∈ (Finset.univ : Finset Leaf)) => h d)
  have hzero := sum_coboundary_eq_zero sigma potential
  simp only [sub_eq_add_neg, Finset.sum_add_distrib] at hsum hzero
  linarith

/-! ## Exact production magnitude -/

def productionN : Nat := 2 ^ 30

def productionQ : Nat := productionN * (2 ^ 128 + 192) + 1

def productionInjectiveAllowance : Nat :=
  productionQ * injectiveCoefficient * productionN ^ 7

/-- The remaining injective allowance has bit length `385`. -/
theorem production_injectiveAllowance_bitBounds :
    2 ^ 384 <= productionInjectiveAllowance ∧
      productionInjectiveAllowance < 2 ^ 385 := by
  norm_num [productionInjectiveAllowance, productionQ, productionN, injectiveCoefficient]

/-- Exact production all-injective source, written without any dependency on the remote G155
falling-factorial chain. -/
def productionInjectiveSource : Nat :=
  (productionN * (productionN - 1) * (productionN - 2) * (productionN - 3) *
    (productionN - 4) * (productionN - 5) * (productionN - 6)) ^ 2

/-- Relative scale diagnostic: the allowed centered injective defect is between `2^-36` and
`2^-35` of the raw all-injective source.  A positive-cardinality proof therefore misses by more
than thirty-five bits even before completion-fiber losses. -/
theorem production_injectiveSource_to_allowance :
    2 ^ 35 * productionInjectiveAllowance < productionInjectiveSource ∧
      productionInjectiveSource < 2 ^ 36 * productionInjectiveAllowance := by
  norm_num [productionInjectiveAllowance, productionInjectiveSource, productionQ, productionN,
    injectiveCoefficient]

/-- The ordered-to-subset symmetry factor in the depth-seven injective sector. -/
theorem depthSeven_order_factor : Nat.factorial 7 ^ 2 = 25401600 := by
  norm_num [Nat.factorial]

#print axioms sum_completionMultiplicity_eq_card
#print axioms sum_centeredPacketDefect_eq
#print axioms injective_defect_le_of_leaf_slack
#print axioms sum_coboundary_eq_zero
#print axioms injective_defect_le_of_leaf_coboundary
#print axioms two_leaf_coboundary_exists_iff_global_bound
#print axioms sum_le_of_involution_pair_bound
#print axioms conjugate_pair_energy_no_cancellation
#print axioms unit_phase_energy_invariant
#print axioms sum_invariant_energy_eq_card_mul
#print axioms exists_heavy_leaf_of_sum_gt_card_mul
#print axioms exists_leaf_violating_coboundary_of_sum_gt
#print axioms production_injectiveAllowance_bitBounds
#print axioms production_injectiveSource_to_allowance

end ArkLib.ProximityGap.Frontier.BGKInjectivePacketDefectConsumer
