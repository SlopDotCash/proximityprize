/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCorePacking

/-!
# Four-cluster capacity at the lattice predecessor

After the integral five-core barrier, a saturated primitive cluster has at
most four source lines.  At the lattice point immediately below the amplified
counterexample, every event needs two fresh coordinates beyond a saturated
source core.  Fresh petals belonging to distinct scalars on one source line
are disjoint.

The abstract line-core packing inequality closes the count in two ways.  The
original saturated argument uses

```text
2 |Gamma_i| + |D_i| <= n,
```

and every saturated core has size at least `n/2`.  Summing gives
`sum_i |Gamma_i| <= n`.

At the concrete P1 predecessor, saturation is not needed.  If a core leaves
two coordinates before the agreement threshold, the exact packing law gives

```text
2 |Gamma_i| <= n - t + 2.
```

The P1 arithmetic satisfies `2 * (n - t + 2) <= n`, so four such clusters
again carry at most `n` labels, with no lower bound on their core sizes.

This file isolates that final counting step.  The remaining global lower-bound
work is structural: extract at most four such source clusters from an
arbitrary bad stack and verify only the two-fresh cutoff on their common cores.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.RateQuarterPredecessorFourClusterCapacity

open HalfPredecessorLineCorePacking

attribute [local instance] Classical.propDecidable

variable {U Gamma : Type} [Fintype U] [DecidableEq U]

/-- A single line-core packing inequality with a two-fresh gap gives the
uniform bound `2L <= n-t+2`.  Unlike the coarser `2L+z <= n` consequence,
this retains the full factor `t-z` and therefore needs no lower bound on the
core size `z`. -/
theorem two_mul_label_card_le_complement_add_two
    {n t z L : Nat} (ht : t ≤ n) (htwoFresh : z + 2 ≤ t)
    (hpacking : L * max 1 (t - z) + z ≤ n) :
    2 * L ≤ n - t + 2 := by
  by_cases hL : L = 0
  · simp only [hL, mul_zero, zero_le]
  have hLpos : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr hL
  have hz : z ≤ t := by omega
  have hgap : 2 ≤ t - z := by omega
  have hmax : max 1 (t - z) = t - z := max_eq_right (by omega)
  rw [hmax] at hpacking
  have htz : t - z + z = t := Nat.sub_add_cancel hz
  have hrewrite :
      (L - 1) * (t - z) + t = L * (t - z) + z := by
    have hLdecomp : L - 1 + 1 = L := Nat.sub_add_cancel hLpos
    calc
      (L - 1) * (t - z) + t =
          (L - 1) * (t - z) + (t - z + z) := by rw [htz]
      _ =
          (L - 1 + 1) * (t - z) + z := by ring
      _ = L * (t - z) + z := by rw [hLdecomp]
  have hrest : (L - 1) * (t - z) ≤ n - t := by
    have : (L - 1) * (t - z) + t ≤ n := by
      rw [hrewrite]
      exact hpacking
    omega
  have hmul : 2 * (L - 1) ≤ (L - 1) * (t - z) := by
    simpa [mul_comm] using Nat.mul_le_mul_left (L - 1) hgap
  omega

/-- Four polynomial-line clusters with two fresh coordinates per label carry
at most the universe size whenever the complement-to-threshold arithmetic has
the P1 shape.  No saturation or half-core lower bound is required. -/
theorem fourTwoFreshCluster_label_card_le_universe
    (G : Fin 4 → Finset Gamma)
    (A : Fin 4 → Gamma → Finset U)
    (D : Fin 4 → Finset U)
    (t : Nat)
    (ht : t ≤ Fintype.card U)
    (hroom : 2 * (Fintype.card U - t + 2) ≤ Fintype.card U)
    (hcore : ∀ i gamma, gamma ∈ G i → D i ⊆ A i gamma)
    (hdisj : ∀ i gamma, gamma ∈ G i → ∀ beta, beta ∈ G i →
      gamma ≠ beta → Disjoint (A i gamma \ D i) (A i beta \ D i))
    (hsize : ∀ i gamma, gamma ∈ G i → t ≤ (A i gamma).card)
    (htwoFresh : ∀ i, (D i).card + 2 ≤ t) :
    (∑ i : Fin 4, (G i).card) ≤ Fintype.card U := by
  have hpack : ∀ i : Fin 4,
      (G i).card * max 1 (t - (D i).card) + (D i).card ≤
        Fintype.card U := by
    intro i
    exact lineCore_packing (G i) (A i) (D i) t
      (fun gamma hgamma => hcore i gamma hgamma)
      (fun gamma hgamma beta hbeta hne =>
        hdisj i gamma hgamma beta hbeta hne)
      (fun gamma hgamma => hsize i gamma hgamma)
      (fun _gamma _hgamma hlarge => by
        have := htwoFresh i
        omega)
  have hcap : ∀ i : Fin 4,
      2 * (G i).card ≤ Fintype.card U - t + 2 := by
    intro i
    exact two_mul_label_card_le_complement_add_two ht
      (htwoFresh i) (hpack i)
  have h0 := hcap 0
  have h1 := hcap 1
  have h2 := hcap 2
  have h3 := hcap 3
  rw [Fin.sum_univ_four]
  omega

/-- Four half-universe cores, with two disjoint fresh coordinates required per
label inside each cluster, support at most `|U|` labels altogether. -/
theorem fourCluster_label_card_le_universe
    (G : Fin 4 → Finset Gamma)
    (A : Fin 4 → Gamma → Finset U)
    (D : Fin 4 → Finset U)
    (t : Nat)
    (hcore : ∀ i gamma, gamma ∈ G i → D i ⊆ A i gamma)
    (hdisj : ∀ i gamma, gamma ∈ G i → ∀ beta, beta ∈ G i →
      gamma ≠ beta → Disjoint (A i gamma \ D i) (A i beta \ D i))
    (hsize : ∀ i gamma, gamma ∈ G i → t ≤ (A i gamma).card)
    (htwoFresh : ∀ i, (D i).card + 2 ≤ t)
    (hhalf : ∀ i, Fintype.card U ≤ 2 * (D i).card) :
    (∑ i : Fin 4, (G i).card) ≤ Fintype.card U := by
  have hpack : ∀ i : Fin 4,
      2 * (G i).card + (D i).card ≤ Fintype.card U := by
    intro i
    have hline := lineCore_packing (G i) (A i) (D i) t
      (fun gamma hgamma => hcore i gamma hgamma)
      (fun gamma hgamma beta hbeta hne =>
        hdisj i gamma hgamma beta hbeta hne)
      (fun gamma hgamma => hsize i gamma hgamma)
      (fun _gamma _hgamma ht => by
        have := htwoFresh i
        omega)
    have htwo : 2 ≤ max 1 (t - (D i).card) := by
      have := htwoFresh i
      omega
    have hmul : 2 * (G i).card ≤
        (G i).card * max 1 (t - (D i).card) := by
      rw [mul_comm 2]
      exact Nat.mul_le_mul_left (G i).card htwo
    exact (Nat.add_le_add_right hmul (D i).card).trans hline
  have hp0 := hpack 0
  have hp1 := hpack 1
  have hp2 := hpack 2
  have hp3 := hpack 3
  have hh0 := hhalf 0
  have hh1 := hhalf 1
  have hh2 := hhalf 2
  have hh3 := hhalf 3
  rw [Fin.sum_univ_four]
  omega

/-- At the amplified endpoint `6z=53m-8`, a saturated core is larger than
half of the `16m`-point universe. -/
theorem saturated_core_ge_half
    {m z : Nat} (hm : 8 ≤ m) (hz : 6 * z = 53 * m - 8) :
    16 * m ≤ 2 * z := by
  have hm8 : 8 ≤ 53 * m := by omega
  have hz' : 6 * z + 8 = 53 * m := by omega
  omega

/-- Concrete-parameter wrapper: four saturated cores at `n=16m`, with two
fresh coordinates per event, carry at most `16m` labels. -/
theorem fourSaturatedCluster_label_card_le
    (G : Fin 4 → Finset Gamma)
    (A : Fin 4 → Gamma → Finset U)
    (D : Fin 4 → Finset U)
    (t m z : Nat)
    (hm : 8 ≤ m) (hU : Fintype.card U = 16 * m)
    (hz : 6 * z = 53 * m - 8)
    (hcoreCard : ∀ i, z ≤ (D i).card)
    (hcore : ∀ i gamma, gamma ∈ G i → D i ⊆ A i gamma)
    (hdisj : ∀ i gamma, gamma ∈ G i → ∀ beta, beta ∈ G i →
      gamma ≠ beta → Disjoint (A i gamma \ D i) (A i beta \ D i))
    (hsize : ∀ i gamma, gamma ∈ G i → t ≤ (A i gamma).card)
    (htwoFresh : ∀ i, (D i).card + 2 ≤ t) :
    (∑ i : Fin 4, (G i).card) ≤ 16 * m := by
  rw [← hU]
  apply fourCluster_label_card_le_universe G A D t hcore hdisj hsize htwoFresh
  intro i
  rw [hU]
  exact (saturated_core_ge_half hm hz).trans
    (Nat.mul_le_mul_left 2 (hcoreCard i))

end ArkLib.ProximityGap.Frontier.RateQuarterPredecessorFourClusterCapacity

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateQuarterPredecessorFourClusterCapacity
#print axioms fourCluster_label_card_le_universe
#print axioms two_mul_label_card_le_complement_add_two
#print axioms fourTwoFreshCluster_label_card_le_universe
#print axioms saturated_core_ge_half
#print axioms fourSaturatedCluster_label_card_le
