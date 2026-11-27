/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-!
# Projective minor covers of an eighth-rate quartet

Local four-face charges bound the common homogeneous degree of the minors. A syzygy
degree inequality constrains any rational right factor of their projective map.
The independent-component estimates in the accompanying note use Corvaja–Zannier's
Theorem 2 and Proposition 2. This file verifies the counting, integer descent, and
the finite list of remaining large degrees.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.EighthQuartetMinorCovers

open Finset

/-- Minimum aggregate order of the four triangle determinants at a site with `w` owners. -/
def faceMinimum (w : ℕ) : ℕ := if w = 4 then 8 else if w = 3 then 5 else if w = 2 then 2 else 0

/-- The minimum face order spends additional degree beyond twice the excess owner count. -/
theorem local_common_order {w g total : ℕ} (hw : w ≤ 4) (hface : faceMinimum w ≤ total)
    (hcommon : 4 * g ≤ total) : g + 2 * (w - 1) ≤ total := by
  interval_cases w <;> simp [faceMinimum] at hface <;> omega

/-- Summing the local excesses also controls common homogeneous zeros off the physical domain. -/
theorem common_degree {ι : Type*} (S : Finset ι) (g excess total : ι → ℕ) {d s : ℕ}
    (hlocal : ∀ x ∈ S, g x + 2 * excess x ≤ total x)
    (hface : ∑ x ∈ S, total x ≤ 8 * d) (hinc : 4 * d ≤ (∑ x ∈ S, excess x) + s) :
    ∑ x ∈ S, g x ≤ 2 * s := by
  have h := sum_le_sum hlocal
  rw [sum_add_distrib, ← mul_sum] at h
  omega

/-- The number of sites owned by exactly two heads differs from `4*d` by at most the indicated
one-sided allowance. -/
theorem double_sites {d s x₀ x₂ x₃ x₄ : ℕ}
    (hinc : x₂ + 2*x₃ + 3*x₄ + s = 4*d + x₀)
    (htri : 2*x₀ + x₃ + 2*x₄ ≤ 2*s) : 4*d ≤ x₂ + 5*s := by omega

/-- Removing rank-drop sites leaves nearly full fibers. The common degree cancels from the
lower bound on protected ordered sheet pairs per component valency. -/
theorem protected_slots {d s h x₂ e cap : ℕ}
    (hd : 4*d ≤ x₂ + 5*s) (he : x₂ ≤ e + h) (hc : cap + 2*h ≤ 4*d) :
    cap + h ≤ e + 5*s ∧ 4*d + cap ≤ 2*e + 10*s := by omega

/-- A degree-`q` pullback of a plane map of degree `m`. The degree of any nonzero row syzygy
upstairs is at least `d-h`, in particular for one pulled up from degree `m/2` downstairs. -/
theorem cover_remainder {q m d h : ℕ} (hdegree : q*m + h = 2*d)
    (hsyz : d ≤ q*(m/2) + h) : 2 * (d % q) ≤ h := by
  let k := m - m/2
  have hkadd : k + m/2 = m := by dsimp [k]; omega
  have htwok : m ≤ 2*k := by dsimp [k]; omega
  have hparts : q*k + q*(m/2) = q*m := by rw [← Nat.mul_add, hkadd]
  have hkd : q*k ≤ d := by omega
  have hadd : d - q*k + k*q = d := by rw [Nat.mul_comm k q]; omega
  have hrem : d%q = (d-q*k)%q := by
    conv_lhs => rw [← hadd]
    simp
  have hle := Nat.mod_le (d-q*k) q
  have htwo : q*m ≤ 2 * (q*k) := by
    calc q*m ≤ q*(2*k) := Nat.mul_le_mul_left q htwok
         _ = _ := by ring
  omega

/-- A large right factor forces even outer degree and the exact homogeneous common degree. -/
theorem balanced_large_cover {q m d h : ℕ} (hdegree : q*m + h = 2*d)
    (hsyz : d ≤ q*(m/2) + h) (hlarge : h < q) :
    m % 2 = 0 ∧ h = 2 * (d % q) := by
  have hp : m = 2*(m/2) + m%2 := by omega
  have hsplit : q*m = 2*(q*(m/2)) + q*(m%2) := by
    calc q*m = q*(2*(m/2)+m%2) := congrArg (q * ·) hp
         _ = _ := by ring
  have heven : m%2 = 0 := by
    by_contra h
    have hone : m%2 = 1 := by omega
    rw [hone, Nat.mul_one] at hsplit
    omega
  rw [heven, Nat.mul_zero, Nat.add_zero] at hsplit
  have hd : d = h/2 + (m/2)*q := by rw [Nat.mul_comm (m/2) q]; omega
  have hc : (h/2)%q = h/2 := Nat.mod_eq_of_lt (by omega)
  have hrem : d%q = h/2 := by rw [hd]; simpa using hc
  exact ⟨heven, by omega⟩

private abbrev n : ℕ := 1073741824
private abbrev d : ℕ := 134217727

/-- The named-field characteristic guards and the separation from all nontoric Möbius graphs. -/
theorem field_guards : 12*n^2*(2*d)^2 < n*(2^129+13)+1 ∧
    18*n*(2*d) < n*(2^129+13)+1 ∧ 3143679 < 4*d-40 := by decide

/-- The two geometric component estimates force these valency floors at the worst allowed slack. -/
theorem correspondence_floors {r P : ℕ} (hp : 536870868 ≤ P)
    (hcubic : P^3 ≤ 108*n^2*r) (hlinear : 74*P ≤ 26*n + 74*73*r) :
    1242757 ≤ r ∧ 2186442 ≤ r := by
  have hpow : (536870868:ℕ)^3 ≤ P^3 := Nat.pow_le_pow_left hp 3
  norm_num [n] at hcubic hlinear hpow
  omega

/-- The half outer degree fits in sixty-one for a nontoric cover. -/
theorem short_outer {q t a : ℕ} (hq : 2186443 ≤ q) (hdiv : q*t + a = d) :
    t ≤ 61 := by
  by_contra! h
  have hh := Nat.mul_le_mul hq h
  norm_num [d] at hdiv hh
  omega

/-- Complete list of possible large right degrees for one residue. The auxiliary loop uses
the half outer degree, in decreasing order for ascending right degrees. -/
def largeRow (a : ℕ) : List ℕ :=
  ((List.range 62).reverse.filter fun t => 0 < t ∧ (d-a)%t = 0 ∧ 2186443 ≤ (d-a)/t).map
    fun t => (d-a)/t

/-- Every possible large degree is represented by its half outer degree in the finite list. -/
theorem mem_largeRow {q t a : ℕ} (hq : 2186443 ≤ q) (ht : 0 < t) (hdiv : q*t+a=d) :
    q ∈ largeRow a := by
  have hshort := short_outer hq hdiv
  have heq : d-a = q*t := by omega
  have hquot : (d-a)/t = q := by rw [heq, Nat.mul_div_cancel _ ht]
  apply List.mem_map.mpr
  refine ⟨t, ?_, hquot⟩
  simp [heq, hquot, Nat.mul_div_cancel _ ht, ht, hq, show t < 62 by omega]

/-- Enumerating physical-degree residues 1 through 4 leaves fourteen possible large degrees. -/
theorem large_rows :
    largeRow 1 = [22369621,44739242,67108863,134217726] ∧
    largeRow 2 = [5368709,26843545,134217725] ∧
    largeRow 3 = [4329604,33554431,67108862,134217724] ∧
    largeRow 4 = [3273603,44739241,134217723] := by decide +kernel

#print axioms common_degree
#print axioms cover_remainder
#print axioms balanced_large_cover
#print axioms correspondence_floors
#print axioms mem_largeRow
#print axioms large_rows

end ArkLib.ProximityGap.Frontier.EighthQuartetMinorCovers
