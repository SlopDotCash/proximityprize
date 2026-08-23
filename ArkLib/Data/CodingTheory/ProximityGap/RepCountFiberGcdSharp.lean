/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountFiberPolyBound
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupRepresentationRoots

/-!
# The fibre rep-count is bounded by the GCD degree -- sharpening O213 (#389 / #444)

`RepCountFiberPolyBound` (O213) handed the Garcia-Voloch rep count to the polynomial
machinery via the explicit shifted-power polynomial `P_c := (X+1)^n - C (c^n)`, giving
`r(c) <= (P_c.roots.toFinset).card <= P_c.natDegree = n`.  But that degree-`n` bound is
**wildly loose** in the thin prize regime: a fibre element `w` is a root of `P_c`
**and** of `X^n - 1` (it lies in `mu_n`), so it is a common root, hence a root of
`gcd(X^n - 1, P_c)`.  This file proves the sharper bound

> **`repCount_le_fiberGcd_natDegree`** : `r(c) <= deg gcd(X^n - 1, (X+1)^n - C (c^n))`,

the genuinely Stepanov-relevant object.  The probe
`scripts/probes/probe_fiber_gcd_maxr.py` confirms over the **full** `F_p*` (every `c`),
on thin 2-power `mu_n` at primes `p >> n^3`, `p == 1 mod n` (e.g. `p=12289,n=16`;
`p=40961,n=16`), that
`r(c) = deg gcd(X^n-1, (1+X)^n - c^n)` and `deg gcd < n` for **every** `c` (max `r(c)=2`
even at the worst case, vs the degree-`n` bound) -- so the gcd is the sharp target and
the O213 degree-`n` bound is far from tight.  This is the upper-bound direction (which
needs no separability/splitting), the analogue for the **O213 shifted-power fibre form**
`(X+1)^n - C(c^n)` of `SubgroupRepresentationRoots.representationCount_le_gcd_degree`
(which works the **different** polynomial `(C c - X)^n - 1` over the `c - z` form).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.  No Weil, no
Stepanov auxiliary; a clean structural sharpening composing the proven O213 fibre
identity with the common-root/gcd divisibility.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- A fibre element `ζ` (in `mu_n` with `(1 + ζ)^n = c^n`) is a root of **both**
`X^n - 1` and `shiftedPowPoly n c`, hence a root of their gcd:
`(X - C ζ) ∣ gcd (X^n - 1) (shiftedPowPoly n c)`. -/
theorem dvd_fiberGcd_of_fiber {n : ℕ} {ζ c : F}
    (hζn : ζ ^ n = 1) (hζc : (1 + ζ) ^ n = c ^ n) :
    (X - C ζ) ∣ gcd (X ^ n - 1 : F[X]) (shiftedPowPoly n c) := by
  classical
  -- `ζ` is a root of `X^n - 1`
  have hr1 : (X ^ n - 1 : F[X]).IsRoot ζ := by
    simp [Polynomial.IsRoot.def, hζn]
  -- `ζ` is a root of `shiftedPowPoly n c` (the O213 fibre-root lemma)
  have hr2 : (shiftedPowPoly n c).IsRoot ζ := isRoot_shiftedPowPoly_of_fiber c ζ hζc
  -- `X - C ζ` divides each, hence divides the gcd
  exact dvd_gcd (Polynomial.dvd_iff_isRoot.mpr hr1) (Polynomial.dvd_iff_isRoot.mpr hr2)

/-- **The fibre injects into the roots of `gcd(X^n - 1, shiftedPowPoly n c)`.**
The rep-count fibre `{ζ ∈ mu_n : (1+ζ)^n = c^n}` is a subset of the root set of the gcd,
a strictly sharper container than the `shiftedPowPoly`-only root set of O213. -/
theorem repCount_le_fiberGcd_roots {n : ℕ} (hn : 1 ≤ n) {G : Finset F}
    (hG : ∀ x : F, x ∈ G ↔ x ≠ 0 ∧ x ^ n = 1) {c : F} (hc : c ≠ 0) :
    repCount G c ≤ (gcd (X ^ n - 1 : F[X]) (shiftedPowPoly n c)).roots.toFinset.card := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hgne : gcd (X ^ n - 1 : F[X]) (shiftedPowPoly n c) ≠ 0 := by
    intro h
    rw [_root_.gcd_eq_zero_iff] at h
    exact ArkLib.ProximityGap.SubgroupRepresentationRoots.X_pow_sub_one_ne_zero (by omega) h.1
  rw [repCount_eq_fiber_card hn0 hG hc]
  apply Finset.card_le_card
  intro ζ hζ
  simp only [Finset.mem_filter] at hζ
  obtain ⟨hζG, hζc⟩ := hζ
  obtain ⟨_, hζn⟩ := (hG ζ).mp hζG
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hgne]
  exact Polynomial.dvd_iff_isRoot.mp (dvd_fiberGcd_of_fiber hζn hζc)

/-- **The fibre rep count is bounded by the gcd degree (sharpening O213).**
`r(c) <= deg gcd(X^n - 1, (X+1)^n - C (c^n))`.  This is the sharp Stepanov target: in the
thin prize regime the probe shows the gcd has degree `< n` for **every** `c` (max `r(c)=2`),
so this strictly improves O213's `r(c) <= n` -- the rep count is the degree of the gcd of
`G`'s defining polynomial and the explicit shifted-power polynomial. -/
theorem repCount_le_fiberGcd_natDegree {n : ℕ} (hn : 1 ≤ n) {G : Finset F}
    (hG : ∀ x : F, x ∈ G ↔ x ≠ 0 ∧ x ^ n = 1) {c : F} (hc : c ≠ 0) :
    repCount G c ≤ (gcd (X ^ n - 1 : F[X]) (shiftedPowPoly n c)).natDegree := by
  classical
  calc repCount G c
      ≤ (gcd (X ^ n - 1 : F[X]) (shiftedPowPoly n c)).roots.toFinset.card :=
        repCount_le_fiberGcd_roots hn hG hc
    _ ≤ Multiset.card (gcd (X ^ n - 1 : F[X]) (shiftedPowPoly n c)).roots :=
        (gcd (X ^ n - 1 : F[X]) (shiftedPowPoly n c)).roots.toFinset_card_le
    _ ≤ (gcd (X ^ n - 1 : F[X]) (shiftedPowPoly n c)).natDegree :=
        Polynomial.card_roots' _

/-- **The gcd bound refines the degree-`n` bound.** `deg gcd(X^n-1, P_c) <= n`, so the
fibre gcd bound `repCount_le_fiberGcd_natDegree` is never weaker than O213's
`repCount_le_n`, and (per the probe) is strictly sharper in the thin regime. -/
theorem fiberGcd_natDegree_le {n : ℕ} (hn : 1 ≤ n) (c : F) :
    (gcd (X ^ n - 1 : F[X]) (shiftedPowPoly n c)).natDegree ≤ n := by
  classical
  -- gcd divides `shiftedPowPoly n c`, whose degree is `n`
  have hPne : shiftedPowPoly n c ≠ 0 := shiftedPowPoly_ne_zero hn c
  have hdvd : gcd (X ^ n - 1 : F[X]) (shiftedPowPoly n c) ∣ shiftedPowPoly n c :=
    gcd_dvd_right _ _
  calc (gcd (X ^ n - 1 : F[X]) (shiftedPowPoly n c)).natDegree
      ≤ (shiftedPowPoly n c).natDegree := Polynomial.natDegree_le_of_dvd hdvd hPne
    _ = n := shiftedPowPoly_natDegree hn c

end ArkLib.ProximityGap.AdditiveEnergyRepBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.dvd_fiberGcd_of_fiber
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_le_fiberGcd_roots
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_le_fiberGcd_natDegree
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.fiberGcd_natDegree_le
