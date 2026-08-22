/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G56AllDepthPatternDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyEssential

/-!
# LANE G63: the primitive-depth weighted census is pinned AT-OR-ABOVE the DC floor

This file formalizes the census-side circularity that the adversarial critic isolated with an
exact numeric law across the thin-prime family (the `resonant`/`n=16,p=17` probes): the
primitive-depth weighted collision census

`census G r := negSymCount G (2r) + wraparoundExcessR ζ m r`   (the G56 split of `rEnergy`)

has `q·census ≥ n^{2r}` at *every* prime and depth — i.e. `total/dc ≥ 1`, `total/dc → 1`, and
**NEVER `total/dc → 0`**. The would-be exponent gain needs the census to be a *strict sub-floor*
certificate, `q·census < n^{2r}` (equivalently `total/dc < 1`), so that bounding the census by the
Wick ceiling would beat the DC/Parseval moment `n^{2r}/q`. This file proves that is impossible:
the census total IS the raw `r`-fold additive energy of `Gset ζ m` (G56), whose full moment
already contains the DC term `‖η_0‖^{2r} = |G|^{2r}` (`DCEnergyEssential.q_mul_energy_ge_dc`).
So the census reconstructs the very floor it would need to be strictly under.

## The statement

Write `q = |F|`, `n = 2m`, `G = Gset ζ m`, `census G r = negSymCount G (2r) + wraparoundExcessR`.
The exact chain is

`q·census G r = q·rEnergy G r ≥ |G|^{2r} = (2m)^{2r} = n^{2r}`,

the first equality being the G56 all-depth split, the middle inequality being the DC lower bound
`q·E_r ≥ |G|^{2r}` (`b=0` moment mass, all other terms nonnegative), and `|G| = 2m` being
`Gset_card`.

## What is proved (all axiom-clean, all on existing G56 / DCEnergyEssential objects)

1. `census` : the primitive-depth weighted collision census `negSymCount G (2r) + wraparoundExcessR`.
2. `q_mul_census_eq_q_mul_energy` : `q·census = q·rEnergy G r` (the G56 split, cast to `ℝ`).
3. `q_mul_census_ge_dcFloor` : **the circularity core.** `n^{2r} ≤ q·census G r`. The census total
   is at-or-above the DC floor `n^{2r}` — it cannot be pushed below by any depth weighting.
4. `census_ge_dcFloor_div` : the divided form `n^{2r}/q ≤ census G r` (for `q > 0`): the census is
   at least the DC/Parseval floor `n^{2r}/q`, the exact left side of the moment the prize must bound.
5. `not_census_strict_subfloor` : **the no-go.** There is NO strict-sub-floor certificate:
   `¬ (q·census G r < n^{2r})`. Any argument that would beat the moment by bounding the census
   below the floor is refuted — bounding the census bounds `n^{2r}/q`, which re-derives BGK/Paley.
6. `not_census_strict_subfloor_div` : the divided restatement `¬ (census G r < n^{2r}/q)` (`q>0`).
7. `censusIsStrictSubfloorCertificate` / `not_censusIsStrictSubfloorCertificate` : an honest
   scope marker naming the refuted route — the census is not a strict-sub-floor certificate. No
   axioms, no goal weakening; the census-side circularity is a theorem, not a definition.

This is a **precise route no-go**, not a closure and not a wrapper. It does not bound
`wraparoundExcessR` and does not close CORE (`M(μ_n) ≤ C√(n log(p/n))` remains open / on-BGK). It
converts the measured `total/dc → 1` law into a kernel-checked theorem that the primitive-depth
weighted census can never be a strict sub-floor bound at any prime or depth, closing the
"primitive-weighting buys a sub-floor" door the same way the char-`0` and pure-DC-gate doors were
closed (G59 / G61). It complements G61 (gate vs target, off-floor slack wedge) from the census
side: G61 separates the *gate* from the target; G63 pins the *census total itself* at-or-above the
floor.

Issue #466.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

open scoped Classical

namespace ArkLib.ProximityGap.Frontier.G63PrimitiveCensusPinnedAtDCFloor

open ArkLib.ProximityGap.Frontier.E3StrataCount (negSymCount)
open ArkLib.ProximityGap.Frontier.G56AllDepthPatternDecomposition
  (wraparoundExcessR Gset Gset_card rEnergy_Gset_eq_negSymCount_add_wraparoundExcessR)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.DCEnergyEssential (q_mul_energy_ge_dc)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **primitive-depth weighted collision census** at depth `r`: the antipodally balanced count
`negSymCount G (2r)` plus the wraparound excess `wraparoundExcessR ζ m r`. By the G56 all-depth
split this is exactly `rEnergy (Gset ζ m) r`; it is the object the critic ran on `μ_n` at thin
adversarial primes and measured `q·census → n^{2r}` (i.e. `total/dc → 1`). -/
noncomputable def census (ζ : F) (m r : ℕ) : ℕ :=
  negSymCount (Gset ζ m) (2 * r) + wraparoundExcessR ζ m r

/-- The census, cast to `ℝ`, equals the `r`-fold additive energy of `Gset ζ m` (the G56 split). -/
theorem census_eq_rEnergy_real {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    (census ζ m r : ℝ) = (rEnergy (Gset ζ m) r : ℝ) := by
  have hnat : census ζ m r = rEnergy (Gset ζ m) r := by
    rw [census]
    convert (rEnergy_Gset_eq_negSymCount_add_wraparoundExcessR hm hprim).symm using 3
  exact_mod_cast hnat

/-- `q·census = q·rEnergy (Gset ζ m) r`.  The census carries the full additive-energy mass. -/
theorem q_mul_census_eq_q_mul_energy {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m)) :
    (Fintype.card F : ℝ) * (census ζ m r : ℝ)
      = (Fintype.card F : ℝ) * (rEnergy (Gset ζ m) r : ℝ) := by
  rw [census_eq_rEnergy_real hm hprim]

/-- **The circularity core.**  `n^{2r} ≤ q·census G r`.  The primitive-depth weighted census total
is at-or-above the DC floor `n^{2r} = (2m)^{2r} = |G|^{2r}`: its full moment already contains the
principal-character mass `‖η_0‖^{2r} = |G|^{2r}`, and every other frequency contributes
nonnegatively.  So no depth weighting pushes the census below the floor — `total/dc ≥ 1` always.
Requires only a primitive additive character `ψ` (which drives the moment identity). -/
theorem q_mul_census_ge_dcFloor {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ((2 * m : ℕ) : ℝ) ^ (2 * r) ≤ (Fintype.card F : ℝ) * (census ζ m r : ℝ) := by
  rw [q_mul_census_eq_q_mul_energy hm hprim]
  have hdc := q_mul_energy_ge_dc hψ (Gset ζ m) r
  have hcard : (Gset ζ m).card = 2 * m := Gset_card hm hprim
  rw [hcard] at hdc
  exact hdc

/-- **The DC/Parseval floor form.**  `n^{2r}/q ≤ census G r` for `q > 0`.  The census is at least
the DC floor `n^{2r}/q = Σ_{b≠0}‖η_b‖^{2r}/q + (DC mass)/q` — the exact left side of the moment the
prize must bound.  A census bound below this is impossible, hence cannot beat the moment. -/
theorem census_ge_dcFloor_div {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (hq : (0 : ℝ) < (Fintype.card F : ℝ)) :
    ((2 * m : ℕ) : ℝ) ^ (2 * r) / (Fintype.card F : ℝ) ≤ (census ζ m r : ℝ) := by
  rw [div_le_iff₀ hq]
  have h := q_mul_census_ge_dcFloor (r := r) hm hprim hψ
  linarith [h]

/-- **The no-go — no strict sub-floor certificate exists.**  `¬ (q·census G r < n^{2r})`.  The
would-be exponent gain needs the census strictly below the floor so a Wick ceiling on the census
would beat the moment `n^{2r}/q`; the circularity core shows the census total is pinned at-or-above
`n^{2r}`, so no such strict-sub-floor certificate exists.  Bounding the census therefore bounds
`n^{2r}/q` (the Parseval identity's own left side), i.e. re-derives BGK/Paley rather than beating
it. -/
theorem not_census_strict_subfloor {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ¬ ((Fintype.card F : ℝ) * (census ζ m r : ℝ) < ((2 * m : ℕ) : ℝ) ^ (2 * r)) := by
  exact not_lt.mpr (q_mul_census_ge_dcFloor (r := r) hm hprim hψ)

/-- The divided restatement of the no-go: `¬ (census G r < n^{2r}/q)` for `q > 0`. -/
theorem not_census_strict_subfloor_div {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (hq : (0 : ℝ) < (Fintype.card F : ℝ)) :
    ¬ ((census ζ m r : ℝ) < ((2 * m : ℕ) : ℝ) ^ (2 * r) / (Fintype.card F : ℝ)) := by
  exact not_lt.mpr (census_ge_dcFloor_div (r := r) hm hprim hψ hq)

/-- The route the no-go refutes: "the primitive-depth weighted census is a strict sub-floor
certificate", i.e. `q·census < n^{2r}`.  A scope marker for honesty — the census-side circularity
is a proven refutation of exactly this proposition, not a bound on `wraparoundExcessR` and not a
CORE closure. -/
def censusIsStrictSubfloorCertificate (ζ : F) (m r : ℕ) : Prop :=
  (Fintype.card F : ℝ) * (census ζ m r : ℝ) < ((2 * m : ℕ) : ℝ) ^ (2 * r)

/-- The census is provably NOT a strict-sub-floor certificate.  Honest scope marker, no axioms. -/
theorem not_censusIsStrictSubfloorCertificate {ζ : F} {m r : ℕ}
    (hm : 0 < m) (hprim : IsPrimitiveRoot ζ (2 * m))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ¬ censusIsStrictSubfloorCertificate ζ m r := by
  unfold censusIsStrictSubfloorCertificate
  exact not_census_strict_subfloor (r := r) hm hprim hψ

#print axioms census_eq_rEnergy_real
#print axioms q_mul_census_eq_q_mul_energy
#print axioms q_mul_census_ge_dcFloor
#print axioms census_ge_dcFloor_div
#print axioms not_census_strict_subfloor
#print axioms not_census_strict_subfloor_div
#print axioms not_censusIsStrictSubfloorCertificate

end ArkLib.ProximityGap.Frontier.G63PrimitiveCensusPinnedAtDCFloor
