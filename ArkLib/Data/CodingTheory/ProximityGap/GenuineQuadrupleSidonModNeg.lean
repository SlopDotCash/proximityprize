/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2CharFreeLowerBound
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyCharacterization

/-!
# The genuine-quadruple obstruction IS Sidon-modulo-negation (#444 k=2 / `ν` face)

`E2CharFreeLowerBound` proved the char-free LOWER bound `E2(μ_n) ≥ 2n²−n` and named the exact
obstruction to the matching UPPER bound `E2(μ_n) ≤ 3n²−3n` as the Prop
`E2CharFree.GenuineQuadruple` (a normalized extra additive relation `1 + B = C + D` with
`{1,B} ≠ {C,D}`).  Its docstring asserts in prose that the upper bound "is equivalent to the
NON-existence of a genuine quadruple", but that connection was left as a HOOK, never a theorem.
Separately, `SidonEnergyIff` / `AdditiveEnergyCharacterization` closed
`E2(G) = 3n²−3n ↔ SidonModNeg G`.  The missing brick is the bridge between the two obstruction
objects: the char-free `GenuineQuadruple` Prop and the structural `SidonModNeg` hypothesis that
all the energy-exact theorems consume.

This file supplies that bridge.  The subtlety the prose glossed (and the probe makes precise):
`SidonModNeg` permits the ZERO-SUM coincidence branch, so `GenuineQuadruple` as stated is NOT the
exact complement, the genuine quadruples with `1 + B = 0` (i.e. `B = -1`) are present on every
negation-closed `μ_n` regardless of Sidon-ness.  The exact complement is the genuine quadruple
with **nonzero sum**:

> `GenuineQuadrupleNZ G : ∃ B C D ∈ G, 1 + B = C + D ∧ 1 + B ≠ 0 ∧ {1,B} ≠ {C,D}`

and the headline (the universal, `1`-normalized direction + its contrapositive) is

> **`not_genuineQuadrupleNZ_of_sidonModNeg`**, for `1 ∈ G` over a field:
> `SidonModNeg G → ¬ GenuineQuadrupleNZ G`.
> **`not_sidonModNeg_of_genuineQuadrupleNZ`**, the contrapositive:
> a nonzero-sum genuine quadruple breaks `SidonModNeg`.

HONEST SCOPE OF THE CONVERSE (the full `iff`).  The reverse implication
`¬ GenuineQuadrupleNZ G → SidonModNeg G` is NOT free for a GENERAL finite set: `SidonModNeg` is a
`∀`-statement over EVERY distinguished left element `a ∈ G`, whereas `GenuineQuadrupleNZ`
normalizes only to the single element `1`.  For a MULTIPLICATIVELY-closed `μ_n` the two coincide
(any coincidence `a + b = c + d` divides through by `a ∈ μ_n` to the `1`-normalized form, since
`a⁻¹ ∈ μ_n` and `μ_n` is closed under multiplication), and the probe confirms the resulting `iff`
holds 0/12 fails on PROPER thin `μ_n`.  We do NOT formalize that multiplicative normalization here
(it would require the subgroup-closure hypotheses); the universal content is the two complete
theorems above, and the `μ_n`-specialized `iff` is recorded as probe-validated, not asserted as a
general-set theorem.  Composing the forward direction with
`additiveEnergy_eq_iff_sidonModNeg` already gives the half that `E2CharFreeLowerBound` needs:
`E(G) = 3|G|²−3|G| → ¬ GenuineQuadrupleNZ G`.

## Probe

`scripts/probes/probe_genuinequad_sidonmodneg.py` (PROPER thin `μ_n`, `n = 2^a`, prize-regime
`p ≫ n³`, `p ≡ 1 mod n`, 3 primes per `n`, NEVER `n = q−1`): across `n = 4..32` the bridge holds
0/12 fails, `SidonModNeg G` exactly when the count of nonzero-sum genuine quadruples is `0`
(witness: `n = 32, p = 32993` is NOT SidonModNeg and has `24` nonzero-sum genuine quadruples),
while the zero-sum genuine quadruples (`B = -1`) number `2n−2` regardless, confirming the
nonzero-sum restriction is essential and not cosmetic.

## Scope (rule 3 / rule 6, honesty contract)

NOT a CORE closure, NOT thinness-essential: pure char-free / field-universal additive combinatorics
(it relates two Props about a finite set; thickness never enters).  It does NOT supply whether
`μ_n` actually IS Sidon-mod-negation at the prize prime; that (the `energyExcess = 0` question,
equivalently the non-existence of a nonzero-sum genuine quadruple at `p ~ n⁴`) is the open
field-arithmetic / sum-product input that `SidonEnergyIff` already names, the `k = 2` shadow of
the BGK wall.  CORE (`M(μ_n) ≤ C√(n log(p/n))`) stays OPEN.  This brick only WIRES the char-free
obstruction Prop into the full `SidonModNeg ↔ E2-exact ↔ repCount≤2` characterization, completing
the hook `E2CharFreeLowerBound` left open.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.GenuineQuadrupleSidonModNeg

open ArkLib.ProximityGap.AdditiveEnergySidonModNeg ArkLib.ProximityGap.E2CharFree
open ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The nonzero-sum genuine quadruple obstruction.**  A genuine extra additive relation
`1 + B = C + D` (with `{1,B} ≠ {C,D}` unordered) whose common sum `1 + B` is nonzero.  This is the
exact complement of `SidonModNeg` for a set containing `1`: the zero-sum case (`1 + B = 0`) is
always permitted by `SidonModNeg`'s zero-sum branch, so it must be excluded here. -/
def GenuineQuadrupleNZ (G : Finset F) : Prop :=
  ∃ B C D : F, B ∈ G ∧ C ∈ G ∧ D ∈ G ∧ (1 : F) + B = C + D ∧ (1 : F) + B ≠ 0 ∧
    ¬ (({(1 : F), B} : Finset F) = {C, D})

/-- Unordered pair equality `{1,B} = {C,D}` is exactly the ordered-trivial disjunction.  This is
the bridge between `SidonModNeg`'s ordered disjunction and `GenuineQuadruple`'s Finset equality. -/
theorem pair_eq_iff_ordered (B C D : F) :
    (({(1 : F), B} : Finset F) = {C, D}) ↔ ((1 : F) = C ∧ B = D) ∨ ((1 : F) = D ∧ B = C) := by
  rw [Finset.ext_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hC : C = 1 ∨ C = B := by have := (h C).mpr (Or.inl rfl); tauto
    have hD : D = 1 ∨ D = B := by have := (h D).mpr (Or.inr rfl); tauto
    have h1mem : (1 : F) = C ∨ (1 : F) = D := (h 1).mp (Or.inl rfl)
    have hBmem : B = C ∨ B = D := (h B).mp (Or.inr rfl)
    -- Decide the ordered match from the four membership facts (all are equalities; close by
    -- substituting and `tauto`).
    rcases h1mem with h1c | h1d
    · rcases hBmem with hbc | hbd
      · rcases hD with hd1 | hdB
        · left; subst h1c; subst hd1; exact ⟨rfl, hbc⟩
        · left; subst h1c; exact ⟨rfl, hdB.symm⟩
      · exact Or.inl ⟨h1c, hbd⟩
    · rcases hBmem with hbc | hbd
      · exact Or.inr ⟨h1d, hbc⟩
      · rcases hC with hc1 | hcB
        · right; subst h1d; subst hc1; exact ⟨rfl, hbd⟩
        · right; subst h1d; exact ⟨rfl, hcB.symm⟩
  · rintro (⟨hC, hD⟩ | ⟨hD, hC⟩) x
    · rw [← hC, ← hD]
    · rw [← hC, ← hD]; tauto

/-- **`SidonModNeg` rules out nonzero-sum genuine quadruples.**  If `G` is Sidon-modulo-negation
and `1 ∈ G`, then no nonzero-sum genuine quadruple exists: any `1 + B = C + D` with `1 + B ≠ 0`
forces `{1,B} = {C,D}` by the ordered-trivial branch of `SidonModNeg`. -/
theorem not_genuineQuadrupleNZ_of_sidonModNeg {G : Finset F} (h1 : (1 : F) ∈ G)
    (hS : SidonModNeg G) : ¬ GenuineQuadrupleNZ G := by
  rintro ⟨B, C, D, hB, hC, hD, hrel, hnz, hne⟩
  -- SidonModNeg on the coincidence `1 + B = C + D`.
  rcases hS 1 h1 B hB C hC D hD hrel with ⟨h1c, hBD⟩ | ⟨h1d, hBC⟩ | hzero
  · exact hne ((pair_eq_iff_ordered B C D).mpr (Or.inl ⟨h1c, hBD⟩))
  · exact hne ((pair_eq_iff_ordered B C D).mpr (Or.inr ⟨h1d, hBC⟩))
  · exact hnz hzero

/-- **A nonzero-sum genuine quadruple breaks `SidonModNeg`.**  The converse: if a nonzero-sum
genuine quadruple exists, `G` cannot be Sidon-modulo-negation. -/
theorem not_sidonModNeg_of_genuineQuadrupleNZ {G : Finset F} (h1 : (1 : F) ∈ G)
    (hG : GenuineQuadrupleNZ G) : ¬ SidonModNeg G := by
  intro hS
  exact not_genuineQuadrupleNZ_of_sidonModNeg h1 hS hG

/-- **The char-free obstruction is necessary for a genuine quadruple.**  Contrapositive packaging:
if `G` (containing `1`) admits a nonzero-sum genuine quadruple then its additive energy is NOT the
minimal `3|G|² − 3|G|`, i.e. the energy excess is positive.  Composes
`not_sidonModNeg_of_genuineQuadrupleNZ` with the in-tree
`AdditiveEnergyCharacterization.additiveEnergy_eq_iff_sidonModNeg`. -/
theorem additiveEnergy_ne_of_genuineQuadrupleNZ {G : Finset F} (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) (h1 : (1 : F) ∈ G)
    (hG : GenuineQuadrupleNZ G) :
    additiveEnergy G ≠ 3 * G.card ^ 2 - 3 * G.card := by
  intro hE
  have hS : SidonModNeg G :=
    (additiveEnergy_eq_iff_sidonModNeg h2 h0 hneg).mp hE
  exact not_sidonModNeg_of_genuineQuadrupleNZ h1 hG hS

end ArkLib.ProximityGap.GenuineQuadrupleSidonModNeg

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only on the COMPLETE theorems)
open ArkLib.ProximityGap.GenuineQuadrupleSidonModNeg in
#print axioms pair_eq_iff_ordered
open ArkLib.ProximityGap.GenuineQuadrupleSidonModNeg in
#print axioms not_genuineQuadrupleNZ_of_sidonModNeg
open ArkLib.ProximityGap.GenuineQuadrupleSidonModNeg in
#print axioms not_sidonModNeg_of_genuineQuadrupleNZ
open ArkLib.ProximityGap.GenuineQuadrupleSidonModNeg in
#print axioms additiveEnergy_ne_of_genuineQuadrupleNZ
