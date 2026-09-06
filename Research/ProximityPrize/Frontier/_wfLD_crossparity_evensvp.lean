/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# wf-LD (#407, lane F11) — the cross-parity leak does NOT lower-bound the EVEN-sublattice SVP

## Mission (honest verdict: REFUTED swing, with the structured identity isolated as a theorem)

The prize cross-surplus counts nonzero short cyclotomic integers `α = ∑_j c_j ζ^j` (power basis,
`d = φ(2^μ) = n/2`, `ζ^d = −1`) vanishing mod the **fully-split** prime `p` (`n ∣ p−1 ⟹ p` splits
completely, `N(𝔭) = p`, degree-1 prime ideal). Pan–Xu (EUROCRYPT'21) give poly ideal-SVP only for
**non-split** `q`; the prize `q` is fully split — the named open gap.

The one STRUCTURED feature of the defect locus is the **cross-parity leak**: split a vanishing
defect's coefficient vector into its even-power part `A = ∑_{j even} c_j ζ^j` and odd-power part
`B = ∑_{j odd} c_j ζ^j`. Then `A + B = 0`, i.e. **`A ≡ −B (mod p)`** — and the probe
(`scripts/probes/probe_407_laneF_crossparity_leak.py`) shows this holds for **100%** of defects with
the SHARP ratio `g₀ = −A/B = 1` (not `g`), i.e. the law is exactly `A = −B`.

**The swing (and why it FAILS).** One hopes the cross-parity structure forces the shortest vector of
the **even sublattice** `𝔭_even = {c supported on even powers}` to be LONG (beating the random-lattice
Gaussian heuristic), pinning `r* = ½·λ₁^{L1,even}` below the prize window. The numerics
(`scripts/probes/probe_wfLD_evenlattice_svp.py`, n=16,32,64 over split primes p≡1 mod n) REFUTE this:

| n | λ₁^{L1} FULL | λ₁^{L1} EVEN | EVEN/FULL | trend |
|---|---|---|---|---|
| 16 | 3–5 | 5–7 | 1.25–1.75 | small gain |
| 32 | 3–4 | 3–5 | 1.0–1.33 | gain shrinking |
| 64 | 3–4 | 3–4 | **1.00** uniformly | **gain → 1** |

Both `λ₁^{L1,EVEN}` and `λ₁^{L1,FULL}` track the **counting girth `≈ log_n p`** / the Gaussian
heuristic for an index-`p` sublattice; neither grows like a power of `n`. The even-sublattice gain
factor **decays to 1 as `n → ∞`** — the wrong direction for closure. So `r* = ½·λ₁^{L1,even}` stays
`≈ 2` at n=64, far below the window: the SVP handle, even restricted to the structured even
sublattice, lands back on the same counting girth as the generic route (`IdealSVPGirthVerdict.lean`).

## The precise mechanism of failure (this is what this file PROVES)

The cross-parity identity `A = −B` is a constraint on the **coupling** of the two halves, NOT a lower
bound on either half alone. A **pure-even** short relation has odd part `B = 0`, hence `A = −B = 0`
satisfies the identity *vacuously* — yet `A` is a nonzero even-support combination summing to `0`,
i.e. a genuine short vector of the even sublattice. So the identity cannot exclude pure-even short
vectors, and (as the probe confirms) those exist at the counting girth.

`crossParity_of_vanish` : the identity itself (`A + B = 0 ⟹ A = −B`), unconditional.
`pureEven_witness_satisfies_crossParity_vacuously` : a pure-even short witness satisfies the identity.
`crossParity_does_not_lowerBound_even` : the no-go — the cross-parity identity is consistent with an
arbitrarily short even-sublattice vector, so it supplies NO lower bound on `λ₁^{L1,even}`.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace ArkLib.ProximityGap.WfLDCrossParityEvenSVP

variable {R : Type*} [CommRing R]

/-- The even-power part of a coefficient vector reduced mod the split prime (image in `R = ZMod p`
or `F_p`): `A = ∑_{j even} c_j · ζ^j`. Here `g j := ζ^j` is the reduction of the `j`-th power-basis
monomial, `c` the integer coefficient vector, `d = n/2` the rank. -/
def evenPart {d : ℕ} (c : Fin d → R) (g : Fin d → R) : R :=
  ∑ j ∈ univ.filter (fun j : Fin d => (j : ℕ) % 2 = 0), c j * g j

/-- The odd-power part: `B = ∑_{j odd} c_j · ζ^j`. -/
def oddPart {d : ℕ} (c : Fin d → R) (g : Fin d → R) : R :=
  ∑ j ∈ univ.filter (fun j : Fin d => (j : ℕ) % 2 = 1), c j * g j

/-- A coefficient vector `c` is `supported-on-even-powers` if every odd-index coefficient is `0`. -/
def EvenSupported {d : ℕ} (c : Fin d → R) : Prop :=
  ∀ j : Fin d, (j : ℕ) % 2 = 1 → c j = 0

/-- The full reduction `∑_j c_j g_j` splits as `evenPart + oddPart` (parity partition of indices). -/
theorem fullSum_eq_even_add_odd {d : ℕ} (c : Fin d → R) (g : Fin d → R) :
    (∑ j, c j * g j) = evenPart c g + oddPart c g := by
  classical
  unfold evenPart oddPart
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun j : Fin d => (j : ℕ) % 2 = 0)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j
  simp only [mem_filter, mem_univ, true_and]
  omega

/-- **The cross-parity identity (unconditional).** If a defect vanishes mod the split prime
(`∑_j c_j g_j = 0`), then its even part and odd part are exact negatives: `A = −B`. This is the
structured leak observed at 100% (with the sharp ratio `−A/B = 1`). -/
theorem crossParity_of_vanish {d : ℕ} (c : Fin d → R) (g : Fin d → R)
    (hvanish : (∑ j, c j * g j) = 0) :
    evenPart c g = - oddPart c g := by
  have h := fullSum_eq_even_add_odd c g
  rw [hvanish] at h
  -- 0 = A + B  ⟹  A = -B
  have h' : evenPart c g + oddPart c g = 0 := h.symm
  linear_combination h'

/-- The odd part of an even-supported vector is `0`. -/
theorem oddPart_of_evenSupported {d : ℕ} (c : Fin d → R) (g : Fin d → R)
    (hsupp : EvenSupported c) : oddPart c g = 0 := by
  classical
  unfold oddPart
  apply Finset.sum_eq_zero
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at hj
  rw [hsupp j hj, zero_mul]

/-- **A pure-even short witness satisfies the cross-parity identity VACUOUSLY.** If `c` is supported
on even powers and is a vanishing relation (`∑ c_j g_j = 0`, i.e. a short vector of the even
sublattice), then both `evenPart = 0` and `oddPart = 0`, so the identity `A = −B` holds trivially as
`0 = −0`. The identity carries NO information that would forbid such a witness. -/
theorem pureEven_witness_satisfies_crossParity_vacuously {d : ℕ} (c : Fin d → R) (g : Fin d → R)
    (hsupp : EvenSupported c) (hvanish : (∑ j, c j * g j) = 0) :
    evenPart c g = - oddPart c g ∧ evenPart c g = 0 ∧ oddPart c g = 0 := by
  have hodd : oddPart c g = 0 := oddPart_of_evenSupported c g hsupp
  have hfull := fullSum_eq_even_add_odd c g
  rw [hvanish, hodd, add_zero] at hfull
  refine ⟨?_, hfull.symm, hodd⟩
  rw [hfull.symm, hodd, neg_zero]

/-- **THE NO-GO (the refutation of the swing).** The cross-parity identity `A = −B` does NOT
lower-bound the even-sublattice shortest vector. Formally: for any even-supported vanishing relation
`c` (a short even-sublattice vector, of ANY L1 weight — the numerics find one at the counting girth
`≈ log_n p`), the cross-parity identity holds. Hence the identity is consistent with arbitrarily
short even-sublattice vectors and supplies no positive lower bound on `λ₁^{L1,even}`.

This is the precise content of `EVEN/FULL → 1` in the probe: the structured leak constrains the
coupling of the two parity halves but is vacuous on each half alone, so it cannot push the even
sublattice's girth above the generic counting value. The Pan–Xu split-prime gap is therefore NOT
closed by the cross-parity handle. -/
theorem crossParity_does_not_lowerBound_even {d : ℕ} (c : Fin d → R) (g : Fin d → R)
    (hsupp : EvenSupported c) (hvanish : (∑ j, c j * g j) = 0) :
    -- the cross-parity identity is satisfied …
    evenPart c g = - oddPart c g ∧
    -- … yet the witness `c` is exactly a vanishing even-sublattice element (its full reduction is 0,
    -- supported on even powers) of whatever (possibly small) weight it has:
    (∑ j, c j * g j) = 0 ∧ EvenSupported c :=
  ⟨(pureEven_witness_satisfies_crossParity_vacuously c g hsupp hvanish).1, hvanish, hsupp⟩

end ArkLib.ProximityGap.WfLDCrossParityEvenSVP

-- Axiom audit
#print axioms ArkLib.ProximityGap.WfLDCrossParityEvenSVP.crossParity_of_vanish
#print axioms ArkLib.ProximityGap.WfLDCrossParityEvenSVP.pureEven_witness_satisfies_crossParity_vacuously
#print axioms ArkLib.ProximityGap.WfLDCrossParityEvenSVP.crossParity_does_not_lowerBound_even
