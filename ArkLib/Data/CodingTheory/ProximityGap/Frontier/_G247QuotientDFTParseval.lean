/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G243CosetLiftCarrierParseval
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModDFTParseval

/-!
# G247: quotient DFT Parseval closes the G243 `(Q)` residual (#466)

G243 reduced the carrier Parseval input `(L)` for the carrier-correct large-sieve chain to one
primitive quotient Parseval

```text
(Q)   ∑_{A ∈ Q} ‖value A‖² = m · ‖a‖².
```

Fable G244 checked that this residual is now correctly typed: `Q ≅ ZMod m`, coefficient space
`ZMod m → ℂ`, and `value` is the unnormalized quotient DFT of the coefficient vector.  This file
lands that primitive directly from the existing axiom-clean `ZMod` DFT Parseval theorem and feeds it
into G243's `main_mass_floor`, so the whole G228→G243 input-(A) path no longer has a bare quotient
Parseval hypothesis.

This is a keystone correctness closure, not a prize estimate.  It supplies no signed
sponsor-prime phase cancellation; the live CORE target remains the full rank-5/rank-6 signed
covariance.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G247QuotientDFTParseval

open Finset ZMod
open scoped ComplexConjugate

/-- **Quotient Parseval `(Q)` on `Q ≅ ZMod m`.**

For the unnormalized `ZMod m` DFT used by the quotient-character coordinate,

```text
value A = (𝓕 a) A = ∑ j, ψ(-jA) a_j,
```

the quotient energy is exactly `m` times coefficient energy.  This is the concrete roots-of-unity
orthogonality primitive left open by G243. -/
theorem quotient_parseval_zmod_dft (m : ℕ) [NeZero m] (a : ZMod m → ℂ) :
    ∑ A : ZMod m, ‖(𝓕 a) A‖ ^ 2 = (m : ℝ) * ∑ j : ZMod m, ‖a j‖ ^ 2 := by
  simpa using ProximityGap.Frontier.ZModDFTParseval.dft_parseval (N := m) a

/-- **G243 mass floor with `(Q)` discharged by `ZMod` DFT Parseval.**

Specializes the abstract G243 coset-lift consumer to quotient classes indexed by `ZMod m` and
`value = 𝓕 a`.  The quotient Parseval hypothesis is no longer an external assumption: it is supplied
by `quotient_parseval_zmod_dft`.  Remaining hypotheses are the geometric/campaign inputs already
isolated by G243: exact class size `n`, constancy of the lifted Fourier polynomial on class fibers,
quotient output Parseval, and the sponsor/half-capture premises. -/
theorem main_mass_floor_of_zmod_dft
    {α : Type*} (n m : ℕ) [NeZero m] (C : Finset α) (cls : α → ZMod m) (F : α → ℂ)
    (hn : 0 < n) (hm : 0 < m)
    (a : ZMod m → ℂ) (outputEnergy sNorm2 : ℝ)
    (hconst : ∀ x ∈ C, F x = (𝓕 a) (cls x))
    (hsize : ∀ d : ZMod m, (C.filter (fun x => cls x = d)).card = n)
    (hOutputParseval : outputEnergy ≤
      (∑ d ∈ (Finset.univ : Finset (ZMod m)),
        ‖∑ x ∈ C.filter (fun x => cls x = d), F x‖ ^ 2) / m)
    (hSponsor : (n : ℝ) * ((m : ℝ) - n) ≤ sNorm2)
    (hHalf : sNorm2 / 4 ≤ outputEnergy) :
    (m : ℝ) - n ≤ 4 * n * (∑ j : ZMod m, ‖a j‖ ^ 2) := by
  exact ArkLib.ProximityGap.Frontier.G243CosetLiftCarrierParseval.main_mass_floor
    (C := C) (cls := cls) (D := (Finset.univ : Finset (ZMod m)))
    (F := F) (value := fun A : ZMod m => (𝓕 a) A)
    (n := n) (m := m) (hn := hn) (hm := hm)
    (aNorm2 := ∑ j : ZMod m, ‖a j‖ ^ 2)
    (outputEnergy := outputEnergy) (sNorm2 := sNorm2)
    (by intro x hx; simp) hconst (by intro d hd; exact hsize d)
    (quotient_parseval_zmod_dft m a) hOutputParseval hSponsor hHalf

end ArkLib.ProximityGap.Frontier.G247QuotientDFTParseval

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G247QuotientDFTParseval.quotient_parseval_zmod_dft
#print axioms ArkLib.ProximityGap.Frontier.G247QuotientDFTParseval.main_mass_floor_of_zmod_dft
