/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G242CarrierCorrectQuotientLargeSieve

/-!
# G243: coset-lift carrier Parseval — discharge G242's carrier input hypothesis (#466)

G242 corrected G240's carrier-vs-subgroup typing bug by running the fiber map `x ↦ class(2 − x)`
over the carrier `C = F_p^*` (cardinality `n·m`), where the honest lifted Parseval

```text
(L)   ∑_{x ∈ C} ‖F x‖² = n·m·‖a‖²
```

genuinely holds, rather than over the subgroup `G` (cardinality `n`), where `F` is constant and the
`n·m` energy collapses to a rank-one functional (G241 probe: subgroup sum is
`0.0005–0.019·(n·m·‖a‖²)`).  But G242 still *asserted* `(L)` as an explicit hypothesis
`hInputParseval`.  Every referee pass (G236, G239, G241) validated `(L)` numerically and located its
honest structural source, but nobody kernel-checked the reduction.

This file kernel-checks the **coset-lift** step that turns `(L)` into the genuinely-primitive
quotient Parseval

```text
(Q)   ∑_{A ∈ Q} ‖value A‖² = m·‖a‖²,     value A := F̂_a(A) = the constant of F on the coset A,
```

closing exactly the carrier-vs-subgroup gap that was *actually wrong* (the `n·m`-vs-`n` collapse),
and leaving only the standard finite-abelian quotient Parseval `(Q)` as the last Mathlib character
obligation.

The structural content: the carrier `C = F_p^*` is the disjoint union of the `m` cosets of `G`
(the class-fibers of `cls : x ↦ class x`), each of size exactly `n`; the lifted Fourier polynomial
`F` is **constant on each coset**, with value `value (cls x)`.  Hence by fiberwise summation

```text
∑_{x ∈ C} ‖F x‖² = ∑_{A ∈ Q} ∑_{x ∈ C, cls x = A} ‖F x‖²
                = ∑_{A ∈ Q} n · ‖value A‖²          (constant on each size-`n` fiber)
                = n · ∑_{A ∈ Q} ‖value A‖²
                = n · (m·‖a‖²)                        (quotient Parseval (Q))
                = n·m·‖a‖².
```

This is the honest `(L)` identity, derived from `(Q)` rather than asserted, using only
`Finset.sum_fiberwise_of_maps_to` and a constant-on-fiber collapse — no character theory of its own.
It removes the carrier mismatch from the discharge path: whoever supplies the finite-abelian
quotient Parseval `(Q)` (roots-of-unity orthogonality on `Q ≅ ℤ/m`) now obtains the carrier `(L)`
input for free, correctly typed, and the whole G228→G242 mass-floor chain becomes hypothesis-clean
down to the single `(Q)` primitive.

`main_mass_floor` and `carrier_largesieve_of_coset_lift` package the full chain: given the
constant-on-coset structure, exact per-fiber size `n`, quotient Parseval `(Q)`, output Parseval, and
the sponsor hypotheses, they derive the G233 coefficient mass floor `m − n ≤ 4·n·‖a‖²` with the
carrier input Parseval **fully discharged** from `(Q)` — no bare `(L)` assertion remains.

Keystone correctness repair of the input-(A) discharge path, not a prize move.  It replaces an
asserted carrier identity with a kernel-checked coset-lift reduction; the signed sponsor-prime
covariance at ranks 5 and 6 remains open and on the BGK/Paley wall.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G243CosetLiftCarrierParseval

open Finset
open ArkLib.ProximityGap.Frontier.G242CarrierCorrectQuotientLargeSieve

variable {α β : Type*}

/-! ## Coset-lift energy identity -/

/-- **Coset-lift energy identity.**

Let the carrier `C : Finset α` classify under `cls : α → β` into classes drawn from `D : Finset β`
(`hmaps`), let `F : α → ℂ` be **constant on each class-fiber** with `F x = value (cls x)` on `C`
(`hconst`), and let every class-fiber have cardinality exactly `n` (`hsize`).  Then the total energy
of `F` on the carrier lifts to `n` times the quotient (per-class) energy:

```text
∑_{x ∈ C} ‖F x‖² = n · ∑_{A ∈ D} ‖value A‖².
```

This is the pure combinatorial heart of the carrier Parseval `(L)`: it converts a sum over the
size-`n·m` carrier into `n` times a sum over the size-`m` quotient, using only fiberwise summation
and a constant-on-fiber collapse.  No character theory is used here; the deep content
(roots-of-unity orthogonality) is isolated into the separate quotient Parseval `(Q)` downstream. -/
theorem coset_lift_energy
    [DecidableEq β] (C : Finset α) (cls : α → β) (D : Finset β)
    (F : α → ℂ) (value : β → ℂ) (n : ℕ)
    (hmaps : ∀ x ∈ C, cls x ∈ D)
    (hconst : ∀ x ∈ C, F x = value (cls x))
    (hsize : ∀ d ∈ D, (C.filter (fun x => cls x = d)).card = n) :
    ∑ x ∈ C, ‖F x‖ ^ 2 = (n : ℝ) * ∑ d ∈ D, ‖value d‖ ^ 2 := by
  have hfw : ∑ d ∈ D, ∑ x ∈ C.filter (fun x => cls x = d), ‖F x‖ ^ 2
           = ∑ x ∈ C, ‖F x‖ ^ 2 :=
    Finset.sum_fiberwise_of_maps_to hmaps (fun x => ‖F x‖ ^ 2)
  rw [← hfw, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hval : ∀ x ∈ C.filter (fun x => cls x = d), ‖F x‖ ^ 2 = ‖value d‖ ^ 2 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxC, hxcls⟩ := hx
    rw [hconst x hxC, hxcls]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, hsize d hd, nsmul_eq_mul]

/-- **Carrier input Parseval `(L)` from the coset lift and quotient Parseval `(Q)`.**

Combining the coset-lift energy identity with the finite-abelian quotient Parseval
`∑_{A ∈ D} ‖value A‖² = m·aNorm2` gives the honest carrier input Parseval

```text
∑_{x ∈ C} ‖F x‖² = n·m·aNorm2,
```

the exact `(L)` identity that G242 asserted as a hypothesis, now derived.  This is the correctly
typed replacement for G240's false subgroup-sum `∑_{u ∈ G} = n·m·aNorm2`. -/
theorem carrier_input_parseval_of_quotient
    [DecidableEq β] (C : Finset α) (cls : α → β) (D : Finset β)
    (F : α → ℂ) (value : β → ℂ) (n m : ℕ) (aNorm2 : ℝ)
    (hmaps : ∀ x ∈ C, cls x ∈ D)
    (hconst : ∀ x ∈ C, F x = value (cls x))
    (hsize : ∀ d ∈ D, (C.filter (fun x => cls x = d)).card = n)
    (hQuotParseval : ∑ d ∈ D, ‖value d‖ ^ 2 = (m : ℝ) * aNorm2) :
    ∑ x ∈ C, ‖F x‖ ^ 2 = (n : ℝ) * m * aNorm2 := by
  rw [coset_lift_energy C cls D F value n hmaps hconst hsize, hQuotParseval]
  ring

/-! ## Per-class exact size gives the `≤ n` fiber ceiling -/

/-- **Exact per-class size `= n` yields the fiber ceiling `≤ n`.**

The carrier-correct large sieve (G242) needs the per-class *bound* `≤ n`.  For the quotient-Jacobi
carrier every class has size exactly `n`, which certainly gives `≤ n`; this bridges the exact size
hypothesis used by the coset lift to the ceiling hypothesis used by G242's operator bound. -/
theorem class_size_le_of_eq
    [DecidableEq β] (C : Finset α) (cls : α → β) (D : Finset β) (n : ℕ)
    (hsize : ∀ d ∈ D, (C.filter (fun x => cls x = d)).card = n) :
    ∀ d, d ∈ D → (C.filter (fun x => cls x = d)).card ≤ n := by
  intro d hd
  rw [hsize d hd]

/-! ## Carrier large-sieve operator bound with the coset-lift-discharged input -/

/-- **Carrier large-sieve operator bound `outputEnergy ≤ n²·aNorm2` with `(L)` discharged.**

Same conclusion as G242's `carrier_largesieve_of_fibers`, but the carrier input Parseval `(L)` is
*derived* from the coset-lift structure (`hconst`, exact per-fiber size `hsize`) and the quotient
Parseval `(Q)` (`hQuotParseval`), rather than assumed.  The per-class ceiling `≤ n` needed by
G242 is also obtained from the exact size.

This is the honest operator bound: no bare `n·m` carrier assertion remains; the only third-party
character input is the finite-abelian quotient Parseval on `Q ≅ ℤ/m`. -/
theorem carrier_largesieve_of_coset_lift
    [DecidableEq β] (C : Finset α) (cls : α → β) (D : Finset β)
    (F : α → ℂ) (value : β → ℂ) (n m : ℕ) (hm : 0 < m)
    (aNorm2 outputEnergy : ℝ)
    (hmaps : ∀ x ∈ C, cls x ∈ D)
    (hconst : ∀ x ∈ C, F x = value (cls x))
    (hsize : ∀ d ∈ D, (C.filter (fun x => cls x = d)).card = n)
    (hQuotParseval : ∑ d ∈ D, ‖value d‖ ^ 2 = (m : ℝ) * aNorm2)
    (hOutputParseval : outputEnergy ≤
      (∑ d ∈ D, ‖∑ x ∈ C.filter (fun x => cls x = d), F x‖ ^ 2) / m) :
    outputEnergy ≤ (n : ℝ) ^ 2 * aNorm2 := by
  have hle : ∀ d, (C.filter (fun x => cls x = d)).card ≤ n := by
    intro d
    by_cases hd : d ∈ D
    · rw [hsize d hd]
    · -- outside `D` the fiber is empty (no `x ∈ C` maps there), so its card is `0 ≤ n`
      have hempty : C.filter (fun x => cls x = d) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hxC hcx
        exact hd (hcx ▸ hmaps x hxC)
      rw [hempty]
      exact Nat.zero_le n
  have hInput : ∑ x ∈ C, ‖F x‖ ^ 2 = (n : ℝ) * m * aNorm2 :=
    carrier_input_parseval_of_quotient C cls D F value n m aNorm2 hmaps hconst hsize hQuotParseval
  exact carrier_largesieve_of_fibers C cls D F n m hm aNorm2 outputEnergy
    hmaps hle hInput hOutputParseval

/-! ## Fully-discharged G233 mass floor on the coset-lift carrier -/

/-- **G233 coefficient-mass floor with the carrier input Parseval fully discharged.**

The honest end of the G228→G242 chain: the large-sieve input `(A)` is discharged with the fiber map
on the carrier `C = F_p^*`, and the carrier Parseval `(L)` `∑_{x ∈ C} ‖F x‖² = n·m·aNorm2` is itself
*derived* from the coset-lift structure and the finite-abelian quotient Parseval `(Q)`
`∑_{A ∈ Q} ‖value A‖² = m·aNorm2` — not asserted.  The only remaining third-party obligation is
`(Q)`, the standard roots-of-unity orthogonality on `Q ≅ ℤ/m`.

Compared with G242's `l2_mass_floor_of_carrier_fibers`, the carrier `hInputParseval` hypothesis is
gone: it is replaced by the constant-on-coset structure `hconst`, the exact per-fiber size `hsize`,
and the quotient Parseval `hQuotParseval`.  Everything else (fiber Cauchy, fiber count, the `n²`
cancellation, the mass floor) is kernel-checked. -/
theorem main_mass_floor
    [DecidableEq β] (C : Finset α) (cls : α → β) (D : Finset β)
    (F : α → ℂ) (value : β → ℂ) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (aNorm2 outputEnergy sNorm2 : ℝ)
    (hmaps : ∀ x ∈ C, cls x ∈ D)
    (hconst : ∀ x ∈ C, F x = value (cls x))
    (hsize : ∀ d ∈ D, (C.filter (fun x => cls x = d)).card = n)
    (hQuotParseval : ∑ d ∈ D, ‖value d‖ ^ 2 = (m : ℝ) * aNorm2)
    (hOutputParseval : outputEnergy ≤
      (∑ d ∈ D, ‖∑ x ∈ C.filter (fun x => cls x = d), F x‖ ^ 2) / m)
    (hSponsor : (n : ℝ) * ((m : ℝ) - n) ≤ sNorm2)
    (hHalf : sNorm2 / 4 ≤ outputEnergy) :
    (m : ℝ) - n ≤ 4 * n * aNorm2 := by
  have hInput : ∑ x ∈ C, ‖F x‖ ^ 2 = (n : ℝ) * m * aNorm2 :=
    carrier_input_parseval_of_quotient C cls D F value n m aNorm2 hmaps hconst hsize hQuotParseval
  have hle : ∀ d, (C.filter (fun x => cls x = d)).card ≤ n := by
    intro d
    by_cases hd : d ∈ D
    · rw [hsize d hd]
    · have hempty : C.filter (fun x => cls x = d) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hxC hcx
        exact hd (hcx ▸ hmaps x hxC)
      rw [hempty]
      exact Nat.zero_le n
  exact l2_mass_floor_of_carrier_fibers C cls D F n m hn hm aNorm2 outputEnergy sNorm2
    hmaps hle hInput hOutputParseval hSponsor hHalf

end ArkLib.ProximityGap.Frontier.G243CosetLiftCarrierParseval
