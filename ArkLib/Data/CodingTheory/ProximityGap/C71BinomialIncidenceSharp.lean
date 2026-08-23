/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MultiplicativeRigidityAttainment
import ArkLib.Data.CodingTheory.ProximityGap.C71BinomialIncidenceGcd

/-!
# Conjecture 7.1 residual: the binomial `μ_n`-incidence gcd bound is SHARP (#444, #389)

`C71BinomialIncidenceGcd.binomial_incidence_card_le_gcd` proves the thin-subgroup binomial-direction
incidence bound `#{x ∈ S : x ≠ 0 ∧ x^i − c x^j = 0} ≤ gcd(i−j, n)` for any `S ⊆ μ_n`. This file
supplies the matching **SHARPNESS / attainment** side: there is a binomial direction realising the
bound *exactly*, so `gcd(i−j, n)` is the genuine worst-case incidence over the strata, not merely an
upper bound. The witness is the worst-case target `c = 1` (`γ = 1`) isolated by the attainment
criterion (`MultiplicativeRigidityAttainment.pow_one_eq_card_eq_gcd`): the direction `X^i − X^j`
vanishes at *exactly* `gcd(i−j, n)` points of the full thin subgroup `μ_n`.

Concretely, over the carrier of a finite cyclic subgroup `H ≤ Fˣ` of order `n` (the thin `μ_n`),
`#{x ∈ (H : Set Fˣ).image Units.val : x ≠ 0 ∧ x^i − x^j = 0} = gcd(i−j, n)`. The `Units.val`
injection transports the exact subgroup count `binomial_self_agree_card_eq_gcd` to the `F`-valued
`Finset` the C71 incidence machinery consumes, with no loss.

Probe `scripts/probes/probe_c71_binomial_incidence_sharp.py` (EXACT `F_p`, thin `μ_n` `n=2^a`
`a∈2..5`, `p ≡ 1 mod n`, `(p−1)/n ≥ 2`, `p > n³` + Fermat 257/65537, never `n = q−1`): the witness
`X^d − 1` has *exactly* `gcd(d,n)` roots in `μ_n` (the subgroup `μ_{gcd(d,n)} ≤ μ_n`), `552/552`.

## Theorems
* `binomial_self_incidence_image_card_eq_gcd` — on the `Units.val`-image of a finite cyclic
  `H ≤ Fˣ` of order `n`, the binomial direction `X^i − X^j` (`j < i`) vanishes at *exactly*
  `gcd(i−j, n)` nonzero points. The `≤`-bound `binomial_incidence_card_le_gcd` is therefore SHARP.

NON-MOMENT (cyclic-group power-map count + injective transport). EXTEND-proven (sits on
`binomial_self_agree_card_eq_gcd` and `binomial_incidence_card_le_gcd`). Axiom-clean. NOT a CORE /
Conj-7.1 closure — the strata→soundness bridge stays open; this only pins the worst-case incidence
exactly (and the worst case can be `~n/2`, so sharpness here does *not* beat the wall).
-/

open Finset

namespace ArkLib.ProximityGap.C71BinomialIncidenceSharp

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The binomial `μ_n`-incidence gcd bound is attained.** On the `Units.val`-image of a finite
cyclic subgroup `H ≤ Fˣ` of order `n`, the binomial direction `X^i − X^j` (`j < i`) vanishes at
*exactly* `Nat.gcd (i − j) n` nonzero points. Combined with
`C71BinomialIncidenceGcd.binomial_incidence_card_le_gcd` (`≤ gcd`), this shows the incidence bound is
SHARP: `gcd(i − j, n)` is the genuine worst-case binomial incidence over the thin strata. -/
theorem binomial_self_incidence_image_card_eq_gcd
    {H : Subgroup Fˣ} [Fintype H] [IsCyclic H] [DecidableEq H]
    {i j : ℕ} (hji : j < i) :
    (((univ : Finset H).image (fun x : H => ((x : Fˣ) : F))).filter
        (fun y : F => y ≠ 0 ∧ y ^ i - y ^ j = 0)).card
      = Nat.gcd (i - j) (Fintype.card H) := by
  classical
  -- The map `e : H → F`, `x ↦ (x : Fˣ) : F`, is injective (composition of two injections).
  have hinj : Function.Injective (fun x : H => ((x : Fˣ) : F)) := by
    intro a b hab
    apply Subtype.ext
    exact Units.val_injective (by simpa using hab)
  -- Push the filter through the image (`Finset.filter_image`), then count via injectivity.
  rw [Finset.filter_image, Finset.card_image_of_injective _ hinj]
  -- The transported predicate `(↑x ≠ 0 ∧ (↑x)^i - (↑x)^j = 0)` on `H` is equivalent to
  -- `(x : Fˣ)^i = (x : Fˣ)^j` (units are nonzero; lift the `F`-power equality to `Fˣ`).
  have hpred : (univ.filter fun x : H => ((x : Fˣ) : F) ≠ 0 ∧
        ((x : Fˣ) : F) ^ i - ((x : Fˣ) : F) ^ j = 0)
      = univ.filter fun x : H => (x : Fˣ) ^ i = (x : Fˣ) ^ j := by
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨_, hroot⟩
      have heq : ((x : Fˣ) : F) ^ i = ((x : Fˣ) : F) ^ j := sub_eq_zero.mp hroot
      apply Units.val_injective
      push_cast
      simpa using heq
    · intro hU
      refine ⟨Units.ne_zero _, ?_⟩
      have hF : ((x : Fˣ) : F) ^ i = ((x : Fˣ) : F) ^ j := by
        have := congrArg (fun u : Fˣ => (u : F)) hU
        push_cast at this
        simpa using this
      rw [sub_eq_zero]; exact hF
  rw [hpred]
  -- now the exact subgroup count (target `γ = 1`, via `c₁ = c₂ = 1`)
  have hself := MultiplicativeRigidity.binomial_self_agree_card_eq_gcd (H := H) (1 : Fˣ) hji
  simpa using hself

/-- **Coprime-step sharpness: exactly one incidence.** When the binomial exponent gap `i-j` is
coprime to the subgroup order, the sharp gcd-attainment theorem specializes to a single root on
the full thin subgroup. This is the matching lower/attainment side for the `≤ 1` C71 coprime-row
upper bound in `C71BinomialIncidenceGcd`. -/
theorem binomial_self_incidence_image_card_eq_one_of_coprime
    {H : Subgroup Fˣ} [Fintype H] [IsCyclic H] [DecidableEq H]
    {i j : ℕ} (hji : j < i) (hcop : Nat.Coprime (i - j) (Fintype.card H)) :
    (((univ : Finset H).image (fun x : H => ((x : Fˣ) : F))).filter
        (fun y : F => y ≠ 0 ∧ y ^ i - y ^ j = 0)).card = 1 := by
  simpa [hcop.gcd_eq_one] using
    binomial_self_incidence_image_card_eq_gcd (F := F) (H := H) hji

/-- **Divisible-step sharpness: the whole subgroup is incident.** At the opposite edge from the
coprime rows, if the subgroup order divides the exponent gap, the witness `X^i - X^j` vanishes on
all `|H|` points of the thin subgroup. This records the exact large-incidence face of the same gcd
law, and is only a sharpness/obstruction datum, not a route to CORE. -/
theorem binomial_self_incidence_image_card_eq_card_of_dvd
    {H : Subgroup Fˣ} [Fintype H] [IsCyclic H] [DecidableEq H]
    {i j : ℕ} (hji : j < i) (hdiv : Fintype.card H ∣ i - j) :
    (((univ : Finset H).image (fun x : H => ((x : Fˣ) : F))).filter
        (fun y : F => y ≠ 0 ∧ y ^ i - y ^ j = 0)).card = Fintype.card H := by
  simpa [Nat.gcd_eq_right hdiv] using
    binomial_self_incidence_image_card_eq_gcd (F := F) (H := H) hji

end ArkLib.ProximityGap.C71BinomialIncidenceSharp

/-! ## Axiom audit -/
namespace ArkLib.ProximityGap.C71BinomialIncidenceSharp

#print axioms binomial_self_incidence_image_card_eq_gcd
#print axioms binomial_self_incidence_image_card_eq_one_of_coprime
#print axioms binomial_self_incidence_image_card_eq_card_of_dvd

end ArkLib.ProximityGap.C71BinomialIncidenceSharp
