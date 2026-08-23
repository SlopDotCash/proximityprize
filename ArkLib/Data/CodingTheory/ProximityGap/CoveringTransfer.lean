/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupSumsetConjecture

/-!
# Covering transfer under surjective additive maps (#389)

> **`sumsetDistinct_image_eq_univ`** — if `f : F →+ F'` is surjective and injective on `G`, and the
> `ℓ`-fold distinct sumset of `G` is all of `F`, then the `ℓ`-fold distinct sumset of `f '' G` is all
> of `F'`.

This generalizes the Mersenne `⟨−2⟩` covering (`mersenne_admissible`,
`sumsetDistinct_signedPowers_eq_univ`) to **every primitive prime factor** `q ∣ 2^m − 1`: take
`f = ZMod.castHom (q ∣ 2^m−1) : ZMod (2^m−1) →+ ZMod q` (surjective), `G = signedPowers m`. For `m`
odd with `ord(2 mod q) = m`, `f` is injective on `⟨−2⟩` (the `2m` signed powers stay distinct mod `q`),
so the `m`-fold distinct sumset of `⟨−2⟩ mod q` is *all* of `ZMod q`.

Numerically (m=7..20), every largest primitive factor `q` of `2^m−1` (Mersenne **and** non-Mersenne:
17, 73, 89, 43, 151, 257, …) is a Conj 1.12 witness, with the only binding constraint being the order
bound `2m ≤ 10 log₂ q` (i.e. `q ≥ 2^{m/5}`). So Conj 1.12 follows from "`∃^∞ m: P(2^m−1) ≥ 2^{m/5}`"
(a large-prime-factor statement, cf. Stewart) — a different, broader sufficient condition than the
infinitude of Mersenne primes. The covering half is proved here; the large-factor half is open.
Axiom-clean. Issue #389.
-/

open Finset
open ArkLib.ProximityGap.SubgroupSumset

namespace ArkLib.ProximityGap.CoveringTransfer

variable {F F' : Type*} [AddCommMonoid F] [AddCommMonoid F'] [DecidableEq F] [DecidableEq F']

/-- The `ℓ`-fold distinct sumset commutes with an additive hom injective on `G`: the image of a
distinct `ℓ`-sum is a distinct `ℓ`-sum of the images. -/
theorem image_sumsetDistinct_subset (f : F →+ F') (G : Finset F) (ℓ : ℕ)
    (hinj : Set.InjOn f G) :
    (sumsetDistinct G ℓ).image f ⊆ sumsetDistinct (G.image f) ℓ := by
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [sumsetDistinct, Finset.mem_image] at hx
  obtain ⟨S, hS, rfl⟩ := hx
  rw [Finset.mem_powersetCard] at hS
  have hSinj : Set.InjOn f S := hinj.mono hS.1
  rw [sumsetDistinct, Finset.mem_image]
  refine ⟨S.image f, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    exact ⟨Finset.image_subset_image hS.1, by rw [Finset.card_image_of_injOn hSinj, hS.2]⟩
  · rw [map_sum, Finset.sum_image (fun a ha b hb => hSinj ha hb)]

/-- **Covering transfer.** A surjective additive hom, injective on `G`, carries a full `ℓ`-fold
distinct-sumset covering of `F` to a full covering of `F'`. -/
theorem sumsetDistinct_image_eq_univ [Fintype F] [Fintype F'] (f : F →+ F')
    (hf : Function.Surjective f) (G : Finset F) (ℓ : ℕ) (hinj : Set.InjOn f G)
    (hcov : sumsetDistinct G ℓ = Finset.univ) :
    sumsetDistinct (G.image f) ℓ = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro y
  obtain ⟨x, rfl⟩ := hf y
  have hx : f x ∈ (sumsetDistinct G ℓ).image f := by
    rw [Finset.mem_image]; exact ⟨x, by rw [hcov]; exact Finset.mem_univ x, rfl⟩
  exact image_sumsetDistinct_subset f G ℓ hinj hx

end ArkLib.ProximityGap.CoveringTransfer

#print axioms ArkLib.ProximityGap.CoveringTransfer.sumsetDistinct_image_eq_univ
