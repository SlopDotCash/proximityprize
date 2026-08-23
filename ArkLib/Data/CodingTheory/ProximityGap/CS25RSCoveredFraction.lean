/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveredFraction
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# CS25 covered fraction, instantiated for Reed–Solomon codes (#82)

The Reed–Solomon code `ReedSolomon.code domain deg` is a `Submodule` (closed under `±`, containing
`0`), so it directly satisfies the linearity hypotheses of the general covered-fraction bound
`card_close_mul_near_ge`.  Instantiating gives, for the RS code as a finset `rsCodeFinset`:

  `|RS| · |B(0,r)| ≤ |{w : Δ₀(w, RS) ≤ r}| · |{v ∈ RS : Δ₀(0,v) ≤ 2r}|`,

the CS25 covered-fraction lower bound specialized to RS codes (the proximity-gap target #82).
-/

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The Reed–Solomon code as a `Finset` of codewords (its carrier is finite over a finite field). -/
noncomputable def rsCodeFinset (domain : ι ↪ F) (deg : ℕ) : Finset (ι → F) :=
  (Set.toFinite ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F))).toFinset

@[simp]
theorem mem_rsCodeFinset (domain : ι ↪ F) (deg : ℕ) (v : ι → F) :
    v ∈ rsCodeFinset domain deg ↔ v ∈ ReedSolomon.code domain deg := by
  simp [rsCodeFinset, Set.Finite.mem_toFinset]

/-- **CS25 covered-fraction lower bound for Reed–Solomon codes (#82).**  `|RS|·|B(0,r)| ≤
|close|·|near|`, where `close = {w : Δ₀(w,RS) ≤ r}` and `near = {v∈RS : Δ₀(0,v) ≤ 2r}` (provided
`|RS|·V > 0`).  Direct instantiation of the general bound via the RS code's `Submodule` closure. -/
theorem rs_card_close_mul_near_ge (domain : ι ↪ F) (deg r : ℕ)
    (hpos : 0 < (rsCodeFinset domain deg).card
        * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    (rsCodeFinset domain deg).card
        * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
      ≤ (Finset.univ.filter (fun w : ι → F => closeCount (rsCodeFinset domain deg) r w ≠ 0)).card
          * ((rsCodeFinset domain deg).filter
              (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card := by
  refine card_close_mul_near_ge (rsCodeFinset domain deg) r ?_ ?_ hpos
  · intro a ha b hb
    rw [mem_rsCodeFinset] at ha hb ⊢
    exact Submodule.sub_mem _ ha hb
  · intro a ha b hb
    rw [mem_rsCodeFinset] at ha hb ⊢
    exact Submodule.add_mem _ ha hb

/-- **The RS code finset is the evaluation image of the degree-`<deg` polynomials.**
`rsCodeFinset domain deg = image of (univ : Finset (degreeLT F deg)) under `p ↦ evalOnPoints domain p`.
This is `ReedSolomon.code = (degreeLT).map evalOnPoints` at the `Finset` level — the bridge for
counting RS codewords via their defining polynomials. -/
theorem rsCodeFinset_eq_image (domain : ι ↪ F) (deg : ℕ)
    [Fintype (Polynomial.degreeLT F deg)] :
    rsCodeFinset domain deg
      = (Finset.univ : Finset (Polynomial.degreeLT F deg)).image
          (fun p : Polynomial.degreeLT F deg =>
            ReedSolomon.evalOnPoints domain (p : Polynomial F)) := by
  ext v
  rw [mem_rsCodeFinset, Finset.mem_image]
  constructor
  · intro hv
    have hmap : v ∈ (Polynomial.degreeLT F deg).map (ReedSolomon.evalOnPoints domain) := hv
    rw [Submodule.mem_map] at hmap
    obtain ⟨p, hp, hpv⟩ := hmap
    exact ⟨⟨p, hp⟩, Finset.mem_univ _, hpv⟩
  · rintro ⟨p, _, hpv⟩
    show v ∈ (Polynomial.degreeLT F deg).map (ReedSolomon.evalOnPoints domain)
    rw [Submodule.mem_map]
    exact ⟨↑p, p.2, hpv⟩

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rs_card_close_mul_near_ge
#print axioms ArkLib.CS25.rsCodeFinset_eq_image
