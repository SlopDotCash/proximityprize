/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWindowedLaw

/-!
# Issue #232 — THE SUBDIVISION ENGINE: canonical cosets split into canonical
# sub-cosets (the natural-DCS splitting rung, general form)

The constructive engine of the packing tree program (O122's named next): a
canonical `μ_d`-coset at modulus `n` is the disjoint union of `u` canonical
`μ_{d/u}`-cosets, for ANY `u ∣ d` — the "prime splitting" step of natural
disjoint covering systems, proven once at full generality:

* `step_identity` — the modulus bookkeeping `n / (d/u) = u · (n/d)`;
* `sub_base_lt` — the sub-bases `r + i·(n/d)` (`i < u`) are canonical;
* `cosetOf_subdivide` — **the splitting identity**
  `cosetOf n d r = ⋃_{i<u} cosetOf n (d/u) (r + i·(n/d))`;
* `subdivide_parts_disjoint` — the parts are pairwise disjoint;
* `isPacket_subdivide` — the `IsPacket` form: a `μ_d`-packet is a disjoint
  union of `u` canonical `μ_{d/u}`-packets.

`isPacket_merge` (O106) is the exact inverse rung — merging a packet of
fattened bases into one bigger coset; with this file the splitting tree of
natural DCS theory has both directions machine-checked, and any
tree-realizable modulus multiset yields an explicit packing by iterating
`cosetOf_subdivide` down the tree (the tree law's constructive half, probed
by `probe_packing_tree_law.py`).

Probe grounding: the refinement phenomenology is check (A) of
`probe_window_fiber_threads.py` (exhaustive at `n = 12, 18, 20, 24, 36`,
every `t`).
-/

namespace PackingSubdivision

open Finset DeBruijnWindowedLaw

/-- The modulus bookkeeping of one splitting step: `n / (d/u) = u · (n/d)`
for `u ∣ d ∣ n`. -/
lemma step_identity {n d u : ℕ} (hu : u ∣ d) (hu0 : 0 < u) (hd : d ∣ n)
    (hd0 : 0 < d) : n / (d / u) = u * (n / d) := by
  obtain ⟨c, rfl⟩ := hu
  obtain ⟨m, rfl⟩ := hd
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · omega
    · exact h
  rw [Nat.mul_div_cancel_left c hu0,
    Nat.mul_div_cancel_left m hd0,
    show u * c * m = c * (u * m) by ring,
    Nat.mul_div_cancel_left _ hc0]

/-- Sub-coset bases are canonical: `r + i·(n/d) < n/(d/u)` for `r < n/d`,
`i < u`. -/
lemma sub_base_lt {n d u r i : ℕ} (hu : u ∣ d) (hu0 : 0 < u) (hd : d ∣ n)
    (hd0 : 0 < d) (hr : r < n / d) (hi : i < u) :
    r + i * (n / d) < n / (d / u) := by
  rw [step_identity hu hu0 hd hd0]
  calc r + i * (n / d) < n / d + i * (n / d) := Nat.add_lt_add_right hr _
    _ = (i + 1) * (n / d) := by ring
    _ ≤ u * (n / d) := Nat.mul_le_mul_right _ (by omega)

/-- **The splitting identity**: a canonical `μ_d`-coset is the union of `u`
canonical `μ_{d/u}`-cosets over the bases `r + i·(n/d)`, `i < u`. -/
lemma cosetOf_subdivide {n d u r : ℕ} (hu : u ∣ d) (hu0 : 0 < u) (hd : d ∣ n)
    (hd0 : 0 < d) :
    cosetOf n d r
      = (Finset.range u).biUnion
          (fun i => cosetOf n (d / u) (r + i * (n / d))) := by
  have hstep : n / (d / u) = u * (n / d) := step_identity hu hu0 hd hd0
  have hdu : d / u * u = d := Nat.div_mul_cancel hu
  ext x
  simp only [cosetOf, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j % u, Nat.mod_lt _ hu0, j / u, ?_, ?_⟩
    · have := Nat.mod_add_div j u
      have hjd : j < d / u * u := by rwa [hdu]
      exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hjd)
    · rw [hstep]
      have hsplit : j = j % u + u * (j / u) := (Nat.mod_add_div j u).symm
      calc r + j % u * (n / d) + j / u * (u * (n / d))
          = r + (j % u + u * (j / u)) * (n / d) := by ring
        _ = r + j * (n / d) := by rw [← hsplit]
  · rintro ⟨i, hi, k, hk, rfl⟩
    refine ⟨i + u * k, ?_, ?_⟩
    · calc i + u * k < u + u * k := by omega
        _ = u * (k + 1) := by ring
        _ ≤ u * (d / u) := Nat.mul_le_mul_left _ (by omega)
        _ = d := by rw [mul_comm]; exact hdu
    · rw [hstep]
      ring

/-- The subdivision parts are pairwise disjoint (distinct sub-bases). -/
lemma subdivide_parts_disjoint {n d u r : ℕ} (hu : u ∣ d) (hu0 : 0 < u)
    (hd : d ∣ n) (hd0 : 0 < d) (hn : 0 < n) (hr : r < n / d)
    {i j : ℕ} (hi : i < u) (hj : j < u) (hij : i ≠ j) :
    Disjoint (cosetOf n (d / u) (r + i * (n / d)))
      (cosetOf n (d / u) (r + j * (n / d))) := by
  have hs : 0 < n / d :=
    Nat.div_pos (Nat.le_of_dvd hn hd) hd0
  refine Finset.disjoint_left.mpr fun x hx hx' => ?_
  have h1 := mod_of_mem_cosetOf (sub_base_lt hu hu0 hd hd0 hr hi) hx
  have h2 := mod_of_mem_cosetOf (sub_base_lt hu hu0 hd hd0 hr hj) hx'
  have : r + i * (n / d) = r + j * (n / d) := h1.symm.trans h2
  have : i * (n / d) = j * (n / d) := by omega
  exact hij (Nat.eq_of_mul_eq_mul_right hs this)

/-- **The `IsPacket` form**: a canonical `μ_d`-packet is the disjoint union of
`u` canonical `μ_{d/u}`-packets — the natural-DCS splitting rung.  Inverse of
O106's `isPacket_merge`. -/
lemma isPacket_subdivide {n d u : ℕ} (hu : u ∣ d) (hu0 : 0 < u) (hd : d ∣ n)
    (hd0 : 0 < d) (hn : 0 < n) {P : Finset ℕ}
    (hP : DeBruijnTwoPrimeAssembly.IsPacket n d P) :
    ∃ Qs : Finset (Finset ℕ), Qs.card = u ∧
      (∀ Q ∈ Qs, DeBruijnTwoPrimeAssembly.IsPacket n (d / u) Q) ∧
      (↑Qs : Set (Finset ℕ)).PairwiseDisjoint id ∧ P = Qs.biUnion id := by
  classical
  obtain ⟨r, hr, rfl⟩ := hP
  refine ⟨(Finset.range u).image
    (fun i => cosetOf n (d / u) (r + i * (n / d))), ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    by_contra hne
    have hij' : cosetOf n (d / u) (r + i * (n / d))
        = cosetOf n (d / u) (r + j * (n / d)) := hij
    have hdisj := subdivide_parts_disjoint hu hu0 hd hd0 hn hr
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hne
    have hdupos : 0 < d / u := Nat.div_pos (Nat.le_of_dvd hd0 hu) hu0
    have hmem : r + i * (n / d) ∈ cosetOf n (d / u) (r + i * (n / d)) :=
      base_mem_cosetOf hdupos
    exact Finset.disjoint_left.mp hdisj hmem (hij' ▸ hmem)
  · intro Q hQ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
    exact ⟨r + i * (n / d),
      sub_base_lt hu hu0 hd hd0 hr (Finset.mem_range.mp hi), rfl⟩
  · intro Q₁ h₁ Q₂ h₂ hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h₁)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h₂)
    have hij : i ≠ j := fun hcon => hne (by rw [hcon])
    exact subdivide_parts_disjoint hu hu0 hd hd0 hn hr
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  · show cosetOf n d r
        = ((Finset.range u).image
            (fun i => cosetOf n (d / u) (r + i * (n / d)))).biUnion id
    calc cosetOf n d r
        = (Finset.range u).biUnion
            (fun i => cosetOf n (d / u) (r + i * (n / d))) :=
          cosetOf_subdivide hu hu0 hd hd0
      _ = ((Finset.range u).image
            (fun i => cosetOf n (d / u) (r + i * (n / d)))).biUnion id := by
          ext x
          simp only [Finset.mem_biUnion, Finset.mem_image, id_eq]
          constructor
          · rintro ⟨i, hi, hx⟩
            exact ⟨_, ⟨i, hi, rfl⟩, hx⟩
          · rintro ⟨Q, ⟨i, hi, rfl⟩, hx⟩
            exact ⟨i, hi, hx⟩

/-! ## Tooth: the n = 12 μ_6-coset splits into three μ_2-cosets, kernel-checked -/

example : cosetOf 12 6 1
    = (Finset.range 3).biUnion (fun i => cosetOf 12 2 (1 + i * 2)) :=
  cosetOf_subdivide (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : cosetOf 12 6 1 = {1, 3, 5, 7, 9, 11} := by decide

end PackingSubdivision

#print axioms PackingSubdivision.step_identity
#print axioms PackingSubdivision.cosetOf_subdivide
#print axioms PackingSubdivision.subdivide_parts_disjoint
#print axioms PackingSubdivision.isPacket_subdivide
