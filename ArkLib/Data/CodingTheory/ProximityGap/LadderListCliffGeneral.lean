/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LadderListCliff

/-!
# THE LADDER CLIFF AT EVERY RATE (#389): the whole ladder family has `O(n^{r−1})` list

Generalizes the `r = 2` cliff (`ladder_r2_list_card_le`) to every `r` by a choice-free
double-count: each valid `r`-subset summing to `c`, paired with one of its `r` elements,
injects (via `(T, x) ↦ T.erase x`) into the `(r−1)`-subsets — because the removed element
`x = c − Σ(T∖{x})` is forced by the sum.

* `subset_sum_fibre_card_mul_le` — **the sharp combinatorial core**: for any finite `M`,
  `r · #{r-subsets of M summing to c} ≤ C(|M|, r−1)`.  (At `r = 2` this is `≤ |M|/2`,
  sharper than the pairing bound `≤ |M|`.)
* `ladder_list_card_mul_le` — hence, via the exact bijection `ladder_list_iff`, the ladder
  word `x^{2r} + λx^{2r−2}`'s agreement-`≥ 2r` codeword list over `μ_n ⊂ F_p` obeys
  `r · #list ≤ C(n/2, r−1)`, i.e. `#list ≤ C(n/2, r−1)/r = O(n^{r−1})` — **the entire
  ladder family has polynomial sub-Johnson list, at every rate**.

So `ExplainableCoreSupply`-style polynomial supply holds for every ladder word, with no
generic-prime hypothesis beyond the rigidity transfer threshold.  The matching statement
for *non-ladder* words (no word beats the fibre) is the open word-domination wall.
Issue #389.
-/

open Finset Polynomial

namespace ProximityGap.LadderList

open ProximityGap.SpikeFloor ProximityGap.LadderListModP

variable {L : Type} [Field L] [DecidableEq L]

/-- **The sharp combinatorial core**: for any finite set `M` and constant `c`,
`r · #{r-subsets of M summing to c} ≤ C(|M|, r−1)`.  Choice-free double count: the
incidence `(T, x ∈ T)` injects into the `(r−1)`-subsets via `T ↦ T.erase x`, since the
removed `x = c − Σ(T∖x)` is forced. -/
theorem subset_sum_fibre_card_mul_le (M : Finset L) (c : L) {r : ℕ} (hr : 1 ≤ r) :
    r * ((M.powersetCard r).filter (fun T => ∑ t ∈ T, t = c)).card
      ≤ M.card.choose (r - 1) := by
  classical
  set V := (M.powersetCard r).filter (fun T => ∑ t ∈ T, t = c) with hV
  -- the incidence set of pairs `⟨T, x ∈ T⟩`
  set S : Finset (Σ _ : Finset L, L) := V.sigma (fun T => T) with hS
  -- `|S| = r · |V|`
  have hScard : S.card = r * V.card := by
    rw [hS, Finset.card_sigma]
    have hsz : ∀ T ∈ V, T.card = r := fun T hT =>
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
    rw [Finset.sum_congr rfl hsz, Finset.sum_const, smul_eq_mul, mul_comm]
  -- the map `⟨T, x⟩ ↦ T.erase x` lands in `(r−1)`-subsets
  have hmaps : ∀ s ∈ S, (s.1.erase s.2) ∈ M.powersetCard (r - 1) := by
    rintro ⟨T, x⟩ hs
    rw [hS, Finset.mem_sigma] at hs
    obtain ⟨hTV, hx⟩ := hs
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hTV).1
    refine Finset.mem_powersetCard.mpr ⟨(Finset.erase_subset _ _).trans hTsub, ?_⟩
    rw [Finset.card_erase_of_mem hx, hTcard]
  -- and is injective: the removed element `x = c − Σ(T∖x)` is forced
  have hinj : Set.InjOn (fun s : Σ _ : Finset L, L => s.1.erase s.2) S := by
    rintro ⟨T, x⟩ hsa ⟨T', x'⟩ hsb hfeq
    rw [Finset.mem_coe, hS, Finset.mem_sigma] at hsa hsb
    obtain ⟨hTa, hx⟩ := hsa
    obtain ⟨hTb, hx'⟩ := hsb
    simp only at hfeq
    obtain ⟨_, hsuma⟩ := Finset.mem_filter.mp hTa
    obtain ⟨_, hsumb⟩ := Finset.mem_filter.mp hTb
    have hxa : x = c - ∑ t ∈ T.erase x, t := by
      rw [← Finset.add_sum_erase _ _ hx] at hsuma; rw [← hsuma]; ring
    have hxb : x' = c - ∑ t ∈ T'.erase x', t := by
      rw [← Finset.add_sum_erase _ _ hx'] at hsumb; rw [← hsumb]; ring
    have hxeq : x = x' := by rw [hxa, hxb, hfeq]
    refine Sigma.ext ?_ (by rw [hxeq])
    calc T = insert x (T.erase x) := (Finset.insert_erase hx).symm
      _ = insert x' (T'.erase x') := by rw [hfeq, hxeq]
      _ = T' := Finset.insert_erase hx'
  calc r * V.card = S.card := hScard.symm
    _ ≤ (M.powersetCard (r - 1)).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = M.card.choose (r - 1) := Finset.card_powersetCard _ _

variable {p : ℕ} [Fact p.Prime] {n ν r k : ℕ} {g lam : ZMod p} {dom : Fin n ↪ ZMod p}

/-- **THE GENERAL-RATE FIBRE CAP**: `r ·` (the number of valid `r`-fibre sets) `≤ C(n/2, r−1)`. -/
theorem ladder_fibre_card_mul_le (hr : 1 ≤ r) (hν : 1 ≤ ν)
    (hg : IsPrimitiveRoot g (2 ^ ν)) (hn : n = 2 ^ ν) :
    r * (((muHalf p n).powersetCard r).filter (fun T => ∑ t ∈ T, t = -lam)).card
      ≤ (n / 2).choose (r - 1) := by
  rw [← muHalf_card (p := p) hν hg hn]
  exact subset_sum_fibre_card_mul_le (muHalf p n) (-lam) hr

open Classical in
/-- **THE LADDER CLIFF AT EVERY RATE**: over `μ_n ⊂ ZMod p` (`p > (2r)^{2^{ν−1}}`), the
ladder word `x^{2r} + λx^{2r−2}`'s agreement-`≥ 2r` codeword list `Lst` obeys
`r · #Lst ≤ C(n/2, r−1)` — polynomial sub-Johnson list at every rate. -/
theorem ladder_list_card_mul_le (hr : 1 ≤ r) (hν : 1 ≤ ν) (hg : IsPrimitiveRoot g (2 ^ ν))
    (hn : n = 2 ^ ν) (hroot : ∀ i, (dom i) ^ n = 1) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * r - 2)
    (hk3 : 2 * r - 3 ≤ k) (hp : (2 * r) ^ 2 ^ (ν - 1) < p) :
    r * ((Finset.univ : Finset (Fin n → ZMod p)).filter
        (fun c => c ∈ (rsCode dom k : Submodule (ZMod p) (Fin n → ZMod p)) ∧
          2 * r ≤ (Finset.univ.filter
            (fun i => c i = ladderWord dom r lam i)).card)).card
      ≤ (n / 2).choose (r - 1) := by
  classical
  have hnhalf : 0 < n / 2 := by
    rw [hn]
    have h1 : (2 : ℕ) ^ ν = 2 * 2 ^ (ν - 1) := by
      conv_lhs => rw [show ν = (ν - 1) + 1 by omega, pow_succ']
    have h2 : 0 < 2 ^ (ν - 1) := Nat.two_pow_pos _
    omega
  set FIB := ((muHalf p n).powersetCard r).filter (fun T => ∑ t ∈ T, t = -lam) with hFIB
  have hlisteq : ((Finset.univ : Finset (Fin n → ZMod p)).filter
      (fun c => c ∈ (rsCode dom k : Submodule (ZMod p) (Fin n → ZMod p)) ∧
        2 * r ≤ (Finset.univ.filter
          (fun i => c i = ladderWord dom r lam i)).card))
      = FIB.image (ladderFibreCodeword dom r lam) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hFIB]
    rw [ladder_list_iff hν hg hn hroot hk1 hk2 hk3 hp c]
    constructor
    · rintro ⟨T, hTcard, hTmu, hTsum, rfl⟩
      exact ⟨T, ⟨Finset.mem_powersetCard.mpr ⟨fun t ht =>
        (mem_muHalf hnhalf).mpr (hTmu t ht), hTcard⟩, hTsum⟩, rfl⟩
    · rintro ⟨T, ⟨hTpow, hTsum⟩, rfl⟩
      obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTpow
      exact ⟨T, hTcard, fun t ht => (mem_muHalf hnhalf).mp (hTsub ht), hTsum, rfl⟩
  rw [hlisteq]
  calc r * (FIB.image (ladderFibreCodeword dom r lam)).card
      ≤ r * FIB.card := Nat.mul_le_mul_left r Finset.card_image_le
    _ ≤ (n / 2).choose (r - 1) := ladder_fibre_card_mul_le hr hν hg hn

end ProximityGap.LadderList

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.LadderList.subset_sum_fibre_card_mul_le
#print axioms ProximityGap.LadderList.ladder_fibre_card_mul_le
#print axioms ProximityGap.LadderList.ladder_list_card_mul_le
