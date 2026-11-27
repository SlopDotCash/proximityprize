/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._SYZ21ShorteningAndCoverage
import ArkLib.Research.ProximityGap.Frontier._SYZ43AutoInstantiation

/-!
# Multiplicity-3 Twisted-Syzygy Confinement and Determinantal Union-Rank (`hrank`)

This module proves the algebraic and determinantal structure of G87 twisted syndrome syzygies for
Reed–Solomon witness families (`DOSSIER.md` §3.2 F3, `_SYZ43AutoInstantiation.lean`):

1. **Multiplicity-3 Support Confinement (`twisted_syzygy_confined_to_multThree`).**
   For any witness-support family `S : Fin r → Finset ι`, injective scalar tuple `γ : Fin r → F`,
   and anchored linear functionals `L_i` satisfying `∑ L_i = 0` and `∑ γ_i • L_i = 0`, every `L_a`
   vanishes on all standard basis vectors `Pi.single x 1` outside the multiplicity-`≥ 3` locus
   `multThreeLocus S = {x | 3 ≤ #{i | x ∈ S_i}}`.
2. **Vandermonde / Lagrange Leaf Elimination and Iterated Peeling (`rs_twisted_syzygy_leaf_zero`,
   `peeled_bridge_linearIndependent`).**
   On `RS[α, k]`, if `(S_a ∩ multThreeLocus S).card ≤ k`, Lagrange interpolation
   (`ArkLib.CS25.evalOnS_surjective`) forces `L_a = 0`. Iterating across any
   `PeeledSupportFamily k S` proves `LinearIndependent F` for the anchored G87 bridge functionals
   without `SYZ56` overlap chaining (working even when every pairwise intersection satisfies
   `|S_i ∩ S_j| < k`).
3. **Unconditional 3-Witness Full Rank and `n = 2^30` `hrank` Realizations
   (`three_witness_bridge_linearIndependent`, `hrank_of_peeled_tight_cover`,
   `production_k4Tight_hrank`, `production_subKOverlap_linearIndependent`).**
   - Every 3-witness family with `|S_0 ∩ S_1 ∩ S_2| ≤ k` and injective `γ` is `LinearIndependent`
     in `Module.Dual F (SyndromePair (RS[α, k]))` (single-copy polynomial syzygies disappear under
     the `γ`-twist).
   - Every peeled tight cover (`∑ (|S_i| - k) = 2(|U| - k)`) realizes exact `hrank`
     `finrank F (span (range φ)) = 2(|U| - k)`, discharging `SYZ43`'s `hrank` hypothesis and
     forcing `|U| ≤ n - 1` on non-codeword stacks.
   - Explicit `n = 2^30, k = 2^29, t = 715827884` strip families certify both exact `hrank`
     (`715827888 = 2(894784856 - 2^29)`) and full G87 rank with strictly sub-`k` pairwise overlaps
     (`477218590 < 2^29`).
4. **Full-Domain Rank-Deficiency Boundary (`plantable_cannot_realize_full_domain_hrank`).**
   For any non-codeword stack `(u₀, u₁)`, no annihilating functional family can realize `hrank`
   at `Ucard = n` (`finrank ≤ 2(n - k) - 1 < 2(n - k)`).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CarbonSYZMultiplicityThreeHrank

open Finset Polynomial Module Submodule
open ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge
open ArkLib.ProximityGap.SYZ42
open ArkLib.ProximityGap.SYZ43

/-! ## 1. Multiplicity-3 support confinement of twisted G87 syzygies -/

section Confinement

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A linear functional `ℓ` on `ι → F` is anchored on `S : Finset ι` if it vanishes on every
coordinate basis vector outside `S`. -/
def AnchoredOn (S : Finset ι) (ℓ : Module.Dual F (ι → F)) : Prop :=
  ∀ x : ι, x ∉ S → ℓ (Pi.single x 1) = 0

/-- If `ℓ` vanishes on all basis vectors outside `K_set` and `v` vanishes on `K_set`, `ℓ v = 0`. -/
theorem apply_eq_zero_of_eq_zero_on (K_set : Finset ι) (ℓ : Module.Dual F (ι → F))
    (hsupp : ∀ x : ι, x ∉ K_set → ℓ (Pi.single x 1) = 0)
    {v : ι → F} (hv0 : ∀ x ∈ K_set, v x = 0) :
    ℓ v = 0 := by
  have hv_sum : v = ∑ x : ι, v x • (Pi.single x (1 : F) : ι → F) := by
    funext y
    rw [Finset.sum_apply, Finset.sum_eq_single y]
    · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro x _ hxy
      rw [Pi.smul_apply, Pi.single_apply]
      split_ifs with h
      · exact False.elim (hxy h.symm)
      · simp only [smul_eq_mul, mul_zero]
    · intro hy
      exact False.elim (hy (Finset.mem_univ y))
  rw [hv_sum, map_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x ∈ K_set
  · rw [map_smul, hv0 x hx, zero_smul]
  · rw [map_smul, hsupp x hx, smul_zero]

/-- The multiplicity-`≥ 3` coordinate locus of a support family `S : Fin r → Finset ι`. -/
def multThreeLocus {r : ℕ} (S : Fin r → Finset ι) : Finset ι :=
  Finset.univ.filter (fun x : ι => 3 ≤ (Finset.univ.filter (fun i : Fin r => x ∈ S i)).card)

/-- **Multiplicity-3 Support Confinement Theorem.**
If `γ : Fin r → F` is injective, each `L i` is anchored on `S i`, `∑ L i = 0`, and
`∑ γ i • L i = 0`, then every `L a` vanishes on every coordinate `x ∉ multThreeLocus S`. -/
theorem twisted_syzygy_confined_to_multThree {r : ℕ} {S : Fin r → Finset ι}
    {γ : Fin r → F} (hγ : Function.Injective γ)
    {L : Fin r → Module.Dual F (ι → F)} (hanch : ∀ i, AnchoredOn (S i) (L i))
    (hsum0 : ∑ i : Fin r, L i = 0) (hsum1 : ∑ i : Fin r, γ i • L i = 0)
    (a : Fin r) (x : ι) (hx : x ∉ multThreeLocus S) :
    L a (Pi.single x 1) = 0 := by
  by_cases hxa : x ∈ S a
  · set fib : Finset (Fin r) := Finset.univ.filter (fun i : Fin r => x ∈ S i)
    have hlt3 : fib.card < 3 := by
      by_contra hge
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, Nat.le_of_not_lt hge⟩)
    have ha_fib : a ∈ fib := Finset.mem_filter.mpr ⟨Finset.mem_univ a, hxa⟩
    by_cases hemp : fib.erase a = ∅
    · have hval0 : (∑ i : Fin r, L i) (Pi.single x 1) = 0 := by
        rw [hsum0, LinearMap.zero_apply]
      rw [LinearMap.sum_apply, Finset.sum_eq_single a] at hval0
      · exact hval0
      · intro i _ hia
        have hi_not_fib : i ∉ fib := by
          intro hif
          have hmem : i ∈ fib.erase a := Finset.mem_erase.mpr ⟨hia, hif⟩
          rw [hemp] at hmem
          simp at hmem
        exact hanch i x fun hxi => hi_not_fib (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxi⟩)
      · intro ha_univ
        exact False.elim (ha_univ (Finset.mem_univ a))
    · obtain ⟨b, hb_erase⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hba : b ≠ a := (Finset.mem_erase.mp hb_erase).1
      have herase_le : (fib.erase a).card ≤ 1 := by
        have hcard_er := Finset.card_erase_of_mem ha_fib
        omega
      have hother : ∀ i : Fin r, i ≠ a → i ≠ b → L i (Pi.single x 1) = 0 := by
        intro i hia hib
        have hi_not_fib : i ∉ fib := by
          intro hif
          have hi_er : i ∈ fib.erase a := Finset.mem_erase.mpr ⟨hia, hif⟩
          have hpair_sub : ({b, i} : Finset (Fin r)) ⊆ fib.erase a := by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact hb_erase
            · exact hi_er
          have h2 : 2 ≤ (fib.erase a).card := by
            have hc := Finset.card_le_card hpair_sub
            rwa [Finset.card_pair hib.symm] at hc
          omega
        exact hanch i x fun hxi => hi_not_fib (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxi⟩)
      have helim : (∑ i : Fin r, (γ i - γ b) * L i (Pi.single x 1)) = 0 := by
        have h0 := congrArg (fun f : Module.Dual F (ι → F) => f (Pi.single x 1)) hsum0
        have h1 := congrArg (fun f : Module.Dual F (ι → F) => f (Pi.single x 1)) hsum1
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
          smul_eq_mul] at h0 h1
        have hlin :
            (∑ i : Fin r, (γ i - γ b) * L i (Pi.single x 1)) =
              (∑ i : Fin r, γ i * L i (Pi.single x 1)) -
                γ b * (∑ i : Fin r, L i (Pi.single x 1)) := by
          simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
        rw [hlin, h1, h0, mul_zero, sub_zero]
      rw [Finset.sum_eq_single a] at helim
      · have hdiff_ne : γ a - γ b ≠ 0 := sub_ne_zero.mpr fun hab => hba (hγ hab).symm
        exact (mul_eq_zero.mp helim).resolve_left hdiff_ne
      · intro i _ hia
        by_cases hib : i = b
        · subst hib
          rw [sub_self, zero_mul]
        · rw [hother i hia hib, mul_zero]
      · intro ha_univ
        exact False.elim (ha_univ (Finset.mem_univ a))
  · exact hanch a x hxa

end Confinement

/-! ## 2. Vandermonde leaf elimination, iterated peeling, and anchored G87 bridge functionals -/

section RSPeelingAndBridge

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Vandermonde / Lagrange Leaf Elimination on `ReedSolomon.code α k`.**
If `L_a` participates in an injective-`γ` twisted syzygy of `RS[α, k]`-annihilating anchored
functionals and `(S a ∩ multThreeLocus S).card ≤ k`, then `L a = 0`. -/
theorem rs_twisted_syzygy_leaf_zero (α : ι ↪ F) (k : ℕ) {r : ℕ} {S : Fin r → Finset ι}
    {γ : Fin r → F} (hγ : Function.Injective γ)
    {L : Fin r → Module.Dual F (ι → F)}
    (hanch : ∀ i, AnchoredOn (S i) (L i))
    (hannC : ∀ i, ∀ c ∈ ReedSolomon.code α k, L i c = 0)
    (hsum0 : ∑ i : Fin r, L i = 0) (hsum1 : ∑ i : Fin r, γ i • L i = 0)
    {a : Fin r} (hcard : (S a ∩ multThreeLocus S).card ≤ k) :
    L a = 0 := by
  apply LinearMap.ext
  intro v
  set Ka : Finset ι := S a ∩ multThreeLocus S
  have hsupp : ∀ x : ι, x ∉ Ka → L a (Pi.single x 1) = 0 := by
    intro x hxKa
    by_cases hxs : x ∈ S a
    · have hxm3 : x ∉ multThreeLocus S := fun hm3 => hxKa (Finset.mem_inter.mpr ⟨hxs, hm3⟩)
      exact twisted_syzygy_confined_to_multThree hγ hanch hsum0 hsum1 a x hxm3
    · exact hanch a x hxs
  obtain ⟨p, hp_eval⟩ := ArkLib.CS25.evalOnS_surjective α k Ka hcard (fun s : ↥Ka => v (s : ι))
  set c : ι → F := ReedSolomon.evalOnPoints α (p : F[X])
  have hc_mem : c ∈ ReedSolomon.code α k := Submodule.mem_map.mpr ⟨(p : F[X]), p.2, rfl⟩
  have hdiff0 : ∀ x ∈ Ka, (v - c) x = 0 := by
    intro x hx
    have hpx : (p : F[X]).eval (α x) = v x := congrFun hp_eval ⟨x, hx⟩
    change v x - (p : F[X]).eval (α x) = 0
    rw [hpx, sub_self]
  have hLa_diff : L a (v - c) = 0 := apply_eq_zero_of_eq_zero_on Ka (L a) hsupp hdiff0
  have hv_split : v = (v - c) + c := (sub_add_cancel v c).symm
  rw [hv_split, map_add, hLa_diff, hannC a c hc_mem, add_zero, LinearMap.zero_apply]

/-- Recursive multiplicity-3 leaf-peeling predicate on `S : Fin r → Finset ι`: at each prefix
length `m + 1`, `S (Fin.last m)` meets `multThreeLocus` of the prefix in at most `k` points. -/
def PeeledSupportFamily (k : ℕ) : ∀ {r : ℕ}, (Fin r → Finset ι) → Prop
  | 0, _ => True
  | r + 1, S =>
    (S (Fin.last r) ∩ multThreeLocus S).card ≤ k ∧
      PeeledSupportFamily k (fun i : Fin r => S i.castSucc)

theorem multThreeLocus_castSucc_subset {r : ℕ} (S : Fin (r + 1) → Finset ι) :
    multThreeLocus (fun i : Fin r => S i.castSucc) ⊆ multThreeLocus S := by
  intro x hx
  rw [multThreeLocus, Finset.mem_filter] at hx ⊢
  refine ⟨Finset.mem_univ x, hx.2.trans ?_⟩
  have hinj : Function.Injective (Fin.castSucc : Fin r → Fin (r + 1)) := Fin.castSucc_injective r
  calc (Finset.univ.filter (fun i : Fin r => x ∈ S i.castSucc)).card
      = ((Finset.univ.filter (fun i : Fin r => x ∈ S i.castSucc)).map
          ⟨Fin.castSucc, hinj⟩).card := (Finset.card_map _).symm
    _ ≤ (Finset.univ.filter (fun j : Fin (r + 1) => x ∈ S j)).card := by
        refine Finset.card_le_card fun j hj => ?_
        rcases Finset.mem_map.mp hj with ⟨i, hi, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩

/-- Global multiplicity-3 bound `(multThreeLocus S).card ≤ k` implies `PeeledSupportFamily k S`. -/
theorem peeledSupportFamily_of_multThreeLocus_card_le {k : ℕ} :
    ∀ {r : ℕ} (S : Fin r → Finset ι), (multThreeLocus S).card ≤ k → PeeledSupportFamily k S
  | 0, _, _ => trivial
  | r + 1, S, hcard => by
    refine ⟨(Finset.card_le_card Finset.inter_subset_right).trans hcard, ?_⟩
    exact peeledSupportFamily_of_multThreeLocus_card_le (fun i : Fin r => S i.castSucc)
      ((Finset.card_le_card (multThreeLocus_castSucc_subset S)).trans hcard)

/-- **Iterated Multiplicity-3 Peeling Theorem.**
Every `PeeledSupportFamily k S` over `RS[α, k]` with injective scalars `γ` has no nontrivial
anchored twisted syzygies (`∀ i, L i = 0`). -/
theorem peeled_twisted_syzygy_zero (α : ι ↪ F) (k : ℕ) :
    ∀ {r : ℕ} {S : Fin r → Finset ι} (_hpeel : PeeledSupportFamily k S)
      {γ : Fin r → F} (_hγ : Function.Injective γ)
      {L : Fin r → Module.Dual F (ι → F)}
      (_hanch : ∀ i, AnchoredOn (S i) (L i))
      (_hannC : ∀ i, ∀ c ∈ ReedSolomon.code α k, L i c = 0)
      (_hsum0 : ∑ i : Fin r, L i = 0) (_hsum1 : ∑ i : Fin r, γ i • L i = 0)
      (i : Fin r), L i = 0
  | 0, _, _, _, _, _, _, _, _, _, i => Fin.elim0 i
  | r + 1, S, ⟨hlast_card, hrest_peel⟩, γ, hγ, L, hanch, hannC, hsum0, hsum1, i => by
    have hlast0 : L (Fin.last r) = 0 :=
      rs_twisted_syzygy_leaf_zero α k hγ hanch hannC hsum0 hsum1 hlast_card
    have hsum0' : ∑ j : Fin r, L j.castSucc = 0 := by
      rw [Fin.sum_univ_castSucc, hlast0, add_zero] at hsum0
      exact hsum0
    have hsum1' : ∑ j : Fin r, γ j.castSucc • L j.castSucc = 0 := by
      rw [Fin.sum_univ_castSucc, hlast0, smul_zero, add_zero] at hsum1
      exact hsum1
    have hrest0 : ∀ j : Fin r, L j.castSucc = 0 :=
      peeled_twisted_syzygy_zero α k hrest_peel (hγ.comp (Fin.castSucc_injective r))
        (fun j => hanch j.castSucc) (fun j => hannC j.castSucc) hsum0' hsum1'
    exact Fin.lastCases hlast0 hrest0 i

/-- Lift per-witness `C`-annihilating functionals `ℓ i j` with weights `γ i` to the G87 syndrome
pair space `SyndromePair C`. -/
noncomputable def liftAnchoredBridge (C : Submodule F (ι → F)) {r : ℕ} {m : Fin r → ℕ}
    (γ : Fin r → F) (ℓ : ∀ i : Fin r, Fin (m i) → Module.Dual F (ι → F))
    (hker : ∀ i j, C ≤ LinearMap.ker (ℓ i j)) :
    (Σ i : Fin r, Fin (m i)) → Module.Dual F (SyndromePair C) :=
  fun p =>
    (C.liftQ (ℓ p.1 p.2) (hker p.1 p.2)).comp (LinearMap.fst F _ _) +
      γ p.1 • (C.liftQ (ℓ p.1 p.2) (hker p.1 p.2)).comp (LinearMap.snd F _ _)

omit [DecidableEq F] [Fintype ι] in
/-- If each per-witness block `ℓ i` is linearly independent and no nontrivial anchored twisted
syzygy exists, then `liftAnchoredBridge` is globally `LinearIndependent F`. -/
theorem liftAnchoredBridge_linearIndependent_of_no_twisted_syzygy
    (C : Submodule F (ι → F)) {r : ℕ} {S : Fin r → Finset ι} {m : Fin r → ℕ}
    (γ : Fin r → F) (ℓ : ∀ i : Fin r, Fin (m i) → Module.Dual F (ι → F))
    (hli : ∀ i, LinearIndependent F (ℓ i))
    (hanch : ∀ i j, AnchoredOn (S i) (ℓ i j))
    (hker : ∀ i j, C ≤ LinearMap.ker (ℓ i j))
    (hkill : ∀ L : Fin r → Module.Dual F (ι → F),
      (∀ i, AnchoredOn (S i) (L i)) →
      (∀ i, ∀ c ∈ C, L i c = 0) →
      ∑ i : Fin r, L i = 0 →
      ∑ i : Fin r, γ i • L i = 0 →
      ∀ i, L i = 0) :
    LinearIndependent F (liftAnchoredBridge C γ ℓ hker) := by
  rw [Fintype.linearIndependent_iff]
  intro cc hcc
  set L : Fin r → Module.Dual F (ι → F) := fun i => ∑ j : Fin (m i), cc ⟨i, j⟩ • ℓ i j
  have hL_anch : ∀ i, AnchoredOn (S i) (L i) := by
    intro i x hx
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, hanch i _ x hx, smul_zero,
      Finset.sum_const_zero]
  have hL_ann : ∀ i, ∀ c ∈ C, L i c = 0 := by
    intro i c hc
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.mem_ker.mp (hker i _ hc), smul_zero, Finset.sum_const_zero]
  have hsum0 : ∑ i : Fin r, L i = 0 := by
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun f => f ((C.mkQ v, 0) : SyndromePair C)) hcc
    simp only [liftAnchoredBridge, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.zero_apply,
      Submodule.mkQ_apply, Submodule.liftQ_apply, map_zero, smul_zero, add_zero] at hv
    rw [Fintype.sum_sigma] at hv
    simpa only [L, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] using hv
  have hsum1 : ∑ i : Fin r, γ i • L i = 0 := by
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun f => f ((0, C.mkQ v) : SyndromePair C)) hcc
    simp only [liftAnchoredBridge, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.zero_apply,
      Submodule.mkQ_apply, Submodule.liftQ_apply, map_zero, zero_add] at hv
    rw [Fintype.sum_sigma] at hv
    have hswap :
        (∑ i : Fin r, ∑ j : Fin (m i), cc ⟨i, j⟩ • (γ i • (ℓ i j) v)) =
          (∑ i : Fin r, γ i • ∑ j : Fin (m i), cc ⟨i, j⟩ • (ℓ i j) v) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [smul_eq_mul]
      ring
    rw [hswap] at hv
    simpa only [L, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] using hv
  have hL0 : ∀ i, L i = 0 := hkill L hL_anch hL_ann hsum0 hsum1
  rintro ⟨i, j⟩
  exact Fintype.linearIndependent_iff.mp (hli i) (fun j' => cc ⟨i, j'⟩) (hL0 i) j

/-- **Exact MDS-shortening anchored row functionals on `ReedSolomon.code α k`.**
For any `S : Finset ι` with `k ≤ S.card`, there exist `S.card - k` linearly independent functionals
on `ι → F` anchored on `S` and annihilating `RS[α, k]` (and vanishing on `u₀ + γ • u₁` whenever a
codeword agrees with `u₀ + γ • u₁` on `S`). -/
theorem exists_anchored_rs_rowFunctionals (α : ι ↪ F) (k : ℕ) {S : Finset ι}
    (hS : k ≤ S.card) :
    ∃ ℓ : Fin (S.card - k) → Module.Dual F (ι → F),
      LinearIndependent F ℓ ∧
      (∀ j, AnchoredOn S (ℓ j)) ∧
      (∀ j, ∀ c ∈ ReedSolomon.code α k, ℓ j c = 0) ∧
      (∀ (u₀ u₁ : ι → F) (γ : F),
        (∃ c ∈ ReedSolomon.code α k, ∀ x ∈ S, c x = u₀ x + γ * u₁ x) →
        ∀ j, ℓ j (u₀ + γ • u₁) = 0) := by
  classical
  set C := ReedSolomon.code α k
  set res : (ι → F) →ₗ[F] ((↥S : Type _) → F) :=
    LinearMap.funLeft F F (fun s : ↥S => (s : ι))
  set M : Submodule F ((↥S : Type _) → F) := C.map res
  set π : (ι → F) →ₗ[F] (((↥S : Type _) → F) ⧸ M) := M.mkQ.comp res
  have hπsurj : Function.Surjective π :=
    (Submodule.mkQ_surjective M).comp
      (LinearMap.funLeft_surjective_of_injective F F _ Subtype.val_injective)
  have hM_eq : M = LinearMap.range (ArkLib.CS25.evalOnS α k S) := by
    ext w
    simp only [M, C, ReedSolomon.code, Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
    · rintro ⟨⟨p, hp⟩, rfl⟩
      exact ⟨ReedSolomon.evalOnPoints α p, ⟨p, hp, rfl⟩, rfl⟩
  have hM_fr : Module.finrank F M = k := by
    rw [hM_eq]
    exact ArkLib.ProximityGap.Frontier.SYZ21.punctureDim_of_le_card α k S hS
  have hdimS : Module.finrank F ((↥S : Type _) → F) = S.card := by
    rw [Module.finrank_pi, Fintype.card_coe]
  have hqM := Submodule.finrank_quotient_add_finrank M
  have hdual : Module.finrank F (Module.Dual F (((↥S : Type _) → F) ⧸ M)) = S.card - k := by
    rw [Subspace.dual_finrank_eq]
    omega
  set b := Module.finBasis F (Module.Dual F (((↥S : Type _) → F) ⧸ M))
  set eIdx : Fin (S.card - k) ≃
      Fin (Module.finrank F (Module.Dual F (((↥S : Type _) → F) ⧸ M))) := finCongr hdual.symm
  set lam : Fin (S.card - k) → Module.Dual F (((↥S : Type _) → F) ⧸ M) := fun j => b (eIdx j)
  have hlam_li : LinearIndependent F lam := b.linearIndependent.comp _ eIdx.injective
  refine ⟨fun j => (lam j).comp π, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro a ha
    have hlam0 : ∑ j, a j • lam j = 0 := by
      apply LinearMap.ext
      intro q
      obtain ⟨v, rfl⟩ := hπsurj q
      have hv := congrArg (fun f => f v) ha
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.zero_apply] using hv
    exact Fintype.linearIndependent_iff.mp hlam_li a hlam0
  · intro j x hx
    have hres0 : res (Pi.single x (1 : F) : ι → F) = 0 := by
      funext s
      rw [LinearMap.funLeft_apply, Pi.zero_apply, Pi.single_apply]
      split_ifs with hsx
      · exact False.elim (hx (hsx ▸ s.2))
      · rfl
    simp only [π, LinearMap.comp_apply, hres0, map_zero]
  · intro j c hc
    have hπc : π c = 0 := by
      simp only [π, LinearMap.comp_apply, Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero M).mpr (Submodule.mem_map_of_mem hc)
    simp only [LinearMap.comp_apply, hπc, map_zero]
  · intro u₀ u₁ γ ⟨c, hcC, hc_eq⟩ j
    have hres_line : res (u₀ + γ • u₁) = res c := by
      funext s
      simpa only [res, LinearMap.funLeft_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
        (hc_eq (s : ι) s.2).symm
    have hπline : π (u₀ + γ • u₁) = 0 := by
      simp only [π, LinearMap.comp_apply, hres_line, Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero M).mpr (Submodule.mem_map_of_mem hcC)
    simp only [LinearMap.comp_apply, hπline, map_zero]

/-- **Peeled-Family G87 Full-Rank Theorem.**
For any `PeeledSupportFamily k S` (`k ≤ (S i).card`) on `RS[α, k]` and injective `γ : Fin r → F`,
there exists an anchored G87 bridge family
`φ : (Σ i : Fin r, Fin ((S i).card - k)) → Module.Dual F (SyndromePair (RS[α, k]))` that is
**`LinearIndependent F φ`** (exact span dimension `∑ i, ((S i).card - k)`) and annihilates
`syndromePair (RS[α, k]) u₀ u₁` whenever each `u₀ + γ i • u₁` agrees with a codeword on `S i`. -/
theorem peeled_bridge_linearIndependent (α : ι ↪ F) (k : ℕ) {r : ℕ}
    {S : Fin r → Finset ι} (hS : ∀ i, k ≤ (S i).card) (hpeel : PeeledSupportFamily k S)
    {γ : Fin r → F} (hγ : Function.Injective γ) :
    ∃ φ : (Σ i : Fin r, Fin ((S i).card - k)) →
        Module.Dual F (SyndromePair (ReedSolomon.code α k)),
      LinearIndependent F φ ∧
      Module.finrank F (Submodule.span F (Set.range φ)) = ∑ i : Fin r, ((S i).card - k) ∧
      ∀ (u₀ u₁ : ι → F),
        (∀ i, ∃ c ∈ ReedSolomon.code α k, ∀ x ∈ S i, c x = u₀ x + γ i * u₁ x) →
        ∀ p, φ p (syndromePair (ReedSolomon.code α k) u₀ u₁) = 0 := by
  classical
  choose ℓ hli hanch hann hline using fun i => exists_anchored_rs_rowFunctionals α k (hS i)
  have hker : ∀ i j, ReedSolomon.code α k ≤ LinearMap.ker (ℓ i j) := fun i j c hc =>
    LinearMap.mem_ker.mpr (hann i j c hc)
  set φ := liftAnchoredBridge (ReedSolomon.code α k) γ ℓ hker
  have hφ_li : LinearIndependent F φ :=
    liftAnchoredBridge_linearIndependent_of_no_twisted_syzygy (ReedSolomon.code α k) γ ℓ hli hanch
      hker fun L hLa hLc hs0 hs1 =>
        peeled_twisted_syzygy_zero α k hpeel hγ hLa hLc hs0 hs1
  have hφ_fr : Module.finrank F (Submodule.span F (Set.range φ)) =
      ∑ i : Fin r, ((S i).card - k) := by
    rw [finrank_span_eq_card hφ_li, Fintype.card_sigma]
    simp only [Fintype.card_fin]
  refine ⟨φ, hφ_li, hφ_fr, fun u₀ u₁ hwit p => ?_⟩
  have hl := hline p.1 u₀ u₁ (γ p.1) (hwit p.1) p.2
  rw [map_add, map_smul] at hl
  simpa only [φ, liftAnchoredBridge, syndromePair, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, Submodule.mkQ_apply,
    Submodule.liftQ_apply] using hl

end RSPeelingAndBridge

/-! ## 3. Three-witness unconditional independence and `hrank` on peeled tight covers -/

section ThreeWitnessAndHrank

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For `r = 3` supports, `multThreeLocus S` equals the triple intersection `S 0 ∩ S 1 ∩ S 2`. -/
theorem multThreeLocus_three_eq_inter (S : Fin 3 → Finset ι) :
    multThreeLocus S = S 0 ∩ S 1 ∩ S 2 := by
  ext x
  simp only [multThreeLocus, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · intro h3
    have hall : Finset.univ.filter (fun i : Fin 3 => x ∈ S i) = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        (by simpa only [Finset.card_univ, Fintype.card_fin] using h3)
    have hm : ∀ i : Fin 3, x ∈ S i := fun i => by
      have hi : i ∈ Finset.univ.filter (fun i : Fin 3 => x ∈ S i) := by
        rw [hall]
        exact Finset.mem_univ i
      exact (Finset.mem_filter.mp hi).2
    exact ⟨⟨hm 0, hm 1⟩, hm 2⟩
  · rintro ⟨⟨h0, h1⟩, h2⟩
    have hall : Finset.univ.filter (fun i : Fin 3 => x ∈ S i) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rcases i with ⟨_ | _ | _ | _, hi⟩
      · exact h0
      · exact h1
      · exact h2
      · omega
    rw [hall, Finset.card_univ, Fintype.card_fin]

/-- **Unconditional 3-Witness G87 Linear Independence (`|S₀ ∩ S₁ ∩ S₂| ≤ k`).**
Whenever `(S 0 ∩ S 1 ∩ S 2).card ≤ k` (automatic on every `RegionSyzygyRealizable` or `SYZ50`
witness) and `γ : Fin 3 → F` is injective, the G87 bridge functionals are `LinearIndependent F`
(single-copy polynomial syzygies disappear under the `γ`-twist!), forcing
`((S 0).card - k) + ((S 1).card - k) + ((S 2).card - k) + 1 ≤ 2 * (n - k)` on any non-codeword
stack `(u₀, u₁)` when `k ≤ n`. -/
theorem three_witness_bridge_linearIndependent (α : ι ↪ F) {k : ℕ}
    {S : Fin 3 → Finset ι} (hS : ∀ i, k ≤ (S i).card)
    (htriple : (S 0 ∩ S 1 ∩ S 2).card ≤ k)
    {γ : Fin 3 → F} (hγ : Function.Injective γ) :
    ∃ φ : (Σ i : Fin 3, Fin ((S i).card - k)) →
        Module.Dual F (SyndromePair (ReedSolomon.code α k)),
      LinearIndependent F φ ∧
      Module.finrank F (Submodule.span F (Set.range φ)) =
        ((S 0).card - k) + ((S 1).card - k) + ((S 2).card - k) ∧
      ∀ (u₀ u₁ : ι → F),
        (u₀ ∉ ReedSolomon.code α k ∨ u₁ ∉ ReedSolomon.code α k) →
        (∀ i, ∃ c ∈ ReedSolomon.code α k, ∀ x ∈ S i, c x = u₀ x + γ i * u₁ x) →
        ((S 0).card - k) + ((S 1).card - k) + ((S 2).card - k) + 1 ≤
          2 * (Fintype.card ι - Module.finrank F (ReedSolomon.code α k)) := by
  have hm3 : (multThreeLocus S).card ≤ k := by
    rwa [multThreeLocus_three_eq_inter]
  obtain ⟨φ, hli, hfr, hann⟩ :=
    peeled_bridge_linearIndependent α k hS (peeledSupportFamily_of_multThreeLocus_card_le S hm3) hγ
  have hsum3 : (∑ i : Fin 3, ((S i).card - k)) =
      ((S 0).card - k) + ((S 1).card - k) + ((S 2).card - k) := by
    rw [Fin.sum_univ_three]
  rw [hsum3] at hfr
  refine ⟨φ, hli, hfr, fun u₀ u₁ hstack hwit => ?_⟩
  have hne : syndromePair (ReedSolomon.code α k) u₀ u₁ ≠ 0 := by
    rw [Ne, syndromePair_eq_zero_iff]
    rcases hstack with h | h
    · exact fun hc => h hc.1
    · exact fun hc => h hc.2
  have hcap := ArkLib.ProximityGap.Frontier.SYZ20JointRankSuperadditive.plantable_span_cap hne
    (Set.range φ) (by rintro _ ⟨p, rfl⟩; exact hann u₀ u₁ hwit p)
  rwa [hfr, finrank_syndromePair] at hcap

/-- **Exact `hrank` Realization and `RealizabilityCore` Discharge for Peeled Tight Covers.**
If a `PeeledSupportFamily k S` with support union `U = Finset.univ.biUnion S` satisfies the tight
double-shortening identity `∑ i, ((S i).card - k) = 2 * (U.card - k)`, the G87 bridge functionals
satisfy `finrank F (span (range φ)) = 2 * (U.card - k)` (`SYZ43`'s `hrank`!), constructing
`SYZ42.RealizabilityCore` and forcing `U.card ≤ n - 1` on any non-codeword stack when `k ≤ n`. -/
theorem hrank_and_realizabilityCore_of_peeled_tight_cover (α : ι ↪ F) {n k : ℕ}
    (hn : Fintype.card ι = n) (hk : k ≤ n)
    {r : ℕ} {S : Fin r → Finset ι} (hS : ∀ i, k ≤ (S i).card)
    (hpeel : PeeledSupportFamily k S)
    (htight : ∑ i : Fin r, ((S i).card - k) = 2 * ((Finset.univ.biUnion S).card - k))
    {γ : Fin r → F} (hγ : Function.Injective γ) :
    ∃ φ : (Σ i : Fin r, Fin ((S i).card - k)) →
        Module.Dual F (SyndromePair (ReedSolomon.code α k)),
      Module.finrank F (Submodule.span F (Set.range φ)) =
        2 * ((Finset.univ.biUnion S).card - k) ∧
      ∀ (u₀ u₁ : ι → F),
        (u₀ ∉ ReedSolomon.code α k ∨ u₁ ∉ ReedSolomon.code α k) →
        (∀ i, ∃ c ∈ ReedSolomon.code α k, ∀ x ∈ S i, c x = u₀ x + γ i * u₁ x) →
        Nonempty
            (RealizabilityCore (K := F) (V := SyndromePair (ReedSolomon.code α k))
              n k (Finset.univ.biUnion S).card) ∧
          2 * ((Finset.univ.biUnion S).card - k) + 1 ≤ 2 * (n - k) := by
  obtain ⟨φ, _hli, hfr, hann⟩ := peeled_bridge_linearIndependent α k hS hpeel hγ
  have hrank : Module.finrank F (Submodule.span F (Set.range φ)) =
      2 * ((Finset.univ.biUnion S).card - k) := hfr.trans htight
  have hk_code : Module.finrank F (ReedSolomon.code α k) = k := by
    have hU := ArkLib.ProximityGap.Frontier.SYZ21.punctureDim_of_le_card α k Finset.univ
      (by rw [Finset.card_univ, hn]; exact hk)
    let resU : (ι → F) →ₗ[F] (↥(Finset.univ : Finset ι) → F) :=
      LinearMap.funLeft F F (fun s : ↥(Finset.univ : Finset ι) => (s : ι))
    let fU : ReedSolomon.code α k →ₗ[F] (↥(Finset.univ : Finset ι) → F) :=
      resU.comp (ReedSolomon.code α k).subtype
    have hrange : LinearMap.range fU = LinearMap.range (ArkLib.CS25.evalOnS α k Finset.univ) := by
      ext w
      simp only [fU, resU, ReedSolomon.code, LinearMap.mem_range,
        LinearMap.comp_apply, Submodule.coe_subtype]
      constructor
      · rintro ⟨⟨_, ⟨p, hp, rfl⟩⟩, rfl⟩
        exact ⟨⟨p, hp⟩, rfl⟩
      · rintro ⟨⟨p, hp⟩, rfl⟩
        exact ⟨⟨ReedSolomon.evalOnPoints α p, ⟨p, hp, rfl⟩⟩, rfl⟩
    have hker : LinearMap.ker fU = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro c hc
      rw [LinearMap.mem_ker] at hc
      apply Subtype.ext
      funext i
      exact congrFun hc ⟨i, Finset.mem_univ i⟩
    have : FiniteDimensional F (ι → F) := Module.Finite.pi
    have : FiniteDimensional F (ReedSolomon.code α k) :=
      FiniteDimensional.of_injective (ReedSolomon.code α k).subtype Subtype.val_injective
    have hrn := LinearMap.finrank_range_add_finrank_ker fU
    rw [hrange, hU, hker, finrank_bot, add_zero] at hrn
    exact hrn.symm
  refine ⟨φ, hrank, fun u₀ u₁ hstack hwit => ?_⟩
  let core :=
    realizabilityCore_of_overBudget_stack (ReedSolomon.code α k) hn hk_code hstack φ
      (hann u₀ u₁ hwit) hrank
  refine ⟨⟨core⟩, ?_⟩
  exact ArkLib.ProximityGap.Frontier.SYZ20JointRankSuperadditive.union_card_lt_length
    core.toSuperadditiveUnion

omit [DecidableEq F] in
/-- **Full-Domain `hrank` Obstruction (`|U| = n`).**
For any non-codeword stack `(u₀, u₁)` on `C : Submodule F (ι → F)` with `Fintype.card ι = n` and
`Module.finrank F C = k`, no family `φ` of functionals annihilating `syndromePair C u₀ u₁` can
realize `finrank F (span (range φ)) = 2 * (n - k)`. -/
theorem plantable_cannot_realize_full_domain_hrank (C : Submodule F (ι → F)) {n k : ℕ}
    (hn : Fintype.card ι = n) (hk : Module.finrank F C = k)
    {u₀ u₁ : ι → F} (hstack : u₀ ∉ C ∨ u₁ ∉ C)
    {D : Type*} (φ : D → Module.Dual F (SyndromePair C))
    (hann : ∀ p, φ p (syndromePair C u₀ u₁) = 0) :
    Module.finrank F (Submodule.span F (Set.range φ)) ≠ 2 * (n - k) := by
  intro hfull
  have hne : syndromePair C u₀ u₁ ≠ 0 := by
    rw [Ne, syndromePair_eq_zero_iff]
    rcases hstack with h | h
    · exact fun hc => h hc.1
    · exact fun hc => h hc.2
  have hcap := ArkLib.ProximityGap.Frontier.SYZ20JointRankSuperadditive.plantable_span_cap hne
    (Set.range φ) (by rintro _ ⟨p, rfl⟩; exact hann p)
  rw [hfull, finrank_syndromePair, hn, hk] at hcap
  omega

end ThreeWitnessAndHrank

/-! ## 4. Production `n = 2^30` strip realizations: exact `K_4` `hrank` & sub-`k` overlap rank -/

section ProductionRealizations

/-- Contiguous block `[start, start + len)` inside `Fin n`. -/
def finBlock {n : ℕ} (start len : ℕ) (h : start + len ≤ n) : Finset (Fin n) :=
  (Finset.range len).attach.map
    ⟨fun j => ⟨start + j.1, by have := Finset.mem_range.mp j.2; omega⟩,
      fun i j hij => Subtype.ext
        (by have h : start + i.1 = start + j.1 := congrArg Fin.val hij; omega)⟩

theorem card_finBlock {n : ℕ} (start len : ℕ) (h : start + len ≤ n) :
    (finBlock start len h).card = len := by
  rw [finBlock, Finset.card_map, Finset.card_attach, Finset.card_range]

@[simp]
theorem mem_finBlock {n : ℕ} {start len : ℕ} {h : start + len ≤ n} {x : Fin n} :
    x ∈ finBlock start len h ↔ start ≤ x.val ∧ x.val < start + len := by
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨⟨j, hj⟩, _, heq⟩
    have hval : start + j = x.val := congrArg Fin.val heq
    have hj' := Finset.mem_range.mp hj
    omega
  · rintro ⟨hlo, hhi⟩
    refine Finset.mem_map.mpr
      ⟨⟨x.val - start, Finset.mem_range.mpr (by omega)⟩, Finset.mem_attach _ _,
        Fin.ext (by change start + (x.val - start) = x.val; omega)⟩

theorem disjoint_finBlock {n s₁ l₁ s₂ l₂ : ℕ} {h₁ : s₁ + l₁ ≤ n} {h₂ : s₂ + l₂ ≤ n}
    (hsep : s₁ + l₁ ≤ s₂) :
    Disjoint (finBlock s₁ l₁ h₁) (finBlock s₂ l₂ h₂) := by
  refine Finset.disjoint_left.mpr fun x hx₁ hx₂ => ?_
  rw [mem_finBlock] at hx₁ hx₂
  omega

/-- The symbolic `K_4` star-edge 4-witness tight cover on `Fin n`: a shared `k`-core plus the
4 vertex-star triples of 6 disjoint `e`-point edge blocks (`|U| = k + 6e`, `|S_i| = k + 3e`). -/
def k4TightSupports {n : ℕ} (k e : ℕ) (hfit : k + 6 * e ≤ n) (i : Fin 4) : Finset (Fin n) :=
  let B0 := finBlock 0 k (by omega)
  let E0 := finBlock k e (by omega)
  let E1 := finBlock (k + e) e (by omega)
  let E2 := finBlock (k + 2 * e) e (by omega)
  let E3 := finBlock (k + 3 * e) e (by omega)
  let E4 := finBlock (k + 4 * e) e (by omega)
  let E5 := finBlock (k + 5 * e) e (by omega)
  match i with
  | ⟨0, _⟩ => B0 ∪ E0 ∪ E1 ∪ E2
  | ⟨1, _⟩ => B0 ∪ E0 ∪ E3 ∪ E4
  | ⟨2, _⟩ => B0 ∪ E1 ∪ E3 ∪ E5
  | ⟨3, _⟩ => B0 ∪ E2 ∪ E4 ∪ E5

theorem card_k4TightSupports {n k e : ℕ} (hfit : k + 6 * e ≤ n) (i : Fin 4) :
    (k4TightSupports k e hfit i).card = k + 3 * e := by
  have card4 : ∀ {a₁ l₁ a₂ l₂ a₃ l₃ a₄ l₄ : ℕ}
      (h₁ : a₁ + l₁ ≤ n) (h₂ : a₂ + l₂ ≤ n) (h₃ : a₃ + l₃ ≤ n) (h₄ : a₄ + l₄ ≤ n),
      a₁ + l₁ ≤ a₂ → a₂ + l₂ ≤ a₃ → a₃ + l₃ ≤ a₄ →
      (finBlock a₁ l₁ h₁ ∪ finBlock a₂ l₂ h₂ ∪ finBlock a₃ l₃ h₃ ∪ finBlock a₄ l₄ h₄).card =
        l₁ + l₂ + l₃ + l₄ := by
    intro a₁ l₁ a₂ l₂ a₃ l₃ a₄ l₄ h₁ h₂ h₃ h₄ hs12 hs23 hs34
    have hd12 : Disjoint (finBlock a₁ l₁ h₁) (finBlock a₂ l₂ h₂) := disjoint_finBlock hs12
    have hd123 : Disjoint (finBlock a₁ l₁ h₁ ∪ finBlock a₂ l₂ h₂) (finBlock a₃ l₃ h₃) :=
      Finset.disjoint_union_left.mpr ⟨disjoint_finBlock (by omega), disjoint_finBlock hs23⟩
    have hd1234 :
        Disjoint (finBlock a₁ l₁ h₁ ∪ finBlock a₂ l₂ h₂ ∪ finBlock a₃ l₃ h₃)
          (finBlock a₄ l₄ h₄) :=
      Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr
            ⟨disjoint_finBlock (by omega), disjoint_finBlock (by omega)⟩,
          disjoint_finBlock hs34⟩
    rw [Finset.card_union_of_disjoint hd1234, Finset.card_union_of_disjoint hd123,
      Finset.card_union_of_disjoint hd12, card_finBlock, card_finBlock, card_finBlock,
      card_finBlock]
  fin_cases i
  · dsimp only [k4TightSupports]
    rw [card4 _ _ _ _ (by omega) (by omega) (by omega)]
    omega
  · dsimp only [k4TightSupports]
    rw [card4 _ _ _ _ (by omega) (by omega) (by omega)]
    omega
  · dsimp only [k4TightSupports]
    rw [card4 _ _ _ _ (by omega) (by omega) (by omega)]
    omega
  · dsimp only [k4TightSupports]
    rw [card4 _ _ _ _ (by omega) (by omega) (by omega)]
    omega

theorem card_biUnion_k4TightSupports {n k e : ℕ} (hfit : k + 6 * e ≤ n) :
    (Finset.univ.biUnion (k4TightSupports k e hfit)).card = k + 6 * e := by
  have heq :
      Finset.univ.biUnion (k4TightSupports k e hfit) = finBlock 0 (k + 6 * e) (by omega) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_finBlock, zero_add]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;>
        · simp only [k4TightSupports, Finset.mem_union, mem_finBlock] at hi
          omega
    · intro hx
      by_cases h0 : x.val < k + 3 * e
      · refine ⟨0, ?_⟩
        simp only [k4TightSupports, Finset.mem_union, mem_finBlock]
        omega
      · by_cases h1 : x.val < k + 5 * e
        · refine ⟨1, ?_⟩
          simp only [k4TightSupports, Finset.mem_union, mem_finBlock]
          omega
        · refine ⟨2, ?_⟩
          simp only [k4TightSupports, Finset.mem_union, mem_finBlock]
          omega
  rw [heq, card_finBlock]

theorem multThreeLocus_k4TightSupports_card_le {n k e : ℕ} (hfit : k + 6 * e ≤ n) :
    (multThreeLocus (k4TightSupports k e hfit)).card ≤ k := by
  have hsub : multThreeLocus (k4TightSupports k e hfit) ⊆ finBlock 0 k (by omega) := by
    intro x hx
    rw [mem_finBlock]
    by_contra hge
    have hk_le : k ≤ x.val := by omega
    rw [multThreeLocus, Finset.mem_filter] at hx
    have hcap2 :
        ∀ i₁ i₂ : Fin 4,
          (∀ i : Fin 4, x ∈ k4TightSupports k e hfit i → i = i₁ ∨ i = i₂) →
          (Finset.univ.filter (fun i : Fin 4 => x ∈ k4TightSupports k e hfit i)).card ≤ 2 := by
      intro i₁ i₂ hsub_pair
      have hs :
          Finset.univ.filter (fun i : Fin 4 => x ∈ k4TightSupports k e hfit i) ⊆ {i₁, i₂} := by
        intro i hi
        rcases hsub_pair i (Finset.mem_filter.mp hi).2 with rfl | rfl <;> simp
      exact (Finset.card_le_card hs).trans (Finset.card_insert_le i₁ {i₂} |>.trans (by simp))
    have hle2 :
        (Finset.univ.filter (fun i : Fin 4 => x ∈ k4TightSupports k e hfit i)).card ≤ 2 := by
      by_cases he0 : x.val < k + e
      · refine hcap2 0 1 fun i hi => ?_
        rcases i with ⟨_ | _ | _ | _ | _, hi_lt⟩
        · left; exact Fin.ext rfl
        · right; exact Fin.ext rfl
        · dsimp only [k4TightSupports] at hi
          simp only [Finset.mem_union, mem_finBlock] at hi; omega
        · dsimp only [k4TightSupports] at hi
          simp only [Finset.mem_union, mem_finBlock] at hi; omega
        · omega
      · by_cases he1 : x.val < k + 2 * e
        · refine hcap2 0 2 fun i hi => ?_
          rcases i with ⟨_ | _ | _ | _ | _, hi_lt⟩
          · left; exact Fin.ext rfl
          · dsimp only [k4TightSupports] at hi
            simp only [Finset.mem_union, mem_finBlock] at hi; omega
          · right; exact Fin.ext rfl
          · dsimp only [k4TightSupports] at hi
            simp only [Finset.mem_union, mem_finBlock] at hi; omega
          · omega
        · by_cases he2 : x.val < k + 3 * e
          · refine hcap2 0 3 fun i hi => ?_
            rcases i with ⟨_ | _ | _ | _ | _, hi_lt⟩
            · left; exact Fin.ext rfl
            · dsimp only [k4TightSupports] at hi
              simp only [Finset.mem_union, mem_finBlock] at hi; omega
            · dsimp only [k4TightSupports] at hi
              simp only [Finset.mem_union, mem_finBlock] at hi; omega
            · right; exact Fin.ext rfl
            · omega
          · by_cases he3 : x.val < k + 4 * e
            · refine hcap2 1 2 fun i hi => ?_
              rcases i with ⟨_ | _ | _ | _ | _, hi_lt⟩
              · dsimp only [k4TightSupports] at hi
                simp only [Finset.mem_union, mem_finBlock] at hi; omega
              · left; exact Fin.ext rfl
              · right; exact Fin.ext rfl
              · dsimp only [k4TightSupports] at hi
                simp only [Finset.mem_union, mem_finBlock] at hi; omega
              · omega
            · by_cases he4 : x.val < k + 5 * e
              · refine hcap2 1 3 fun i hi => ?_
                rcases i with ⟨_ | _ | _ | _ | _, hi_lt⟩
                · dsimp only [k4TightSupports] at hi
                  simp only [Finset.mem_union, mem_finBlock] at hi; omega
                · left; exact Fin.ext rfl
                · dsimp only [k4TightSupports] at hi
                  simp only [Finset.mem_union, mem_finBlock] at hi; omega
                · right; exact Fin.ext rfl
                · omega
              · refine hcap2 2 3 fun i hi => ?_
                rcases i with ⟨_ | _ | _ | _ | _, hi_lt⟩
                · dsimp only [k4TightSupports] at hi
                  simp only [Finset.mem_union, mem_finBlock] at hi; omega
                · dsimp only [k4TightSupports] at hi
                  simp only [Finset.mem_union, mem_finBlock] at hi; omega
                · left; exact Fin.ext rfl
                · right; exact Fin.ext rfl
                · omega
    omega
  exact (Finset.card_le_card hsub).trans (by rw [card_finBlock])

/-- **Production `n = 2^30, k = 2^29, t = 715827884` Exact `hrank` Realization.**
Over every field `F` with an injective `2^30`-point evaluation domain `α : Fin (2^30) ↪ F`
(including both certified prize primes) and any 4 distinct scalars `γ : Fin 4 → F`, the `K_4`
strip witness family (`e = 59652324`, `|S_i| = 715827884`, `|U| = 894784856`) realizes exact
`hrank`: `finrank F (span (range φ)) = 2 * (|U| - 2^29) = 715827888`. -/
theorem production_k4Tight_hrank {F : Type*} [Field F] [DecidableEq F]
    (α : Fin (2 ^ 30) ↪ F) {γ : Fin 4 → F} (hγ : Function.Injective γ) :
    let hfit : 2 ^ 29 + 6 * 59652324 ≤ 2 ^ 30 := by norm_num
    let S := k4TightSupports (n := 2 ^ 30) (2 ^ 29) 59652324 hfit
    (∀ i, (S i).card = 715827884) ∧
      (Finset.univ.biUnion S).card = 894784856 ∧
      ∃ φ : (Σ i : Fin 4, Fin ((S i).card - 2 ^ 29)) →
          Module.Dual F (SyndromePair (ReedSolomon.code α (2 ^ 29))),
        Module.finrank F (Submodule.span F (Set.range φ)) =
          2 * ((Finset.univ.biUnion S).card - 2 ^ 29) ∧
        Module.finrank F (Submodule.span F (Set.range φ)) = 715827888 := by
  have hfit : 2 ^ 29 + 6 * 59652324 ≤ 2 ^ 30 := by norm_num
  set S := k4TightSupports (n := 2 ^ 30) (2 ^ 29) 59652324 hfit
  have hcardS : ∀ i, (S i).card = 715827884 := fun i => by
    rw [card_k4TightSupports hfit i]
    norm_num
  have hcardU : (Finset.univ.biUnion S).card = 894784856 := by
    rw [card_biUnion_k4TightSupports hfit]
    norm_num
  have hpeel : PeeledSupportFamily (2 ^ 29) S :=
    peeledSupportFamily_of_multThreeLocus_card_le S (multThreeLocus_k4TightSupports_card_le hfit)
  have htight :
      ∑ i : Fin 4, ((S i).card - 2 ^ 29) = 2 * ((Finset.univ.biUnion S).card - 2 ^ 29) := by
    simp only [hcardS, hcardU, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    norm_num
  obtain ⟨φ, hrank, _⟩ :=
    hrank_and_realizabilityCore_of_peeled_tight_cover α (Fintype.card_fin (2 ^ 30)) (by norm_num)
      (fun i => by rw [hcardS i]; norm_num) hpeel htight hγ
  refine ⟨hcardS, hcardU, φ, hrank, ?_⟩
  rw [hrank, hcardU]
  norm_num

/-- Complement blocks `C_i` (`|C_i| = 3p + q`) of the symmetric sub-`k`-overlap 4-witness family. -/
def subKComplement {n : ℕ} (p q : ℕ) (hfit : 6 * p + 4 * q ≤ n) (i : Fin 4) : Finset (Fin n) :=
  let P01 := finBlock 0 p (by omega)
  let P02 := finBlock p p (by omega)
  let P03 := finBlock (2 * p) p (by omega)
  let P12 := finBlock (3 * p) p (by omega)
  let P13 := finBlock (4 * p) p (by omega)
  let P23 := finBlock (5 * p) p (by omega)
  let Q0 := finBlock (6 * p) q (by omega)
  let Q1 := finBlock (6 * p + q) q (by omega)
  let Q2 := finBlock (6 * p + 2 * q) q (by omega)
  let Q3 := finBlock (6 * p + 3 * q) q (by omega)
  match i with
  | ⟨0, _⟩ => P01 ∪ P02 ∪ P03 ∪ Q0
  | ⟨1, _⟩ => P01 ∪ P12 ∪ P13 ∪ Q1
  | ⟨2, _⟩ => P02 ∪ P12 ∪ P23 ∪ Q2
  | ⟨3, _⟩ => P03 ∪ P13 ∪ P23 ∪ Q3

/-- Strictly sub-`k`-overlap 4-witness strip family `S_i = (subKComplement p q hfit i)ᶜ`. -/
def subKOverlapSupports {n : ℕ} (p q : ℕ) (hfit : 6 * p + 4 * q ≤ n) (i : Fin 4) :
    Finset (Fin n) :=
  (subKComplement p q hfit i)ᶜ

theorem card_subKOverlapSupports {n p q : ℕ} (hfit : 6 * p + 4 * q ≤ n) (i : Fin 4) :
    (subKOverlapSupports p q hfit i).card = n - (3 * p + q) := by
  have card4 : ∀ {a₁ l₁ a₂ l₂ a₃ l₃ a₄ l₄ : ℕ}
      (h₁ : a₁ + l₁ ≤ n) (h₂ : a₂ + l₂ ≤ n) (h₃ : a₃ + l₃ ≤ n) (h₄ : a₄ + l₄ ≤ n),
      a₁ + l₁ ≤ a₂ → a₂ + l₂ ≤ a₃ → a₃ + l₃ ≤ a₄ →
      (finBlock a₁ l₁ h₁ ∪ finBlock a₂ l₂ h₂ ∪ finBlock a₃ l₃ h₃ ∪ finBlock a₄ l₄ h₄).card =
        l₁ + l₂ + l₃ + l₄ := by
    intro a₁ l₁ a₂ l₂ a₃ l₃ a₄ l₄ h₁ h₂ h₃ h₄ hs12 hs23 hs34
    have hd12 : Disjoint (finBlock a₁ l₁ h₁) (finBlock a₂ l₂ h₂) := disjoint_finBlock hs12
    have hd123 : Disjoint (finBlock a₁ l₁ h₁ ∪ finBlock a₂ l₂ h₂) (finBlock a₃ l₃ h₃) :=
      Finset.disjoint_union_left.mpr ⟨disjoint_finBlock (by omega), disjoint_finBlock hs23⟩
    have hd1234 :
        Disjoint (finBlock a₁ l₁ h₁ ∪ finBlock a₂ l₂ h₂ ∪ finBlock a₃ l₃ h₃)
          (finBlock a₄ l₄ h₄) :=
      Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr
            ⟨disjoint_finBlock (by omega), disjoint_finBlock (by omega)⟩,
          disjoint_finBlock hs34⟩
    rw [Finset.card_union_of_disjoint hd1234, Finset.card_union_of_disjoint hd123,
      Finset.card_union_of_disjoint hd12, card_finBlock, card_finBlock, card_finBlock,
      card_finBlock]
  rw [subKOverlapSupports, Finset.card_compl, Fintype.card_fin]
  have hC : (subKComplement p q hfit i).card = 3 * p + q := by
    fin_cases i <;>
      · dsimp only [subKComplement]
        rw [card4 _ _ _ _ (by omega) (by omega) (by omega)]
        omega
  rw [hC]

theorem inter_card_subKOverlapSupports {n p q : ℕ} (hfit : 6 * p + 4 * q ≤ n)
    {i j : Fin 4} (hne : i ≠ j) :
    (subKOverlapSupports p q hfit i ∩ subKOverlapSupports p q hfit j).card =
      n - (5 * p + 2 * q) := by
  have hCi : ∀ m : Fin 4, (subKComplement p q hfit m).card = 3 * p + q := by
    intro m
    have hc := card_subKOverlapSupports hfit m
    have hle : (subKComplement p q hfit m).card ≤ n := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (subKComplement p q hfit m)
    rw [subKOverlapSupports, Finset.card_compl, Fintype.card_fin] at hc
    omega
  have hinter : (subKComplement p q hfit i ∩ subKComplement p q hfit j).card = p := by
    have block_eq : ∀ s : ℕ, (hs : s + p ≤ n) →
        subKComplement p q hfit i ∩ subKComplement p q hfit j = finBlock s p hs →
        (subKComplement p q hfit i ∩ subKComplement p q hfit j).card = p := by
      intro s hs heq
      rw [heq, card_finBlock]
    fin_cases i <;> fin_cases j
    · exact False.elim (hne rfl)
    · refine block_eq 0 (by omega) ?_
      ext x; simp only [subKComplement, Finset.mem_inter, Finset.mem_union, mem_finBlock]; omega
    · refine block_eq p (by omega) ?_
      ext x; simp only [subKComplement, Finset.mem_inter, Finset.mem_union, mem_finBlock]; omega
    · refine block_eq (2 * p) (by omega) ?_
      ext x; simp only [subKComplement, Finset.mem_inter, Finset.mem_union, mem_finBlock]; omega
    · refine block_eq 0 (by omega) ?_
      ext x; simp only [subKComplement, Finset.mem_inter, Finset.mem_union, mem_finBlock]; omega
    · exact False.elim (hne rfl)
    · refine block_eq (3 * p) (by omega) ?_
      ext x; simp only [subKComplement, Finset.mem_inter, Finset.mem_union, mem_finBlock]; omega
    · refine block_eq (4 * p) (by omega) ?_
      ext x; simp only [subKComplement, Finset.mem_inter, Finset.mem_union, mem_finBlock]; omega
    · refine block_eq p (by omega) ?_
      ext x; simp only [subKComplement, Finset.mem_inter, Finset.mem_union, mem_finBlock]; omega
    · refine block_eq (3 * p) (by omega) ?_
      ext x; simp only [subKComplement, Finset.mem_inter, Finset.mem_union, mem_finBlock]; omega
    · exact False.elim (hne rfl)
    · refine block_eq (5 * p) (by omega) ?_
      ext x; simp only [subKComplement, Finset.mem_inter, Finset.mem_union, mem_finBlock]; omega
    · refine block_eq (2 * p) (by omega) ?_
      ext x; simp only [subKComplement, Finset.mem_inter, Finset.mem_union, mem_finBlock]; omega
    · refine block_eq (4 * p) (by omega) ?_
      ext x; simp only [subKComplement, Finset.mem_inter, Finset.mem_union, mem_finBlock]; omega
    · refine block_eq (5 * p) (by omega) ?_
      ext x; simp only [subKComplement, Finset.mem_inter, Finset.mem_union, mem_finBlock]; omega
    · exact False.elim (hne rfl)
  have hunion : (subKComplement p q hfit i ∪ subKComplement p q hfit j).card = 5 * p + 2 * q := by
    have hadd := Finset.card_union_add_card_inter (subKComplement p q hfit i)
      (subKComplement p q hfit j)
    rw [hCi i, hCi j, hinter] at hadd
    omega
  have hcompl_inter :
      subKOverlapSupports p q hfit i ∩ subKOverlapSupports p q hfit j =
        (subKComplement p q hfit i ∪ subKComplement p q hfit j)ᶜ := by
    ext x
    simp only [subKOverlapSupports, Finset.mem_inter, Finset.mem_compl, Finset.mem_union, not_or]
  rw [hcompl_inter, Finset.card_compl, Fintype.card_fin, hunion]

theorem multThreeLocus_subKOverlapSupports_card_le {n p q : ℕ} (hfit : 6 * p + 4 * q ≤ n) :
    (multThreeLocus (subKOverlapSupports p q hfit)).card ≤ n - 6 * p := by
  have hsub : multThreeLocus (subKOverlapSupports p q hfit) ⊆ (finBlock 0 (6 * p) (by omega))ᶜ := by
    intro x hx
    rw [Finset.mem_compl, mem_finBlock]
    rintro ⟨_, hlt6⟩
    rw [multThreeLocus, Finset.mem_filter] at hx
    have hcap2 :
        ∀ i₁ i₂ : Fin 4,
          (∀ i : Fin 4, x ∈ subKOverlapSupports p q hfit i → i = i₁ ∨ i = i₂) →
          (Finset.univ.filter (fun i : Fin 4 => x ∈ subKOverlapSupports p q hfit i)).card ≤ 2 := by
      intro i₁ i₂ hsub_pair
      have hs :
          Finset.univ.filter (fun i : Fin 4 => x ∈ subKOverlapSupports p q hfit i) ⊆ {i₁, i₂} := by
        intro i hi
        rcases hsub_pair i (Finset.mem_filter.mp hi).2 with rfl | rfl <;> simp
      exact (Finset.card_le_card hs).trans (Finset.card_insert_le i₁ {i₂} |>.trans (by simp))
    have hle2 :
        (Finset.univ.filter (fun i : Fin 4 => x ∈ subKOverlapSupports p q hfit i)).card ≤ 2 := by
      by_cases hp1 : x.val < p
      · refine hcap2 2 3 fun i hi => ?_
        rcases i with ⟨_ | _ | _ | _ | _, hi_lt⟩
        · dsimp only [subKOverlapSupports, subKComplement] at hi
          simp only [Finset.mem_compl, Finset.mem_union, mem_finBlock] at hi; omega
        · dsimp only [subKOverlapSupports, subKComplement] at hi
          simp only [Finset.mem_compl, Finset.mem_union, mem_finBlock] at hi; omega
        · left; exact Fin.ext rfl
        · right; exact Fin.ext rfl
        · omega
      · by_cases hp2 : x.val < 2 * p
        · refine hcap2 1 3 fun i hi => ?_
          rcases i with ⟨_ | _ | _ | _ | _, hi_lt⟩
          · dsimp only [subKOverlapSupports, subKComplement] at hi
            simp only [Finset.mem_compl, Finset.mem_union, mem_finBlock] at hi; omega
          · left; exact Fin.ext rfl
          · dsimp only [subKOverlapSupports, subKComplement] at hi
            simp only [Finset.mem_compl, Finset.mem_union, mem_finBlock] at hi; omega
          · right; exact Fin.ext rfl
          · omega
        · by_cases hp3 : x.val < 3 * p
          · refine hcap2 1 2 fun i hi => ?_
            rcases i with ⟨_ | _ | _ | _ | _, hi_lt⟩
            · dsimp only [subKOverlapSupports, subKComplement] at hi
              simp only [Finset.mem_compl, Finset.mem_union, mem_finBlock] at hi; omega
            · left; exact Fin.ext rfl
            · right; exact Fin.ext rfl
            · dsimp only [subKOverlapSupports, subKComplement] at hi
              simp only [Finset.mem_compl, Finset.mem_union, mem_finBlock] at hi; omega
            · omega
          · by_cases hp4 : x.val < 4 * p
            · refine hcap2 0 3 fun i hi => ?_
              rcases i with ⟨_ | _ | _ | _ | _, hi_lt⟩
              · left; exact Fin.ext rfl
              · dsimp only [subKOverlapSupports, subKComplement] at hi
                simp only [Finset.mem_compl, Finset.mem_union, mem_finBlock] at hi; omega
              · dsimp only [subKOverlapSupports, subKComplement] at hi
                simp only [Finset.mem_compl, Finset.mem_union, mem_finBlock] at hi; omega
              · right; exact Fin.ext rfl
              · omega
            · by_cases hp5 : x.val < 5 * p
              · refine hcap2 0 2 fun i hi => ?_
                rcases i with ⟨_ | _ | _ | _ | _, hi_lt⟩
                · left; exact Fin.ext rfl
                · dsimp only [subKOverlapSupports, subKComplement] at hi
                  simp only [Finset.mem_compl, Finset.mem_union, mem_finBlock] at hi; omega
                · right; exact Fin.ext rfl
                · dsimp only [subKOverlapSupports, subKComplement] at hi
                  simp only [Finset.mem_compl, Finset.mem_union, mem_finBlock] at hi; omega
                · omega
              · refine hcap2 0 1 fun i hi => ?_
                rcases i with ⟨_ | _ | _ | _ | _, hi_lt⟩
                · left; exact Fin.ext rfl
                · right; exact Fin.ext rfl
                · dsimp only [subKOverlapSupports, subKComplement] at hi
                  simp only [Finset.mem_compl, Finset.mem_union, mem_finBlock] at hi; omega
                · dsimp only [subKOverlapSupports, subKComplement] at hi
                  simp only [Finset.mem_compl, Finset.mem_union, mem_finBlock] at hi; omega
                · omega
    omega
  exact (Finset.card_le_card hsub).trans
    (by rw [Finset.card_compl, Fintype.card_fin, card_finBlock])

/-- **Production `n = 2^30` Full-Rank G87 Family with Strictly Sub-`k` Pairwise Overlaps.**
At `n = 2^30, k = 2^29`, `p = 119304646, q = 2`, every witness support has exact strip size
`715827884`, **every pairwise intersection has size `477218590 < 2^29 = k`** (so `SYZ56` overlap
chaining fails on every pair!), yet `(multThreeLocus S).card ≤ 357913948 ≤ 2^29 = k`, certifying
full linear independence (`finrank = 715827888`) over every injective `2^30`-point domain! -/
theorem production_subKOverlap_linearIndependent {F : Type*} [Field F] [DecidableEq F]
    (α : Fin (2 ^ 30) ↪ F) {γ : Fin 4 → F} (hγ : Function.Injective γ) :
    let hfit : 6 * 119304646 + 4 * 2 ≤ 2 ^ 30 := by norm_num
    let S := subKOverlapSupports (n := 2 ^ 30) 119304646 2 hfit
    (∀ i, (S i).card = 715827884) ∧
      (∀ i j, i ≠ j → (S i ∩ S j).card = 477218590 ∧ (S i ∩ S j).card < 2 ^ 29) ∧
      ∃ φ : (Σ i : Fin 4, Fin ((S i).card - 2 ^ 29)) →
          Module.Dual F (SyndromePair (ReedSolomon.code α (2 ^ 29))),
        LinearIndependent F φ ∧
        Module.finrank F (Submodule.span F (Set.range φ)) = 715827888 := by
  have hfit : 6 * 119304646 + 4 * 2 ≤ 2 ^ 30 := by norm_num
  set S := subKOverlapSupports (n := 2 ^ 30) 119304646 2 hfit
  have hcardS : ∀ i, (S i).card = 715827884 := fun i => by
    rw [card_subKOverlapSupports hfit i]
    norm_num
  have hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 477218590 ∧ (S i ∩ S j).card < 2 ^ 29 := by
    intro i j hne
    have hc : (S i ∩ S j).card = 477218590 := by
      rw [inter_card_subKOverlapSupports hfit hne]
      norm_num
    exact ⟨hc, by rw [hc]; norm_num⟩
  have hm3 : (multThreeLocus S).card ≤ 2 ^ 29 :=
    (multThreeLocus_subKOverlapSupports_card_le hfit).trans (by norm_num)
  obtain ⟨φ, hli, hfr, _⟩ :=
    peeled_bridge_linearIndependent α (2 ^ 29) (fun i => by rw [hcardS i]; norm_num)
      (peeledSupportFamily_of_multThreeLocus_card_le S hm3) hγ
  have hfr_val : Module.finrank F (Submodule.span F (Set.range φ)) = 715827888 := by
    rw [hfr]
    simp only [hcardS, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    norm_num
  exact ⟨hcardS, hinter, φ, hli, hfr_val⟩

end ProductionRealizations

#print axioms twisted_syzygy_confined_to_multThree
#print axioms rs_twisted_syzygy_leaf_zero
#print axioms peeled_twisted_syzygy_zero
#print axioms peeled_bridge_linearIndependent
#print axioms three_witness_bridge_linearIndependent
#print axioms hrank_and_realizabilityCore_of_peeled_tight_cover
#print axioms plantable_cannot_realize_full_domain_hrank
#print axioms production_k4Tight_hrank
#print axioms production_subKOverlap_linearIndependent

end ArkLib.ProximityGap.Frontier.CarbonSYZMultiplicityThreeHrank
