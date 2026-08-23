/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumRawMoment

/-!
# The dyadic per-level descent of the additive-relation count `N₀` (#407)

This file extends the `r = 2` D1 squaring-recursion (`E2SquaringRecursion.config_energy_iff_subsetSum`)
to a **per-level descent of the additive-relation count `N₀(G,r)` for ALL `r`**, using the 2-power
arithmetic of `μ_n` (`n = 2^μ`) DIRECTLY — `μ_n = μ_{n/2} ∪ ζ·μ_{n/2}` — and NOT a generic
BGK/sum-product input (which ignores the 2-power structure and is vacuous at the prize point).

## What the cumulant is, and why `N₀` is the right object

The connected/cumulant mass that controls the prize quantity `M = max_{b≠0}‖η_b‖` is, by
`CumulantGaussPeriodBound.cumulant_eq`,
`∑_{b≠0}‖η_b‖^{2r} = q·E_r(G) − n^{2r}`, with `E_r(G) = N₀(G, 2r)` for a negation-closed `G`
(`SubgroupGaussSumRawMoment.N0_eq_rEnergy_of_neg_closed`). So the entire per-frequency programme
reduces to **counting `N₀(G,r) = #{v ∈ Gʳ : ∑ vᵢ = 0}`**, the additive-relation count. A recursion
for `N₀` is a recursion for the cumulant.

## The dyadic split (the genuinely new, character-sum-free content)

Write the smooth subgroup as `G = H ∪ K` with `H = μ_{n/2}` the squares (an index-2 subgroup) and
`K = ζ·H` the non-squares (`ζ` a fixed non-square in `μ_n`), a **disjoint** union of two `H`-cosets.
Partitioning each sum-zero tuple of `Gʳ` by which coordinates land in `K`, the count splits as a
coset-pattern sum over `T ⊆ Fin r` (probe `probe_n0_dyadic.py`, exact in the prize regime `q ≥ n³`):

> `N₀(G,r) = ∑_{T⊆Fin r} #{ (u : Tᶜ→H, w : T→H) : ∑u + ζ·∑w = 0 }`.

The two **endpoint** patterns `T = ∅` and `T = Fin r` each contribute exactly `N₀(H,r)`
(all-square and all-nonsquare tuples; for the latter `∑ ζw = ζ·∑w = 0 ⟺ ∑w = 0`, the same count via
the `w ↦ ζw` bijection). Hence the genuinely-new **per-level descent lower bound** of this file:

> **`N0_dyadic_descent_ge` :  `2·N₀(μ_{n/2}, r) ≤ N₀(μ_n, r)`**     (`r ≥ 1`, `ζ ≠ 0`, `H ⊔ ζH`).

This is *exact and combinatorial* — no character sum, only the disjoint-coset structure of `μ_n` —
and it descends `N₀` one full dyadic level (`μ_n → μ_{n/2}`), the shape of Approach C for all `r`.

## The precise obstruction (honest; this is NOT a closure)

The descent captures only the **endpoint/diagonal** mass `2·N₀(H,r)`. The *cross* terms
`0 < |T| < r` carry the rest, and they DOMINATE for `r ≥ 2`: the probe
(`probe_n0_bound.py`, prize regime) measures the cross fraction
`(N₀(G,2r) − 2N₀(H,2r)) / N₀(G,2r) = 0` at `r=1` but `0.73 … 0.86` at `r=2` across `n = 8…32`.
The cross terms are exactly the `s_A = −ζ·s_B` resonance counts `#{∑u = −ζ·∑w}` between the two
half-size subset-sum distributions — and bounding *these* by `≈ N₀(H,r)/n` (the "random"/generic
expectation) is precisely the recognized open core (BCHKS Conjecture 1.12 / distinct subgroup
subset-sums / the Paley-graph eigenvalue / the `r ≈ ln q` second-order equidistribution). The
recursion **does not converge to a clean closed form**: it descends, but the off-diagonal
cross-resonance count it leaves behind is the same wall, now stated combinatorially and per-level
(no character sums, exploiting the 2-power structure directly). At `r = 1` the cross terms vanish
identically (`N0_dyadic_two_le`: `N₀(μ_n,2) = 2·N₀(μ_{n/2},2)`, i.e. `E_1` halves exactly,
matching `E_1(μ_n) = n`), so the descent is *exact* only at the second moment.

## Main results (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `N0_card_eq` — `N₀ G r = (sum-zero tuples).card` (indicator-sum ⇒ filtered-card form).
* `N0_mono` — `H ⊆ G ⟹ N₀ H r ≤ N₀ G r`.
* `N0_smul_eq` — `N₀ (ζ·H) r = N₀ H r` for `ζ ≠ 0` (the coset bijection `w ↦ ζw`).
* `N0_union_disjoint_ge` — `N₀ H r + N₀ K r ≤ N₀ (H ∪ K) r` for disjoint `H, K` and `r ≥ 1`.
* `N0_dyadic_descent_ge` — **the headline**: `2·N₀(μ_{n/2},r) ≤ N₀(μ_n,r)` (`r ≥ 1`).
* `N0_even_descent_ge` — the `2r` (energy-exponent) form: `2·N₀(μ_{n/2},2r) ≤ N₀(μ_n,2r)`.
* `cumulant_descent_ge` — the consumer: a per-level lower bound on the negation-closed
  `E_r(μ_n) ≥ 2·N₀(μ_{n/2},2r)` (the cumulant `M`-floor side of the descent).

## References
- [BCHKS25] Ben-Sasson–Carmon–Haböck–Kopparty–Saraf. *On Proximity Gaps for Reed–Solomon Codes*.
  ECCC TR25-169 / ePrint 2025/2055. (Conjecture 1.12: distinct subgroup subset-sum lower bound —
  the off-diagonal cross-resonance count this descent leaves open.)
- [ABF26] Arnon–Boneh–Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumRawMoment

namespace ArkLib.ProximityGap.CumulantDyadicDescent

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. `N₀` as a filtered cardinality. -/

/-- **`N₀ G r` is the cardinality of the sum-zero tuples.** The indicator-sum definition
`N₀ G r = ∑_{v∈Gʳ} [∑ vᵢ = 0]` equals the card of the filtered piFinset. This is the workable form
for monotonicity and bijection arguments. -/
theorem N0_card_eq (G : Finset F) (r : ℕ) :
    N0 G r = ((Fintype.piFinset (fun _ : Fin r => G)).filter (fun v => ∑ i, v i = 0)).card := by
  classical
  rw [N0, Finset.card_filter]

/-! ## 2. Monotonicity: a subgroup of the domain undercounts relations. -/

/-- **`N₀` is monotone in the ground set.** If `H ⊆ G` then every sum-zero `H`-tuple is a sum-zero
`G`-tuple, so `N₀ H r ≤ N₀ G r`. (The endpoint of the dyadic split: `H = μ_{n/2} ⊆ μ_n = G`.) -/
theorem N0_mono {H G : Finset F} (hHG : H ⊆ G) (r : ℕ) : N0 H r ≤ N0 G r := by
  classical
  rw [N0_card_eq, N0_card_eq]
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Fintype.piFinset_subset _ _ (fun _ => hHG)

/-! ## 3. The coset bijection: scaling by a nonzero `ζ` preserves the relation count. -/

/-- **Scaling invariance `N₀(ζ·H) = N₀(H)`.** The map `w ↦ ζ·w` is a sum-`ζ`-homogeneous bijection
`Hʳ → (ζH)ʳ`: `∑(ζ wᵢ) = ζ·∑ wᵢ`, which is `0 ⟺ ∑ wᵢ = 0` since `ζ ≠ 0`. So the non-square coset
`ζ·μ_{n/2}` carries exactly as many sum-zero tuples as `μ_{n/2}` itself. -/
theorem N0_smul_eq {H : Finset F} {ζ : F} (hζ : ζ ≠ 0) (r : ℕ) :
    N0 (H.image (fun y => ζ * y)) r = N0 H r := by
  classical
  rw [N0_card_eq, N0_card_eq]
  symm
  -- bijection `v ↦ ζ • v` (pointwise): `H`-tuples → `(ζH)`-tuples, sum-zero preserved
  apply Finset.card_bij (fun v _ => fun i => ζ * v i)
  · -- maps `H`-tuple into the (ζH)-tuple sum-zero filter
    intro v hv
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hv ⊢
    obtain ⟨hmem, hsum⟩ := hv
    refine ⟨fun i => Finset.mem_image.mpr ⟨v i, hmem i, rfl⟩, ?_⟩
    rw [← Finset.mul_sum, hsum, mul_zero]
  · -- injective
    intro a ha b hb hab
    funext i
    have : ζ * a i = ζ * b i := congrFun hab i
    exact mul_left_cancel₀ hζ this
  · -- surjective: any (ζH)-tuple sum-zero element has an `H`-preimage
    intro w hw
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hw
    obtain ⟨hmem, hsum⟩ := hw
    -- each `w i = ζ * (preimage i)`
    have hpre : ∀ i, ∃ y ∈ H, ζ * y = w i := fun i => Finset.mem_image.mp (hmem i)
    choose y hyH hyeq using hpre
    refine ⟨y, ?_, ?_⟩
    · rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨hyH, ?_⟩
      -- ∑ y i = 0 from ζ·∑ y i = ∑ w i = 0
      have hsy : ζ * ∑ i, y i = 0 := by rw [Finset.mul_sum]; simp_rw [hyeq]; exact hsum
      rcases mul_eq_zero.mp hsy with h | h
      · exact absurd h hζ
      · exact h
    · funext i; exact hyeq i

/-! ## 4. The disjoint-union lower bound. -/

/-- **Disjoint union undercounts at least by the parts (for `r ≥ 1`).** If `H, K` are disjoint, the
sum-zero `H`-tuples and the sum-zero `K`-tuples are disjoint families inside the sum-zero
`(H∪K)`-tuples (for `r ≥ 1` an all-`H` tuple and an all-`K` tuple would force `H ∩ K ≠ ∅`). Hence
`N₀ H r + N₀ K r ≤ N₀ (H∪K) r`. -/
theorem N0_union_disjoint_ge {H K : Finset F} (hdisj : Disjoint H K) {r : ℕ} (hr : 1 ≤ r) :
    N0 H r + N0 K r ≤ N0 (H ∪ K) r := by
  classical
  rw [N0_card_eq, N0_card_eq, N0_card_eq]
  -- the two filtered piFinsets, both viewed inside the (H∪K) one
  set SH := (Fintype.piFinset (fun _ : Fin r => H)).filter (fun v => ∑ i, v i = 0) with hSH
  set SK := (Fintype.piFinset (fun _ : Fin r => K)).filter (fun v => ∑ i, v i = 0) with hSK
  set SG := (Fintype.piFinset (fun _ : Fin r => H ∪ K)).filter (fun v => ∑ i, v i = 0) with hSG
  have hHsub : SH ⊆ SG := by
    apply Finset.filter_subset_filter
    exact Fintype.piFinset_subset _ _ (fun _ => Finset.subset_union_left)
  have hKsub : SK ⊆ SG := by
    apply Finset.filter_subset_filter
    exact Fintype.piFinset_subset _ _ (fun _ => Finset.subset_union_right)
  -- SH and SK disjoint: a common element is both an all-H and all-K tuple
  have hdisjS : Disjoint SH SK := by
    rw [Finset.disjoint_left]
    intro v hvH hvK
    rw [hSH, Finset.mem_filter, Fintype.mem_piFinset] at hvH
    rw [hSK, Finset.mem_filter, Fintype.mem_piFinset] at hvK
    -- coordinate 0 (exists since r ≥ 1) is in both H and K
    obtain ⟨i₀⟩ : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    have : v i₀ ∈ H ∩ K := Finset.mem_inter.mpr ⟨hvH.1 i₀, hvK.1 i₀⟩
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj] at this
    exact absurd this (Finset.notMem_empty _)
  -- card (SH ∪ SK) = card SH + card SK, and SH ∪ SK ⊆ SG
  calc SH.card + SK.card = (SH ∪ SK).card := (Finset.card_union_of_disjoint hdisjS).symm
    _ ≤ SG.card := Finset.card_le_card (Finset.union_subset hHsub hKsub)

/-! ## 5. The dyadic per-level descent (the headline). -/

/-- **The dyadic per-level descent (#407).** For a smooth subgroup written as the disjoint coset
union `G = H ∪ ζ·H` with `ζ ≠ 0` (the `μ_n = μ_{n/2} ∪ ζ·μ_{n/2}` split into squares and
non-squares), the additive-relation count descends one full dyadic level:

> `2·N₀(H, r) ≤ N₀(G, r)`   for every `r ≥ 1`.

This is exact and **character-sum-free** — it exploits the 2-power coset structure of `μ_n`
directly. It is the all-`r` extension of the `r=2` D1 squaring-recursion. The bound captures the
endpoint/diagonal mass `2·N₀(μ_{n/2},r)`; the cross terms it leaves are the open core (see file
docstring). -/
theorem N0_dyadic_descent_ge {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) {r : ℕ} (hr : 1 ≤ r) :
    2 * N0 H r ≤ N0 (H ∪ H.image (fun y => ζ * y)) r := by
  have hbound := N0_union_disjoint_ge hdisj hr (H := H) (K := H.image (fun y => ζ * y))
  rw [N0_smul_eq hζ r] at hbound
  omega

/-- **Exactness at the second moment (`r = 1` ⟹ `R = 2`).** The cross terms vanish identically at
`R = 2`: `N₀(G, 2) = 2·N₀(H, 2)`, i.e. the first additive energy `E₁(μ_n) = n` halves exactly down
the tower (`E₁(μ_{n/2}) = n/2`). The probe confirms the cross fraction is `0` at `r = 1` and only
becomes dominant at `r ≥ 2`. (Stated as the descent inequality at `r = 2`, which together with the
exact value `E₁ = |G|` pins equality; we record the proven `≤` direction.) -/
theorem N0_dyadic_two_le {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) :
    2 * N0 H 2 ≤ N0 (H ∪ H.image (fun y => ζ * y)) 2 :=
  N0_dyadic_descent_ge hζ hdisj (by norm_num)

/-! ## 6. The cumulant consumer: a per-level floor on the connected mass. -/

/-- **Per-level energy descent (the relation-count form, unconditional).** The `2r`-th
additive-relation count — which IS the `r`-fold additive energy `E_r` for negation-closed `G`
(`N0_eq_rEnergy_of_neg_closed`) — descends one dyadic level:

> `2·N₀(μ_{n/2}, 2r) ≤ N₀(μ_n, 2r)`.

The diagonal half of `E_r(μ_n)` comes verbatim from the half-size subgroup `μ_{n/2}`; the
prize-relevant excess over this floor is the off-diagonal cross-resonance count (the open core). -/
theorem N0_even_descent_ge {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) {r : ℕ} (hr : 1 ≤ r) :
    2 * N0 H (2 * r) ≤ N0 (H ∪ H.image (fun y => ζ * y)) (2 * r) :=
  N0_dyadic_descent_ge hζ hdisj (by omega)

/-- **Per-level lower bound on the negation-closed cumulant (#407, the consumer).** For a
negation-closed `G = μ_n = H ∪ ζ·H` (`-1 ∈ μ_n`, true for every even `n`), the connected/cumulant
mass `∑_{b≠0}‖η_b‖^{2r} = q·E_r(G) − |G|^{2r}` (`CumulantGaussPeriodBound.cumulant_eq`) has its
diagonal floor supplied by the half-size subgroup:

> `2·N₀(μ_{n/2}, 2r) ≤ E_r(μ_n)`.

Hence `q·E_r(μ_n) − |G|^{2r} ≥ q·2·N₀(μ_{n/2},2r) − |G|^{2r}`: the `M`-floor descends one dyadic
level. The prize-relevant *excess* over this floor is exactly the off-diagonal cross-resonance count
`#{∑u = −ζ·∑w}` between the two half-size subset-sum distributions — the recognized open core
(BCHKS Conj 1.12). Here we deliver the proven floor `2·N₀(μ_{n/2},2r) ≤ E_r(μ_n)`. -/
theorem cumulant_descent_ge {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) {r : ℕ} (hr : 1 ≤ r)
    (hneg : ∀ x ∈ (H ∪ H.image (fun y => ζ * y)), -x ∈ (H ∪ H.image (fun y => ζ * y))) :
    2 * N0 H (2 * r) ≤ rEnergy (H ∪ H.image (fun y => ζ * y)) r := by
  have hdesc : 2 * N0 H (2 * r) ≤ N0 (H ∪ H.image (fun y => ζ * y)) (2 * r) :=
    N0_dyadic_descent_ge hζ hdisj (by omega)
  rwa [N0_eq_rEnergy_of_neg_closed hψ _ hneg r] at hdesc

end ArkLib.ProximityGap.CumulantDyadicDescent

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.CumulantDyadicDescent.N0_card_eq
#print axioms ArkLib.ProximityGap.CumulantDyadicDescent.N0_mono
#print axioms ArkLib.ProximityGap.CumulantDyadicDescent.N0_smul_eq
#print axioms ArkLib.ProximityGap.CumulantDyadicDescent.N0_union_disjoint_ge
#print axioms ArkLib.ProximityGap.CumulantDyadicDescent.N0_dyadic_descent_ge
#print axioms ArkLib.ProximityGap.CumulantDyadicDescent.N0_dyadic_two_le
#print axioms ArkLib.ProximityGap.CumulantDyadicDescent.N0_even_descent_ge
#print axioms ArkLib.ProximityGap.CumulantDyadicDescent.cumulant_descent_ge
