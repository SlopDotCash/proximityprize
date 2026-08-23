/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# `|S|` divides the zero-sum count of a multiplicative subgroup — at ALL orders, incl. ODD (#444)

`NegationClosedWalk.zeroSumCount S r` is the campaign's `r`-tuple zero-sum count, the object the
located thinness-essential SIGNED period-power sum equals (`SignedPeriodZeroSumBridge`):
`∑_ψ η_ψ^r = q · zeroSumCount S r`, and `∑_{ψ≠0} η_ψ^r = q · zeroSumCount S r − |S|^r`.

`SignedZeroSumCountEven` proved `2 ∣ zeroSumCount S r` (the global-negation `c ↦ −c` parity). This
file proves the **full** divisibility — the order of the whole subgroup, not just the `{±1}` part:

>   if `S` is a multiplicative subgroup of `Fˣ` carried as a `Finset F` (closed under `*` and `⁻¹`,
>   contains `1`, and `0 ∉ S`), then `|S| ∣ zeroSumCount S r` for every `r ≥ 1`.

For the prize subgroup `S = μ_n` this is `n ∣ zeroSumCount(μ_n, r)`, at every `r` including the ODD
orders the always-`2r` additive-energy ladder cannot see. (`2 ∣ ·` is the special case `S ⊇ {±1}`.)

## The mechanism (the new content)

The **dilation** action of `S` on `r`-tuples, `g • c = fun i => g · c i`, is **free** on the
zero-sum tuples: it maps `S`-tuples to `S`-tuples (`S` mult-closed) and preserves the zero-sum
constraint
(`∑_i g·c i = g·∑_i c i = 0`), and a fixed tuple `g·c = c` with `r ≥ 1` forces `g · c 0 = c 0`
with `c 0 ∈ S` so `c 0 ≠ 0` (since `0 ∉ S`), hence `g = 1`. A free action of `S` partitions the
zero-sum set into orbits each of size exactly `|S|`, so `|S| ∣ zeroSumCount S r`.

This is realised concretely (no `MulAction` plumbing) by the **first-coordinate normalisation**
`rep c = fun i => (c 0)⁻¹ · c i` (well-defined since `c 0 ∈ S` is a unit): its fibre over a
normalised `u` (`u 0 = 1`) is exactly the orbit `{ g • u : g ∈ S }`, of size `|S|` (free ⟹
`g ↦ g • u` injective because `u 0 = 1 ≠ 0`). The fibre-count identity
`card_eq_orbitCount_mul_size` then gives
`zeroSumCount = (#orbits)·|S|`, i.e. `|S| ∣ zeroSumCount`.

## Why this is prize-relevant (honest scope)

`|S| ∣ zeroSumCount S r` is a sharp *structural* constraint on the SIGNED prize object
`∑_{ψ≠0} η_ψ^r = q · zeroSumCount S r − |S|^r` at general `r`: it pins `q·zeroSumCount` to a
multiple of `q·|S|`, the kind of arithmetic rigidity the sign-blind `|·|`/moment route discards.
NON-MOMENT
(pure additive-tuple counting, no `|·|`), field-universal (any finite mult-subgroup `0 ∉ S`),
EXTEND-proven (reuses the in-tree fibre-count `card_eq_orbitCount_mul_size`; strengthens
`SignedZeroSumCountEven`'s `2 ∣`). It is NOT a CORE bound: bounding `∑_{ψ≠0} η_ψ^r` *quantitatively*
at `r ≈ log q` remains the open BGK wall. `CORE  M(μ_n) ≤ C·√(n·log(q/n))  OPEN.`

Probe: `scripts/probes/probe_zsc_dilation_free.py` (EXACT, thin `μ_n` `n ∈ {4,8}`, `p ≡ 1 mod n`,
`(p−1)/n ≥ 2`, NEVER `n = q−1`, incl. `p > n³` {73,89,521,569} + Fermat 257):
`n ∣ zeroSumCount(μ_n, r)` for every `r ∈ {1..5}` and every probed prime; the dilation freeness is
verified directly (0 fixed-point violations of `g ≠ 1` fixing a zero-sum tuple).

Issue #444.
-/
set_option linter.unusedSectionVars false


open scoped BigOperators

namespace ArkLib.ProximityGap.NegationClosedWalk

open Finset
open ArkLib.ProximityGap.OrbitCountCrossingLaw

variable {F : Type*} [Field F] [DecidableEq F]

/-- First-coordinate normalisation: `normRep c = fun i => (c 0)⁻¹ * c i`. On the zero-sum tuples of
a multiplicative subgroup it is the dilation-orbit representative (its first coordinate is `1`). -/
def normRep {r : ℕ} (hr : 0 < r) (c : Fin r → F) : Fin r → F :=
  fun i => (c ⟨0, hr⟩)⁻¹ * c i

theorem normRep_zero {r : ℕ} (hr : 0 < r) (c : Fin r → F)
    (hc0 : c ⟨0, hr⟩ ≠ 0) : normRep hr c ⟨0, hr⟩ = 1 := by
  simp [normRep, inv_mul_cancel₀ hc0]

/-- **`|S|` divides the zero-sum count of a multiplicative subgroup**, at every order `r ≥ 1`.
The dilation `g • c = (i ↦ g · c i)` acts freely on the zero-sum `r`-tuples of `S` (a fixed tuple
forces `g · c 0 = c 0` with `c 0 ≠ 0`, hence `g = 1`), so the first-coordinate normalisation
`rep c = (c 0)⁻¹ • c` has every fibre a full orbit of size `|S|`. Holds at ODD `r` too. -/
theorem card_dvd_zeroSumCount_of_subgroup {r : ℕ} (hr : 0 < r) (S : Finset F)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hinv : ∀ a ∈ S, a⁻¹ ∈ S)
    (h0 : (0 : F) ∉ S) :
    S.card ∣ zeroSumCount S r := by
  classical
  set B : Finset (Fin r → F) :=
    (Fintype.piFinset (fun _ : Fin r => S)).filter (fun c => ∑ i, c i = 0) with hB
  -- helper: every coordinate of a `B`-member lies in `S`, hence is nonzero.
  have hmemS : ∀ c ∈ B, ∀ i, c i ∈ S := by
    intro c hc i
    rw [hB, mem_filter, Fintype.mem_piFinset] at hc
    exact hc.1 i
  have hne0 : ∀ c ∈ B, ∀ i, c i ≠ 0 := by
    intro c hc i hci
    exact h0 (hci ▸ hmemS c hc i)
  -- `normRep` maps `B` into itself.
  have hmap : ∀ c ∈ B, normRep hr c ∈ B := by
    intro c hc
    rw [hB, mem_filter, Fintype.mem_piFinset] at hc ⊢
    have hc0 : c ⟨0, hr⟩ ∈ S := hc.1 ⟨0, hr⟩
    refine ⟨fun i => ?_, ?_⟩
    · exact hmul _ (hinv _ hc0) _ (hc.1 i)
    · have : ∑ i, normRep hr c i = (c ⟨0, hr⟩)⁻¹ * ∑ i, c i := by
        simp only [normRep, Finset.mul_sum]
      rw [this, hc.2, mul_zero]
  -- each fibre of `normRep` over `B` has card exactly `|S|`.
  have hfib : ∀ u ∈ B.image (normRep hr),
      (B.filter (fun c => normRep hr c = u)).card = S.card := by
    intro u hu
    rw [mem_image] at hu
    obtain ⟨c₀, hc₀B, hc₀u⟩ := hu
    -- u is the normalisation of some c₀ ∈ B; so u 0 = 1 and u i ∈ S.
    have hu0 : u ⟨0, hr⟩ = 1 := by
      rw [← hc₀u]; exact normRep_zero hr c₀ (hne0 c₀ hc₀B ⟨0, hr⟩)
    have huS : ∀ i, u i ∈ S := by
      intro i; rw [← hc₀u]
      have hc0 : c₀ ⟨0, hr⟩ ∈ S := hmemS c₀ hc₀B ⟨0, hr⟩
      exact hmul _ (hinv _ hc0) _ (hmemS c₀ hc₀B i)
    have huB : u ∈ B := hc₀u ▸ hmap c₀ hc₀B
    -- the fibre = image of S under g ↦ (g • u), via the bijection g ↦ g • u.
    -- Build the bijection: the fibre filter equals `S.image (fun g => fun i => g * u i)`.
    have hfilter_eq :
        B.filter (fun c => normRep hr c = u) = S.image (fun g => fun i => g * u i) := by
      ext c
      simp only [mem_filter, mem_image]
      constructor
      · rintro ⟨hcB, hcu⟩
        refine ⟨c ⟨0, hr⟩, hmemS c hcB ⟨0, hr⟩, ?_⟩
        funext i
        -- c i = c 0 * u i  since u i = (c 0)⁻¹ * c i
        have : u i = (c ⟨0, hr⟩)⁻¹ * c i := by rw [← hcu]; rfl
        rw [this, ← mul_assoc, mul_inv_cancel₀ (hne0 c hcB ⟨0, hr⟩), one_mul]
      · rintro ⟨g, hgS, rfl⟩
        constructor
        · -- (fun i => g * u i) ∈ B
          rw [hB, mem_filter, Fintype.mem_piFinset]
          refine ⟨fun i => hmul _ hgS _ (huS i), ?_⟩
          have hsum : ∑ i, g * u i = g * ∑ i, u i := by rw [Finset.mul_sum]
          have huzero : ∑ i, u i = 0 := by
            have := huB; rw [hB, mem_filter] at this; exact this.2
          rw [hsum, huzero, mul_zero]
        · -- normRep (g • u) = u
          funext i
          have hg0 : g ≠ 0 := fun h => h0 (h ▸ hgS)
          simp only [normRep, hu0, mul_one]
          -- goal: g⁻¹ * (g * u i) = u i
          rw [← mul_assoc, inv_mul_cancel₀ hg0, one_mul]
    -- now: fibre card = |S.image (g ↦ g•u)| = |S| since g ↦ g•u is injective (u 0 = 1 ≠ 0).
    rw [hfilter_eq, Finset.card_image_of_injOn]
    intro g hg g' hg' hgg'
    -- g • u = g' • u at coordinate 0 gives g * 1 = g' * 1
    have := congrFun hgg' ⟨0, hr⟩
    simpa [hu0] using this
  -- assemble: zeroSumCount = #orbits * |S|, so |S| ∣ zeroSumCount.
  have hcard := card_eq_orbitCount_mul_size B (normRep hr) S.card hmap hfib
  have : zeroSumCount S r = B.card := rfl
  rw [this, hcard]
  exact Dvd.intro_left _ rfl

end ArkLib.ProximityGap.NegationClosedWalk

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.NegationClosedWalk.card_dvd_zeroSumCount_of_subgroup
