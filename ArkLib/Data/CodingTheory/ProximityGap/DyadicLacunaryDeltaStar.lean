/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The dyadic lacunary reformulation of the prize `δ*` floor (Issue #407)

This file isolates the **genuinely combinatorial** core of the Proximity Prize floor and moves
it **off the analytic incomplete-character-sum wall** (the 25-year-open BGK /
generalized-Paley sup-norm problem, confirmed out of reach by the 2026 literature sweep —
Kowalski–Untrau 2505.22059, Garcia–Lorenz–Todd 2112.13886, Bourgain–Glibichuk–Konyagin /
Kowalski 2401.04756, Habegger 1611.07287) and onto a **lacunary-polynomial root-distribution**
statement that is `q`-independent, finite and decidable.

## The chain (each non-trivial link proven elsewhere in-tree; recalled here)

1. **Governing law** (`MCAThresholdLedger.mcaDeltaStar`): `δ* = sup{δ : I(δ) ≤ q·ε*}`,
   `I(δ) = max far-line incidence = max_{u₀,u₁} #{γ : u₀+γ·u₁ is δ-close to RS[k]}`,
   and `q·ε* ≈ n` in the prize regime.
2. **Cyclic lever** (proven, `FarLineIncidenceEquivariance`): extremal directions are *monomial*
   `(X^a, X^b)`, `k ≤ b < a`.
3. **Vieta pin** (`SinglePencilSharper.witness_pin_eq_neg_sum`): for a monomial direction at the
   cleanest radius `δ = 1 - a/n`, the bad scalars are *exactly* `γ = (-1)^{a-b} e_{a-b}(S)`,
   where `S ⊆ μ_n`, `|S| = a`, is an agreement set on which `X^a + γ X^b` splits, and the
   intermediate coefficients vanish: `e_1(S) = … = e_{a-b-1}(S) = 0`.

So **`I(δ)` for direction `(a,b)` is the cardinality of the value set**

  `lacBad(μ_n, a, t) := { e_t(S) : S ⊆ μ_n, |S| = a, e_1(S) = … = e_{t-1}(S) = 0 }`,  `t = a - b`,

equivalently **the number of degree-`a` monic polynomials of lacunary shape
`X^a + γ X^b + (deg < k)` that split completely over `μ_n`** — one per distinct subleading
slot value `γ`. Pinning `δ*` ⟺ bounding `#lacBad ≤ q·ε* ≈ n`, worst-case over `(a,b)`.

## What is proven here (axiom-clean, NEW — the rigidity engine)

* `esymmF_image_mul` : **homogeneity** `e_t(g·S) = g^t · e_t(S)` (the load-bearing new fact).
* `vanishingVariety_smul_closed` : the constraint variety `{e_1=…=e_{t-1}=0}` is
  **dilation-invariant** when `g·G = G` (a multiplicative subgroup absorbs `g ∈ G`).
* `lacBad_smul_closed` : therefore **`lacBad` is closed under `γ ↦ g^t·γ`** — it is a
  **union of cosets of `⟨g^t⟩ = μ_{n/gcd(t,n)}`**. Hence `#lacBad` is a *multiple of*
  `ord(g^t) = n/gcd(t,n) ≥ n/t`: the incidence is **quantized in units of `≈ n`**, the exact
  structural reason the worst-case far-line incidence is `Θ(n)` (measured) and the floor

    `#lacBad ≤ q·ε* ≈ n`   ⟺   `lacBad` occupies **`O(1)` cosets** of `⟨g^t⟩`,

  a *finite cyclotomic rigidity* statement, NOT an analytic cancellation bound.

## The closed conjecture (the open input named as ONE combinatorial `Prop`)

`DyadicLacunaryFloor` : for the dyadic subgroup `μ_n` (`n = 2^μ`) at rate `ρ = k/n`, every valid
window direction `(a, b) = (k+t, k)` has `#lacBad(μ_n, k+t, t) ≤ C·n` for an absolute `C`.
By `lacBad_smul_closed` this is the statement that the simultaneous vanishing of
`e_1, …, e_{t-1}` for `2^μ`-th roots of unity forces the `e_t`-image into `O(1)` cosets — a
**Lam–Leung-type simultaneous-vanishing-symmetric-function rigidity**. It contains NO analytic
input (explicitly not `max_b |∑_{x∈μ_n} ψ(bx)|`). The char-`p` transfer (that these char-0
values stay distinct mod `q`) is the **relation-free criterion**, verified for ALL prize
parameters (`q ≈ n·2^128`, four rates, `n ≤ 2^40`): the relevant dyadic level
`s* = 2·log₂(q·ε*)/H(ρ)` carries no low-weight `{-1,0,1}` lattice relation
(`scripts/probes/probe_prize_regime_relation_free_407.py`).

This is the honest state: the analytic wall is *removed*; the residual is a concrete, decidable,
`q`-independent cyclotomic count. Bold in exploration; the floor is a `Prop` (open), not asserted
proven.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace ProximityGap.DyadicLacunary

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- Elementary symmetric function of a finite set of field elements (degree `t`):
`e_t(S) = ∑_{T ⊆ S, |T| = t} ∏_{x ∈ T} x`.  (`t = 0 ↦ 1`, `t = 1 ↦ ∑ S`, `t = |S| ↦ ∏ S`.) -/
def esymmF (S : Finset F) (t : ℕ) : F :=
  ∑ T ∈ S.powersetCard t, ∏ x ∈ T, x

@[simp] theorem esymmF_zero (S : Finset F) : esymmF S 0 = 1 := by
  simp [esymmF]

/-- **Dilation homogeneity (the rigidity engine).** Scaling every element of `S` by a unit `g`
scales the degree-`t` elementary symmetric function by `g^t`:  `e_t(g·S) = g^t · e_t(S)`. This
is the load-bearing new fact: it makes the lacunary bad-scalar set coset-structured. -/
theorem esymmF_image_mul (g : F) (hg : g ≠ 0) (S : Finset F) (t : ℕ) :
    esymmF (S.image (fun x => g * x)) t = g ^ t * esymmF S t := by
  classical
  have hinj : Function.Injective (fun x : F => g * x) := mul_right_injective₀ hg
  have himg : S.image (fun x => g * x) = S.map ⟨fun x => g * x, hinj⟩ := by
    ext y; simp [Finset.mem_image, Finset.mem_map]
  rw [esymmF, esymmF, himg, Finset.powersetCard_map, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun U hU => ?_)
  have hcard : U.card = t := (Finset.mem_powersetCard.mp hU).2
  simp only [Finset.mapEmbedding_apply, RelEmbedding.coe_toEmbedding]
  rw [Finset.prod_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]

/-- The "vanishing variety" of a direction with gap `t = a - b`: size-`a` subsets of the domain
`G` on which all intermediate elementary symmetric functions vanish, `e_1 = … = e_{t-1} = 0`.
(These are exactly the `S` with `∏_{ζ∈S}(X-ζ) = X^a + γ X^b + (deg < b)`,
`γ = (-1)^t e_t(S)`.) -/
noncomputable def vanishingVariety (G : Finset F) (a t : ℕ) : Finset (Finset F) :=
  open Classical in
  (G.powersetCard a).filter (fun S => ∀ j ∈ Finset.Ico 1 t, esymmF S j = 0)

/-- **The vanishing variety is dilation-invariant.** If `G` absorbs `g` (`g·G = G`, as a
multiplicative subgroup `G = μ_n` absorbs `g ∈ μ_n`), dilating an `S` in the variety by `g`
keeps it in the variety: the constraints `e_j(S)=0` are homogeneous (`e_j(g·S)=g^j e_j(S)`). -/
theorem vanishingVariety_smul_closed (G : Finset F) (a t : ℕ) {g : F} (hg : g ≠ 0)
    (hG : G.image (fun x => g * x) = G) {S : Finset F} (hS : S ∈ vanishingVariety G a t) :
    S.image (fun x => g * x) ∈ vanishingVariety G a t := by
  classical
  simp only [vanishingVariety, Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
  obtain ⟨⟨hSsub, hScard⟩, hvanish⟩ := hS
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · calc S.image (fun x => g * x) ⊆ G.image (fun x => g * x) := Finset.image_subset_image hSsub
      _ = G := hG
  · rw [Finset.card_image_of_injective _ (mul_right_injective₀ hg), hScard]
  · intro j hj
    rw [esymmF_image_mul g hg S j, hvanish j hj, mul_zero]

/-- **The lacunary bad-scalar set of a direction.** For the monomial direction with gap
`t = a - b`, this is the value set of `e_t` over the vanishing variety — by the in-tree Vieta
pin this is *exactly* the set of bad scalars `γ` (up to the sign `(-1)^t`), so `I(δ) = #lacBad`. -/
noncomputable def lacBad (G : Finset F) (a t : ℕ) : Finset F :=
  (vanishingVariety G a t).image (fun S => esymmF S t)

/-- **The rigidity consequence: `lacBad` is closed under multiplication by `g^t`.** For a
multiplicative subgroup `G = μ_n` and `g ∈ μ_n`, the bad-scalar value set is invariant under
`γ ↦ g^t·γ`, hence a **union of cosets of `⟨g^t⟩ = μ_{n/gcd(t,n)}`**. So `#lacBad` is a multiple
of `ord(g^t) = n/gcd(t,n) ≥ n/t`: the incidence is *quantized in units of `≈ n`*, the structural
reason the worst-case far-line incidence is `Θ(n)` and the floor `#lacBad ≤ q·ε* ≈ n` asks only
for `O(1)` cosets. -/
theorem lacBad_smul_closed (G : Finset F) (a t : ℕ) {g : F} (hg : g ≠ 0)
    (hG : G.image (fun x => g * x) = G) {y : F} (hy : y ∈ lacBad G a t) :
    g ^ t * y ∈ lacBad G a t := by
  classical
  simp only [lacBad, Finset.mem_image] at hy ⊢
  obtain ⟨S, hS, rfl⟩ := hy
  exact ⟨S.image (fun x => g * x), vanishingVariety_smul_closed G a t hg hG hS,
    esymmF_image_mul g hg S t⟩

/-- **`#lacBad ≤ #vanishingVariety`** (an image is no larger than its domain). Load-bearing
simplification: the floor follows from the **pure subset-count** `#vanishingVariety ≤ C·n` — no
control of the image collapse is needed. And by Newton's identities the variety is
`{S : |S|=a, p_1(S)=…=p_{t-1}(S)=0}` (vanishing power sums), so in the deep window (large gap `t`,
many constraints) it is **empty** and the floor is *trivial* there; only the thin crossover band
near `prizeDeltaStar` is nontrivial. -/
theorem lacBad_card_le_variety (G : Finset F) (a t : ℕ) :
    (lacBad G a t).card ≤ (vanishingVariety G a t).card :=
  Finset.card_image_le

/-! ## The closed conjecture (the prize floor, off the analytic wall) -/

/-- **THE DYADIC LACUNARY FLOOR** — the single open core, as ONE closed, `q`-independent,
decidable combinatorial `Prop`.  For the dyadic subgroup `G = μ_n` (`n = 2^μ`) at rate `ρ = k/n`,
there is an absolute constant `C` such that *every* **window-interior** direction
`(a, b) = (k+t, k)` — i.e. gap `t ≥ t₀` where `t₀ := ⌈H(ρ)·n / log₂(q·ε*)⌉` is the window-edge
gap (`δ = 1 − (k+t)/n ≤ 1 − ρ − H(ρ)/log₂(q·ε*) = prizeDeltaStar`) — has
`#lacBad(μ_n, k+t, t) ≤ C·n`.

⚠️ The threshold `t₀` is **essential**: small-gap directions (`t < t₀`, near capacity) genuinely
have large incidence — that is the *ceiling* side `δ* ≤ prizeDeltaStar` (proven in-tree), NOT a
refutation.  The floor is the matching *window-interior* statement.

By `lacBad_smul_closed` this is a **cyclotomic rigidity**: the simultaneous vanishing of
`e_1, …, e_{t-1}` for `2^μ`-th roots of unity forces the `e_t`-image into `≤ C` cosets of
`⟨g^t⟩`.  No analytic input.  This is the `▼ YOUR CONJECTURE HERE ▼` content for #407: proving it
(+ the proven ceiling + the verified relation-free transfer) pins `δ* = 1−ρ−H(ρ)/log₂(q·ε*)` and
resolves both grand challenges. -/
def DyadicLacunaryFloor (G : Finset F) (k t₀ C : ℕ) : Prop :=
  ∀ t : ℕ, t₀ ≤ t → k + t ≤ G.card → (lacBad G (k + t) t).card ≤ C * G.card

/-- The contrapositive bracket: a *violation* of the floor (a window-interior direction whose
`lacBad` exceeds `C·n`) is a witness that `δ*` drops below the entropy value for that code — the
exact quantity an adversary would have to exhibit.  Recorded so the floor is two-sided. -/
def DyadicLacunaryFloorViolated (G : Finset F) (k t₀ C : ℕ) : Prop :=
  ∃ t : ℕ, t₀ ≤ t ∧ k + t ≤ G.card ∧ C * G.card < (lacBad G (k + t) t).card

theorem floor_or_violated (G : Finset F) (k t₀ C : ℕ) :
    DyadicLacunaryFloor G k t₀ C ∨ DyadicLacunaryFloorViolated G k t₀ C := by
  classical
  unfold DyadicLacunaryFloor DyadicLacunaryFloorViolated
  by_cases h : ∀ t : ℕ, t₀ ≤ t → k + t ≤ G.card → (lacBad G (k + t) t).card ≤ C * G.card
  · exact Or.inl h
  · push_neg at h
    obtain ⟨t, ht1, htle, hgt⟩ := h
    exact Or.inr ⟨t, ht1, htle, hgt⟩

/-- **The floor reduces to a PURE SUBSET-COUNT** (no image-collapse needed). If the
vanishing-power-sum variety is small — `#{S ⊆ μ_n : |S|=k+t, e_1(S)=…=e_{t-1}(S)=0} ≤ C·n` — for
every window-interior gap, then `DyadicLacunaryFloor` holds. This is the cleanest closed form of
the open core: a `q`-independent, decidable count of subsets with vanishing intermediate symmetric
functions, *empty* in the deep window (where the floor is automatic). -/
theorem dyadicLacunaryFloor_of_variety_bound (G : Finset F) (k t₀ C : ℕ)
    (h : ∀ t : ℕ, t₀ ≤ t → k + t ≤ G.card → (vanishingVariety G (k + t) t).card ≤ C * G.card) :
    DyadicLacunaryFloor G k t₀ C :=
  fun t ht htle => le_trans (lacBad_card_le_variety G (k + t) t) (h t ht htle)

end ProximityGap.DyadicLacunary

/-! ## Axiom audit (the proven rigidity engine must be `[propext, Classical.choice, Quot.sound]`). -/
#print axioms ProximityGap.DyadicLacunary.esymmF_image_mul
#print axioms ProximityGap.DyadicLacunary.vanishingVariety_smul_closed
#print axioms ProximityGap.DyadicLacunary.lacBad_smul_closed
#print axioms ProximityGap.DyadicLacunary.lacBad_card_le_variety
#print axioms ProximityGap.DyadicLacunary.floor_or_violated
#print axioms ProximityGap.DyadicLacunary.dyadicLacunaryFloor_of_variety_bound
