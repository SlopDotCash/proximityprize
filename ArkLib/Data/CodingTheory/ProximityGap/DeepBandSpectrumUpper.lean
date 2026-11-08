/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The antipodal-pairing UPPER bound on the deep-band subset-sum spectrum (#389)

For a *negation-closed* domain `A = P ⊔ (-P)` (i.e. `-p ∉ P` for `p ∈ P`), every `r`-subset-sum
of `A` is a **signed** sum over a subset `J ⊆ P` with `|J| ≤ r` and `|J| ≡ r (mod 2)`: pairing
`p` with `-p`, a subset `S ⊆ A` contributes `0` from every antipodal pair it contains in full,
`+p` (resp. `-p`) from the singletons.  Hence the `r`-subset-sum spectrum embeds into the finite
set of signed sums `signedSpectrum P r`.  The index `J` is moreover *realizable*: `J` and the
set of fully-contained antipodal pairs are disjoint subsets of `P`, so `r + |J| ≤ 2|P|`.  This
gives the closed-form cardinality ceilings

  `|spectrum_r|  ≤  ∑_{ℓ≤r, ℓ≡r (2), r+ℓ≤2|P|}  C(|P|,ℓ)·2^ℓ  ≤  ∑_{ℓ≤r, ℓ≡r (2)}  C(|P|,ℓ)·2^ℓ`.

The realizable weight set `{ℓ ≤ r : ℓ ≡ r (2), r + ℓ ≤ 2|P|}` is the canonical
`LadderSpectrumFusion.validWeights |P| r`.

**Scope (upper bounds only).**  Both ceilings are proven from the antipodal pairing alone (no
cyclotomic power-basis independence).  Neither is an exact spectrum count in general, and the
coarse ceiling (without `r + ℓ ≤ 2|P|`) is **not** always below the trivial `C(2|P|, r)`: for
`|P| = 2`, `r = 4` (e.g. `P = {1, i}` over `ℂ`, domain `μ₄`) the only `4`-subset is the whole
domain, so the spectrum has size `1`, while the coarse ceiling is `C(2,0) + 4·C(2,2) = 5 > 1 =
C(4,4)` (`coarse_ceiling_exceeds_trivial_example`); at `r = 1` the coarse ceiling equals `2|P| =
C(2|P|,1)`, with no strict improvement.  The refined ceiling removes the spurious `r + ℓ > 2|P|`
terms.  Exactness of the refined mass (`= ∑_{a ∈ validWeights h r} 2^a·C(h,a)`) needs an
injectivity input on the signed data and is proved, under that explicit guard, by
`LadderSpectrumFusionExact.subsetSum_image_card_eq` (for the domain `{g^i : i < 2h}`,
`g^h = −1`).  The matching lower bracket `2^r·C(2^{m-1}, r) ≤ |spectrum|` is `kkh26_lemma1`.

## Main results
* `subset_sum_eq_signed` — the antipodal sum-decomposition `∑_{a∈S} a = ∑_{p∈J} ±p`.
* `spectrum_subset_signedSpectrum` — the spectrum embeds in `signedSpectrum P r`.
* `signedSpectrum_card_le_valid_sum` — the realizable ceiling `∑_{r+ℓ≤2|P|} C(|P|,ℓ)·2^ℓ`.
* `signedSpectrum_card_le_choose_sum` — the coarse ceiling `∑ C(|P|,ℓ)·2^ℓ`.
* `deepband_spectrum_card_le_valid_sum`, `deepband_spectrum_card_le_choose_sum` — the bounds
  applied to the `-∑` deep-band spectrum.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.SpectrumUpper

variable {F : Type*} [Field F] [DecidableEq F]

/-- The signed-sum index image: `J ⊆ P` with `|J| ≤ r`, `|J| ≡ r (mod 2)` and the
realizability condition `r + |J| ≤ 2|P|`, mapped to `∑_{j∈J} ±j`. -/
noncomputable def signedSpectrum (P : Finset F) (r : ℕ) : Finset F := by
  classical
  exact (P.powerset.filter
      (fun J => J.card ≤ r ∧ J.card % 2 = r % 2 ∧ r + J.card ≤ 2 * P.card)).biUnion
    (fun J => (Finset.univ : Finset (J → Bool)).image
      (fun s => ∑ j : J, (if s j then (j : F) else -(j : F))))

/-- **Antipodal sum-decomposition.** `∑_{a∈S} a = ∑_{p∈J}(if p∈S then p else -p)`,
`J = {p∈P : exactly one of p,−p ∈ S}`, for `S ⊆ P ⊔ (-P)`. -/
theorem subset_sum_eq_signed
    (P : Finset F) (hPneg : ∀ p ∈ P, -p ∉ P)
    {S : Finset F} (hSsub : ↑S ⊆ ↑P ∪ ↑(P.image (fun p => -p))) :
    (∑ a ∈ S, a)
      = ∑ p ∈ P.filter (fun p => (p ∈ S) ≠ (-p ∈ S)), (if p ∈ S then p else -p) := by
  classical
  set NP := P.image (fun p => -p) with hNP
  have hPNPdisj : Disjoint P NP := by
    rw [Finset.disjoint_left]; intro x hxP hxN
    rw [hNP, Finset.mem_image] at hxN; obtain ⟨p, hp, rfl⟩ := hxN; exact hPneg p hp hxP
  have hScover : S = (S ∩ P) ∪ (S ∩ NP) := by
    rw [← Finset.inter_union_distrib_left]
    refine (Finset.inter_eq_left.mpr ?_).symm
    intro x hx; have := hSsub hx; simpa [Finset.mem_union] using this
  have hSdisj : Disjoint (S ∩ P) (S ∩ NP) :=
    hPNPdisj.mono Finset.inter_subset_right Finset.inter_subset_right
  have hsplit : (∑ a ∈ S, a) = (∑ a ∈ S ∩ P, a) + (∑ a ∈ S ∩ NP, a) := by
    rw [← Finset.sum_union hSdisj, ← hScover]
  set T := P.filter (fun p => -p ∈ S) with hT
  set U := P.filter (fun p => p ∈ S) with hU
  have hNPsum : (∑ a ∈ S ∩ NP, a) = - ∑ p ∈ T, p := by
    have hbij : S ∩ NP = T.image (fun p => -p) := by
      ext x; constructor
      · intro hx; rw [Finset.mem_inter, hNP, Finset.mem_image] at hx
        obtain ⟨hxS, p, hp, rfl⟩ := hx
        exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hxS⟩, rfl⟩
      · intro hx; rw [Finset.mem_image] at hx; obtain ⟨p, hp, rfl⟩ := hx
        rw [Finset.mem_filter] at hp
        exact Finset.mem_inter.mpr ⟨hp.2, by rw [hNP]; exact Finset.mem_image.mpr ⟨p, hp.1, rfl⟩⟩
    rw [hbij, Finset.sum_image (fun a _ b _ h => neg_injective h), ← Finset.sum_neg_distrib]
  have hPsum : (∑ a ∈ S ∩ P, a) = ∑ p ∈ U, p := by
    congr 1; rw [hU]; ext x; rw [Finset.mem_inter, Finset.mem_filter]; tauto
  have hUsum : (∑ p ∈ U, p) = ∑ p ∈ P, (if p ∈ S then p else 0) := by rw [hU, Finset.sum_filter]
  have hTsum : (∑ p ∈ T, p) = ∑ p ∈ P, (if -p ∈ S then p else 0) := by rw [hT, Finset.sum_filter]
  rw [hsplit, hPsum, hNPsum, hUsum, hTsum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∈ S <;> by_cases hq : -p ∈ S <;> simp [hp, hq]

/-- **Containment**: every `r`-subset-sum of `P ⊔ (-P)` lands in `signedSpectrum P r`. -/
theorem subset_sum_mem_signedSpectrum
    (P : Finset F) (hPneg : ∀ p ∈ P, -p ∉ P)
    {S : Finset F} {r : ℕ} (hScard : S.card = r)
    (hSsub : ↑S ⊆ ↑P ∪ ↑(P.image (fun p => -p))) :
    (∑ a ∈ S, a) ∈ signedSpectrum P r := by
  classical
  set NP := P.image (fun p => -p) with hNP
  set J := P.filter (fun p => (p ∈ S) ≠ (-p ∈ S)) with hJ
  have hdecomp := subset_sum_eq_signed P hPneg (S := S) hSsub
  have hPNPdisj : Disjoint P NP := by
    rw [Finset.disjoint_left]; intro x hxP hxN
    rw [hNP, Finset.mem_image] at hxN; obtain ⟨p, hp, rfl⟩ := hxN; exact hPneg p hp hxP
  set U := P.filter (fun p => p ∈ S) with hU
  set Tt := P.filter (fun p => -p ∈ S) with hTt
  set B := P.filter (fun p => p ∈ S ∧ -p ∈ S) with hB
  have hUcard_add : U.card + Tt.card = J.card + 2 * B.card := by
    simp only [hU, hTt, hJ, hB, Finset.card_filter, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p ∈ S <;> by_cases hq : -p ∈ S <;> simp [hp, hq]
  have hScards : S.card = U.card + Tt.card := by
    have hScover : S = (S ∩ P) ∪ (S ∩ NP) := by
      rw [← Finset.inter_union_distrib_left]
      refine (Finset.inter_eq_left.mpr ?_).symm
      intro x hx; have := hSsub hx; simpa [Finset.mem_union] using this
    have hSdisj : Disjoint (S ∩ P) (S ∩ NP) :=
      hPNPdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    have h1 : S.card = ((S ∩ P) ∪ (S ∩ NP)).card := congrArg Finset.card hScover
    rw [h1, Finset.card_union_of_disjoint hSdisj]
    congr 1
    · rw [hU]; congr 1; ext x; rw [Finset.mem_inter, Finset.mem_filter]; tauto
    · rw [hTt]
      have hbij : S ∩ NP = Tt.image (fun p => -p) := by
        ext x; constructor
        · intro hx; rw [Finset.mem_inter, hNP, Finset.mem_image] at hx
          obtain ⟨hxS, p, hp, rfl⟩ := hx
          exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hxS⟩, rfl⟩
        · intro hx; rw [Finset.mem_image] at hx; obtain ⟨p, hp, rfl⟩ := hx
          rw [Finset.mem_filter] at hp
          exact Finset.mem_inter.mpr ⟨hp.2, by rw [hNP]; exact Finset.mem_image.mpr ⟨p, hp.1, rfl⟩⟩
      rw [hbij, Finset.card_image_of_injective _ neg_injective, hTt]
  have hJBdisj : Disjoint J B := by
    rw [hJ, hB, Finset.disjoint_filter]
    intro p _ h1 h2
    exact h1 (by simp [h2.1, h2.2])
  have hJB : J.card + B.card ≤ P.card := by
    rw [← Finset.card_union_of_disjoint hJBdisj]
    exact Finset.card_le_card
      (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hJle : J.card ≤ r := by omega
  have hJpar : J.card % 2 = r % 2 := by omega
  have hJreal : r + J.card ≤ 2 * P.card := by omega
  rw [signedSpectrum, Finset.mem_biUnion]
  refine ⟨J, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
    hJle, hJpar, hJreal⟩, ?_⟩
  rw [Finset.mem_image]
  refine ⟨fun j => decide ((j : F) ∈ S), Finset.mem_univ _, ?_⟩
  rw [hdecomp, ← Finset.sum_attach J (fun p => if p ∈ S then p else -p)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [decide_eq_true_eq]

/-- **The `r`-subset-sum spectrum is contained in `signedSpectrum`** — hence its cardinality is
bounded by `|signedSpectrum P r|`, the `±`-factoring ceiling. -/
theorem spectrum_subset_signedSpectrum
    (P : Finset F) (hPneg : ∀ p ∈ P, -p ∉ P) (r : ℕ) :
    ((P ∪ P.image (fun p => -p)).powersetCard r).image (fun S => ∑ a ∈ S, a)
      ⊆ signedSpectrum P r := by
  classical
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨S, hS, rfl⟩ := hx
  rw [Finset.mem_powersetCard] at hS
  refine subset_sum_mem_signedSpectrum P hPneg hS.2 ?_
  exact_mod_cast hS.1

/-- **Card ceiling**: the number of distinct `r`-subset-sums of `P ⊔ (-P)` is at most
`|signedSpectrum P r|`. -/
theorem subset_sum_card_le_signedSpectrum
    (P : Finset F) (hPneg : ∀ p ∈ P, -p ∉ P) (r : ℕ) :
    (((P ∪ P.image (fun p => -p)).powersetCard r).image (fun S => ∑ a ∈ S, a)).card
      ≤ (signedSpectrum P r).card :=
  Finset.card_le_card (spectrum_subset_signedSpectrum P hPneg r)

/-- `|signedSpectrum P r| ≤ ∑_{J ⊆ P, |J|≤r, |J|≡r (2), r+|J|≤2|P|} 2^{|J|}` — each index `J`
contributes at most `2^{|J|}` signs. -/
theorem signedSpectrum_card_le_sum (P : Finset F) (r : ℕ) :
    (signedSpectrum P r).card
      ≤ ∑ J ∈ P.powerset.filter
          (fun J => J.card ≤ r ∧ J.card % 2 = r % 2 ∧ r + J.card ≤ 2 * P.card), 2 ^ J.card := by
  classical
  rw [signedSpectrum]
  refine le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum ?_)
  intro J _
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

/-- **The realizable closed-form ceiling** (`#389`): grouping the index sets by cardinality,
`|signedSpectrum P r| ≤ ∑_{ℓ≤r, ℓ≡r (2), r+ℓ≤2|P|} C(|P|,ℓ)·2^ℓ`.  The index set is the canonical
realizable weight set `LadderSpectrumFusion.validWeights |P| r`.  This is an UPPER bound from the
antipodal pairing alone (no cyclotomic independence); exactness requires an injectivity input,
see `LadderSpectrumFusionExact.subsetSum_image_card_eq`. -/
theorem signedSpectrum_card_le_valid_sum (P : Finset F) (r : ℕ) :
    (signedSpectrum P r).card
      ≤ ∑ ℓ ∈ (Finset.range (r + 1)).filter (fun ℓ => ℓ % 2 = r % 2 ∧ r + ℓ ≤ 2 * P.card),
          P.card.choose ℓ * 2 ^ ℓ := by
  classical
  refine le_trans (signedSpectrum_card_le_sum P r) ?_
  -- regroup the filtered powerset sum by cardinality
  rw [← Finset.sum_fiberwise_of_maps_to
        (g := fun J => J.card)
        (t := (Finset.range (r + 1)).filter (fun ℓ => ℓ % 2 = r % 2 ∧ r + ℓ ≤ 2 * P.card))
        (by
          intro J hJ
          simp only [Finset.mem_filter, Finset.mem_powerset] at hJ
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_le hJ.2.1, hJ.2.2.1, hJ.2.2.2⟩)]
  apply Finset.sum_le_sum
  intro ℓ _
  -- inner fiber: J ⊆ P with J.card = ℓ (and the filter conditions), summand 2^ℓ
  have hbound : ∀ J ∈ (P.powerset.filter
      (fun J => J.card ≤ r ∧ J.card % 2 = r % 2 ∧ r + J.card ≤ 2 * P.card)).filter
        (fun J => J.card = ℓ),
      2 ^ J.card = 2 ^ ℓ := by
    intro J hJ
    rw [Finset.mem_filter] at hJ
    rw [hJ.2]
  rw [Finset.sum_congr rfl hbound, Finset.sum_const, smul_eq_mul]
  gcongr
  -- count of such J ≤ C(|P|, ℓ)
  refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_powersetCard ℓ P))
  intro J hJ
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset] at hJ
  exact Finset.mem_powersetCard.mpr ⟨hJ.1.1, hJ.2⟩

/-- **The coarse closed-form ceiling** (`#389`):
`|signedSpectrum P r| ≤ ∑_{ℓ≤r, ℓ≡r (2)} C(|P|,ℓ)·2^ℓ`, obtained from
`signedSpectrum_card_le_valid_sum` by dropping the realizability condition `r + ℓ ≤ 2|P|`.  It is
an UPPER bound only, and in general neither exact nor below the trivial `C(2|P|, r)` (see
`coarse_ceiling_exceeds_trivial_example`). -/
theorem signedSpectrum_card_le_choose_sum (P : Finset F) (r : ℕ) :
    (signedSpectrum P r).card
      ≤ ∑ ℓ ∈ (Finset.range (r + 1)).filter (fun ℓ => ℓ % 2 = r % 2),
          P.card.choose ℓ * 2 ^ ℓ := by
  refine le_trans (signedSpectrum_card_le_valid_sum P r) (Finset.sum_le_sum_of_subset ?_)
  intro ℓ hℓ
  simp only [Finset.mem_filter] at hℓ ⊢
  exact ⟨hℓ.1, hℓ.2.1⟩

/-- **The coarse ceiling is not below the trivial bound in general.**  At `|P| = 2`, `r = 4`
(e.g. `P = {1, i}` over `ℂ`, domain `μ₄`, whose spectrum has exactly one value), the coarse mass
`∑_{ℓ≤4, ℓ even} C(2,ℓ)·2^ℓ` is `5`, exceeding the trivial `C(4,4) = 1`; the realizable mass
(with `4 + ℓ ≤ 4`) is `1`. -/
theorem coarse_ceiling_exceeds_trivial_example :
    ∑ ℓ ∈ (Finset.range (4 + 1)).filter (fun ℓ => ℓ % 2 = 4 % 2), (2 : ℕ).choose ℓ * 2 ^ ℓ = 5 ∧
      (4 : ℕ).choose 4 = 1 ∧
      ∑ ℓ ∈ (Finset.range (4 + 1)).filter (fun ℓ => ℓ % 2 = 4 % 2 ∧ 4 + ℓ ≤ 2 * 2),
        (2 : ℕ).choose ℓ * 2 ^ ℓ = 1 := by
  decide

/-- **The deep-band bad-scalar bridge, realizable form** (`#389`).  For the deep-band subset-sum
spectrum `(μ.powersetCard r).image (fun S => -∑_{ζ∈S} ζ)` of a *negation-closed* domain
`μ = P ⊔ (-P)`:

  `|spectrum_r| ≤ ∑_{ℓ≤r, ℓ≡r (2), r+ℓ≤2|P|} C(|P|,ℓ)·2^ℓ`.

An UPPER bound from antipodal pairing alone; equality needs an injectivity guard on the signed
data (`LadderSpectrumFusionExact.subsetSum_image_card_eq`). -/
theorem deepband_spectrum_card_le_valid_sum
    (P : Finset F) (hPneg : ∀ p ∈ P, -p ∉ P)
    (μ : Finset F) (hμ : μ = P ∪ P.image (fun p => -p)) (r : ℕ) :
    ((μ.powersetCard r).image (fun S => -∑ a ∈ S, a)).card
      ≤ ∑ ℓ ∈ (Finset.range (r + 1)).filter (fun ℓ => ℓ % 2 = r % 2 ∧ r + ℓ ≤ 2 * P.card),
          P.card.choose ℓ * 2 ^ ℓ := by
  classical
  subst hμ
  have hcard : (((P ∪ P.image (fun p => -p)).powersetCard r).image (fun S => -∑ a ∈ S, a)).card
      = (((P ∪ P.image (fun p => -p)).powersetCard r).image (fun S => ∑ a ∈ S, a)).card := by
    rw [show (fun S => -∑ a ∈ S, a) = (fun x : F => -x) ∘ (fun S => ∑ a ∈ S, a) from rfl,
      ← Finset.image_image, Finset.card_image_of_injective _ neg_injective]
  rw [hcard]
  exact le_trans (subset_sum_card_le_signedSpectrum P hPneg r)
    (signedSpectrum_card_le_valid_sum P r)

/-- **The deep-band bad-scalar bridge, coarse form** (`#389`).  For the deep-band subset-sum
spectrum `(μ.powersetCard r).image (fun S => -∑_{ζ∈S} ζ)` of a *negation-closed* domain
`μ = P ⊔ (-P)` (the case `μ = μ_{2^m}`, `P` the lower half, `-ζ^j = ζ^{j+2^{m-1}}`):

  `|spectrum_r| ≤ ∑_{ℓ≤r, ℓ≡r (2)} C(|P|,ℓ)·2^ℓ`.

This is an UPPER bound only.  It is not the exact spectrum cardinality in general and is not
always below the trivial `C(2|P|, r)` (`coarse_ceiling_exceeds_trivial_example`); in the dilute
range `r ≤ |P|` the realizability condition `r + ℓ ≤ 2|P|` is automatic and the coarse and
realizable masses coincide.  Use `deepband_spectrum_card_le_valid_sum` for the realizable mass. -/
theorem deepband_spectrum_card_le_choose_sum
    (P : Finset F) (hPneg : ∀ p ∈ P, -p ∉ P)
    (μ : Finset F) (hμ : μ = P ∪ P.image (fun p => -p)) (r : ℕ) :
    ((μ.powersetCard r).image (fun S => -∑ a ∈ S, a)).card
      ≤ ∑ ℓ ∈ (Finset.range (r + 1)).filter (fun ℓ => ℓ % 2 = r % 2),
          P.card.choose ℓ * 2 ^ ℓ := by
  classical
  subst hμ
  -- the `-∑` spectrum has the same cardinality as the `+∑` spectrum (negation is injective)
  have hcard : (((P ∪ P.image (fun p => -p)).powersetCard r).image (fun S => -∑ a ∈ S, a)).card
      = (((P ∪ P.image (fun p => -p)).powersetCard r).image (fun S => ∑ a ∈ S, a)).card := by
    rw [show (fun S => -∑ a ∈ S, a) = (fun x : F => -x) ∘ (fun S => ∑ a ∈ S, a) from rfl,
      ← Finset.image_image, Finset.card_image_of_injective _ neg_injective]
  rw [hcard]
  exact le_trans (subset_sum_card_le_signedSpectrum P hPneg r)
    (signedSpectrum_card_le_choose_sum P r)

end ArkLib.ProximityGap.SpectrumUpper
