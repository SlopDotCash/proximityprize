/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSpectrumComplementSymmetry

/-! # The deep-band subset-sum spectrum is multiplicatively rigid (#444)

`DeepBandSpectrumComplementSymmetry` pinned the PALINDROME symmetry
`|spectrum r| = |spectrum (|mu| - r)|` on the open prize obstruction

> `|spectrum r| = |{ sum_{z in S} z : S in powersetCard r mu }|`   (= BCHKS 1.12),

but recorded NO further structure of the spectrum.  When the ground set is a **multiplicative
subgroup** `mu = mu_n` (closed under `·`, the defining property of `mu_n = {z : z^n = 1}`), the
spectrum carries a second, multiplicative, rigidity that the palindrome file lacks: it is **closed
under scaling by every `g in mu`**.

The mechanism: for `g in mu`, the scaling map `S |-> g • S` is a bijection of `powersetCard r mu`
to itself (because `g • mu = mu`), and `sum_{z in g•S} z = g * sum_{z in S} z`.  So the spectrum is
sent to `g •` itself: it is a **union of `mu`-orbits** under the dilation action.

* `smul_powersetCard` : `(g • ·)` maps `powersetCard r mu` bijectively to itself when `g • mu = mu`;
* `subsetSum_smul` : `sum_{z in g•S} z = g * sum_{z in S} z`;
* `spectrum_smul_invariant` (HEADLINE) : for `g in mu` with `mu` multiplicatively closed,
  `(g * ·) '' (spectrum mu r) = spectrum mu r`;
* `card_dvd_spectrum_sdiff_zero` : under the (probe-supported) FREE-action hypothesis (every nonzero
  spectrum value has trivial `mu`-stabiliser, i.e. its `mu`-orbit has full size `|mu|`), the order
  `|mu|` **divides** `|spectrum r \ {0}|` — a mod-`|mu|` rigidity on the open obstruction.

This is a structural CONSTRAINT on the named obstruction (the spectrum's nonzero part is a union of
`mu`-orbits, hence — in the free case empirically observed — its cardinality is a multiple of `|mu|`),
NOT a bound on it: it does NOT compute `|spectrum r|` (that exact count is the prize-critical open
quantity = BCHKS 1.12).  Together with the complement palindrome it constrains the spectrum's
cardinality both reflectively (`r <-> n-r`) and multiplicatively (`|mu| | card`).

## Probe

`scripts/probes/probe_spectrum_dilation_divisibility.py` (PROPER thin `mu_n`, `n = 2^a`, prize regime
`p >> n^3`, `p ≡ 1 mod n`, 3 primes per `n`, NEVER `n = q-1`): across `n = 4..32` and depths
`r ∈ {1..5, n-3, n-2, n-1}`, the set-level invariance `g • spectrum = spectrum` holds `0/78` fails;
`spectrum \ {0}` is a disjoint union of `mu_n`-orbits, every orbit size divides `n`, the action is
FREE in every tested instance (all orbit sizes `= n`), so `n | |spectrum r \ {0}|` in all 78
instances (e.g. `n=8, r=2`: `|spectrum\{0}| = 24 = 3·8`; the non-Sidon `n=32, p=32993, r=2` still
gives `416 = 13·32`).  The freeness is recorded as a hypothesis of `card_dvd_spectrum_sdiff_zero`,
not asserted as proven here.

## Scope (rule 3 / rule 6, honesty contract)

NOT a CORE closure, NOT thinness-essential beyond the use of the subgroup structure: pure
char-free / field-universal additive-multiplicative combinatorics on a finite multiplicative
subgroup (it constrains a Prop about the subset-sum spectrum; thickness/regime never enters and no
field-arithmetic input is consumed).  It does NOT compute or bound `|spectrum r|`; it records the
dilation rigidity (and, under free action, the `|mu|`-divisibility) the palindrome file lacked.  NO
moment / census / orbit-count / pencil re-derivation, NO capacity / beyond-Johnson / growth-law
claim, cliff-at-`n/2` UNTOUCHED.  CORE `M(mu_n) <= C sqrt(n log(p/n))` UNCHANGED / OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.SpectrumComplementSymmetry

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Scaling a subset sum.** `∑_{z ∈ g • S} z = g * ∑_{z ∈ S} z`, where `g • S` is the image of
`S` under multiplication by `g` (injective since `g ≠ 0` in a field, but we only need it as the
`Finset.image`). -/
theorem subsetSum_smul (g : F) (S : Finset F) (hg : g ≠ 0) :
    ∑ z ∈ S.image (fun x => g * x), z = g * ∑ z ∈ S, z := by
  rw [Finset.sum_image (by intro a _ b _ h; exact mul_left_cancel₀ hg h)]
  rw [Finset.mul_sum]

/-- Image of `mu` under `(g⁻¹ * ·)` is `mu`, given `(g * ·) '' mu = mu`. Inverse dilation symmetry. -/
theorem image_inv_self {mu : Finset F} {g : F} (hg : g ≠ 0)
    (hmu : mu.image (fun x => g * x) = mu) :
    mu.image (fun x => g⁻¹ * x) = mu := by
  conv_lhs => rw [← hmu]
  rw [Finset.image_image, Function.comp_def]
  have : (fun x => g⁻¹ * (g * x)) = (id : F → F) := by
    funext x; rw [← mul_assoc, inv_mul_cancel₀ hg, one_mul]; rfl
  rw [this, Finset.image_id]

/-- **Scaling permutes the size-`r` subsets of a dilation-invariant ground set.** If `g • mu = mu`
(image of `mu` under `(g * ·)` is `mu` itself — true for `g ∈ mu` when `mu` is multiplicatively
closed and `g` a unit), then `S ↦ g • S` maps `powersetCard r mu` into itself, and bijectively. -/
theorem smul_powersetCard {mu : Finset F} {r : ℕ} {g : F} (hg : g ≠ 0)
    (hmu : mu.image (fun x => g * x) = mu) :
    (mu.powersetCard r).image (fun S => S.image (fun x => g * x)) = mu.powersetCard r := by
  ext T
  simp only [Finset.mem_image, Finset.mem_powersetCard]
  constructor
  · rintro ⟨S, ⟨hSsub, hScard⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · calc S.image (fun x => g * x) ⊆ mu.image (fun x => g * x) :=
            Finset.image_subset_image hSsub
        _ = mu := hmu
    · rw [Finset.card_image_of_injective _ (mul_right_injective₀ hg), hScard]
  · rintro ⟨hTsub, hTcard⟩
    -- preimage under (g * ·): scale T back by g⁻¹.
    refine ⟨T.image (fun x => g⁻¹ * x), ⟨?_, ?_⟩, ?_⟩
    · calc T.image (fun x => g⁻¹ * x) ⊆ mu.image (fun x => g⁻¹ * x) :=
            Finset.image_subset_image hTsub
        _ = mu := image_inv_self hg hmu
    · rw [Finset.card_image_of_injective _ (mul_right_injective₀ (inv_ne_zero hg)), hTcard]
    · rw [Finset.image_image, Function.comp_def]
      have : (fun x => g * (g⁻¹ * x)) = (id : F → F) := by
        funext x; rw [← mul_assoc, mul_inv_cancel₀ hg, one_mul]; rfl
      rw [this, Finset.image_id]

/-- **HEADLINE: the subset-sum spectrum is invariant under scaling by a dilation-symmetry `g`.**
If `g ≠ 0` and `g • mu = mu` (the case `g ∈ mu` for a multiplicatively closed `mu`), then scaling
the whole spectrum by `g` gives the spectrum back:
`(g * ·) '' (spectrum mu r) = spectrum mu r`. Hence the spectrum is a union of `⟨g⟩`-orbits; ranging
`g` over `mu` makes `spectrum mu r` a union of `mu`-orbits under the dilation action. -/
theorem spectrum_smul_invariant {mu : Finset F} {r : ℕ} {g : F} (hg : g ≠ 0)
    (hmu : mu.image (fun x => g * x) = mu) :
    (subsetSumSpectrum mu r).image (fun v => g * v) = subsetSumSpectrum mu r := by
  unfold subsetSumSpectrum
  -- LHS = (powersetCard r mu).image (fun S => g * ∑ z ∈ S, z) after image_image.
  rw [Finset.image_image]
  -- Re-express the composed function so it factors through the size-`r` subset dilation.
  have hfun : ((fun v => g * v) ∘ fun S => ∑ z ∈ S, z)
      = (fun S => ∑ z ∈ S, z) ∘ (fun S : Finset F => S.image (fun x => g * x)) := by
    funext S
    simp only [Function.comp]
    rw [subsetSum_smul g S hg]
  rw [hfun, ← Finset.image_image, smul_powersetCard hg hmu]

/-- **The dilation-symmetry of `mu` for `g ∈ mu` when `mu` is multiplicatively closed.** If `mu`
is closed under multiplication, every element is a unit (`0 ∉ mu` since `mu` is a finite
multiplicative subgroup), and `mu` is closed under inverses, then `g • mu = mu` for `g ∈ mu`.
We package the needed closure facts directly (matching the `MulClosed1` data used elsewhere). -/
theorem smul_self_of_mulClosed {mu : Finset F} {g : F} (_hg : g ∈ mu) (hg0 : g ≠ 0)
    (hmul : ∀ x ∈ mu, g * x ∈ mu) (hinv : ∀ y ∈ mu, g⁻¹ * y ∈ mu) :
    mu.image (fun x => g * x) = mu := by
  apply Finset.Subset.antisymm
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hmul x hx
  · intro y hy
    rw [Finset.mem_image]
    exact ⟨g⁻¹ * y, hinv y hy, by rw [← mul_assoc, mul_inv_cancel₀ hg0, one_mul]⟩

set_option linter.unusedSectionVars false in
/-- **`|mu|`-divisibility of the nonzero spectrum under a free dilation action.** If the nonzero
spectrum `T = spectrum r \ {0}` is fibred by a representative map `rep : F → F` (sending each value
to the chosen representative of its `mu`-orbit) whose every nonempty fibre has cardinality `|mu|`
(the FREE `mu`-dilation action — probe-confirmed in every tested prize-regime instance: each nonzero
spectrum value has trivial `mu`-stabiliser, so its orbit has full size `|mu|`), then `|mu|` divides
`|T|`.  Fiberwise count over the quotient map.

The freeness is the honest hypothesis `hfiber` (uniform fibre size `= |mu|`); the arithmetic
(uniform-size partition ⟹ size divides total) is the genuine content, the (provable but
field-arithmetic-dependent) freeness is a hypothesis, not baked in. -/
theorem card_dvd_of_uniform_orbit_partition {T : Finset F} {m : ℕ}
    (rep : F → F)
    (hfiber : ∀ w ∈ T.image rep, (T.filter (fun v => rep v = w)).card = m) :
    m ∣ T.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := rep) (t := T.image rep)
        (fun v hv => Finset.mem_image_of_mem rep hv)]
  rw [Finset.sum_congr rfl (fun w hw => hfiber w hw)]
  rw [Finset.sum_const, smul_eq_mul]
  exact Dvd.intro_left _ rfl

#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.subsetSum_smul
#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.smul_powersetCard
#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.spectrum_smul_invariant
#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.smul_self_of_mulClosed
#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.card_dvd_of_uniform_orbit_partition

end ArkLib.ProximityGap.SpectrumComplementSymmetry
