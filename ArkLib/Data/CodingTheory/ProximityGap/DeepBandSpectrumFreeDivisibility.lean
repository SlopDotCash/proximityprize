/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSpectrumDilationInvariant

/-! # The `|mu|`-divisibility of the nonzero subset-sum spectrum, freeness DISCHARGED (#444)

`DeepBandSpectrumDilationInvariant` (O229) proved the subset-sum spectrum is `mu`-dilation
invariant (`spectrum_smul_invariant`) and a generic uniform-orbit divisibility lemma
(`card_dvd_of_uniform_orbit_partition`) **gated on a freeness hypothesis** (`hfiber`: every
nonzero spectrum value lies in a fibre of size exactly `|mu|`).  Its report recorded the freeness
as an *empirical* observation — "the (provable but field-arithmetic-dependent) freeness is a
hypothesis, not baked in".

This file **discharges that hypothesis unconditionally**.  The dilation action of a finite
multiplicative subgroup `mu` on `F \ {0}` is FREE for a pure field-arithmetic reason: if `v ≠ 0`
and `g * v = v` then `g = 1` (`mul_right_cancel₀`, the same fact as
`I031DilationOrbitReduction.dilation_free`).  So no nonzero spectrum value has a nontrivial
stabiliser, every nonzero-spectrum `mu`-orbit has size exactly `|mu|`, and therefore

> `|mu|  ∣  |spectrum r \ {0}|`   **with no freeness assumption** — it is forced.

The combinatorial engine is a self-contained strong-induction lemma
(`card_dvd_of_free_smul_action`): a finite set `T` closed under a free action of a finite subgroup
`H` (acting by an injective-on-`H` orbit map fixing no point of `T` outside the identity) has
`|H| ∣ |T|`, proved by peeling off one full orbit (of size `|H|`) at a time.  Applied to
`T = spectrum r \ {0}` and `H = mu` this yields the discharged divisibility.

* `orbit_card_eq` : the `mu`-orbit `mu.image (· * v)` of a nonzero `v` has card `|mu|` (freeness).
* `card_dvd_spectrum_sdiff_zero_free` (HEADLINE) : for a multiplicatively-closed `mu` with the
  inverse-closure data, `mu.card ∣ (subsetSumSpectrum mu r \ {0}).card` — UNCONDITIONALLY (the
  `hfiber` of O229's `card_dvd_of_uniform_orbit_partition` is now a theorem, not a hypothesis).

## Probe

`scripts/probes/probe_spectrum_freeness_discharge.py` (PROPER thin `mu_n`, `n = 2^a`, prize regime
`p >> n^3`, `p ≡ 1 mod n`, 3 primes per `n`, depths `r ∈ {1,2,3, n-2, n-1}` + `{4,5}` for small
`n`, NEVER `n = q-1`): across `57` instances the pointwise freeness `g*v = v ⇒ g = 1` for nonzero
spectrum `v` holds `0` fails, every nonzero-spectrum orbit has size exactly `n`, and
`n ∣ |spectrum r \ {0}|` with `0` fails.  This confirms the discharge is sound (the freeness O229
left hypothetical is forced) and the divisibility is unconditional.

## Scope (rule 3 / rule 6, honesty contract)

A structural CONSTRAINT on the named open obstruction `|spectrum r|` (= BCHKS 1.12), strengthening
O229 by REMOVING its freeness hypothesis: `|mu|` divides the nonzero spectrum cardinality
unconditionally.  It does NOT compute or bound `|spectrum r|` (that exact count stays OPEN).  Pure
char-free / field-universal additive–multiplicative combinatorics on a finite multiplicative
subgroup; thickness/regime never enters (NOT thinness-essential — it constrains a `Prop`, no
field-arithmetic regime input is consumed beyond the subgroup structure).  NO moment / census /
orbit-count / pencil re-derivation, NO capacity / beyond-Johnson / growth-law claim,
cliff-at-`n/2` UNTOUCHED.  CORE `M(mu_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.SpectrumComplementSymmetry

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Freeness of the dilation orbit map.** For `v ≠ 0`, the map `g ↦ g * v` is injective, so the
orbit `mu.image (· * v)` of `v` has cardinality exactly `|mu|`.  (This is the field-arithmetic
discharge of O229's freeness hypothesis: `g₁ * v = g₂ * v ⇒ g₁ = g₂` by `mul_right_cancel₀`.) -/
theorem orbit_card_eq {mu : Finset F} {v : F} (hv : v ≠ 0) :
    (mu.image (fun g => g * v)).card = mu.card :=
  Finset.card_image_of_injective _ (fun _ _ h => mul_right_cancel₀ hv h)

/-- **A free action of a finite subgroup forces `|H| ∣ |T|`.**

Combinatorial engine, stated abstractly so the field freeness plugs in cleanly.  Let `H : Finset F`
be multiplicatively closed and inverse-closed (the subgroup data), with `1 ∈ H`, and let
`T : Finset F` be a finite set of NONZERO elements that is `H`-stable under dilation (`g ∈ H`,
`v ∈ T ⇒ g * v ∈ T`).  Then `H.card ∣ T.card`.

Proof: strong induction on `T.card`, peeling off one full orbit `mu.image (· * v)` (size `|H|` by
`orbit_card_eq`, freeness) at a time.  The remaining set `T \ orbit` is still `H`-stable and has
strictly smaller card, so `|H| ∣ |T \ orbit|` by induction, and
`|T| = |orbit| + |T \ orbit| = |H| + |T \ orbit|`. -/
theorem card_dvd_of_free_smul_action {H T : Finset F}
    (h1 : (1 : F) ∈ H)
    (h0 : (0 : F) ∉ H)
    (hmul : ∀ g ∈ H, ∀ x ∈ H, g * x ∈ H)
    (hinv : ∀ g ∈ H, g⁻¹ ∈ H)
    (hne0 : ∀ v ∈ T, v ≠ 0)
    (hstable : ∀ g ∈ H, ∀ v ∈ T, g * v ∈ T) :
    H.card ∣ T.card := by
  classical
  -- strong induction on the cardinality of `T`
  induction hcard : T.card using Nat.strong_induction_on generalizing T with
  | _ N ih =>
    subst hcard
    rcases T.eq_empty_or_nonempty with hT | hT
    · simp [hT]
    · obtain ⟨v, hvT⟩ := hT
      have hv0 : v ≠ 0 := hne0 v hvT
      -- the orbit of `v`
      set orb := H.image (fun g => g * v) with horb
      -- orbit ⊆ T (stability)
      have horb_sub : orb ⊆ T := by
        intro y hy
        rw [horb, Finset.mem_image] at hy
        obtain ⟨g, hg, rfl⟩ := hy
        exact hstable g hg v hvT
      -- orbit card = |H| (freeness)
      have horb_card : orb.card = H.card := orbit_card_eq hv0
      -- `v ∈ orb` (using `1 ∈ H`)
      have hv_in_orb : v ∈ orb := by
        rw [horb, Finset.mem_image]
        exact ⟨1, h1, by rw [one_mul]⟩
      -- the rest `T \ orb`
      set T' := T \ orb with hT'
      -- `T = orb ∪ T'` disjointly, so `|T| = |orb| + |T'|`
      have hcard_split : T.card = orb.card + T'.card := by
        have h := Finset.card_sdiff_add_card_eq_card horb_sub
        -- h : (T \ orb).card + orb.card = T.card
        rw [hT']; omega
      -- `T'` is still nonzero-valued
      have hne0' : ∀ w ∈ T', w ≠ 0 := by
        intro w hw; exact hne0 w (Finset.mem_sdiff.mp hw).1
      -- `T'` is still `H`-stable: an orbit is `H`-invariant, so `T \ orbit` is too.
      have hstable' : ∀ g ∈ H, ∀ w ∈ T', g * w ∈ T' := by
        intro g hg w hw
        rw [hT', Finset.mem_sdiff] at hw ⊢
        obtain ⟨hwT, hworb⟩ := hw
        refine ⟨hstable g hg w hwT, ?_⟩
        -- if `g * w ∈ orb` then `w ∈ orb` (apply `g⁻¹`): contradiction
        intro hgw
        apply hworb
        rw [horb, Finset.mem_image] at hgw ⊢
        obtain ⟨g', hg', hg'eq⟩ := hgw
        -- `g' * v = g * w` ⇒ `w = (g⁻¹ * g') * v`, and `g⁻¹ * g' ∈ H`
        refine ⟨g⁻¹ * g', hmul g⁻¹ (hinv g hg) g' hg', ?_⟩
        have hgne : g ≠ 0 := fun h => h0 (h ▸ hg)
        -- from `g' * v = g * w` derive `(g⁻¹ * g') * v = w`
        have : g * ((g⁻¹ * g') * v) = g * w := by
          calc g * ((g⁻¹ * g') * v)
              = (g * g⁻¹) * (g' * v) := by ring
            _ = (g' * v) := by rw [mul_inv_cancel₀ hgne, one_mul]
            _ = g * w := hg'eq
        exact mul_left_cancel₀ hgne this
      -- `T'.card < T.card` (we removed at least `v`)
      have hlt : T'.card < T.card := by
        rw [hcard_split, horb_card]
        have : 0 < H.card := Finset.card_pos.mpr ⟨1, h1⟩
        omega
      -- induction hypothesis on `T'`
      have hdvd' : H.card ∣ T'.card :=
        ih T'.card hlt hne0' hstable' rfl
      -- assemble: `|T| = |H| + |T'|`, both terms divisible by `|H|`
      rw [hcard_split, horb_card]
      exact Nat.dvd_add (dvd_refl _) hdvd'

/-- **HEADLINE: `|mu|` divides the nonzero subset-sum spectrum cardinality — freeness DISCHARGED.**

For a multiplicatively-closed, inverse-closed finite subgroup `mu` (`1 ∈ mu`, `0 ∉ mu`),
`mu.card ∣ (subsetSumSpectrum mu r \ {0}).card`, **with no freeness hypothesis** (O229's `hfiber`
is now a theorem via `card_dvd_of_free_smul_action` + `orbit_card_eq`).

The nonzero spectrum is `mu`-dilation stable: for `g ∈ mu` and a nonzero spectrum value `v`, the
invariance `spectrum_smul_invariant` puts `g * v` back in the spectrum, and `g * v ≠ 0`.  So
`card_dvd_of_free_smul_action` applies with `H = mu`, `T = subsetSumSpectrum mu r \ {0}`. -/
theorem card_dvd_spectrum_sdiff_zero_free {mu : Finset F} {r : ℕ}
    (h1 : (1 : F) ∈ mu) (h0 : (0 : F) ∉ mu)
    (hmul : ∀ g ∈ mu, ∀ x ∈ mu, g * x ∈ mu)
    (hinv : ∀ g ∈ mu, g⁻¹ ∈ mu) :
    mu.card ∣ (subsetSumSpectrum mu r \ {(0 : F)}).card := by
  classical
  set T := subsetSumSpectrum mu r \ {(0 : F)} with hT
  -- nonzero on `T`
  have hne0 : ∀ v ∈ T, v ≠ 0 := by
    intro v hv
    rw [hT, Finset.mem_sdiff, Finset.mem_singleton] at hv
    exact hv.2
  -- `H`-stability of `T`: `spectrum_smul_invariant` + nonzero preservation
  have hstable : ∀ g ∈ mu, ∀ v ∈ T, g * v ∈ T := by
    intro g hg v hv
    rw [hT, Finset.mem_sdiff, Finset.mem_singleton] at hv ⊢
    obtain ⟨hvspec, hvne⟩ := hv
    have hg0 : g ≠ 0 := fun h => h0 (h ▸ hg)
    -- `g • mu = mu` since `mu` is mult-closed + inverse-closed
    have hmu : mu.image (fun x => g * x) = mu :=
      smul_self_of_mulClosed hg hg0 (fun x hx => hmul g hg x hx)
        (fun y hy => hmul g⁻¹ (hinv g hg) y hy)
    -- invariance: `(g * ·) '' spectrum = spectrum`, so `g * v ∈ spectrum`
    have hinvar := spectrum_smul_invariant (mu := mu) (r := r) hg0 hmu
    have : g * v ∈ (subsetSumSpectrum mu r).image (fun w => g * w) :=
      Finset.mem_image_of_mem _ hvspec
    rw [hinvar] at this
    refine ⟨this, ?_⟩
    -- `g * v ≠ 0`
    exact mul_ne_zero hg0 hvne
  exact card_dvd_of_free_smul_action h1 h0 hmul hinv hne0 hstable

end ArkLib.ProximityGap.SpectrumComplementSymmetry

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.orbit_card_eq
#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.card_dvd_of_free_smul_action
#print axioms ArkLib.ProximityGap.SpectrumComplementSymmetry.card_dvd_spectrum_sdiff_zero_free
