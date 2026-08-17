/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# `DeltaStarOP1BindingN16` — the binding `O_P = 1` at `n = 16`, machine-checked (#444)

The far-line MCA binding direction `x^{n/2+1} + γ·x^{n/2-1}` on `μ_n` (the
character-twisted nodal direction `χ(x)·(x + γ/x)`) has incidence `#bad γ = 1 + (n/2)·O_P`,
where `O_P` counts the distinct nonzero Schur-ratio dilation-orbits (the "benign-plateau"
orbit law). At the binding agreement depth, the campaign's central proxy-face question is
whether `O_P = 1` (a single orbit).

This file CLOSES that question at `n = 16` (proxy face), via a new mechanism discovered
numerically (`scripts/probes/probe_444_{gapped_product,odd_descent,e2_reduction,e2_charzero}.py`):

* the bad interpolating `f` are exactly the ODD polynomials, so `ψ_f - γ := f·x^{n/2+1} - x² - γ`
  is an EVEN polynomial — the agreement level set is antipodal-symmetric and descends via
  `y = x²` to `μ_8`;
* clearing the descended `Φ_γ(y) = c₃y⁶ + c₁y⁵ - y - γ` by `y³` on `μ_8` gives a monic degree-4
  polynomial `y⁴ + γy³ + 0·y² - c₃y - c₁` that must split over `μ_8`; by Vieta a bad `γ`
  corresponds to a 4-subset `{η_j} ⊆ μ_8` with `e₂(η) = 0` and `γ = -e₁(η)`;
* `e₂ = 0` on `μ_8` is the CHAR-0 cyclotomic condition `M_r = M_{r+4}` on pairwise-sum
  multiplicities (since `ζ₈⁴ = -1` and `{1,ζ,ζ²,ζ³}` is a `ℚ`-basis), hence p-independent.

The remaining content is the FINITE combinatorial fact, certified here by `decide`
(NOT `native_decide` — axiom-clean): among the `e₂ = 0` 4-subsets of `ℤ/8`, the ones with
nonzero sum form a single orbit under the dilation `J ↦ J + 1`. Hence `O_P = 1`.

NOTE (honest scope — this is the `n = 16` binding; persistence to `n ≥ 32` is OPEN).
Cross-validated: NubsCarson's direct sweep and lalalune/0xSolace's Schur-ratio dilation-eigenvector
orbit law independently confirm `O_P = 1` at the binding rung for `n = 8, 16`. The direct sweep
(`probe_444_OP_direct_sweep.py`) shows the `O_P = 1` ONSET coincides exactly with `level-set = n/2`
(n=8 at c=2, n=16 at c=3), which is the configuration this descent encodes. Whether `O_P = 1`
persists for `n ≥ 32` is NOT settled here: the `level-set = n/2` config at `n = 32` is rate-dependent
in the model and its identification with the true `n = 32` binding rung is unvalidated (direct
brute-force infeasible) — so neither "persists" nor "fails" is established at `n ≥ 32`. (An earlier
note here over-claimed a refutation; corrected.) One model-independent fact does stand: the char-`p`
additive-energy defect for `e₂ = 0` has its ONSET at `μ_16` (zero defect on `μ_8`; on `μ_16` the
char-`p` count 150/118/86/70 at p = 97/193/257/65537 exceeds the char-0 value 70 at small `p`),
a clean small-scale sighting of the BGK wall. See `docs/kb/deltastar-444-subsetsum-binding.md`.
-/

namespace ArkLib.ProximityGap.DeltaStarOP1BindingN16

open Finset

set_option maxRecDepth 10000

/-- Pairwise-sum multiplicity of a 4-subset `J ⊆ ℤ/8` at residue `r`:
the number of 2-element subsets of `J` whose sum is `r`. -/
def pairMult (J : Finset (ZMod 8)) (r : ZMod 8) : ℕ :=
  ((powersetCard 2 J).filter (fun s => s.sum id = r)).card

/-- The char-0 (cyclotomic) condition `e₂(J) = 0`: the pairwise-sum multiplicities are
antipodally balanced, `M_r = M_{r+4}`. Over `ℚ(ζ₈)` this is exactly `∑ pairs ζ^{i+j} = 0`,
since `ζ₈⁴ = -1` and `{1, ζ, ζ², ζ³}` is a basis. (`abbrev` so `Decidable` sees through it.) -/
abbrev e2vanish (J : Finset (ZMod 8)) : Prop :=
  ∀ r : ZMod 8, pairMult J r = pairMult J (r + 4)

/-- `e₁(J) = 0`: `J` is closed under the antipodal map `x ↦ x + 4` (multiplication by
`-1 = ζ₈⁴` on `μ_8`); its sum of roots then vanishes (antipodal pairs cancel). These are the
trivial `γ = 0` configurations. -/
abbrev e1zero (J : Finset (ZMod 8)) : Prop := J.image (· + 4) = J

/-- The dilation / shift action on configurations, `J ↦ J + 1` (multiplication by `ζ₈`). -/
def shift (J : Finset (ZMod 8)) : Finset (ZMod 8) := J.image (· + 1)

/-- The base representative of the single nonzero binding orbit. -/
def base : Finset (ZMod 8) := {0, 1, 2, 5}

/-- The `e₂ = 0` four-subsets of `ℤ/8` are exactly 10 in number. -/
theorem e2vanish_card :
    (((univ : Finset (ZMod 8)).powersetCard 4).filter (fun J => e2vanish J)).card = 10 := by
  decide

/-- Of those, exactly 2 have `e₁ = 0` (the `μ_4`-cosets, giving `γ = 0`). -/
theorem e2vanish_e1zero_card :
    (((univ : Finset (ZMod 8)).powersetCard 4).filter
      (fun J => e2vanish J ∧ e1zero J)).card = 2 := by decide

/-- **The binding `O_P = 1` at `n = 16` (proxy face).** The `e₂ = 0` four-subsets of `ℤ/8`
with nonzero sum (`¬ e₁ = 0`) form a SINGLE orbit under the dilation `J ↦ J + 1`: each is an
iterate `shift^[t] base`. Since the nonzero bad `γ = -e₁` are the dilation images of one base
configuration, there is exactly one Schur-ratio orbit, i.e. `O_P = 1`. -/
theorem binding_OP_eq_one (J : Finset (ZMod 8))
    (hcard : J.card = 4) (h2 : e2vanish J) (h1 : ¬ e1zero J) :
    ∃ t : Fin 8, J = shift^[t.val] base := by
  revert J; decide

/-- There are exactly 8 nonzero binding configurations (`e₂ = 0`, `¬ e₁ = 0`). Combined with
`binding_OP_eq_one` (each is a dilate `shift^[t] base`) this pins the orbit: a single dilation
orbit of size 8, giving the benign-plateau incidence `#bad = 1 + 8·O_P = 1 + 8·1 = 9`. -/
theorem nonzero_binding_card :
    (((univ : Finset (ZMod 8)).powersetCard 4).filter
      (fun J => e2vanish J ∧ ¬ e1zero J)).card = 8 := by decide

end ArkLib.ProximityGap.DeltaStarOP1BindingN16
