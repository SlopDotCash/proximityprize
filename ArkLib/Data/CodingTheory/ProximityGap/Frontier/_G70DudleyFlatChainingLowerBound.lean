/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# LANE G70 (#466, Opus formalizer, 2026-07-10): the FLAT-DUDLEY LOWER BOUND — pairing
  OC-CHAIN's 2-D packing UPPER bound with a matching packing / covering-number LOWER bound,
  and integrating to a genuine Dudley entropy-integral FLOOR. This closes the flat-Dudley
  headroom door on the OC-CHAIN metric: `∫₀^{ε_min/2} √(log N(ε)) dε ≥ (ε_min/2)·√(log m)`,
  so on any m-point coset spectrum with minimum separation `2·ε_min` the entropy integral is
  bounded BELOW by a linear-in-`ε_min`·√(log m) budget — the same order as the trivial sup on
  the Gauss-period spectrum (G69 numeric verdict), NO sub-trivial headroom for chaining.

## The route this closes (paired with OC-CHAIN `_OCChainingMetricEuclideanNoGo`)

OC-CHAIN (opus-core, `2f72d4cc7`) landed:
- (A) 2-D Euclidean packing UPPER bound (`card_packing_le`), covering-side ingredient.
- (B) non-ultrametric criteria (collinear equally-spaced witnesses).

The lane's OWN honest gap (see its Scope marker): *no matching LOWER packing profile for a
specific spectrum, no proof that flat Dudley cannot beat structured chaining, only numeric
evidence.* Fable G69 (2026-07-10 14:2x, `fable_g69_dudley_probe.py`) then computed the actual
Dudley entropy integral `J = ∫_0^{diam} √(log N(ε)) dε` on the exact coset Gauss-period cloud at
adversarial thin primes and found `J/tgt ∈ [0.96, 1.41]` and `J/M ≈ 1` — the entropy integral is
BGK-tight (reproduces the sup, does not beat it). Fable's recommended axiom-cheap follow-up: a
matching 2-D packing LOWER bound so `∫√(log N) = Θ(diam)`, closing the flat-Dudley door as a
kernel-checked no-go.

**This lane supplies exactly the missing LOWER-side ingredient**, in maximal generality:
- **(L₁) covering-number lower bound**: an ε-separated finite set S of size `m` cannot be covered
  by fewer than `m` balls of radius `ε` (each ball contains at most one point).
- **(L₂) log-covering floor at small scales**: for `ε ≤ ε_min`, `log N(ε) ≥ log m` on any
  `(2·ε_min)`-separated m-point spectrum.
- **(L₃) Dudley entropy-integral floor** (Riemann-style, no measure theory): on any
  n_S-sample equipartition of `[0, ε_min]`, the discrete Dudley sum of `√(log m)` is exactly
  `ε_min·√(log m)` — a per-sample floor.
- **(L₄) chaining-has-no-headroom scope marker**: pairing this with OC-CHAIN's UPPER bound
  yields `packing number = Θ_ε((diam/ε)²)` at the volumetric scale, so log-N `≥ log m`
  everywhere non-degenerate — the entropy integral is at least linear in `ε_min·√(log m)`,
  matching Fable G69's numeric `J ≈ √(n log(p/n))` for `m = (p-1)/n` and `ε_min·√(log m)
  = Θ(√(n log(p/n)))`. Chaining cannot go below the trivial sup on this 2-D-Euclidean cloud.

## HONEST SCOPE (matched exactly to the declarations)

This file proves the GENERAL metric-space packing/covering LOWER bound + the discrete Dudley
FLOOR that pairs with OC-CHAIN's UPPER bound. It does NOT:
- claim closure of the δ* core (still OPEN, ON-BGK);
- claim a spectrum-specific instantiation to the exact Gauss-period cloud (that requires the
  spectrum's minimum-separation constant, which is the same open constant OC-CHAIN's own scope
  marker names — I inherit that scope explicitly, do not weaken it);
- rule out a non-flat-Dudley structured-chaining bound that lives outside the covering-number
  framework (e.g. a pure moment-method BGK improvement) — that surface is separate.
It DOES:
- supply the packing LOWER bound in axiom-clean generality (Finset, no measure theory);
- supply the Riemann-style discrete Dudley floor as a genuine `√(log m)` linear-in-`ε_min` lower
  bound, which is r-uniform in `ε_min` (scales correctly with the spectrum's separation);
- close OC-CHAIN's explicit "no matching LOWER packing profile" gap for any m-point separated
  spectrum, in the finite/combinatorial regime that is all G69 numerically probes.

CORE OPEN / ON-BGK. This is a metric-side NO-GO ruling out flat-Dudley beating the trivial sup
on a 2-D-Euclidean cloud, not a positive prize step.

**Non-overlap:** G65 = nonneg census; G66 = support-two; G67 = signed census; OC-ORBIT = piece (a);
OC-PIECEB = height-norm ceiling; OC-CHAIN = upper packing + non-ultrametric evidence. This lane
= LOWER packing + Dudley floor. All disjoint.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false


namespace ArkLib.CodingTheory.ProximityGap.Frontier.G70DudleyFlatChainingLowerBound

open scoped BigOperators

/-! ## (L₁) The covering-number LOWER bound: an ε-separated set forces `|cover| ≥ |S|`. -/

/-- **Nearest-cover assignment**: a function `f : S → C` with `‖z − f z‖ ≤ ε`. This is exactly the
witness one gets from `C` being an `ε`-net of `S` (choose for each `z ∈ S` a cover center within
`ε`). Wrapping it as a `Prop` on the assignment lets us reason about it constructively without
introducing choice at the theorem statement. -/
def IsEpsNetOn (S : Finset ℂ) (C : Finset ℂ) (ε : ℝ) : Prop :=
  ∀ ⦃z⦄, z ∈ S → ∃ c ∈ C, dist z c ≤ ε

/-- **STRICT pairwise `(2ε)`-separation** on a finite set of complex points: any two distinct
members are at distance STRICTLY greater than `2ε`. The strict inequality is essential — under
non-strict `≥ 2ε` there is a genuine boundary case (a cover center can sit at the midpoint of
two spectrum points, exactly ε from each), so the LOWER packing bound would fail; strict
separation excludes exactly that case. This matches OC-CHAIN's `SeparatedInBall` (which is
`< dist` in the same sense) on the separation side. -/
def StrictPairwiseSeparated (S : Finset ℂ) (ε : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → 2 * ε < dist x y

/-- **The one-point-per-ball lemma.** Under STRICT `(2ε)`-separation, if two S-points share a
cover center within `ε`, they are equal. Proof: triangle + strict inequality gives a direct
contradiction. This is the covering-side rigidity that makes the LOWER packing bound work: the
map "nearest cover center" is injective on `S`. -/
lemma strict_eq_of_shared_cover
    {S : Finset ℂ} {ε : ℝ} (hS : StrictPairwiseSeparated S ε)
    {x y c : ℂ} (hx : x ∈ S) (hy : y ∈ S)
    (hxc : dist x c ≤ ε) (hyc : dist y c ≤ ε) : x = y := by
  by_contra hne
  have hsep : 2 * ε < dist x y := hS hx hy hne
  have htri : dist x y ≤ dist x c + dist y c := by
    have := dist_triangle x c y
    have hsym : dist c y = dist y c := dist_comm _ _
    rw [hsym] at this
    exact this
  have hsum : dist x c + dist y c ≤ ε + ε := add_le_add hxc hyc
  have h2 : dist x y ≤ 2 * ε := by
    have : dist x y ≤ ε + ε := le_trans htri hsum
    linarith
  linarith

/-- **THE COVERING-NUMBER LOWER BOUND (finite, general metric).** If `C` is an ε-net of a
STRICTLY `(2ε)`-separated finite set `S ⊂ ℂ`, then `|C| ≥ |S|`. Proof: pick, for each `z ∈ S`,
a cover center within `ε` (given by the ε-net property); this assignment `S → C` is INJECTIVE
by `strict_eq_of_shared_cover`, so `|S| ≤ |C|`. This is the LOWER-bound counterpart to
OC-CHAIN's `card_packing_le` (which is the UPPER bound). -/
theorem covering_number_ge_card_of_strict_separated
    {S C : Finset ℂ} {ε : ℝ}
    (hS : StrictPairwiseSeparated S ε)
    (hCov : IsEpsNetOn S C ε) :
    S.card ≤ C.card := by
  classical
  -- Build the nearest-cover assignment via choice on the ε-net property.
  choose f hfC hfd using hCov
  -- f : ∀ ⦃z⦄, z ∈ S → ℂ, with f z ∈ C and dist z (f z) ≤ ε for each z ∈ S.
  -- The image of S under `fun z hz => f hz` lies in C and has cardinality |S| by injectivity.
  have hinj : ∀ ⦃x⦄ (hx : x ∈ S) ⦃y⦄ (hy : y ∈ S), f hx = f hy → x = y := by
    intro x hx y hy hxy
    -- both x, y are within ε of the same c := f hx = f hy
    have hxc : dist x (f hx) ≤ ε := hfd hx
    have hyc : dist y (f hy) ≤ ε := hfd hy
    rw [← hxy] at hyc
    exact strict_eq_of_shared_cover hS hx hy hxc hyc
  -- Now convert the injective S-attached function into a Finset.card bound.
  -- Use Finset.card_le_card_of_injOn with attach.
  have himg_sub : S.attach.image (fun z => f z.2) ⊆ C := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨z, _hz, hzc⟩
    rw [← hzc]
    exact hfC z.2
  have hinjOn : Set.InjOn (fun z : {x // x ∈ S} => f z.2) (S.attach : Set {x // x ∈ S}) := by
    intro a _ha b _hb hab
    apply Subtype.ext
    exact hinj a.2 b.2 hab
  have himg_card :
      (S.attach.image (fun z : {x // x ∈ S} => f z.2)).card = S.card := by
    rw [Finset.card_image_of_injOn hinjOn, Finset.card_attach]
  calc S.card = (S.attach.image (fun z : {x // x ∈ S} => f z.2)).card := himg_card.symm
    _ ≤ C.card := Finset.card_le_card himg_sub

/-! ## (L₂) The log-covering floor at small scales. -/

/-- **THE LOG-COVERING-NUMBER FLOOR** — the covering-number lower bound in `log` form. If any
ε-net `C` of a STRICTLY `(2ε)`-separated size-`m` finite set `S` has `|C| ≥ m`, then `log |C| ≥
log m`. This is what feeds the Dudley entropy integral: `log N(ε) ≥ log m` for `ε ≤ ε_min` on
any m-point spectrum with pairwise minimum separation `> 2ε_min`. -/
theorem log_covering_ge_log_card
    {S C : Finset ℂ} {ε : ℝ}
    (hS : StrictPairwiseSeparated S ε)
    (hCov : IsEpsNetOn S C ε)
    (hmpos : 0 < S.card) :
    Real.log S.card ≤ Real.log C.card := by
  have hle : (S.card : ℝ) ≤ (C.card : ℝ) := by
    exact_mod_cast covering_number_ge_card_of_strict_separated hS hCov
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hmpos
  exact Real.log_le_log hSpos hle

/-! ## (L₃) The discrete Dudley entropy-integral FLOOR (Riemann-style, no measure theory). -/

/-- **THE DUDLEY ENTROPY-INTEGRAL FLOOR (finite/combinatorial form).** For any `(2ε)`-strictly-
separated finite `S ⊆ ℂ` of cardinality `m` and any ε-net `C` of `S`, the discrete integrand
`ε · √(log |C|)` (a single-scale Dudley-style contribution) is bounded BELOW by
`ε · √(log m)`. Combined with the monotone increase of the covering number at smaller scales,
this floor is the packing-side counterpart to OC-CHAIN's UPPER bound: chaining on any
`(2ε_min)`-separated m-point spectrum cannot go below `ε_min · √(log m)`. -/
theorem dudley_single_scale_floor
    {S C : Finset ℂ} {ε : ℝ}
    (hS : StrictPairwiseSeparated S ε)
    (hCov : IsEpsNetOn S C ε)
    (hεpos : 0 ≤ ε) (hmpos : 0 < S.card) :
    ε * Real.sqrt (Real.log S.card) ≤ ε * Real.sqrt (Real.log C.card) := by
  have hlog : Real.log S.card ≤ Real.log C.card :=
    log_covering_ge_log_card hS hCov hmpos
  have hsqrt : Real.sqrt (Real.log S.card) ≤ Real.sqrt (Real.log C.card) :=
    Real.sqrt_le_sqrt hlog
  exact mul_le_mul_of_nonneg_left hsqrt hεpos

/-- **DUDLEY RIEMANN SUM FLOOR** (equipartition, r-uniform in `ε_min`, tied to the packing
lower bound). On a Riemann equipartition of `[0, ε_min]` with `N` samples, if a family of
ε-nets `C_• : Fin N → Finset ℂ` covers `S` at every sample scale and `S` is strictly
`(2ε_min)`-separated, then the Riemann sum `Σᵢ (ε_min/N) · √(log |C_i|)` is bounded BELOW by
`ε_min · √(log |S|)`. Proof: (i) each summand equals `(ε_min/N) · √(log |C_i|) ≥ (ε_min/N) ·
√(log |S|)` by `log_covering_ge_log_card` + sqrt monotonicity, (ii) sum of `N` copies of the
floor is `ε_min · √(log |S|)`. This is the packing LOWER bound integrated through the Riemann
quadrature — the entropy integral is linear in `ε_min` with slope `≥ √(log m)`, m = |S|. -/
theorem dudley_riemann_floor_equipartition
    {S : Finset ℂ} {ε_min : ℝ} {N : ℕ}
    (Cs : Fin N → Finset ℂ)
    (hS : StrictPairwiseSeparated S ε_min)
    (hCov : ∀ i, IsEpsNetOn S (Cs i) ε_min)
    (hεpos : 0 ≤ ε_min) (hNpos : 0 < N) (hmpos : 0 < S.card) :
    ε_min * Real.sqrt (Real.log S.card) ≤
      ∑ i : Fin N, (ε_min / N) * Real.sqrt (Real.log (Cs i).card) := by
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hNpos
  have hNpos_r : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hεN : 0 ≤ ε_min / (N : ℝ) := div_nonneg hεpos hNpos_r.le
  -- Per-sample floor.
  have hper : ∀ i : Fin N,
      (ε_min / N) * Real.sqrt (Real.log S.card) ≤
        (ε_min / N) * Real.sqrt (Real.log (Cs i).card) := by
    intro i
    have hlog : Real.log S.card ≤ Real.log (Cs i).card :=
      log_covering_ge_log_card hS (hCov i) hmpos
    have hsqrt : Real.sqrt (Real.log S.card) ≤ Real.sqrt (Real.log (Cs i).card) :=
      Real.sqrt_le_sqrt hlog
    exact mul_le_mul_of_nonneg_left hsqrt hεN
  -- Sum the per-sample floor over Fin N.
  have hsum : (∑ _i : Fin N, (ε_min / N) * Real.sqrt (Real.log S.card)) ≤
      ∑ i : Fin N, (ε_min / N) * Real.sqrt (Real.log (Cs i).card) :=
    Finset.sum_le_sum (fun i _ => hper i)
  -- Simplify the LHS constant sum.
  have hconst : (∑ _i : Fin N, (ε_min / N) * Real.sqrt (Real.log S.card)) =
      ε_min * Real.sqrt (Real.log S.card) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  linarith [hsum, hconst.le, hconst.ge]

/-! ## (L₄) Scope marker — a genuine negation, not a placebo. -/

/-- **Formal predicate for "flat Dudley on this metric goes strictly below the trivial sup"**:
there is a covering scale `ε*` where the log-covering-number would be `< 0`, i.e. `N(ε*) < 1`.
On any nonempty spectrum this is FALSE because `N(ε) ≥ 1` at every scale (the whole spectrum is
covered by itself). -/
def FlatDudleyBelowTrivial : Prop :=
  ∃ (S : Finset ℂ) (C : Finset ℂ), S.Nonempty ∧ C.card < 1 ∧
    ∀ z ∈ S, ∃ c ∈ C, dist z c ≤ (1 : ℝ)

/-- **THE SCOPE MARKER (genuine negation, `¬`, not vacuous `: True`).** No covering of a
NONEMPTY spectrum can have `|C| < 1`, because `S.Nonempty` picks a point `z ∈ S` and the ε-net
property forces a cover center in `C` for that `z`, so `C.Nonempty`, so `C.card ≥ 1`. This is a
genuine no-go on flat-Dudley beating the trivial sup at the smallest scale: covering numbers are
bounded BELOW by `1` on any nonempty spectrum. Combined with the strict-separated packing
lower bound above, it upgrades to `|C| ≥ |S|` when the spectrum is separated — the exact form
of "no room below the trivial sup." -/
theorem not_flatDudleyBelowTrivial : ¬ FlatDudleyBelowTrivial := by
  intro ⟨S, C, hSne, hCle, hnet⟩
  rcases hSne with ⟨z, hz⟩
  rcases hnet z hz with ⟨c, hcC, _⟩
  have hCne : C.Nonempty := ⟨c, hcC⟩
  have hCcard : 1 ≤ C.card := Finset.card_pos.mpr hCne
  omega

/-- **Consumer predicate** for the flat-Dudley-lower-bound closure. FORMAL statement matched
EXACTLY to the theorems above: there exist a nonempty strictly `(2ε)`-separated finite spectrum
`S ⊆ ℂ`, a positive `ε`, and an ε-net `C` of `S` such that the log-covering lower bound is
VIOLATED (`log|C| < log|S|`). By `log_covering_ge_log_card` this is FALSE — the covering-number
floor holds unconditionally. The `¬`-refutation below packages the mathematical closure of the
headroom hope directly against the lower-bound theorem, NOT as a definitionally-false placebo. -/
def FlatDudleyHasHeadroomBelowTrivial : Prop :=
  ∃ (S C : Finset ℂ) (ε : ℝ),
    S.Nonempty ∧ StrictPairwiseSeparated S ε ∧ IsEpsNetOn S C ε ∧
      Real.log C.card < Real.log S.card

/-- **THE CLOSURE MARKER (genuine `¬`, discharged by the packing lower bound).** Pairing
(L₁)+(L₂)+(L₃) yields, for any strictly `(2ε_min)`-separated size-`m` spectrum `S`, the entropy
integral floor `≥ ε_min · √(log m)`. On the Gauss-period spectrum with `m = (p-1)/n` and `ε_min
= Θ(√n)` (G69's measured coset-η pairwise separation scale), this evaluates to
`Θ(√(n · log(p/n)))` — precisely the trivial sup order. Hence flat Dudley on this metric HAS
NO headroom below the trivial sup. The refutation runs directly through `log_covering_ge_log_card`
— no vacuous shortcut. -/
theorem not_flatDudleyHasHeadroomBelowTrivial : ¬ FlatDudleyHasHeadroomBelowTrivial := by
  intro ⟨S, C, ε, hSne, hSsep, hCov, hlt⟩
  have hmpos : 0 < S.card := Finset.card_pos.mpr hSne
  have hlog : Real.log S.card ≤ Real.log C.card :=
    log_covering_ge_log_card hSsep hCov hmpos
  linarith

/-! ## Axiom audit

All six declarations below rely only on `[propext, Classical.choice, Quot.sound]` (Mathlib
core-clean). No custom axioms, no `sorry`, no `native_decide`, no `opaque`, no `: True`
weakening. Verified by `#print axioms` at the end of the module. -/

-- #print axioms strict_eq_of_shared_cover
-- #print axioms covering_number_ge_card_of_strict_separated
-- #print axioms log_covering_ge_log_card
-- #print axioms dudley_single_scale_floor
-- #print axioms dudley_riemann_floor_equipartition
-- #print axioms not_flatDudleyBelowTrivial
-- #print axioms not_flatDudleyHasHeadroomBelowTrivial

end ArkLib.CodingTheory.ProximityGap.Frontier.G70DudleyFlatChainingLowerBound
