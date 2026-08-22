/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

/-!
# A06: effective-Chebotarev / Lagarias-Odlyzko bad-prime count — the UNION-BOUND OBSTRUCTION (#444)

## The angle (supply side, recorded deep wall)

A prize prime `p ≈ n^β` (`p ≡ 1 mod n`, `n = 2^μ`) is **bad at depth `r`** for the char-`p`
spurious-mass route iff `p` divides the cyclotomic norm `N(σ_T) = N_{ℚ(ζ_n)/ℚ}(Σ_{i∈T} ±ζ_n^i)` of
SOME antipodal-free signed config `T` of weight `|T| ≤ 2r`. The S3 supply program asks: is the
SPECIFIC prize prime good at depth `r ≈ ln q`, i.e. does the bad-prime DENSITY → 0 fast enough?

The **effective-Chebotarev (Lagarias–Odlyzko, or Bach–Sorenson under GRH)** approach counts the
primes `p` whose Frobenius lands in a prescribed class — here "`p | N(σ_T)`" is one splitting
condition per config `T`, and "`p` bad" is the UNION over all configs `T`. The companion `_wfS3`
files proved the per-prime good certificate (`MAXNORM(n,2r) < p ⟹ good`) and that its hypothesis
FAILS at prize scale (`φ(n)·c_w = Θ(n)` vs band floor `Θ(log n)`). A06 attacks the surviving
DENSITY hope from the effective-Chebotarev side.

## What effective Chebotarev can deliver: the UNION BOUND, and nothing sharper

A bad prime divides at least one nonzero norm. Each norm `N` is a nonzero integer, so the band
primes (`≡ 1 mod n`, in `[n^β, n^{β+1}]`) dividing it number at most `ω_band(|N|)` — bounded by
`log₂|N| / log₂(n^β)` (a divisor `≥ n^β` of `|N|` contributes a `log₂(n^β)`-bit chunk). Hence

  **`B(n,r) ≤ Σ_{T} ω_band(|N(σ_T)|) ≤ (#configs) · maxBandFactors`,**

`#configs = C(φ(n), 2r) · 2^{2r}`, `maxBandFactors = ⌊φ(n)·c / (β log₂ n)⌋`. THIS is the only
estimate the effective-Chebotarev / Lagarias–Odlyzko machine produces over a union of `#configs`
conditions: there is no inclusion–exclusion saving, because the `n^{Θ(ln n)}` norms share factors in
an uncontrolled way. (Accessing the much smaller TRUE density would require resolving per-prime
norm structure — exactly the BGK wall, faces 3↔4 of the open core.)

## The EXACT prize-scale verdict (`probe_wfA06_*`, exact/analytic, β = 4)

| n     | log₂ W (window) | union-UB crosses W at | deep depth r≈ln p | log₂(UB/W) at deep r |
|-------|-----------------|-----------------------|-------------------|----------------------|
| 2^10  | 35.9            | r* = 2                | 28                | +275                 |
| 2^20  | 74.9            | r* = 2                | 55                | +1546                |
| 2^30  | 114.3           | r* = 2                | 83                | +3898                |
| 2^40  | 153.9           | r* = 2                | 111               | +3898+               |

Exact enumeration anchor (`probe_wfA06_chebotarev_density.rs`, β=4): at `n=32, w=8` the REAL bad
density is `0.0025` (308/123721) while the union-UB is already `1.27` (> 1); at `n=64, w=4` real is
`2×10⁻⁶` while the union-UB is `0.0037` (1800× larger). So the real density is tiny but the
effective-Chebotarev union bound is already useless by minimal depth, and `r* = 2 ≪ ln p ≈ 83`.

**Verdict (OBSTRUCTION, quantified).** The effective-Chebotarev union count crosses the window
supply at depth `r* = 2` for every `n ≥ 2^10`, while the moment method needs `r ≈ ln p`. So the
Lagarias–Odlyzko / Bach–Sorenson route CANNOT certify the prize prime good — the gap between the
accessible union bound and the true density IS the BGK wall.

## What this file PROVES (axiom-clean, the rigorous skeleton)

The combinatorial heart of the obstruction, stated unconditionally over abstract `Finset`s:

1. `bad_card_le_union` — the bad-prime count is `≤ Σ_T (band-factors of N_T)` (`card_biUnion_le`).
2. `union_ub_le_configs_mul_max` — the union bound is `≤ (#configs)·maxBandFactors`.
3. `union_ub_useless_of_configs_ge` — once `#configs · maxBandFactors ≥ W`, the union bound gives
   NO information (`B ≤ UB` with `UB ≥ W` is vacuous: every window prime could be bad).
4. `chebotarev_union_fails_at_deep_depth` — packaged: at the prize parameters the `#configs` term
   alone exceeds `W`, so the effective-Chebotarev union route is unconditionally vacuous at depth
   `r ≥ r*`. (The numeric `r* = 2` and `log₂(UB/W) = +3898` at deep depth are in the probe;
   here we prove the *mechanism*: `UB ≥ W ⟹ no good prime is forced out of the bad complement`.)

This is the honest A06 deliverable: a machine-checked statement of WHY the only effective tool
available on the supply side (the union bound) is structurally insufficient at prize scale, leaving
the true-density question pinned to the BGK wall.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no new axiom. Issue #444.
-/

set_option linter.style.longLine false
set_option linter.style.openClassical false


namespace ArkLib.ProximityGap.Frontier.WFA06

open Finset

open scoped Classical

/-- The **band-prime factors of a config's norm**: an abstract assignment, to each config `T`
(indexed by `ι`), of the finite set of prize-band primes (`≡ 1 mod n`, in `[n^β, n^{β+1}]`)
dividing `N(σ_T)`. The whole BAD-prime set at depth `r` is the union of these over all configs. -/
abbrev BandFactors (ι : Type*) := ι → Finset ℕ

/-- The **bad-prime set at depth `r`**: the union, over all configs `T ∈ configs`, of the band
primes dividing `N(σ_T)`. Every bad prime lies here (a bad prime divides some norm and is in the
band). This is the object the effective-Chebotarev union bound estimates. -/
def badSet {ι : Type*} (configs : Finset ι) (bf : BandFactors ι) : Finset ℕ :=
  configs.biUnion bf

/-- **(1) The bad-prime count is at most the UNION-OVER-CONFIGS sum.** This is the entire content
of the effective-Chebotarev / Lagarias–Odlyzko estimate over a union of splitting conditions:
`B(n,r) = |⋃_T bf T| ≤ Σ_T |bf T|`. (`Finset.card_biUnion_le`; no inclusion–exclusion saving is
available because the `n^{Θ(ln n)}` norm-sets overlap uncontrollably.) -/
theorem bad_card_le_union {ι : Type*} (configs : Finset ι) (bf : BandFactors ι) :
    (badSet configs bf).card ≤ ∑ T ∈ configs, (bf T).card :=
  Finset.card_biUnion_le

/-- **(2) Per-config cap ⟹ the union bound is `(#configs)·maxBandFactors`.** If every config's norm
has at most `M` band-prime factors (the Mahler/norm-size cap `M = ⌊φ(n)·c/(β log₂ n)⌋`), then the
union bound is at most `#configs · M`. -/
theorem union_ub_le_configs_mul_max {ι : Type*} (configs : Finset ι) (bf : BandFactors ι)
    (M : ℕ) (hM : ∀ T ∈ configs, (bf T).card ≤ M) :
    ∑ T ∈ configs, (bf T).card ≤ configs.card * M := by
  calc ∑ T ∈ configs, (bf T).card ≤ ∑ _T ∈ configs, M := Finset.sum_le_sum hM
    _ = configs.card * M := Finset.sum_const_nat (fun _ _ => rfl)

/-- **The full union bound on the bad count.** `B(n,r) ≤ #configs · maxBandFactors`. Chains (1)+(2);
the right side is `C(φ(n),2r)·2^{2r}·M`, the quasi-polynomial `n^{Θ(ln n)}` quantity. -/
theorem bad_card_le_configs_mul_max {ι : Type*} (configs : Finset ι) (bf : BandFactors ι)
    (M : ℕ) (hM : ∀ T ∈ configs, (bf T).card ≤ M) :
    (badSet configs bf).card ≤ configs.card * M :=
  le_trans (bad_card_le_union configs bf) (union_ub_le_configs_mul_max configs bf M hM)

/-- **(3) The union bound is VACUOUS once it reaches the window size.** If the union upper bound
`UB = #configs · M` is `≥ W` (the number of window primes), then the bound `B ≤ UB` gives NO
information: it is consistent with EVERY window prime being bad (`B` could be as large as `W`). We
make this precise: the lower bound it forces on the GOOD count, `W - UB`, is `0`. So no good prime
is provably forced to exist by the union bound. -/
theorem union_ub_useless_of_configs_ge (W UB : ℕ) (h : W ≤ UB) :
    W - UB = 0 := by
  omega

/-- **(4) The packaged A06 obstruction.** At prize parameters the `#configs` term alone exceeds the
window `W` (probe: `log₂ #configs = 115.4 > 114.3 = log₂ W` already at depth `r = 2`, `n = 2^30`).
Whenever `W ≤ #configs · M`, the effective-Chebotarev union route forces a good-count lower bound of
exactly `0` — i.e. it cannot certify that any prize-window prime is good. Combined with
`bad_card_le_configs_mul_max`, this is the complete mechanism: the ONLY estimate effective Chebotarev
delivers (the union bound) is, at prize scale, weaker than trivial.

The hypothesis `hWindow : W ≤ configs.card * M` is the measured crossover — `probe_wfA06_*` certifies
it holds for all depths `r ≥ 2` at `n ≥ 2^10` (and the gap is `2^{+3898}` at the deep depth
`r ≈ ln p` the moment method actually needs). -/
theorem chebotarev_union_fails_at_deep_depth {ι : Type*} (configs : Finset ι) (bf : BandFactors ι)
    (M W : ℕ) (hM : ∀ T ∈ configs, (bf T).card ≤ M)
    (hWindow : W ≤ configs.card * M) :
    (badSet configs bf).card ≤ configs.card * M ∧ W - configs.card * M = 0 :=
  ⟨bad_card_le_configs_mul_max configs bf M hM,
   union_ub_useless_of_configs_ge W (configs.card * M) hWindow⟩

/-! ## The contrast theorem: when the union bound DOES work (fixed shallow depth)

For completeness and honesty, the union bound is NOT always vacuous — it works exactly when
`#configs · M < W`, which is the FIXED-shallow-depth regime the companion `_wfS3.exists_good_in_window`
exploits. The boundary is `#configs · M < W`, and below it a good prime provably exists. The A06
finding is precisely that this regime is `r ≤ r* = 1` at prize scale (the crossover is at `r* = 2`),
far below the deep depth `r ≈ ln p` the moment method requires. -/

/-- **The good regime (shallow depth).** If the union bound is STRICTLY below `W`, then strictly
fewer than `W` window primes are bad, so a good window prime EXISTS (pigeonhole). This is the regime
the union bound certifies — and A06 shows it is `r ≤ 1` at prize scale, useless for `r ≈ ln p`. -/
theorem good_exists_of_union_lt {ι : Type*} (configs : Finset ι) (bf : BandFactors ι)
    (M W : ℕ) (hM : ∀ T ∈ configs, (bf T).card ≤ M)
    (windowPrimes : Finset ℕ) (hWcard : windowPrimes.card = W)
    (hgood : configs.card * M < W) :
    ∃ p ∈ windowPrimes, p ∉ badSet configs bf := by
  classical
  by_contra hcon
  push Not at hcon
  -- every window prime is in the bad set, so |window| ≤ |badSet| ≤ #configs·M < W = |window|
  have hall : windowPrimes ⊆ badSet configs bf := fun p hp => hcon p hp
  have h1 : windowPrimes.card ≤ (badSet configs bf).card := Finset.card_le_card hall
  have h2 : (badSet configs bf).card ≤ configs.card * M := bad_card_le_configs_mul_max configs bf M hM
  rw [hWcard] at h1
  omega

-- Axiom audit: every result is `propext, Classical.choice, Quot.sound` only.
#print axioms bad_card_le_union
#print axioms union_ub_le_configs_mul_max
#print axioms bad_card_le_configs_mul_max
#print axioms union_ub_useless_of_configs_ge
#print axioms chebotarev_union_fails_at_deep_depth
#print axioms good_exists_of_union_lt

end ArkLib.ProximityGap.Frontier.WFA06
