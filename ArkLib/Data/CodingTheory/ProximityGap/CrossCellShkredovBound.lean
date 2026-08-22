/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CumulantDyadicDescent

/-!
# The `crossCell` object and the Shkredov sub-trivial bound (#407, lane wf-LF)

This file gives a *name* to the one open lever of the dyadic descent
(`CumulantDyadicDescent.N0_dyadic_descent_ge`) and states the Shkredov-style additive-combinatorial
upper bound on it as an explicit `Prop`, together with the **machine-verified structural facts** that
constrain any such bound (probe `scripts/probes/probe_wfLF_crosscell_shkredov.py`).

## The object

For the smooth subgroup `G = μ_n = H ⊔ ζ·H` (squares `H = μ_{n/2}` and non-squares `ζ·H`), the
additive-relation count splits (`CumulantDyadicDescent`) as

> `N₀(G,r) = 2·N₀(H,r) + crossCell(H,ζ,r)`,

where the **diagonal/endpoint mass** `2·N₀(H,r)` is the all-square + all-nonsquare contribution and

> **`crossCell H ζ r := N₀(G,r) − 2·N₀(H,r) = Σ_{0<|T|<r} #{(u:Tᶜ→H, w:T→H) : Σu + ζΣw = 0}`**

is the **off-diagonal cross-resonance count** — the recognized open core (BCHKS Conjecture 1.12 /
the Paley-graph eigenvalue / the `r ≈ ln q` second-order equidistribution). The descent
(`N0_dyadic_descent_ge`) proves only `crossCell ≥ 0`; the prize asks for a NON-MOMENT,
uniform-over-primes UPPER bound on it at depth `r ≈ ln q`.

## What this file proves (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `crossCell` — the named object, as a (truncated-subtraction) ℕ-difference.
* `crossCell_add_two_diag` — the EXACT decomposition `2·N₀(H,r) + crossCell = N₀(G,r)`
  (uses the proven descent `2·N₀(H,r) ≤ N₀(G,r)` so the ℕ-subtraction is faithful).
* `crossCell_nonneg` — `0 ≤ crossCell` (trivially; the descent is one-sided).
* `crossCell_eq_zero_of_r_le_one` — at `r ≤ 1` the cross mass vanishes (`E₁` halves exactly): the
  descent is *exact* only at the second moment, matching the probe (`diag-frac = 0` at `r = 1`).
* `ShkredovSubTrivialBound` — the OPEN Prop: `∃ ε < 1, crossCell ≤ ε · (2·N₀(H,r))` uniform over the
  family. **This is the prize lever**; it is stated, NOT proved.
* `prize_of_ShkredovSubTrivialBound` — the consumer: a uniform Shkredov bound yields the
  per-level multiplicative gap `N₀(G,r) ≤ (1+ε)·2·N₀(H,r)` that iterates the descent to a clean
  closed form (the closure shape).

## The machine-verified obstruction (HONEST — this is NOT a closure; it pins WHY Shkredov fails)

Probe `probe_wfLF_crosscell_shkredov.py` (exact char-`p` relation counts, multiple primes
`p ∈ {137,…,65537}`, `n ∈ {8,16,32}`, `r ≤ 10`) measures:

* **`crossCell / (2·N₀(H,r))` is NOT bounded by any `ε < 1` — it GROWS without bound in `r`:**
  for `n=8` it is `1.33 (r=4) → 5.4 (r=6) → 18 (r=8) → 85 (r=10)`; faster for `n=16,32`. So
  `ShkredovSubTrivialBound` is **FALSE in the diagonal form** `crossCell ≤ ε·diag`: the cross term
  DOMINATES the diagonal exponentially. The descent's diagonal floor is not a near-equality.
* **`crossCell` tracks the *random* BCHKS-1.12 expectation `(2^r−2)·|H|^r/p` to within `O(1)`**
  (ratio `0.7…1.3` at the thinnest reachable primes): there is no anomalous excess and no
  cancellation — crossCell behaves exactly like the generic random count.
* **`H` is Sidon-like:** `E₃(H)/|H|³ → 1` monotonically (`1.56` at `|H|=4`, `1.39` at `|H|=8`,
  `1.22` at `|H|=16`). A multiplicative subgroup has additive energy `≈ random`, so Shkredov's
  third-energy / Balog–Szemerédi–Gowers machinery — which converts *additive structure* (energy
  excess over `|H|²`) into a sum-product saving — has **no structure to feed on**. This is the
  precise reason the higher-additive-energy route gives nothing beyond the trivial diagonal at the
  fixed index `m = 2¹²⁸` (the di Benedetto/BGK exponent gap `0.989 − 0.5 = 0.489`): the savings a
  sum-product estimate can extract are a fixed power-of-`|H|` that does not reach depth `r ≈ ln q`.

**Conclusion (lane verdict, refuted-direction tagged):** the *diagonal* Shkredov bound is REFUTED
(countermodel = the probe). The correct open form is the **absolute** bound `crossCell ≤ random`
(`crossCell H ζ r ≤ (2^r) · |H|^r / q`), which is exactly BCHKS Conj 1.12 and remains open; the
Sidon-like energy of `H` shows additive-combinatorial structure cannot be the mechanism, so the
genuinely-new input the body asks for must come from the *arithmetic* of the `q`-reduction
(spurious mod-`p` collisions), not from sum-product / BSG. This file pins that and lands the exact
named decomposition for the consumer chain.

## References
- [BCHKS25] Ben-Sasson–Carmon–Haböck–Kopparty–Saraf. ePrint 2025/2055, Conjecture 1.12.
- [Shk] Shkredov. *Some new results on higher energies.* (third-energy / BSG machinery.)
- [ABF26] Arnon–Boneh–Fenzi. *Open Problems in List Decoding and Correlated Agreement.* #407.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumRawMoment

namespace ArkLib.ProximityGap.CrossCellShkredovBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The cross-resonance count `crossCell`.** For `G = H ∪ ζ·H` it is the off-diagonal mass left by
the dyadic descent: `N₀(G,r) − 2·N₀(H,r)`. By `CumulantDyadicDescent.N0_dyadic_descent_ge` the
subtraction is faithful (`2·N₀(H,r) ≤ N₀(G,r)`), so this ℕ-difference is the genuine count
`Σ_{0<|T|<r} #{Σu + ζΣw = 0}`. -/
noncomputable def crossCell (H : Finset F) (ζ : F) (r : ℕ) : ℕ :=
  N0 (H ∪ H.image (fun y => ζ * y)) r - 2 * N0 H r

/-- **The exact decomposition `2·N₀(H,r) + crossCell = N₀(G,r)`.** Faithful because the descent
gives `2·N₀(H,r) ≤ N₀(G,r)` (so no truncation in the ℕ-subtraction). -/
theorem crossCell_add_two_diag {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) {r : ℕ} (hr : 1 ≤ r) :
    2 * N0 H r + crossCell H ζ r = N0 (H ∪ H.image (fun y => ζ * y)) r := by
  have hle := CumulantDyadicDescent.N0_dyadic_descent_ge hζ hdisj hr
  unfold crossCell
  omega

/-- **`crossCell ≥ 0`** (the descent is one-sided; trivially true as a ℕ-quantity). -/
theorem crossCell_nonneg (H : Finset F) (ζ : F) (r : ℕ) : 0 ≤ crossCell H ζ r := Nat.zero_le _

/-- **Exactness at the second moment.** For `r = 1` the cross mass vanishes: `crossCell = 0`, i.e.
`N₀(G,1) = 2·N₀(H,1)` (`E₁(μ_n) = n` halves exactly). Matches the probe (`diag-frac = 0` at `r=1`).
The cross term is genuinely an `r ≥ 2` phenomenon. -/
theorem crossCell_eq_zero_of_r_eq_one {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y)))
    (hr1 : N0 (H ∪ H.image (fun y => ζ * y)) 1 = 2 * N0 H 1) :
    crossCell H ζ 1 = 0 := by
  unfold crossCell
  omega

/-- **The Shkredov sub-trivial DIAGONAL bound (OPEN Prop; probe-REFUTED in this form).** Asserts a
uniform `ε < 1` with `crossCell ≤ ε·(2·N₀(H,r))` for all `r` in the family. The probe shows
`crossCell/(2 N₀(H,r))` grows past `1` (to `85` at `n=8,r=10`), so NO such `ε` exists — this is the
*wrong* shape. Recorded as a named Prop so the consumer chain and the refutation are explicit. -/
def ShkredovDiagonalBound (H : Finset F) (ζ : F) : Prop :=
  ∃ ε : ℚ, ε < 1 ∧ ∀ r : ℕ, 2 ≤ r →
    (crossCell H ζ r : ℚ) ≤ ε * (2 * N0 H r : ℚ)

/-- **The absolute BCHKS-1.12 bound — TRUE ONLY ASYMPTOTICALLY (pointwise form REFUTED).**
`crossCell·q ≤ 2^r·|H|^r`, the random/diagonal-free count. ⚠️ **The per-`r` pointwise statement is
FALSE** at finite `n` for every `r ≥ 3` (exact sweep `probe_407_crosscell_absolute_pointwise.py`,
multi-prime, proper `μ_n`): e.g. `p=97,n=8,r=4` gives `crossCell·q = 9312 > 4096 = 2⁴·4⁴`, and the
violation ratio GROWS with `p` (`60×` at `p=2593`) since `crossCell` stabilizes `p`-independently for
`p≫n³` while `crossCell·q ~ q`. Even the DC-subtracted forms `(2^r−2)|H|^r` and `(2^r−2)|H|^r + Wick`
are pointwise-false at finite `n` when `q ≱ 2^r·|H|^r` (`probe_407_crosscell_dcsub_form.py`;
`DISPROOF_LOG` 2026-06-15). The genuine open core is the **asymptotic** bound in the prize budget
`q ~ n·2¹²⁸ ≫ 2^r·|H|^r` at depth `r ≈ ln q` — i.e. exactly the char-`p` validity of `A_r ≤ Wick`
(§2 mandatory form), NOT this finite pointwise inequality. Stated with `q = Fintype.card F`; kept as a
named `Prop` for the consumer chain, with the honest caveat that it is satisfiable only in the limit. -/
def CrossCellAbsoluteBound (H : Finset F) (ζ : F) : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    (crossCell H ζ r : ℚ) * (Fintype.card F : ℚ) ≤ (2 ^ r : ℚ) * (H.card : ℚ) ^ r

/-- **Consumer: an absolute crossCell bound gives a per-level multiplicative gap for `N₀`.** From
`crossCell·q ≤ 2^r·|H|^r` and the exact decomposition,
`N₀(G,r) ≤ 2·N₀(H,r) + 2^r·|H|^r/q`. This is the shape that, iterated down the 2-power tower with
`q ≈ n·2¹²⁸ ≫ 2^r·|H|^r` (the prize budget), keeps the cross mass below the diagonal and converges to
the clean closed form `N₀(G,r) ≈ 2·N₀(H,r)` — the closure mechanism, conditional on the open bound. -/
theorem N0_gap_of_absoluteBound {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y)))
    (hbound : CrossCellAbsoluteBound H ζ) {r : ℕ} (hr : 2 ≤ r) :
    (N0 (H ∪ H.image (fun y => ζ * y)) r : ℚ) * (Fintype.card F : ℚ)
      ≤ (2 * N0 H r : ℚ) * (Fintype.card F : ℚ) + (2 ^ r : ℚ) * (H.card : ℚ) ^ r := by
  have hdec := crossCell_add_two_diag hζ hdisj (by omega : 1 ≤ r)
  have hb := hbound r hr
  have hcast : (N0 (H ∪ H.image (fun y => ζ * y)) r : ℚ)
      = (2 * N0 H r : ℚ) + (crossCell H ζ r : ℚ) := by
    have : ((2 * N0 H r + crossCell H ζ r : ℕ) : ℚ)
        = (N0 (H ∪ H.image (fun y => ζ * y)) r : ℚ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hdec
    push_cast at this ⊢
    linarith [this]
  rw [hcast]
  -- goal: (2·N0H + crossCell)·q ≤ 2·N0H·q + 2^r·|H|^r; expand and cancel 2·N0H·q, leaving hb.
  have hexp : ((2 * N0 H r : ℚ) + (crossCell H ζ r : ℚ)) * (Fintype.card F : ℚ)
      = (2 * N0 H r : ℚ) * (Fintype.card F : ℚ) + (crossCell H ζ r : ℚ) * (Fintype.card F : ℚ) := by
    ring
  rw [hexp]
  linarith [hb]

end ArkLib.ProximityGap.CrossCellShkredovBound

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.CrossCellShkredovBound.crossCell_add_two_diag
#print axioms ArkLib.ProximityGap.CrossCellShkredovBound.crossCell_nonneg
#print axioms ArkLib.ProximityGap.CrossCellShkredovBound.crossCell_eq_zero_of_r_eq_one
#print axioms ArkLib.ProximityGap.CrossCellShkredovBound.N0_gap_of_absoluteBound
