/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
* `crossCell_eq_zero_of_r_eq_one` — at `r = 1` the cross mass vanishes, *given* the vanishing
  identity `N₀(G,1) = 2·N₀(H,1)` as the premise `hr1`; `crossCell_one_eq_zero` proves the same
  conclusion from `ζ ≠ 0` and disjointness alone (then `0 ∉ G`, so both raw first-order relation
  counts are `0`). Note `N₀(·,1)` is the order-`1` raw tuple count, not a second moment.
* `ShkredovDiagonalBound` — the named Prop `∃ ε < 1, ∀ r ≥ 2, crossCell ≤ ε · (2·N₀(H,r))`;
  stated, NOT proved, and refuted by the probe below (the ratio grows without bound in `r`).
* `CrossCellAbsoluteBound` — the named Prop `∀ r ≥ 2, crossCell·q ≤ 2^r·|H|^r`; stated, NOT
  proved, and refuted as a finite pointwise statement by exact sweeps (see its docstring).
* `N0_gap_of_absoluteBound` — the valid conditional consumer: `CrossCellAbsoluteBound` and the
  exact decomposition give `N₀(G,r)·q ≤ 2·N₀(H,r)·q + 2^r·|H|^r`. Its additive term `n^r/q` is
  small only at bounded depth `r < log q / log n`, not at `r ≈ ln q`.

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
(countermodel = the probe). The proposed replacement, the **absolute** bound `crossCell ≤ random`
(`crossCell H ζ r ≤ (2^r) · |H|^r / q` for all `r ≥ 2`, `CrossCellAbsoluteBound` below), is
**also refuted** as a finite pointwise statement by later exact sweeps (see its docstring); a
correct asymptotic replacement must still be stated with a consistent joint limit (see the caveat
on `CrossCellAbsoluteBound`) and is not formalized here. The
Sidon-like energy of `H` suggests additive-combinatorial structure cannot be the mechanism, so the
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

/-- **Vanishing at tuple order `r = 1`, from an assumed identity.** If `N₀(G,1) = 2·N₀(H,1)`
(supplied as the premise `hr1`; this declaration does not derive it), then `crossCell H ζ 1 = 0`.
`N₀(·,1)` is the order-`1` raw relation count `#{x ∈ G : x = 0}`, not a second moment. The
unconditional version, deriving the identity from `ζ ≠ 0` and disjointness, is
`crossCell_one_eq_zero`. -/
theorem crossCell_eq_zero_of_r_eq_one {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y)))
    (hr1 : N0 (H ∪ H.image (fun y => ζ * y)) 1 = 2 * N0 H 1) :
    crossCell H ζ 1 = 0 := by
  unfold crossCell
  omega

/-- The order-`1` raw relation count vanishes on a set avoiding `0`: `N₀(G,1) = #{x ∈ G : x = 0}`. -/
theorem N0_one_eq_zero_of_zero_not_mem {G : Finset F} (h0 : (0 : F) ∉ G) : N0 G 1 = 0 := by
  unfold N0
  refine Finset.sum_eq_zero fun v hv => ?_
  have hv0 : v 0 ∈ G := Fintype.mem_piFinset.mp hv 0
  have hne : v 0 ≠ 0 := fun h => h0 (h ▸ hv0)
  simp [hne]

/-- **Unconditional vanishing at tuple order `r = 1`.** For `ζ ≠ 0` and `H` disjoint from `ζ·H`,
`0 ∉ H` (else `0 = ζ·0 ∈ ζ·H`) and hence `0 ∉ H ∪ ζ·H`, so both order-`1` relation counts are `0`
and `crossCell H ζ 1 = 0`, with no extra premise. -/
theorem crossCell_one_eq_zero {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) :
    crossCell H ζ 1 = 0 := by
  have hH : (0 : F) ∉ H := by
    intro h
    exact Finset.disjoint_left.mp hdisj h (Finset.mem_image.mpr ⟨0, h, mul_zero ζ⟩)
  have hG : (0 : F) ∉ H ∪ H.image (fun y => ζ * y) := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hH h
    · obtain ⟨y, hy, hy0⟩ := Finset.mem_image.mp h
      rcases mul_eq_zero.mp hy0 with h1 | h1
      · exact hζ h1
      · exact hH (h1 ▸ hy)
  unfold crossCell
  rw [N0_one_eq_zero_of_zero_not_mem hG]
  exact Nat.zero_sub _

/-- **The Shkredov sub-trivial DIAGONAL bound (OPEN Prop; probe-REFUTED in this form).** Asserts a
uniform `ε < 1` with `crossCell ≤ ε·(2·N₀(H,r))` for all `r` in the family. The probe shows
`crossCell/(2 N₀(H,r))` grows past `1` (to `85` at `n=8,r=10`), so NO such `ε` exists — this is the
*wrong* shape. Recorded as a named Prop so the consumer chain and the refutation are explicit. -/
def ShkredovDiagonalBound (H : Finset F) (ζ : F) : Prop :=
  ∃ ε : ℚ, ε < 1 ∧ ∀ r : ℕ, 2 ≤ r →
    (crossCell H ζ r : ℚ) ≤ ε * (2 * N0 H r : ℚ)

/-- **The absolute BCHKS-1.12-style bound — finite pointwise form REFUTED; no consistent asymptotic
replacement is stated here.**
`crossCell·q ≤ 2^r·|H|^r`, the random/diagonal-free count. ⚠️ **The per-`r` pointwise statement is
FALSE** at finite `n` for every `r ≥ 3` (exact sweep `probe_407_crosscell_absolute_pointwise.py`,
multi-prime, proper `μ_n`): e.g. `p=97,n=8,r=4` gives `crossCell·q = 9312 > 4096 = 2⁴·4⁴`, and the
violation ratio GROWS with `p` (`60×` at `p=2593`) since `crossCell` stabilizes `p`-independently for
`p≫n³` while `crossCell·q ~ q`. The same mechanism defeats every `q`-independent budget: at fixed
`r`, once `crossCell` has stabilized at its char-`0` value (e.g. `crossCell(μ₈, μ₄, 4) = 168 − 2·36
= 96` at `p = 97, 193, 577, 2593`), `crossCell·q` grows linearly in `q`, so whenever that char-`0`
value is positive the bound FAILS for all sufficiently large `q` and can never hold "in the limit
`q/(2^r|H|^r) → ∞`". In particular the DC-subtracted forms `(2^r−2)|H|^r` and
`(2^r−2)|H|^r + Wick` hold at the small primes `p ≤ 193` and fail at the large ones `p ≥ 577`
for `n = 8, r = 4` (`crossCell·p = 18528 ≤ 30464` at `p = 193`, `55392 > 30464` at `p = 577`;
`probe_407_crosscell_dcsub_form.py`; `DISPROOF_LOG` 2026-06-15; exact computer counts, not in-tree
Lean refutations). An earlier description of these forms as failing only when `q` is too small
and as "satisfiable only in the limit" inverted the data and is withdrawn (audit CW-DL03a-01 /
CW-DL07b-03); any surviving open form must be normalized or centered with a `q`-scaled budget
(e.g. `A_r ≤ Wick`).

**The regime `q ≫ 2^r·|H|^r` is incompatible with logarithmic depth.** With `n = 2|H|` the right
side is `2^r·|H|^r = n^r`, and `q ≫ n^r` forces `r < log q / log n`. At depth `r ≈ ln q` one has
`log(n^r) ≈ ln q · log n`, which exceeds `log q` as soon as `n` grows; e.g. at the production
scale `n = 2^30`, `q ≈ n·2^128 = 2^158`, `r ≈ ln q ≈ 109` gives `n^r ≈ 2^3270 ≫ q`. So an earlier
description of the open core as "the asymptotic bound in the prize budget `q ~ n·2¹²⁸ ≫ 2^r·|H|^r`
at depth `r ≈ ln q`" was inconsistent and is withdrawn. A correct replacement must state a
consistent joint limit in `(n, q, r)` and distinguish the raw tuple order `r` counted by `N₀`,
the even-order energies, and DC-subtracted error terms (cf. the char-`p` validity of
`A_r ≤ Wick`); no such replacement is formalized here. Stated with `q = Fintype.card F` and kept
only as a named `Prop` for the conditional consumer chain; as an all-`r` finite statement it is
the refuted specification above. -/
def CrossCellAbsoluteBound (H : Finset F) (ζ : F) : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    (crossCell H ζ r : ℚ) * (Fintype.card F : ℚ) ≤ (2 ^ r : ℚ) * (H.card : ℚ) ^ r

/-- **Consumer: an absolute crossCell bound gives a per-level multiplicative gap for `N₀`.** From
`crossCell·q ≤ 2^r·|H|^r` and the exact decomposition,
`N₀(G,r) ≤ 2·N₀(H,r) + 2^r·|H|^r/q`. This implication is valid, but its premise is the
all-`r` finite `CrossCellAbsoluteBound`, which is refuted by exact computation at proper `μ_n`
instances. Moreover the added term `2^r·|H|^r/q = n^r/q` is small only when `r < log q / log n`
(bounded depth); at the depth `r ≈ ln q` of the prize discussion it is astronomically large
(`n^r ≈ 2^3270` vs `q ≈ 2^158` at `n = 2^30`), so this shape does not keep the cross mass below
the diagonal there and gives no closure mechanism in that regime. -/
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
#print axioms ArkLib.ProximityGap.CrossCellShkredovBound.N0_one_eq_zero_of_zero_not_mem
#print axioms ArkLib.ProximityGap.CrossCellShkredovBound.crossCell_one_eq_zero
#print axioms ArkLib.ProximityGap.CrossCellShkredovBound.N0_gap_of_absoluteBound
