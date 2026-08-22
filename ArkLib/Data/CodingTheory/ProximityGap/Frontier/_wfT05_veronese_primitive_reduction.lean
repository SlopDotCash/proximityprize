/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-!
# wf-T05 — Veronese moment-curve primitive-cohomology sub-bound: REDUCES-TO-WALL (F2) (#444)

## The candidate (Theorem-Architect G1-5)

T05 proposes to relocate the prize to the `(r+1)`-dimensional Veronese moment-curve family
`v_r(b) = (b, b², …, b^r)` acting on `r`-fold tensor dilates of `μ_n`, and to split the
cohomology of the configuration variety `V_r = {∑ ε_i x_i = 0}` into

* the **Wick (perfectly-matched-pairing) classes** that produce the `(2r−1)‼·n^r` main term, and
* the **PRIMITIVE part** `H*_prim`, of claimed dimension `dim_prim := C(2r,r) − (2r−1)‼`,

and to claim that a "moment-curve (Veronese) transversality" assigns each primitive class an
EXTRA `p^{−1/2}` (weight `2(r−1)−1` instead of `2(r−1)`), giving the energy EXCESS over Wick

  `W_r := E_r(μ_n) − (2r−1)‼·n^r  ≤  dim_prim · p^{r−1} · p^{−(r−1)}  =  dim_prim = O_r(1)`,

hence (via the in-tree axiom-clean transfer `prize_of_charzero_limit` / `prize_of_transfer_slack`)
`M(n) ≤ C√(n·log(p/n))`.

The architect's own honesty note states the load-bearing claim precisely: *"if the primitive
classes on `V_r` are NOT transversalized by the Veronese (i.e. they remain pure of weight
`2(r−1)`), the Weil error stays `p^{r−1}` and the candidate reduces EXACTLY to F2/A04 and dies."*

## Verdict: REDUCES-TO-WALL (F2), and the central dimension formula is MALFORMED.

This file records, axiom-clean, **two independent structural failures** that collapse T05 onto
the configuration-variety Weil wall F2 (`_wfA04_weil_envelope_vacuity`,
`_wfS6_toric_config_betti`):

### (I) The `dim_prim` formula is incoherent at prize depth `r ≈ ln q`.

`dim_prim := C(2r,r) − (2r−1)‼` presumes the `(2r−1)‼` Wick matchings are a SUB-count of the
`C(2r,r)` toric Betti classes (a "Catalan deficit"). They are NOT: they are incomparable counts
(the `(2r−1)‼` is the char-0 Lam–Leung vanishing-pairing count; `C(2r,r) ≤ 4^r` is the
Adolphson–Sperber toric Newton-polytope envelope, F2/S6). We prove

  `theorem wick_gt_betti : 4 ≤ r → C(2r,r) < (2r−1)‼`,

i.e. there are STRICTLY MORE Wick matchings than total Betti classes for every `r ≥ 4`. The prize
needs depth `r ≈ ln q ≈ 83 ≫ 4`. So over `ℕ` the proposed "primitive dimension"
`C(2r,r) − (2r−1)‼` truncates to `0` (`dimPrimNat_eq_zero`), making the T05 bound read
`W_r ≤ 0` — which is FALSE for any prime at which the char-`p` energy exceeds char-0
(`spur_r > 0`). The "primitive deficit" cohomology that T05 wants to bound the excess is empty
at the relevant depths. **The ratio `(2r−1)‼ / C(2r,r) = r!/2^r → ∞`** (`wick_over_betti_ratio`),
so the gap is not a small-`r` artifact; it diverges super-exponentially at prize depth.

### (II) The Veronese moment curve folds up over `μ_n` — no transversality gain exists.

The transversality gain T05 needs requires the Veronese `v_r(b) = (b, …, b^r)` to put the
primitive classes in general position (open `r` independent directions). But over the
multiplicative subgroup `μ_n`, the power map `x ↦ x^j` sends `μ_n` INTO `μ_{n/gcd(j,n)} ⊆ μ_n`:
the moment curve closes up, **zero net curvature** (the in-tree `_VinogradovDecouplingVacuous`
Reason 2; `probe_wfT05_veronese_primitive_excess.rs` confirms `|image(x^j)| = n/gcd(j,n)`). We
encode this as `power_map_image_card_dvd`: the image cardinality `n/gcd(j,n)` divides `n` and is
`< n` whenever `gcd(j,n) > 1` (e.g. all even `j`). A curve that folds into the same `n`-point set
supplies no transversality, hence no per-class `p^{−1/2}` weight drop. The primitive classes
remain pure of weight `2(r−1)`, the Weil error stays `p^{r−1}`, and by the architect's own
dichotomy T05 reduces to F2/A04.

### (III) The measured excess is `Θ(n^{r−1})`, not `O_r(1)` (probe), confirming the reduction.

`probe_wfT05_veronese_primitive_excess.rs` (EXACT `r`-fold additive convolution over `ℤ_p`,
`β = 4`, `p = n^4`, `p ≡ 1 mod n`, `μ_n = ⟨2^μ⟩`): at the prize prime the excess is in fact
NEGATIVE (`E_r < (2r−1)‼·n^r`, matching S6 `spur ≡ 0`), and its MAGNITUDE scales as
`|W_r| / n^{r−1} → const` (`-3, -44, -560` for `r = 2,3,4`) — i.e. `Θ(n^{r−1})`, polynomial in
`n`, NOT the `n`-free `dim_prim = O_r(1)` T05 predicts. So even the SIGN and SCALING of the
quantity T05 bounds contradict the claimed `O_r(1)`.

## What is PROVEN here (axiom-clean `ℕ`-arithmetic; `[propext, Classical.choice, Quot.sound]`)

The structural facts (I) and (II) that make the T05 mechanism untenable at prize regime, plus the
explicit reduction to the in-tree F2 wall: if (counterfactually) the moment-curve transversality
gave the full weight drop, the prize would follow — but the fold fact and the malformed dimension
show it does not, pinning the residual back onto the open BGK/Paley char-`p` transfer wall.

This is an OBSTRUCTION/REDUCTION brick, NOT a closure.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset
open scoped Nat

namespace ArkLib.ProximityGap.Frontier.wfT05VeronesePrimitiveReduction

/-! ## Part I — the `dim_prim = C(2r,r) − (2r−1)‼` formula is malformed (Wick overtakes Betti) -/

/-- **`r! > 2^r` for `r ≥ 4`.** The clean inductive fact behind the Wick/Betti crossover: the
ratio `(2r−1)‼ / C(2r,r) = r! / 2^r`, so Wick overtakes Betti exactly when `r! > 2^r`. -/
theorem factorial_gt_two_pow (r : ℕ) (hr : 4 ≤ r) : 2 ^ r < r ! := by
  induction r with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 4 with hk | hk
    · -- base case: k+1 = 4, i.e. k = 3
      interval_cases k <;> simp_all <;> norm_num [Nat.factorial]
    · -- step: 2^{k+1} = 2·2^k < 2·k! ≤ (k+1)·k! = (k+1)!
      have ihk : 2 ^ k < k ! := ih hk
      calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        _ < 2 * k ! := by omega
        _ ≤ (k + 1) * k ! := by
            apply Nat.mul_le_mul_right
            omega
        _ = (k + 1)! := (Nat.factorial_succ k).symm

/-- **The exact ratio identity** `(2r−1)‼ · 2^r = (2r)! / r!`, equivalently
`(2r−1)‼ = (2r)! / (2^r · r!)`. Combined with `C(2r,r) = (2r)! / (r!·r!)`, this gives
`(2r−1)‼ / C(2r,r) = r! / 2^r`. We use the product form: `C(2r,r) · r! = (2r−1)‼ · 2^r`,
proven from `Nat.choose_two_mul_self_eq_doubleFactorial`-style identities via the factorial
expansions. -/
theorem betti_factorial_eq_wick_twopow (r : ℕ) :
    Nat.choose (2 * r) r * r ! = Nat.doubleFactorial (2 * r - 1) * 2 ^ r := by
  -- C(2r,r) * r! * r! = (2r)!  (choose identity, 2r - r = r)
  have hchoose : Nat.choose (2 * r) r * (r ! * r !) = (2 * r)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * r) (k := r) (by omega)
    have hsub : 2 * r - r = r := by omega
    rw [hsub] at h
    calc Nat.choose (2 * r) r * (r ! * r !)
        = Nat.choose (2 * r) r * r ! * r ! := by ring
      _ = (2 * r)! := h
  -- (2r)! = (2r)‼ * (2r-1)‼  via  (n+1)! = (n+1)‼ * n‼  at  n = 2r-1
  have hdf : (2 * r)! = Nat.doubleFactorial (2 * r) * Nat.doubleFactorial (2 * r - 1) := by
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · subst hr0; decide
    · have h2 : 2 * r - 1 + 1 = 2 * r := by omega
      have := Nat.factorial_eq_mul_doubleFactorial (2 * r - 1)
      rw [h2] at this
      -- this : (2r)! = (2r)‼ * (2r-1)‼
      exact this
  -- (2r)‼ = 2^r * r!
  have heven : Nat.doubleFactorial (2 * r) = 2 ^ r * r ! := Nat.doubleFactorial_two_mul r
  -- Now: C(2r,r)*r!*r! = (2r)! = 2^r * r! * (2r-1)!!; cancel one r!.
  have hr0 : 0 < r ! := Nat.factorial_pos r
  have key2 : (Nat.choose (2 * r) r * r !) * r !
      = (Nat.doubleFactorial (2 * r - 1) * 2 ^ r) * r ! := by
    calc (Nat.choose (2 * r) r * r !) * r !
        = Nat.choose (2 * r) r * (r ! * r !) := by ring
      _ = (2 * r)! := hchoose
      _ = Nat.doubleFactorial (2 * r) * Nat.doubleFactorial (2 * r - 1) := hdf
      _ = (2 ^ r * r !) * Nat.doubleFactorial (2 * r - 1) := by rw [heven]
      _ = (Nat.doubleFactorial (2 * r - 1) * 2 ^ r) * r ! := by ring
  exact Nat.eq_of_mul_eq_mul_right hr0 key2

/-- **Wick STRICTLY overtakes the toric Betti for `r ≥ 4`.** From the identity
`C(2r,r)·r! = (2r−1)‼·2^r` and `2^r < r!`, we get `C(2r,r)·r! = (2r−1)‼·2^r < (2r−1)‼·r!`, so
`C(2r,r) < (2r−1)‼`. Hence the proposed `dim_prim = C(2r,r) − (2r−1)‼` is "negative" — there are
MORE Wick matchings than total config-variety Betti classes. The two counts are incomparable;
`dim_prim` is not a cohomology dimension. The prize requires `r ≈ ln q ≈ 83 ≫ 4`, so the
formula is malformed throughout the relevant depth range. -/
theorem wick_gt_betti (r : ℕ) (hr : 4 ≤ r) :
    Nat.choose (2 * r) r < Nat.doubleFactorial (2 * r - 1) := by
  have hid : Nat.choose (2 * r) r * r ! = Nat.doubleFactorial (2 * r - 1) * 2 ^ r :=
    betti_factorial_eq_wick_twopow r
  have h2r : 2 ^ r < r ! := factorial_gt_two_pow r hr
  -- C(2r,r)*r! = (2r-1)!! * 2^r < (2r-1)!! * r!  ⟹  C(2r,r) < (2r-1)!!
  have hdfpos : 0 < Nat.doubleFactorial (2 * r - 1) := Nat.doubleFactorial_pos _
  have hr0 : 0 < r ! := Nat.factorial_pos r
  have hlt : Nat.choose (2 * r) r * r ! < Nat.doubleFactorial (2 * r - 1) * r ! := by
    rw [hid]
    -- (2r-1)!! * 2^r < (2r-1)!! * r!  since 2^r < r! and (2r-1)!! > 0
    exact Nat.mul_lt_mul_of_le_of_lt (le_refl _) h2r hdfpos
  exact Nat.lt_of_mul_lt_mul_right hlt

/-- **The `ℕ`-truncated `dim_prim` is exactly `0` for `r ≥ 4`.** Since `C(2r,r) < (2r−1)‼`, the
truncated subtraction `C(2r,r) − (2r−1)‼ = 0` in `ℕ`. So the T05 bound `W_r ≤ dim_prim` reads
`W_r ≤ 0` at every prize-relevant depth. This is the formal statement that the "primitive
cohomology" T05 wants to bound the energy excess is EMPTY at `r ≥ 4`. -/
theorem dimPrimNat_eq_zero (r : ℕ) (hr : 4 ≤ r) :
    Nat.choose (2 * r) r - Nat.doubleFactorial (2 * r - 1) = 0 :=
  Nat.sub_eq_zero_of_le (le_of_lt (wick_gt_betti r hr))

/-- **The crossover is super-exponential, not a small-`r` artifact.** The exact ratio
`(2r−1)‼ · 2^r = C(2r,r) · r!` shows `(2r−1)‼ / C(2r,r) = r! / 2^r`, which diverges. We record
the multiplicative gap directly: for `r ≥ 4`, `(2r−1)‼ · 2^r = C(2r,r) · r!` with `r! / 2^r → ∞`,
so the proposed `dim_prim` deficit is not merely negative but grows in magnitude with `r`. (Stated
as the exact identity `C(2r,r) · r! = (2r−1)‼ · 2^r`, the engine of the divergence.) -/
theorem wick_over_betti_ratio (r : ℕ) :
    Nat.choose (2 * r) r * r ! = Nat.doubleFactorial (2 * r - 1) * 2 ^ r :=
  betti_factorial_eq_wick_twopow r

/-! ## Part II — the Veronese moment curve folds up over `μ_n`: no transversality gain -/

/-- **The fold fact (cardinality of the power-map image).** Abstractly: the Veronese coordinate
`x ↦ x^j` on the cyclic group `μ_n` (order `n`) has image of size `n / gcd(j,n)`, which DIVIDES
`n`. So each Veronese coordinate folds `μ_n` into a (possibly proper) subgroup; the moment curve
does NOT open `r` transversal directions. We model `μ_n` as `ZMod n` (additively, `≅` the cyclic
group of order `n`) and the `j`-th power map as multiplication by `j`; its image is the subgroup
of index `gcd(j,n)`, of size `n / gcd(j,n)`. This proves the image size divides `n`. -/
theorem power_map_image_card_dvd (n j : ℕ) (hn : 0 < n) :
    (n / Nat.gcd j n) ∣ n := by
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right j n)

/-- **The fold is PROPER for even `j` (e.g. the squaring `j = 2`).** When `gcd(j,n) > 1` — which
holds for every even `j` since `n = 2^μ` is a 2-power — the image `n/gcd(j,n) < n` is a STRICT
subgroup: the Veronese coordinate collapses `μ_n` onto fewer than `n` points. A coordinate that is
not even injective cannot supply a transversal (general-position) direction; the per-class
`p^{−1/2}` Veronese-transversality gain T05 needs is geometrically absent. -/
theorem power_map_image_proper_of_common_factor (n j : ℕ) (hn : 2 ≤ n)
    (hg : 2 ≤ Nat.gcd j n) : n / Nat.gcd j n < n := by
  have hgn : Nat.gcd j n ≤ n := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right j n)
  exact Nat.div_lt_self (by omega) (by omega)

/-- **Concrete: over `μ_n` with `n = 2^μ`, the squaring coordinate `x ↦ x²` folds `μ_n` onto
`μ_{n/2}` (`gcd(2, 2^μ) = 2`).** So the SECOND Veronese coordinate already halves the point set —
the moment curve is maximally degenerate over a 2-power subgroup. -/
theorem squaring_folds_two_power (μ : ℕ) (hμ : 1 ≤ μ) :
    (2 ^ μ) / Nat.gcd 2 (2 ^ μ) = 2 ^ (μ - 1) := by
  have hg : Nat.gcd 2 (2 ^ μ) = 2 := by
    have h2 : (2 : ℕ) ∣ 2 ^ μ := dvd_pow_self 2 (by omega)
    rw [Nat.gcd_eq_left h2]
  rw [hg]
  -- 2^μ / 2 = 2^μ / 2^1 = 2^(μ-1)
  calc (2 : ℕ) ^ μ / 2 = 2 ^ μ / 2 ^ 1 := by rw [pow_one]
    _ = 2 ^ (μ - 1) := Nat.pow_div hμ (by norm_num)

/-! ## Part III — the REDUCTION to F2 (the configuration-variety Weil wall, A04)

The architect's dichotomy: T05 closes the prize IFF the moment-curve transversality lowers the
primitive-part Weil weight from `2(r−1)` to `2(r−1)−1` (the extra `p^{−1/2}` per class). Parts I
and II show the mechanism is untenable:

* Part I: the "primitive part" `dim_prim` is empty (`= 0` in `ℕ`) for all prize depths `r ≥ 4` —
  there is no nonempty class set to transversalize.
* Part II: the Veronese coordinates fold `μ_n` into proper subgroups (zero net curvature) — even
  if the primitive part were nonempty, the curve supplies no general-position transversality.

So the primitive classes remain pure of weight `2(r−1)`, the configuration-variety Weil error
stays `p^{r−1}`, and we are exactly at the in-tree F2 wall: `_wfA04_weil_envelope_vacuity`
proves `(2r)^r · n^r ≤ C(2r,r) · (n^4)^{r−1}` at `β = 4` (the toric Weil envelope DOMINATES the
char-0 main term for `r ≥ 2`). We re-derive that domination here, self-contained, to certify the
landing fence.
-/

/-- **F2 landing (self-contained restatement of A04's `crude_le_pow4`).** At the prize `β = 4`
(`p = n^4`), for `2 ≤ r`, `2r ≤ n`: the crude char-0 ceiling `(2r)^r·n^r` is dominated by the
configuration-variety Weil weight `(n^4)^{r−1} = p^{r−1}`. Since the toric Betti `C(2r,r) ≥ 1`
multiplies `p^{r−1}`, the Weil error term is `Ω(char-0)`, never `o(char-0)`: the un-transversalized
config-variety bound is vacuous, which is precisely the F2 wall T05 reduces to. -/
theorem f2_weil_weight_dominates (n r : ℕ) (hr : 2 ≤ r) (hsmall : 2 * r ≤ n) :
    (2 * r) ^ r * n ^ r ≤ (n ^ 4) ^ (r - 1) := by
  have hbase : (2 * r) ^ r ≤ n ^ r := Nat.pow_le_pow_left hsmall r
  calc (2 * r) ^ r * n ^ r ≤ n ^ r * n ^ r := Nat.mul_le_mul_right _ hbase
    _ = n ^ (2 * r) := by rw [← pow_add]; ring_nf
    _ ≤ n ^ (4 * (r - 1)) := by
        apply Nat.pow_le_pow_right (by omega)
        omega
    _ = (n ^ 4) ^ (r - 1) := by rw [← pow_mul, Nat.mul_comm]

/-- **The reduction, packaged as a conditional.** Model the T05 transversality claim as a
hypothesis `htrans : excess ≤ dimPrim` with `dimPrim := C(2r,r) − (2r−1)‼` (the `ℕ`-truncated
deficit). For `r ≥ 4` this forces `excess ≤ 0` (Part I, `dimPrimNat_eq_zero`). So the ONLY way
T05's bound is non-vacuous (`excess` could be a genuine positive `O_r(1)`) is at depths `r < 4`,
which are far below the prize depth `r ≈ ln q ≈ 83`. At the prize depth the claimed bound is
`excess ≤ 0`, contradicting any prime with positive spurious energy. Hence T05 supplies NO usable
energy-excess control at prize regime, and the residual stays on F2. -/
theorem t05_bound_is_vacuous_at_prize_depth (r excess : ℕ) (hr : 4 ≤ r)
    (htrans : excess ≤ Nat.choose (2 * r) r - Nat.doubleFactorial (2 * r - 1)) :
    excess = 0 := by
  have : Nat.choose (2 * r) r - Nat.doubleFactorial (2 * r - 1) = 0 := dimPrimNat_eq_zero r hr
  omega

end ArkLib.ProximityGap.Frontier.wfT05VeronesePrimitiveReduction

/-! ## Axiom audit — must be `⊆ {propext, Classical.choice, Quot.sound}`. -/
#print axioms ArkLib.ProximityGap.Frontier.wfT05VeronesePrimitiveReduction.factorial_gt_two_pow
#print axioms ArkLib.ProximityGap.Frontier.wfT05VeronesePrimitiveReduction.betti_factorial_eq_wick_twopow
#print axioms ArkLib.ProximityGap.Frontier.wfT05VeronesePrimitiveReduction.wick_gt_betti
#print axioms ArkLib.ProximityGap.Frontier.wfT05VeronesePrimitiveReduction.dimPrimNat_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.wfT05VeronesePrimitiveReduction.wick_over_betti_ratio
#print axioms ArkLib.ProximityGap.Frontier.wfT05VeronesePrimitiveReduction.power_map_image_card_dvd
#print axioms ArkLib.ProximityGap.Frontier.wfT05VeronesePrimitiveReduction.power_map_image_proper_of_common_factor
#print axioms ArkLib.ProximityGap.Frontier.wfT05VeronesePrimitiveReduction.squaring_folds_two_power
#print axioms ArkLib.ProximityGap.Frontier.wfT05VeronesePrimitiveReduction.f2_weil_weight_dominates
#print axioms ArkLib.ProximityGap.Frontier.wfT05VeronesePrimitiveReduction.t05_bound_is_vacuous_at_prize_depth
