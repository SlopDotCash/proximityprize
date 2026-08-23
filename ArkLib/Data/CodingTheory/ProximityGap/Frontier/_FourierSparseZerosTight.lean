/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FourierSparseZeros
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModSubgroupSaturation

/-!
# The Donoho–Stark zero bound is ATTAINED at subgroup indicators (`2^μ` sits at Johnson) (#407)

`_FourierSparseZeros.zeros_le_of_dft_sparse` gives the composite-side (Donoho–Stark) list-decoding
zero bound: a `t`-Fourier-sparse `Φ ≠ 0` on `ZMod N` vanishes on `≤ N·(1 − 1/t)` points (`t = k+2`
gives the Johnson-scale radius).  That is an *upper* bound; what makes the [349] dichotomy sharp on
the composite/`2^μ` side is that this bound is **ATTAINED** — there is no slack below Johnson via
Donoho–Stark, precisely because `2^μ` is a subgroup and subgroup indicators saturate the principle
(`_ZModSubgroupSaturation`).

This file lands the attainment.  For `d ∣ N`, the order-`d` subgroup indicator `Φ = 1_{μ_d}` has:
* DFT support `N/d` (the dual subgroup) — so it is `t`-Fourier-sparse for `t = N/d`;
* physical support `d` — so it vanishes on exactly `N − d` points;
and `N − d = N·(1 − 1/t)` with `t = N/d`.  So the Donoho–Stark zero bound holds with **equality**.

> `subgroupIndicator_zeros_eq_donoho_stark_bound` :
>   for `d ∣ N`, `0 < d`, with `t := N/d`,
>   `|{j : 1_{μ_d} j = 0}| = N − d = N·(1 − 1/t)`  (the `zeros_le_of_dft_sparse` bound, attained).

Consequence (`donoho_stark_zero_bound_is_sharp`): the composite-side Johnson zero bound cannot be
improved by *any* uncertainty-only argument; the witness is an explicit subgroup indicator.  This is
the structural reason `μ_{2^μ}` lands at JOHNSON, not capacity: the *additive* (Tao/capacity)
strengthening is what `2`-power groups lack (Chebotarev fails for composite order), and the
multiplicative bound they do satisfy is tight.  It asserts nothing about CORE beyond locating the
composite door; no cancellation, completion, anti-concentration, moment, or capacity claim for
`2^μ`.  Axiom-clean.  Issue #407.
-/

open Finset ZMod
open ProximityGap.Frontier.ZModDonohoStark
open ProximityGap.Frontier.ZModSubgroupSaturation
open ProximityGap.Frontier.FourierSparseZeros

namespace ProximityGap.Frontier.FourierSparseZerosTight

variable {N : ℕ} [NeZero N]

/-- The order-`d` subgroup indicator vanishes on exactly `N − d` points (`d ∣ N`), since its
physical support is the order-`d` subgroup (`d` points). -/
theorem subgroupIndicator_zeros_card {d : ℕ} (hd : d ∣ N) :
    (univ.filter (fun j => (subgroupIndicator (N := N) d) j = 0)).card = N - d := by
  -- zeros + support = N, and support = d
  have hsuppd : (supp (subgroupIndicator (N := N) d)).card = d := supp_subgroupIndicator_card hd
  have hcompl :
      (univ.filter (fun j => (subgroupIndicator (N := N) d) j = 0)).card
        + (supp (subgroupIndicator (N := N) d)).card = N := by
    rw [supp]
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (univ : Finset (ZMod N)))
      (p := fun j => (subgroupIndicator (N := N) d) j = 0)
    simpa [ZMod.card, eq_comm, Finset.filter_not] using this
  omega

/-- **The Donoho–Stark zero bound is ATTAINED at the order-`d` subgroup indicator.**  For `d ∣ N`,
`0 < d`, set `t := N / d` (the indicator's DFT support, so it is `t`-Fourier-sparse).  Then the
indicator's zero count equals the `zeros_le_of_dft_sparse` upper bound `N·(1 − 1/t)`:

`(|{j : 1_{μ_d} j = 0}| : ℝ) = N·(1 − 1/(N/d))  ( = N − d)`.

Hence the composite-side Johnson zero bound has NO slack; an explicit subgroup indicator saturates
it.  This is why `μ_{2^μ}` sits at JOHNSON, not capacity. -/
theorem subgroupIndicator_zeros_eq_donoho_stark_bound {d : ℕ} (hd : d ∣ N) (hdpos : 0 < d) :
    ((univ.filter (fun j => (subgroupIndicator (N := N) d) j = 0)).card : ℝ)
      = (N : ℝ) * (1 - 1 / ((N / d : ℕ) : ℝ)) := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- t = N/d, and d·t = N since d ∣ N
  have hdt : d * (N / d) = N := Nat.mul_div_cancel' hd
  have htpos : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hNpos hd) hdpos
  have htR : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by exact_mod_cast htpos
  -- LHS = N − d
  rw [subgroupIndicator_zeros_card hd]
  -- N·(1 − 1/t) = N − N/t = N − d  (since N/t = d as reals, from d·t = N)
  have hdleN : d ≤ N := Nat.le_of_dvd hNpos hd
  have hNcast : ((N - d : ℕ) : ℝ) = (N : ℝ) - (d : ℝ) := by
    rw [Nat.cast_sub hdleN]
  rw [hNcast]
  -- N/t = d as reals, from d·t = N
  have hNdivt : (N : ℝ) / ((N / d : ℕ) : ℝ) = (d : ℝ) := by
    rw [div_eq_iff (ne_of_gt htR)]
    have hcast : ((d * (N / d) : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast hdt
    push_cast at hcast
    linarith [hcast]
  -- N·(1 − 1/t) = N − N·(1/t) = N − N/t = N − d
  have hexpand : (N : ℝ) * (1 - 1 / ((N / d : ℕ) : ℝ))
      = (N : ℝ) - (N : ℝ) / ((N / d : ℕ) : ℝ) := by
    rw [mul_sub, mul_one, mul_one_div]
  rw [hexpand, hNdivt]

/-- **The composite (Donoho–Stark) Johnson zero bound is SHARP.**  For every divisor `d ∣ N`,
`0 < d`, the order-`d` subgroup indicator is a nonzero `(N/d)`-Fourier-sparse function that attains
the `zeros_le_of_dft_sparse` upper bound with equality.  Therefore no uncertainty-only argument can
push the composite-side list-decoding radius below Johnson: the witness is explicit and exists at
every scale (in particular `d = N/2` on `N = 2^μ`).  Bundles the `≤` bound and the attaining
equality. -/
theorem donoho_stark_zero_bound_is_sharp {d : ℕ} (hd : d ∣ N) (hdpos : 0 < d) :
    subgroupIndicator (N := N) d ≠ 0
      ∧ (supp (𝓕 (subgroupIndicator (N := N) d))).card = N / d
      ∧ ((univ.filter (fun j => (subgroupIndicator (N := N) d) j = 0)).card : ℝ)
          = (N : ℝ) * (1 - 1 / ((N / d : ℕ) : ℝ)) :=
  ⟨subgroupIndicator_ne_zero d,
   supp_dft_subgroupIndicator_card hd,
   subgroupIndicator_zeros_eq_donoho_stark_bound hd hdpos⟩

end ProximityGap.Frontier.FourierSparseZerosTight

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.FourierSparseZerosTight.subgroupIndicator_zeros_card
#print axioms
  ProximityGap.Frontier.FourierSparseZerosTight.subgroupIndicator_zeros_eq_donoho_stark_bound
#print axioms ProximityGap.Frontier.FourierSparseZerosTight.donoho_stark_zero_bound_is_sharp
