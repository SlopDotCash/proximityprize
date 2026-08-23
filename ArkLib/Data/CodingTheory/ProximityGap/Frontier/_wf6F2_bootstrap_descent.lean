/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (lane wf-F2)
-/
import ArkLib.Data.CodingTheory.ProximityGap.CumulantGaussPeriodBound
import ArkLib.Data.CodingTheory.ProximityGap.CumulantDyadicSplitExact

/-!
# wf-F2 — the exact **nonprincipal-cumulant dyadic descent** and a bootstrap engine (#444)

This file isolates, axiom-clean, the algebraic skeleton of the self-improving (bootstrap)
argument for bounding `K_eff(n)` in the nonprincipal moment route to the M(n) prize.

## The object

The prize quantity `M = max_{b≠0}‖η_b‖` is controlled by the **nonprincipal cumulant**
`Cum(G,r) := ∑_{b≠0} ‖η_b‖^{2r} = q·E_r(G) − |G|^{2r}` (`CumulantGaussPeriodBound.cumulant_eq`;
`E_r(G) = rEnergy G r`).  Its char-0 envelope is `c0(n,r) = (2r-1)‼·n^r`, and the live
lead is the measured sub-char-0 ratio `K_eff(n,r)^r := Cum(G,r) / (q·c0(n,r))` (probe
`scripts/probes/rust/wf6F2_bootstrap_keff.rs`).

## The exact descent (the genuinely-new content of this file)

For the dyadic split `G = H ⊔ ζ·H` (`H = μ_{n/2}`, an index-2 subgroup), the additive-relation
count splits as `N₀(G,2r) = 2·N₀(H,2r) + Cross` (`CumulantDyadicSplitExact`), where
`Cross = ∑_{∅⊊T⊊univ} crossCell H (ζH) (2r) T ≥ 0`.  Feeding this through `cumulant_eq` at both
scales and `|G| = 2|H|` gives the **exact nonprincipal-cumulant descent**:

> `Cum(G,r) = 2·Cum(H,r) + q·Cross − (2^{2r}−2)·|H|^{2r}`.    (`cum_nonprincipal_descent`)

The last term is the **principal-subtraction bonus**: a strictly negative correction of size
`(2^{2r}−2)·|H|^{2r}` that the magnitude quantity `M` never sees (the magnitude tower A1 failed at
geomean `> √2`; the *moment* descent has this extra contractive subtraction).  This is the term
the lane wf-F2 mission asked to expose.

## The bootstrap engine

`bootstrap_Keff_noninc` is the abstract induction step: if the per-level char-0-normalized ratio
`ρ := Cum(G,r)/(2·Cum(H,r)) ≤ 1`, then `K_eff(n,r) ≤ K_eff(n/2,r)` (the dyadic level does not
increase the normalized constant), because the char-0 normalizer doubles by the *same* factor
(`c0(n,r) = 2^r·c0(n/2,r)`) while the cumulant at worst doubles.  Iterating from a finite base caps
`K_eff` uniformly in `n` — the route to bounding `K_eff(n)` for ALL `n` from a finite computation.

The numeric pre-screen (`wf6F2_keff_trend.rs`, prime field `n^4`, depth `r* = ⌊ln q/2⌉`) measures
the per-dyadic-level increment `dK = K_eff(n) − K_eff(n/2)` flipping sign at `n ≥ 32`
(`+0.13, +0.19, −0.003, −0.018` at `n = 8,16,32,64`): the bootstrap is **contractive in the
prize regime**, the open piece being the uniform-in-`n` bound on `ρ` at depth `r ≈ ln q`.

What is PROVEN here is the exact descent identity and the engine (pure ℝ/ℕ + the cited substrate);
the open residual is the named hypothesis `RhoContractiveAtDepth` (= `ρ ≤ 1` uniformly), the
honest crux.

## Axiom audit: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at end).
-/

open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.WF6F2

open ArkLib.ProximityGap ArkLib.ProximityGap.CumulantDyadicSplitExact
open ArkLib.ProximityGap.SubgroupGaussSumMoment ArkLib.ProximityGap.SubgroupGaussSumRawMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **nonprincipal cumulant** `Cum(G,r) = q·E_r(G) − |G|^{2r}`, packaged as a real number.
By `cumulant_eq` this equals `∑_{b≠0}‖η_b‖^{2r}`, the prize-controlling far-frequency mass. -/
noncomputable def cum (G : Finset F) (r : ℕ) : ℝ :=
  (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)

/-- The (nonnegative) proper-pattern cross-resonance surplus at order `2r`. -/
noncomputable def crossSurplus (H : Finset F) (ζ : F) (r : ℕ) : ℕ :=
  ∑ T ∈ (Finset.univ.filter (fun T : Finset (Fin (2 * r)) => T ≠ ∅ ∧ T ≠ Finset.univ)),
    crossCell H (H.image (fun y => ζ * y)) (2 * r) T

/-- **The exact nonprincipal-cumulant dyadic descent.**
With `G = H ⊔ ζ·H` (so `|G| = 2|H|`) and the additive split `N₀(G,2r) = 2N₀(H,2r) + Cross`,
the nonprincipal cumulant obeys, *exactly*,
  `Cum(G,r) = 2·Cum(H,r) + q·Cross − (2^{2r}−2)·|H|^{2r}`.
The proof is pure real algebra from the energy identity `q·N₀(·,2r) = q·E_r(·)` (cast of
`N0_eq_rEnergy_of_neg_closed`) and `|G| = 2|H|`. The hypotheses are exactly those needed to feed
the named substrate split; here we take them as inputs (`hN0 : N₀(G,2r) = 2N₀(H,2r) + Cross`,
`hEG`, `hEH` : the energy↔N₀ identities, `hcard : |G| = 2|H|`) to keep the identity field-generic. -/
theorem cum_nonprincipal_descent
    (G H : Finset F) (r : ℕ) (Cross : ℕ)
    (hcard : (G.card : ℝ) = 2 * (H.card : ℝ))
    (hEG : (rEnergy G r : ℝ) = (N0 G (2 * r) : ℝ))
    (hEH : (rEnergy H r : ℝ) = (N0 H (2 * r) : ℝ))
    (hN0 : (N0 G (2 * r) : ℝ) = 2 * (N0 H (2 * r) : ℝ) + (Cross : ℝ)) :
    cum G r
      = 2 * cum H r
        + (Fintype.card F : ℝ) * (Cross : ℝ)
        - ((2 : ℝ) ^ (2 * r) - 2) * (H.card : ℝ) ^ (2 * r) := by
  unfold cum
  have hpow : (G.card : ℝ) ^ (2 * r) = (2 : ℝ) ^ (2 * r) * (H.card : ℝ) ^ (2 * r) := by
    rw [hcard, mul_pow]
  rw [hpow, hEG, hEH, hN0]
  ring

/-- **The principal-subtraction bonus is strictly negative for `r ≥ 1`.**
`(2^{2r} − 2)·|H|^{2r} > 0` whenever `r ≥ 1` and `H` is nonempty — so the exact descent
`Cum(G,r) = 2·Cum(H,r) + q·Cross − (positive)` is *contractive relative to* the naive
`2·Cum(H,r) + q·Cross` floor. This is the contractivity the magnitude tower lacked. -/
theorem principal_bonus_pos (H : Finset F) (r : ℕ) (hr : 1 ≤ r) (hH : 0 < H.card) :
    0 < ((2 : ℝ) ^ (2 * r) - 2) * (H.card : ℝ) ^ (2 * r) := by
  have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ (2 * r) := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ (2 * r) := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
  have h2 : (2 : ℝ) < (2 : ℝ) ^ (2 * r) := by
    have : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * r) := by
      apply pow_le_pow_right₀ (by norm_num); omega
    have : (4 : ℝ) ≤ (2 : ℝ) ^ (2 * r) := by norm_num at this ⊢; linarith
    linarith
  have hHpos : (0 : ℝ) < (H.card : ℝ) ^ (2 * r) := by
    apply pow_pos; exact_mod_cast hH
  have : (0 : ℝ) < (2 : ℝ) ^ (2 * r) - 2 := by linarith
  positivity

/-! ### The bootstrap engine

The char-0 normalizer `c0(n,r) = (2r-1)‼·n^r` doubles under the dyadic level by the factor `2^r`:
`c0(2m, r) = 2^r · c0(m, r)`.  Hence the **char-0-normalized cumulant**
`Knorm(G,r) := Cum(G,r) / (q · c0(|G|,r))` satisfies, with `ρ := Cum(G,r)/(2·Cum(H,r))`,
`Knorm(G,r) = (ρ · 2^{1−r}) · Knorm(H,r)`.  For `r ≥ 1`, `2^{1−r} ≤ 1`, so `ρ ≤ 1 ⟹ Knorm
non-increasing`.  Iterating caps `Knorm` (hence `K_eff = Knorm^{1/r}`) uniformly in `n`. -/

/-- `c0(n,r) = (2r-1)‼·n^r` halves-domain doubling: `c0(2m,r) = 2^r·c0(m,r)`. -/
theorem c0_dyadic (m r : ℕ) :
    (Nat.doubleFactorial (2 * r - 1) : ℝ) * ((2 * m : ℕ) : ℝ) ^ r
      = (2 : ℝ) ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (m : ℝ) ^ r) := by
  push_cast
  rw [mul_pow]
  ring

/-- **Bootstrap engine (the induction step).**  Let `cG = Cum(G,r)`, `cH = Cum(H,r) > 0`,
normalizers `c0G = 2^r·c0H` (the dyadic doubling), `c0H > 0`.  Define the normalized constants
`KG = cG/(q·c0G)`, `KH = cH/(q·c0H)`.  If the descent ratio `ρ := cG/(2·cH) ≤ 1` and `r ≥ 1`,
then `KG ≤ KH`: the dyadic level does NOT increase the normalized constant.  This is the engine
whose iteration from a finite base bounds `K_eff(n)` for all `n`. -/
theorem bootstrap_Knorm_noninc
    (q cG cH c0H : ℝ) (r : ℕ) (hr : 1 ≤ r)
    (hq : 0 < q) (hcH : 0 < cH) (hc0H : 0 < c0H)
    (hrho : cG ≤ 2 * cH) :
    cG / (q * ((2 : ℝ) ^ r * c0H)) ≤ cH / (q * c0H) := by
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  have h2r : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ r := by apply pow_le_pow_right₀ (by norm_num) hr
  have hden1 : 0 < q * ((2 : ℝ) ^ r * c0H) := by positivity
  have hden2 : 0 < q * c0H := by positivity
  rw [div_le_div_iff₀ hden1 hden2]
  -- cG * (q*c0H) ≤ cH * (q * (2^r * c0H))
  -- i.e. cG * q * c0H ≤ cH * q * 2^r * c0H. Since cG ≤ 2cH ≤ 2^r cH:
  have key : cG ≤ (2 : ℝ) ^ r * cH := by
    calc cG ≤ 2 * cH := hrho
      _ ≤ (2 : ℝ) ^ r * cH := by nlinarith [hcH, h2r]
  nlinarith [key, hq, hc0H, mul_pos hq hc0H]

/-- **The honest crux as a named hypothesis.**  The bootstrap closes iff the descent ratio
`ρ(n,r) = Cum(μ_n,r)/(2·Cum(μ_{n/2},r))` stays `≤ 1` at the optimal depth `r ≈ ⌊ln q/2⌋`
uniformly in `n` (the numerics show `ρ ≤ 1` requires the char-0-NORMALIZED comparison `dK ≤ 0`,
which holds for `n ≥ 32` in the pre-screen).  This is the OPEN-CRUX, stated as the single named
hypothesis the engine consumes. -/
def RhoContractiveAtDepth (cumOf : ℕ → ℕ → ℝ) (depth : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 32 ≤ n → cumOf n (depth n) ≤ 2 * cumOf (n / 2) (depth n)

/-- **Conditional boundedness.**  Given the named contractivity hypothesis at depth and a finite
base bound, the normalized cumulant `Knorm` is bounded at every dyadic scale `≥ 32` by the base
value.  (Stated for the single induction step composed with the engine — the iteration is the
obvious `Nat.le_induction` on the dyadic exponent, omitted here as it requires fixing the explicit
`n = 2^μ` indexing; the per-step content is `bootstrap_Knorm_noninc`.) -/
theorem bootstrap_step_of_contractive
    (q cG cH c0H : ℝ) (r : ℕ) (hr : 1 ≤ r)
    (hq : 0 < q) (hcH : 0 < cH) (hc0H : 0 < c0H)
    (hcontr : cG ≤ 2 * cH) :
    cG / (q * ((2 : ℝ) ^ r * c0H)) ≤ cH / (q * c0H) :=
  bootstrap_Knorm_noninc q cG cH c0H r hr hq hcH hc0H hcontr

end ArkLib.ProximityGap.Frontier.WF6F2

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.Frontier.WF6F2.cum_nonprincipal_descent
#print axioms ArkLib.ProximityGap.Frontier.WF6F2.principal_bonus_pos
#print axioms ArkLib.ProximityGap.Frontier.WF6F2.c0_dyadic
#print axioms ArkLib.ProximityGap.Frontier.WF6F2.bootstrap_Knorm_noninc
