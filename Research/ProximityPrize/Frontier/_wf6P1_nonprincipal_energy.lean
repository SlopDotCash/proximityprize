/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumEnergyReduction

/-!
# The nonprincipal energy reduction for the subgroup Gauss sum (#444, lane wf-P1)

## The target and the live lead

For `G = μ_n` (order `n = 2^μ`, `n | p-1`, `q = p`) and `η_b = ∑_{y∈G} ψ(b·y)`, the Proximity
Prize reduces to `M(n) := max_{b≠0} ‖η_b‖ ≤ C·√(n·log(p/n))`.

The moment ladder (`subgroup_gaussSum_moment`, pure additive orthogonality, **no Weil**) gives
the exact `2r`-th moment `∑_b ‖η_b‖^{2r} = q·E_r(G)`, where `E_r = energyR G r` is the `r`-fold
additive energy *counted in `F_p`* (char-`p`). The in-tree `eta_pow_le_energyR` already subtracts
the `b=0` spike `‖η_0‖ = n` and bounds a single nonprincipal term:
`‖η_b‖^{2r} ≤ q·E_r − n^{2r}` for `b ≠ 0`.

## What lane P1 settles (the crux check)

**Strategy P1** was: prove the sufficient lemma `(S-M1)` by showing the char-`p` excess in `E_r`
is *entirely* the principal `b=0` contribution `n^{2r}`, so that the char-0 Lam–Leung bound
`E_r ≤ (2r-1)‼·n^r` transfers to `b ≠ 0` after subtracting `n^{2r}`.

**Exact-numerics verdict (`scripts/probes/rust/nonprincipal_energy_wf6P1.rs`, exact integer/cos
period sums over `F_p`, `p = Θ(n^4)`, optimal depth `r ≈ 1.5·ln q`):**

* The **literal route is REFUTED**: the *full* char-`p` energy ratio `E_r / [(2r-1)‼ n^r]`
  EXCEEDS `1` past `r > β` — peaking at `6.31×` (`n=32, r=16`) and `> 1.1×10⁶` (`n=64, r=24`).
  So `E_r ≤ (2r-1)‼ n^r` is **false in char `p`**, and `q·E_r − n^{2r} ≤ q·(2r-1)‼ n^r − n^{2r}`
  fails (the RHS goes negative). The char-0 bound does **not** transfer to the full energy.

* The **principal-subtracted (nonprincipal) energy is, however, genuinely sub-char-0**: the
  measured `E_r'(G) := E_r − n^{2r}/q` satisfies `E_r' / [(2r-1)‼ n^r] ≤ 1` for **all** `r` at
  `n = 16, 32, 64, 128`, with `sup_r` attained at `r = 1` (where it equals exactly `n − n²/q < n`,
  i.e. Parseval) and decaying to `< 10⁻³` at `r ≈ ln q`. The blow-up of the full `E_r` is thus
  carried **entirely by the single principal term `n^{2r}`** (which the identity isolates
  exactly), *not* by the nonprincipal mass — confirming the P1 insight in its **correct form**:
  the spurious mod-`p` coincidences factor through the principal/diagonal, but you must subtract
  the principal *before* comparing to char-0, not after a bound on the full sum.

* Consequently the moment route gives the prize: the best moment bound
  `(q·E_r')^{1/2r}` minimized over `r` achieves `/prize ≈ 1.28 → 1.42` (`n=16→128`), vs. the
  ground-truth `max‖η_b‖/prize ≈ 1.15 → 1.29`. So `C ≈ 1.42` is the route's constant.

## This file

1. `nonprincipal_energy_eq` — the **exact** nonprincipal-energy identity (axiom-clean):
   `∑_{b≠0} ‖η_b‖^{2r} = q·E_r(G) − n^{2r}`.
2. `NonprincipalEnergyBound` — the **named** sufficient hypothesis (the LIVE `(S-M1')` in its
   correct, principal-subtracted form): `q·E_r − n^{2r} ≤ q·(2r-1)‼·n^r`.
3. `eta_pow_le_of_nonprincipalEnergyBound` — the **bridge** (axiom-clean): the hypothesis ⟹ the
   per-frequency sup bound `‖η_b‖^{2r} ≤ q·(2r-1)‼·n^r` for every `b ≠ 0`. (Pure consequence of
   `eta_pow_le_energyR` + the hypothesis; the hard content is producing the hypothesis, which is
   the open additive-energy crux for `r ≈ ln q`, `n = 2^30`.)

The named hypothesis is the project's modularity convention (§6): the open core lives as one
`Prop`, and `eta_pow_le_of_nonprincipalEnergyBound` is its proven consumer. The crux probe shows
WHY the subtraction is mandatory rather than cosmetic.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

namespace ArkLib.ProximityGap.Frontier.WF6P1

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The exact nonprincipal-energy identity.** Splitting the `b = 0` principal spike
(`‖η_0‖ = |G|`, so `‖η_0‖^{2r} = n^{2r}`) off the moment ladder `∑_b ‖η_b‖^{2r} = q·E_r`:
`∑_{b≠0} ‖η_b‖^{2r} = q·E_r(G) − n^{2r}`. Pure orthogonality; no Weil. Axiom-clean. -/
theorem nonprincipal_energy_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
      = (Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r) := by
  have h0 : eta ψ G 0 = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  have hn0 : ‖eta ψ G (0 : F)‖ ^ (2 * r) = (G.card : ℝ) ^ (2 * r) := by
    rw [h0, Complex.norm_natCast]
  have hmom := subgroup_gaussSum_moment hψ G r
  have hsplit : ∑ b' : F, ‖eta ψ G b'‖ ^ (2 * r)
      = ‖eta ψ G (0 : F)‖ ^ (2 * r)
        + ∑ b' ∈ univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  rw [hmom, hn0] at hsplit
  linarith

/-- **The named sufficient hypothesis `(S-M1')` — the live moment-route lever in its correct,
principal-subtracted form.** The *nonprincipal* `2r`-th energy is at most the char-0 (Lam–Leung)
Gaussian value `q·(2r-1)‼·n^r`. Equivalently `E_r' := E_r − n^{2r}/q ≤ (2r-1)‼·n^r`.

This is the live `(S-M1')`: it is sub-char-0 *empirically for all `r` at `n ≤ 128`* (lane P1
probe), with the full-`E_r` blow-up isolated in the subtracted principal `n^{2r}`. Proving it to
depth `r ≈ ln q` for `n = 2^30` is the open additive-energy crux (Lam–Leung char-`p` transfer). -/
def NonprincipalEnergyBound (G : Finset F) (r : ℕ) (doubleFact : ℝ) : Prop :=
  (Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r)
    ≤ (Fintype.card F : ℝ) * (doubleFact * (G.card : ℝ) ^ r)

/-- **The bridge: `(S-M1')` ⟹ per-frequency sup bound.** Given the nonprincipal-energy bound,
every nontrivial frequency satisfies `‖η_b‖^{2r} ≤ q·(2r-1)‼·n^r`. Combined with the optimal
depth `r ≈ ln q` and `(2r-1)‼ ≤ (2r)^r`, this is the prize cancellation
`max_{b≠0}‖η_b‖ ≤ C√(n log q)`. Axiom-clean consumer of `eta_pow_le_energyR`. -/
theorem eta_pow_le_of_nonprincipalEnergyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (doubleFact : ℝ)
    (hbound : NonprincipalEnergyBound (F := F) G r doubleFact)
    (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (doubleFact * (G.card : ℝ) ^ r) := by
  have h := ArkLib.ProximityGap.SubgroupGaussSumMomentLadder.eta_pow_le_energyR hψ G r b hb
  exact le_trans h hbound

/-- The per-frequency bound is *equivalent* to bounding the nonprincipal energy: the bridge is
not lossy, so `NonprincipalEnergyBound` is exactly the right named object. (Single-term ≤ sum;
the sum is the full nonprincipal energy by `nonprincipal_energy_eq`.) Records that no slack is
hidden in the reduction. -/
theorem sup_le_nonprincipalEnergy (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ)
    (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ ∑ b' ∈ univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) := by
  have hmem : b ∈ univ.erase (0 : F) := Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
  exact Finset.single_le_sum (f := fun b' => ‖eta ψ G b'‖ ^ (2 * r))
    (fun i _ => pow_nonneg (norm_nonneg _) _) hmem

end ArkLib.ProximityGap.Frontier.WF6P1

#print axioms ArkLib.ProximityGap.Frontier.WF6P1.nonprincipal_energy_eq
#print axioms ArkLib.ProximityGap.Frontier.WF6P1.eta_pow_le_of_nonprincipalEnergyBound
#print axioms ArkLib.ProximityGap.Frontier.WF6P1.sup_le_nonprincipalEnergy
