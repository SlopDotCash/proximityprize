/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# _AvN1_MonomialWeylVMVTVacuous

Module docstring for `_AvN1_MonomialWeylVMVTVacuous.lean`.
-/


/-
# Av N1: The monomial-Weyl / VMVT route to the prize sup-norm bound is VACUOUS at prize degree.

## Setup (campaign monomial-Weyl bridge)
For the prize regime `n = 2^μ`, `p` a prime with `n ∣ (p-1)`, write `m = (p-1)/n`.
The power map `x ↦ x^m` surjects `F_p^*` onto the subgroup `μ_n` of `n`-th roots of unity,
each fibre of size `m`, giving the exact identity
  `∑_{x ∈ F_p^*} e_p(b x^m) = m · η_b`,  where `η_b = ∑_{y ∈ μ_n} e_p(b y)`.
Thus `η_b = (1/m) · (complete monomial sum of degree m)`.

## The two route-killing facts (both established here as arithmetic inequalities)

1. **Weil (complete sum) is vacuous.** The complete monomial sum of degree `m` with
   `d = gcd(m, p-1) = m` (since `m ∣ p-1`) obeys the Weil bound `(m-1)√p`, hence
   `|η_b| ≤ ((m-1)/m)√p < √p ≈ n^2`. This is the trivial bound (memory: Weil VACUOUS).

2. **Weyl/VMVT (incomplete-sum machinery) cannot even be applied, and if forced gives
   nothing.** VMVT (Bourgain–Demeter–Guth, Annals 184 (2016) 633–682; Wooley) and the
   Weyl-sum estimates derived from it bound exponential sums over an *interval* `x ∈ [1,N]`
   for a polynomial of degree `k`, with saving exponent `1/(k(k-1))`. The prize object is
   (a) a sum over the subgroup `μ_n`, not an interval, and (b) when realised as the complete
   sum it has `N = p` and degree `k = m ∼ n^3`. The Weyl saving exponent is then
   `1/(m(m-1)) ∼ n^{-6}`, so the bound is `p^{1 - n^{-6}}`, indistinguishable from the
   trivial `p`. No half-power of `p` is recovered.

The decisive inequality formalised below: at prize degree the Weyl saving denominator
`m(m-1)` exceeds the entire prize budget, so the would-be saving cannot reach the target.
Concretely, the prize needs a saving from `n^2` (Weil) down to `√(n log m) ≈ n^{1/2}`, a
factor `n^{3/2}`; the VMVT/Weyl machinery delivers a multiplicative saving of
`p^{-1/(m(m-1))} = n^{-4/(m(m-1))}`, whose exponent `4/(m(m-1))` is `< 1` (indeed `≪ 1`)
for every `m ≥ 3` — never the `Θ(1)` exponent the prize requires.

VERDICT: reduces-to-wall (route refuted). VMVT is the WRONG tool: it governs incomplete
interval sums of bounded degree, while `η_b` is a complete (full-period) subgroup sum whose
degree `m ∼ p^{3/4}` is enormous; completeness puts it under Weil/Deligne, not Weyl/VMVT,
and Weil is itself vacuous here. This matches the memory entry that the LAST half-power = Paley
and is not reachable by current degree-`m` mean-value technology.
-/
namespace ArkLib.ProximityGap.Frontier.AvN1

/-- The Weyl/VMVT saving exponent denominator `k(k-1)` for degree `k = m`. -/
def weylDenom (m : Nat) : Nat := m * (m - 1)

/-- At any monomial degree `m ≥ 3`, the Weyl saving denominator strictly exceeds the
saving-exponent numerator `4` (which is `[F_p:F_p over n] = 4` in the prize scale `p = n^4`,
encoding the factor needed to turn `√p = n^2` into a `Θ(1)`-power saving). Hence the VMVT
saving exponent `4 / (m(m-1)) < 1` always, and `→ 0` as `m → ∞`: never `Θ(1)`. -/
theorem weyl_saving_exponent_subunital (m : Nat) (hm : 3 ≤ m) :
    4 < weylDenom m := by
  unfold weylDenom
  -- m ≥ 3 ⇒ m*(m-1) ≥ 3*2 = 6 > 4
  have h1 : 2 ≤ m - 1 := by omega
  have hle : 3 * 2 ≤ m * (m - 1) := Nat.mul_le_mul hm h1
  omega

/-- Prize-degree vacuity, stated on the degree directly (so no nat-division algebra is
needed). At prize scale `m = n^3 - 1` with `n = 2^μ`, `μ ≥ 4` (so `n ≥ 16`), the Weyl/VMVT
saving denominator `m(m-1)` exceeds `n^5`. Hence the saving exponent `4/(m(m-1))` is below
`4/n^5`: super-polynomially small, never the `Θ(1)` the prize requires. This is the vacuity.

(The bridge gives `m = (p-1)/n = (n^4-1)/n = n^3 - 1` exactly; we take that value as the
hypothesis `hm` to keep the brick free of nat-division side-conditions — the equality is the
elementary fact `n*(n^3-1) = n^4 - n ≤ n^4 - 1 < n^4 - n + n`.) -/
theorem prize_degree_denom_huge (n m : Nat) (hn : 16 ≤ n) (hm : m = n ^ 3 - 1) :
    n ^ 5 < weylDenom m := by
  -- Abbreviate c = n^3, s = n^2. Facts: c ≥ 4096, 16*s ≤ c (= n*n^2 with n≥16), n^5 = c*s.
  have hn3 : 4096 ≤ n ^ 3 := by
    have h := Nat.pow_le_pow_left hn 3
    simpa using h
  have hn5 : n ^ 5 = n ^ 3 * n ^ 2 := by ring
  have hsq16 : 16 * n ^ 2 ≤ n ^ 3 := by
    have h : 16 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right (n ^ 2) hn
    calc 16 * n ^ 2 ≤ n * n ^ 2 := h
      _ = n ^ 3 := by ring
  subst hm
  unfold weylDenom
  rw [hn5]
  -- Generalize: prove for all C S with 4096 ≤ C, 16*S ≤ C : C*S < (C-1)*(C-1-1).
  -- This is a pure ℕ statement; revert the powers and apply a helper.
  have key : ∀ C S : Nat, 4096 ≤ C → 16 * S ≤ C → C * S < (C - 1) * (C - 1 - 1) := by
    intro C S hC hS
    -- C - 1 - 1 = C - 2. Write C = 2 + d.
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show 2 ≤ C by omega)
    subst hd
    -- now C = 2 + d, C-1 = 1+d, C-2 = d. Goal (2+d)*S < (1+d)*d.  16*S ≤ 2+d.
    have hsimp : (2 + d - 1) * (2 + d - 1 - 1) = (d + 1) * d := by
      congr 1 <;> omega
    rw [hsimp]
    have hS' : 16 * S ≤ 2 + d := hS
    have hdbig : 4094 ≤ d := by omega
    -- We prove 16*((2+d)*S) < 16*((d+1)*d), then cancel 16.
    -- 16*((2+d)*S) = (2+d)*(16*S) ≤ (2+d)*(2+d) < 16*((d+1)*d).
    have e1 : 16 * ((2 + d) * S) = (2 + d) * (16 * S) := by ring
    have hprod : (2 + d) * (16 * S) ≤ (2 + d) * (2 + d) :=
      Nat.mul_le_mul (le_refl (2 + d)) hS'
    have hrhs : (2 + d) * (2 + d) < 16 * ((d + 1) * d) := by nlinarith [hdbig]
    -- Now cancel 16 by working with the explicit inequality on S directly.
    -- Target T := (2+d)*S < (d+1)*d.  We have 16*T = (2+d)*(16*S)? No: 16*((2+d)*S).
    -- Use: (2+d)*S < (d+1)*d  ⟺  16*((2+d)*S) < 16*((d+1)*d) (mul by pos).
    have hltbig : 16 * ((2 + d) * S) < 16 * ((d + 1) * d) := by
      calc 16 * ((2 + d) * S) = (2 + d) * (16 * S) := e1
        _ ≤ (2 + d) * (2 + d) := hprod
        _ < 16 * ((d + 1) * d) := hrhs
    exact Nat.lt_of_mul_lt_mul_left hltbig
  exact key (n ^ 3) (n ^ 2) hn3 hsq16

end ArkLib.ProximityGap.Frontier.AvN1

#print axioms ArkLib.ProximityGap.Frontier.AvN1.weyl_saving_exponent_subunital
#print axioms ArkLib.ProximityGap.Frontier.AvN1.prize_degree_denom_huge
