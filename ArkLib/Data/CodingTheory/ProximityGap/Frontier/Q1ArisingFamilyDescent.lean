/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.SmoothDomainSelfSimilarity

/-!
# Q1-ARISING: the arising rate-1/2 families substitution-reduce to a primitive base panel (#407)

The action-orbit FRI route (Chai–Fan 2026/861) reduces MCA soundness above the Johnson radius to
a *bad-prime gate* on a two-monomial pencil `h_α(z) = z^a + α z^b` over the cyclic FRI domain
`μ_n`, `n = 2^e`.  The bad-prime gate (`_BadPrimePowerGate.lean`) closes the worst case for a
**primitive** pencil (`gcd(a, b, n) = 1`).  This file discharges the remaining **arising-families**
gap: every rate-1/2 family that the protocol actually deploys (Chai–Fan §4) has a pencil whose
exponents share a common factor `d = gcd(a, b, n) > 1` with `n = 2^e` (so `d` is itself a power of
2), and the pencil therefore *substitution-reduces* to a primitive base pencil on `μ_{n/d}`.

Three pieces, all axiom-clean over Mathlib + the in-tree self-similarity substrate:

1. **`pencil_eq_expand`** — algebra.  When `d ∣ a` and `d ∣ b`, the deployment pencil factors
   through the `d`-th power map: `z^a + α z^b = expand_d(z^{a/d} + α z^{b/d})`, i.e. it equals
   `Polynomial.expand F d` of the *base pencil* `H_α(u) = u^{a/d} + α u^{b/d}`.

2. **`agreement_deploy_eq_d_mul_base`** — the agreement descent.  Composing (1) with the proven
   self-similarity theorem `Round16SelfSimilar.agreement_expand`, the deployment agreement of the
   pencil against a base-lifted word equals `d ·` (base agreement).  So the deployment list at
   scale `n` injects from / is governed by the base list at scale `n/d` — the
   "reduce to a finite base panel" pillar, now realized for the actual pencil.

3. **`orbitSize_descent`** — the orbit-count invariant.  The action-orbit theorem bounds soundness
   by the number of `⟨μ_n^{b−a}⟩`-orbits of bad challenges; that group has order
   `orbitSize n a b := n / gcd(b−a, n)`.  We prove this orbit size is **preserved exactly** under
   the substitution: `orbitSize n a b = orbitSize (n/d) (a/d) (b/d)`.  Hence the deployment pencil
   contributes *no new* orbit structure beyond the base — the bad-prime gate on the base panel is
   the whole story.

The three named families (Chai–Fan §4) are instantiated as `*_descends` corollaries with their
explicit `d` (always a power of 2 dividing `n`):

| family            | exponents `(a, b)`            | `d = gcd(a,b,n)` | base on |
|-------------------|-------------------------------|------------------|---------|
| sign-paired 4.4   | `(k, 3k)` (= `k+c, 3k+c`, c=0)| `k`              | `μ_4`   |
| `(k,2k)` 4.7      | `(k, 2k)`                     | `k`              | `μ_4`   |
| `(3k/2,2k)` 4.10  | `(3k/2, 2k)`                  | `k/2`            | `μ_8`   |

with `k = n/4` (rate 1/2).  Each `d` divides `n = 2^e` and is `> 1` (for `e ≥ 2`), so each family
collapses onto a *bounded* base panel (`μ_4` or `μ_8`), where the bad-prime gate / direct
enumeration finishes.  Combined with the primitive converse (Q3-PRIMITIVE: primitive far pencils
stay below Johnson agreement), this closes the universal-`h` / universal-`k` coverage at the prize
regime.

Honest scope.  This file proves the *structural* reduction (factorization, agreement descent,
orbit invariance) that lets the bad-prime gate on the small base panel govern the whole arising
family.  It does **not** re-prove the bad-prime gate (that is `_BadPrimePowerGate.lean`) nor the
primitive converse (Q3); it supplies the bridge that makes the gate apply to the deployed pencils.
-/

open Polynomial Finset

namespace ProximityGap.Frontier.Q1ArisingFamilyDescent

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The pencil factors through the `d`-th power map -/

/-- The two-monomial pencil `h_α(z) = z^a + α z^b`. -/
noncomputable def pencil (a b : ℕ) (α : F) : F[X] :=
  X ^ a + C α * X ^ b

/-- The **base pencil** `H_α(u) = u^{a'} + α u^{b'}` (the deployment pencil with exponents divided
by the common factor `d`). -/
noncomputable def basePencil (a' b' : ℕ) (α : F) : F[X] :=
  X ^ a' + C α * X ^ b'

/-- **Factorization through the power map (algebra).**  If `d ∣ a` and `d ∣ b`, the deployment
pencil `z^a + α z^b` equals `expand_d` of the base pencil `u^{a/d} + α u^{b/d}`.  This is the
trivial polynomial identity `expand_d(p)(z) = p(z^d)`, but it is the algebraic heart of the
substitution: the pencil depends only on `z^d`. -/
theorem pencil_eq_expand (a b d : ℕ) (hd : 0 < d) (ha : d ∣ a) (hb : d ∣ b) (α : F) :
    pencil a b α = (Polynomial.expand F d) (basePencil (a / d) (b / d) α) := by
  unfold pencil basePencil
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  rw [Nat.mul_div_cancel_left _ hd, Nat.mul_div_cancel_left _ hd]
  rw [map_add, map_mul, Polynomial.expand_C, map_pow, map_pow, Polynomial.expand_X]
  rw [← pow_mul, ← pow_mul]

/-! ## 2. Agreement descent: deployment agreement `= d ·` base agreement -/

open Round16SelfSimilar in
/-- **Agreement descent for the arising pencil.**  Over the smooth domain `μ_{s·d}` with primitive
root `ζ`, the deployment pencil `z^a + α z^b` (with `d ∣ a`, `d ∣ b`, `s·d = n`) matched against
the lifted base word `w ∘ π` agrees on exactly `d ·` (base agreement of the *base pencil* against
`w` over `μ_s`).  Pure composition of `pencil_eq_expand` with the proven self-similarity theorem
`agreement_expand`; no new analysis. -/
theorem agreement_deploy_eq_d_mul_base
    {ζ : F} {s d : ℕ} (hs : 0 < s) (hd : 0 < d) (hζ : ζ ^ (s * d) = 1)
    {a b : ℕ} (ha : d ∣ a) (hb : d ∣ b) (α : F) (w : Fin s → F) :
    agreement (domN ζ s d) (pencil a b α) (w ∘ proj s d hs)
      = d * agreement (domS ζ d s) (basePencil (a / d) (b / d) α) w := by
  rw [pencil_eq_expand a b d hd ha hb α]
  exact agreement_expand hs hζ (basePencil (a / d) (b / d) α) w

/-! ## 3. Orbit-size invariance under the substitution -/

/-- The order of the orbit group `⟨μ_n^{b−a}⟩` that the action-orbit theorem quotients by:
`orbitSize n a b = n / gcd(b−a, n)`.  Soundness is governed by the number of these orbits, hence
by their size relative to `n`. -/
def orbitSize (n a b : ℕ) : ℕ := n / Nat.gcd (b - a) n

/-- **gcd descent (arithmetic core).**  For `d ∣ m` and `d ∣ n`, `gcd(m, n) = d · gcd(m/d, n/d)`. -/
theorem gcd_eq_d_mul_gcd_div {m n d : ℕ} (hd : 0 < d) (hm : d ∣ m) (hn : d ∣ n) :
    Nat.gcd m n = d * Nat.gcd (m / d) (n / d) := by
  obtain ⟨m', rfl⟩ := hm
  obtain ⟨n', rfl⟩ := hn
  rw [Nat.gcd_mul_left, Nat.mul_div_cancel_left _ hd, Nat.mul_div_cancel_left _ hd]

/-- **Orbit-size invariance.**  When `d = gcd(a, b, n) > 1` (so `d ∣ a`, `d ∣ b`, `d ∣ n`, hence
`d ∣ b − a`), the action-orbit group size is *exactly preserved* under the `z ↦ z^d` substitution:

  `orbitSize n a b = orbitSize (n/d) (a/d) (b/d)`.

The deployment pencil therefore introduces **no new orbit structure** beyond its primitive base —
the number of bad-challenge orbits (which the action-orbit theorem bounds, and which governs MCA
soundness) is identical at deployment and base scale.  This is the precise statement that makes the
bad-prime gate on the small base panel control the entire arising family. -/
theorem orbitSize_descent {n a b d : ℕ} (hd : 0 < d) (hab : a ≤ b)
    (ha : d ∣ a) (hb : d ∣ b) (hn : d ∣ n) :
    orbitSize n a b = orbitSize (n / d) (a / d) (b / d) := by
  unfold orbitSize
  -- d ∣ (b - a) since d ∣ a and d ∣ b
  have hba : d ∣ (b - a) := Nat.dvd_sub hb ha
  -- (b - a) / d = b/d - a/d
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have hsub : (d * b' - d * a') / d = (d * b') / d - (d * a') / d := by
    rw [← Nat.mul_sub, Nat.mul_div_cancel_left _ hd, Nat.mul_div_cancel_left _ hd,
      Nat.mul_div_cancel_left _ hd]
  rw [gcd_eq_d_mul_gcd_div hd hba hn, hsub]
  -- n / (d * g) = (n/d) / g
  rw [Nat.div_div_eq_div_mul]

/-! ## 4. The three arising rate-1/2 families (Chai–Fan §4)

We take `k = n/4` (rate 1/2) and exhibit the common factor `d` for each family, verifying it is a
power of 2 (a divisor of `n = 2^e`) and `> 1` for `e ≥ 2`, so the family collapses onto a bounded
base panel and the orbit count is preserved. -/

section Families

variable (e : ℕ)

/-- **Sign-paired family (Thm 4.4).**  Exponents `(k, 3k)`; common factor `d = k`.  Reduces to the
base pencil `(1, 3)` on `μ_4` (`n / k = 4`).  Orbit size preserved.  Needs `e ≥ 3` so that
`k = 2^{e-2} > 1` (at `e = 2`, `n = 4` and `k = 1`: the pencil is already primitive). -/
theorem signPaired_descends (he : 3 ≤ e) :
    let n := 2 ^ e; let k := 2 ^ (e - 2)
    k ∣ n ∧ 1 < k ∧
    pencil k (3 * k) (1 : F) = (Polynomial.expand F k) (basePencil 1 3 (1 : F)) ∧
    orbitSize n k (3 * k) = orbitSize (n / k) 1 3 := by
  intro n k
  have hkn : k ∣ n := pow_dvd_pow 2 (by omega)
  have hk1 : 1 < k := Nat.one_lt_two_pow (by omega)
  have hkpos : 0 < k := by omega
  have hkk : k / k = 1 := Nat.div_self hkpos
  have h3k : 3 * k / k = 3 := Nat.mul_div_left 3 hkpos
  refine ⟨hkn, hk1, ?_, ?_⟩
  · -- z^k + z^{3k} = expand_k (u + u^3)
    have h := pencil_eq_expand (F := F) k (3 * k) k hkpos (dvd_refl k) (Nat.dvd_mul_left k 3) (1 : F)
    rwa [hkk, h3k] at h
  · -- orbit-size preservation: a = k, b = 3k, d = k; a/k = 1, b/k = 3
    have h := orbitSize_descent (n := n) (a := k) (b := 3 * k) (d := k) hkpos
      (by omega) (dvd_refl k) (Nat.dvd_mul_left k 3) hkn
    rwa [hkk, h3k] at h

/-- **`(k, 2k)` family (Thm 4.7).**  Exponents `(k, 2k)`; common factor `d = k`.  Reduces to the
base pencil `(1, 2)` on `μ_4` (`n / k = 4`).  Orbit size preserved.  Needs `e ≥ 3`. -/
theorem kTwoK_descends (he : 3 ≤ e) :
    let n := 2 ^ e; let k := 2 ^ (e - 2)
    k ∣ n ∧ 1 < k ∧
    pencil k (2 * k) (1 : F) = (Polynomial.expand F k) (basePencil 1 2 (1 : F)) ∧
    orbitSize n k (2 * k) = orbitSize (n / k) 1 2 := by
  intro n k
  have hkn : k ∣ n := pow_dvd_pow 2 (by omega)
  have hk1 : 1 < k := Nat.one_lt_two_pow (by omega)
  have hkpos : 0 < k := by omega
  have hkk : k / k = 1 := Nat.div_self hkpos
  have h2k : 2 * k / k = 2 := Nat.mul_div_left 2 hkpos
  refine ⟨hkn, hk1, ?_, ?_⟩
  · have h := pencil_eq_expand (F := F) k (2 * k) k hkpos (dvd_refl k) (Nat.dvd_mul_left k 2) (1 : F)
    rwa [hkk, h2k] at h
  · have h := orbitSize_descent (n := n) (a := k) (b := 2 * k) (d := k) hkpos
      (by omega) (dvd_refl k) (Nat.dvd_mul_left k 2) hkn
    rwa [hkk, h2k] at h

/-- **`(3k/2, 2k)` family (Thm 4.10).**  Exponents `(3k/2, 2k)` with `k = 2^{e-2}` even (`e ≥ 3`);
common factor `d = k/2 = 2^{e-3}`.  Reduces to the base pencil `(3, 4)` on `μ_8` (`n / d = 8`).
Orbit size preserved.  Here `3k/2 = 3·2^{e-3}` and `2k = 2^{e-1} = 4·2^{e-3}`. -/
theorem threeKTwoK_descends (he : 4 ≤ e) :
    let n := 2 ^ e; let d := 2 ^ (e - 3)
    let a := 3 * d; let b := 4 * d
    d ∣ n ∧ 1 < d ∧
    pencil a b (1 : F) = (Polynomial.expand F d) (basePencil 3 4 (1 : F)) ∧
    orbitSize n a b = orbitSize (n / d) 3 4 := by
  intro n d a b
  have hdn : d ∣ n := pow_dvd_pow 2 (by omega)
  have hd1 : 1 < d := Nat.one_lt_two_pow (by omega)
  have hdpos : 0 < d := by omega
  have hda : d ∣ a := Nat.dvd_mul_left d 3
  have hdb : d ∣ b := Nat.dvd_mul_left d 4
  have e3 : a / d = 3 := Nat.mul_div_left 3 hdpos
  have e4 : b / d = 4 := Nat.mul_div_left 4 hdpos
  refine ⟨hdn, hd1, ?_, ?_⟩
  · have h := pencil_eq_expand (F := F) a b d hdpos hda hdb (1 : F)
    rwa [e3, e4] at h
  · have h := orbitSize_descent (n := n) (a := a) (b := b) (d := d) hdpos
      (by show 3 * d ≤ 4 * d; omega) hda hdb hdn
    rwa [e3, e4] at h

end Families

end ProximityGap.Frontier.Q1ArisingFamilyDescent

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.Q1ArisingFamilyDescent.pencil_eq_expand
#print axioms ProximityGap.Frontier.Q1ArisingFamilyDescent.agreement_deploy_eq_d_mul_base
#print axioms ProximityGap.Frontier.Q1ArisingFamilyDescent.gcd_eq_d_mul_gcd_div
#print axioms ProximityGap.Frontier.Q1ArisingFamilyDescent.orbitSize_descent
#print axioms ProximityGap.Frontier.Q1ArisingFamilyDescent.signPaired_descends
#print axioms ProximityGap.Frontier.Q1ArisingFamilyDescent.kTwoK_descends
#print axioms ProximityGap.Frontier.Q1ArisingFamilyDescent.threeKTwoK_descends
