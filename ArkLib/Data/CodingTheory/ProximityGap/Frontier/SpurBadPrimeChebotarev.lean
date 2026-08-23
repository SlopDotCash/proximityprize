/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungUnconditionalGeneral
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# The `p ≡ 3 mod 4` Chebotarev exclusion for the char-`p` spurious-collision prime set (Issue #444)

The latest characterization of the prize's open core (commit `40df3426d`, KB doc
`direct-supnorm-data-beta4-2026-06-15.md`) pins the obstruction to an **arithmetic** (p-divisibility),
not metric (size), statement. The char-`p` energy splits as `E_r = E_r^{(0)} + Spur_r(p)`, with the
spurious excess

    `Spur_r(p) = #{ antipodal-free T, |T| ≤ 2r : p ∣ N(σ_T) }`,   `σ_T = Σ_{i∈T} ±ζ_{2^m}^i`,

the count of short antipodal-free relations whose cyclotomic norm is divisible by the prize prime `p`.
A relation `σ_T` is a *genuine in-field* spurious collision at `p` exactly when it vanishes in some
residue field `F_{p^f}` (`f = ord_{2^m}(p)`); the simplest such collisions live already in `F_p`
itself, when `μ_{2^m}` embeds in `ZMod p` (`p ≡ 1 mod 2^m`).

This file proves the **arithmetic substrate** that constrains the bad-prime set away from a full
Chebotarev class: it is the wf-C1 effective-Chebotarev lane's foundational density input.

## The exclusion

`μ_{2^m}` embeds in `ZMod p` (a primitive `2^m`-th root of unity exists) **only** when `2^m ∣ p − 1`.
For `m ≥ 2`, such a `p` carries `i := g^{2^{m−2}}` with `i² = g^{2^{m−1}} = −1` (Lam–Leung
`pow_half_eq_neg_one`), so `−1` is a square mod `p`. By Fermat / `ZMod.exists_sq_eq_neg_one_iff`,
`−1` is a square mod `p` **iff** `p ≢ 3 mod 4`. Hence:

> **`spur_field_excludes_three_mod_four`** — for `m ≥ 2`, a prime `p ≡ 3 mod 4` admits **no** primitive
> `2^m`-th root of unity in `ZMod p`. Equivalently, every prime carrying `μ_{2^m}` in `ZMod p` (in
> particular every prize prime `p ≡ 1 mod 2^m`) satisfies `p ≡ 1 mod 4`.

So the entire `p ≡ 3 mod 4` Chebotarev class is **absent** from the in-field bad-prime set: at those
primes `μ_{2^m}` does not even embed, so there are no antipodal-free relations to vanish, hence the
in-field spurious count is `0`. This is a **density-`1/2` exclusion** on the bad-prime set, exactly the
arithmetic input the effective-Chebotarev count (wf-C1) needs (the bad primes are confined to the
`p ≡ 1 mod 4` half, then further to the `p ≡ 1 mod 2^m` splitting class for genuine embedding).

**Sharper `mod 8` cut (`m ≥ 3`).** `ℚ(ζ_{2^m}) ⊇ ℚ(ζ_8) = ℚ(i, √2)`, so embedding `μ_{2^m}` (`m ≥ 3`)
also forces `√2` into the residue field: `s := ζ_8 + ζ_8⁻¹` has `s² = 2`. By
`ZMod.exists_sq_eq_two_iff`, `2` a square ⇔ `p ≡ ±1 mod 8`; with `p ≡ 1 mod 4` this forces `p ≡ 1
mod 8`. So the bad-prime support is confined to the density-`1/4` class `1 mod 8`
(`prize_prime_one_mod_eight`) — a strict sharpening of the `mod 4` exclusion.

## Probe corroboration

`probe_pdiv_chebotarev.py` (exact, sympy, proper `μ_n`, `n = 2^m`, `m = 2..5`):
- **No prime `p ≡ 3 mod 4` admits a primitive `2^m`-th root** (`m ≥ 2`) — the embedding class is empty.
- The complementary norm-level fact (`probe_pdiv_s2s_law.py`): every relation norm `N(σ_T)` from
  `ℚ(ζ_{2^m})` (`m ≥ 2`) is a **sum of two squares** (verified `m = 3,4,5`, all weight-4 antipodal-free
  norms; random higher weights `0/300` violations), because `ℚ(ζ_{2^m}) ⊇ ℚ(i)` so the field norm
  factors through `N_{ℚ(i)/ℚ}(a + bi) = a² + b²`. Consequently a prime `p ≡ 3 mod 4` divides `N(σ_T)`
  only to an **even** power — it can never supply an *odd-multiplicity* (genuine) spurious collision.
  (The in-field statement above is the clean Lean-formalizable core; the even-valuation norm fact is its
  global counterpart and is recorded as the probe finding.)

## Honest scope (rules 1, 3, 6)

NOT a CORE closure and NOT a new analytic input — it is an exact arithmetic constraint (a Chebotarev
exclusion from an elementary `i² = −1` witness) on the *support* of the spurious-collision count. It does
NOT bound `Spur_r(p)` inside the surviving `p ≡ 1 mod 4` class — at the prize primes (`p ≡ 1 mod 2^m`,
all `≡ 1 mod 4`) the spurious count is exactly where the open BCHKS-1.12 wall lives. It supplies the
density-`1/2` half-class exclusion that the wf-C1 effective-Chebotarev count builds on. CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays **OPEN**.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
- KB `direct-supnorm-data-beta4-2026-06-15.md`; `ShortRelationNormBase.lean` (weight-2 base rung);
  `HaloFreeDivisibility.lean` (divisibility-form census transfer).
- `LamLeungUnconditionalGeneral.lean` (`R12.pow_half_eq_neg_one`); Mathlib
  `ZMod.exists_sq_eq_neg_one_iff` (Fermat's Christmas theorem, `−1` a square iff `p ≢ 3 mod 4`).
-/

set_option linter.style.longLine false
set_option autoImplicit false

namespace ArkLib.ProximityGap.SpurBadPrimeChebotarev

open ArkLib.ProximityGap

variable {p : ℕ}

/-- **`−1` is a square mod `p` whenever a primitive `2^m`-th root exists (`m ≥ 2`).**
If `g : ZMod p` is a primitive `2^m`-th root of unity with `m ≥ 2`, then `i := g^{2^{m−2}}` satisfies
`i² = g^{2^{m−1}} = −1` (Lam–Leung `pow_half_eq_neg_one`), so `−1` is a square in `ZMod p`. -/
theorem isSquare_neg_one_of_primitiveRoot_two_pow [Fact p.Prime] {m : ℕ} (hm : 2 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) :
    IsSquare (-1 : ZMod p) := by
  -- i := g ^ (2 ^ (m - 2)); then i ^ 2 = g ^ (2 ^ (m - 2) + 2 ^ (m - 2)) = g ^ (2 ^ (m - 1)) = -1.
  refine ⟨g ^ (2 ^ (m - 2)), ?_⟩
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm
  have hhalf : g ^ (2 ^ (m - 1)) = -1 := R12.pow_half_eq_neg_one hm1 hg
  have hexp : 2 ^ (m - 2) + 2 ^ (m - 2) = 2 ^ (m - 1) := by
    have : 2 ^ (m - 1) = 2 ^ ((m - 2) + 1) := by congr 1; omega
    rw [this, pow_succ]
    ring
  calc (-1 : ZMod p) = g ^ (2 ^ (m - 1)) := hhalf.symm
    _ = g ^ (2 ^ (m - 2) + 2 ^ (m - 2)) := by rw [hexp]
    _ = g ^ (2 ^ (m - 2)) * g ^ (2 ^ (m - 2)) := by rw [pow_add]

/-- **THE CHEBOTAREV EXCLUSION: no `p ≡ 3 mod 4` prime carries `μ_{2^m}` in `ZMod p` (`m ≥ 2`).**
If `p` is a prime with `p % 4 = 3`, then `ZMod p` contains **no** primitive `2^m`-th root of unity for
`m ≥ 2`. Mechanism: such a root would give `i² = −1` (above), but `−1` is not a square mod a
`3 mod 4` prime (`ZMod.exists_sq_eq_neg_one_iff`). Hence the entire `p ≡ 3 mod 4` class is absent from
the in-field spurious-collision support: `μ_{2^m}` does not embed, so there are no antipodal-free
relations to vanish in `F_p` — the in-field `Spur` contribution is `0`. -/
theorem spur_field_excludes_three_mod_four [Fact p.Prime] {m : ℕ} (hm : 2 ≤ m)
    (h3 : p % 4 = 3) :
    ¬ ∃ g : ZMod p, IsPrimitiveRoot g (2 ^ m) := by
  rintro ⟨g, hg⟩
  have hsq : IsSquare (-1 : ZMod p) := isSquare_neg_one_of_primitiveRoot_two_pow hm hg
  -- but `-1` is a square mod p  ⟺  p % 4 ≠ 3, contradicting h3.
  have hne3 : p % 4 ≠ 3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp hsq
  exact hne3 h3

/-- **Contrapositive (the prize-prime form): carrying `μ_{2^m}` (`m ≥ 2`) forces `p ≡ 1 mod 4`.**
Every prime `p` admitting a primitive `2^m`-th root of unity in `ZMod p` (`m ≥ 2`) — in particular
every prize prime `p ≡ 1 mod 2^m` — satisfies `p % 4 = 1` (an odd prime is `1` or `3` mod `4`, and the
`3` case is excluded). This is the surviving half-class that the wf-C1 effective-Chebotarev count
ranges over. -/
theorem prize_prime_one_mod_four [Fact p.Prime] {m : ℕ} (hm : 2 ≤ m)
    (hg : ∃ g : ZMod p, IsPrimitiveRoot g (2 ^ m)) (hodd : p ≠ 2) :
    p % 4 = 1 := by
  have hp : p.Prime := (Fact.out : p.Prime)
  -- p is odd (p ≠ 2 and prime), so p % 2 = 1, hence p % 4 ∈ {1, 3}.
  have hodd' : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd2
    · exact absurd h2 hodd
    · exact hodd2
  -- p % 4 is 1 or 3 (since p is odd); rule out 3.
  have hne3 : p % 4 ≠ 3 := fun h3 => spur_field_excludes_three_mod_four hm h3 hg
  -- p % 4 ∈ {0,1,2,3}; oddness (p % 2 = 1 ⇒ p % 4 % 2 = 1) kills 0,2; hne3 kills 3.
  omega

/-! ### The sharper `mod 8` cut (`m ≥ 3`): `√2` lives in the field, forcing `2` a square -/

/-- **`2` is a square mod `p` whenever a primitive `2^m`-th root exists (`m ≥ 3`).**
If `g : ZMod p` is a primitive `2^m`-th root of unity with `m ≥ 3`, then `z := g^{2^{m−3}}` is a
primitive `8`-th root of unity, and `s := z + z⁻¹ = z + z^7` satisfies `s² = 2`: expanding,
`s² = z² + 2 + z⁻² = (z² + z⁶) + 2`, and `z²` is a primitive `4`-th root with `z⁶ = (z²)³ = −z²`
(since `(z²)² = z⁴ = −1`), so `z² + z⁶ = 0` and `s² = 2`. Hence `2` is a square in `ZMod p`. This is
the `ℚ(√2) ⊆ ℚ(ζ_8) ⊆ ℚ(ζ_{2^m})` constraint at the residue-field level. -/
theorem isSquare_two_of_primitiveRoot_two_pow [Fact p.Prime] {m : ℕ} (hm : 3 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) :
    IsSquare (2 : ZMod p) := by
  -- z := g ^ (2 ^ (m - 3)) is a primitive 8-th root of unity.
  set z : ZMod p := g ^ (2 ^ (m - 3)) with hz
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm
  -- z ^ 4 = g ^ (2^(m-3) * 4) = g ^ (2^(m-1)) = -1.
  have hz4 : z ^ 4 = -1 := by
    have hhalf : g ^ (2 ^ (m - 1)) = -1 := R12.pow_half_eq_neg_one hm1 hg
    have hexp : 2 ^ (m - 3) * 4 = 2 ^ (m - 1) := by
      have h2 : (2 : ℕ) ^ (m - 3) * 4 = 2 ^ ((m - 3) + 2) := by
        rw [pow_add]; norm_num
      have h3 : (m - 3) + 2 = m - 1 := by omega
      rw [h2, h3]
    rw [hz, ← pow_mul, hexp, hhalf]
  -- z ^ 8 = 1.
  have hz8 : z ^ 8 = 1 := by
    have : z ^ 8 = (z ^ 4) ^ 2 := by ring
    rw [this, hz4]; ring
  -- z⁻¹ = z ^ 7  (since z ^ 8 = 1, z is a unit). Use s = z + z^7.
  refine ⟨z + z ^ 7, ?_⟩
  -- Write everything in terms of z^4 and z^2 so that hz4 (z^4 = -1) collapses it to 2.
  -- (z+z^7)^2 = z^2 + 2 z^8 + z^14, with z^7 = z^4 z^2 z, z^8 = z^4 z^4, z^14 = z^4 z^4 z^4 z^2.
  have e7 : z ^ 7 = (z ^ 4) * (z ^ 2) * z := by ring
  have e2sum : (z + z ^ 7) * (z + z ^ 7)
      = z ^ 2
        + 2 * ((z ^ 4) * (z ^ 4))
        + ((z ^ 4) * (z ^ 4) * (z ^ 4) * (z ^ 2)) := by
    rw [e7]; ring
  rw [e2sum, hz4]
  ring

/-- **THE SHARP CHEBOTAREV CUT (`m ≥ 3`): only `p ≡ 1 mod 8` primes carry `μ_{2^m}`.**
For `m ≥ 3`, a prime `p` admitting a primitive `2^m`-th root of unity in `ZMod p` (in particular every
prize prime `p ≡ 1 mod 2^m`) satisfies `p % 8 = 1`. Mechanism: such a root forces both `−1` a square
(`p ≡ 1 mod 4`, `m ≥ 2`) AND `2` a square (`p ≡ ±1 mod 8` by `exists_sq_eq_two_iff`, the `√2 ∈ ℚ(ζ_8)`
witness above); together `p ≡ 1 mod 8`. So the bad-prime support is confined to the density-`1/4`
residue class `1 mod 8` — a sharpening of the `mod 4` exclusion that the wf-C1 effective-Chebotarev
count builds on. -/
theorem prize_prime_one_mod_eight [Fact p.Prime] {m : ℕ} (hm : 3 ≤ m)
    (hg : ∃ g : ZMod p, IsPrimitiveRoot g (2 ^ m)) (hodd : p ≠ 2) :
    p % 8 = 1 := by
  obtain ⟨g, hgr⟩ := hg
  have hp : p.Prime := (Fact.out : p.Prime)
  -- p ≡ 1 mod 4 from the mod-4 result (m ≥ 2).
  have h4 : p % 4 = 1 := prize_prime_one_mod_four (le_trans (by norm_num) hm) ⟨g, hgr⟩ hodd
  -- 2 is a square ⇒ p % 8 ∈ {1, 7}.
  have hsq2 : IsSquare (2 : ZMod p) := isSquare_two_of_primitiveRoot_two_pow hm hgr
  have h8 : p % 8 = 1 ∨ p % 8 = 7 := (ZMod.exists_sq_eq_two_iff (p := p) hodd).mp hsq2
  -- p % 4 = 1 forces p % 8 ∈ {1, 5}; intersect with {1, 7} ⇒ p % 8 = 1.
  omega

end ArkLib.ProximityGap.SpurBadPrimeChebotarev

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpurBadPrimeChebotarev.isSquare_neg_one_of_primitiveRoot_two_pow
#print axioms ArkLib.ProximityGap.SpurBadPrimeChebotarev.spur_field_excludes_three_mod_four
#print axioms ArkLib.ProximityGap.SpurBadPrimeChebotarev.prize_prime_one_mod_four
#print axioms ArkLib.ProximityGap.SpurBadPrimeChebotarev.isSquare_two_of_primitiveRoot_two_pow
#print axioms ArkLib.ProximityGap.SpurBadPrimeChebotarev.prize_prime_one_mod_eight
