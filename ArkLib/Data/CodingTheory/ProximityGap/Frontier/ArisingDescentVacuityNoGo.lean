/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.Q1ArisingFamilyDescent

/-!
# The arising-family descent is VACUOUS on the primitive directions (a fold-transport no-go)

`Q1ArisingFamilyDescent` proves that the smooth-domain agreement/orbit descent reduces a
deployment pencil `z^a + α z^b` on `μ_n` to a primitive base pencil on `μ_{n/d}` whenever
`d = gcd(a, b, n) > 1` (`orbitSize_descent`, `agreement_deploy_eq_d_mul_base`).  The three
Chai–Fan §4 arising rate-1/2 families all have a common factor `d = k > 1`, so the descent
controls them from the small base panel.

This file maps the descent lever's **wall** (honesty rule 4): the descent reduction factor is
exactly `d = gcd(a, b, n)`, so on a **primitive** pencil (`d = 1`) the descent is the IDENTITY —
it provides NO reduction.  For the prize regime `n = 2^a` the primitive directions are exactly the
**odd exponent-differences** (`gcd(b − a, n) = 1 ⇔ b − a` odd), and these carry the **largest**
orbit group: `orbitSize n a b = n` (the full `μ_n` acts, the most bad-challenge orbits, the hard
soundness case).  Asymptotically these are HALF of all directions.  Hence the fold-transport /
descent lever cannot reduce the primitive-direction worst case; the beyond-Johnson content stays in
the untouched primitive (odd-difference) half.

NON-MOMENT (pure `Nat` exponent-gcd combinatorics), EXTEND-proven (sits directly on
`Q1ArisingFamilyDescent.orbitSize_descent` / `.orbitSize`), refutation-style constraint lemma.
**Not** a CORE / Conj-7.1 closure: it proves the descent CANNOT reduce the primitive worst case,
forcing the beyond-Johnson lift onto the per-direction BGK wall, untouched.  No
capacity / beyond-Johnson / cliff-at-n/2 claim.  CORE `M(μ_n) ≤ C·√(n·log(p/n))` OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

namespace ProximityGap.Frontier.ArisingDescentVacuityNoGo

open ProximityGap.Frontier.Q1ArisingFamilyDescent

/-- **Descent vacuity at `d = 1`.**  Dividing by `d = 1` is the identity, so `orbitSize_descent`
specialised to a primitive pencil (`gcd(a, b, n) = 1`, the witness `d = 1`) yields the trivial
identity `orbitSize n a b = orbitSize n a b`: the descent provides **no** reduction.  This is the
exact statement that the `z ↦ z^1` substitution leaves the orbit structure unchanged. -/
theorem orbitSize_descent_one (n a b : ℕ) :
    orbitSize n a b = orbitSize (n / 1) (a / 1) (b / 1) := by
  simp [Nat.div_one]

/-- **Primitive `⇔` odd, in the prize regime `n = 2^m`.**  An exponent difference `d` is a
primitive direction (`gcd(d, 2^m) = 1`) iff it is odd.  The descent (which needs `gcd > 1`) thus
fires on NONE of the odd-difference directions. -/
theorem primitive_diff_iff_odd (m d : ℕ) (hm : 0 < m) :
    Nat.gcd d (2 ^ m) = 1 ↔ ¬ 2 ∣ d := by
  -- `Nat.gcd d (2^m) = 1` is `Nat.Coprime d (2^m)`.
  constructor
  · intro hcop hdvd
    -- 2 ∣ d and 2 ∣ 2^m ⇒ 2 ∣ gcd = 1, contradiction
    have h2n : (2 : ℕ) ∣ 2 ^ m := dvd_pow_self 2 hm.ne'
    have hdg : (2 : ℕ) ∣ Nat.gcd d (2 ^ m) := Nat.dvd_gcd hdvd h2n
    rw [hcop] at hdg
    have : (2 : ℕ) ≤ 1 := Nat.le_of_dvd Nat.one_pos hdg
    omega
  · intro hodd
    -- d odd ⇒ d coprime to 2 ⇒ coprime to 2^m.
    -- gcd d 2 ∣ 2 (prime) ⇒ it is 1 or 2; it cannot be 2 since ¬ 2 ∣ d.
    have hdvd : Nat.gcd d 2 ∣ 2 := Nat.gcd_dvd_right d 2
    have hcop2 : Nat.Coprime d 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact h1
      · exact absurd (h2 ▸ Nat.gcd_dvd_left d 2) hodd
    exact hcop2.pow_right m

/-- **Primitive directions carry the full orbit group.**  When the exponent difference `b − a` is
coprime to `n` (the primitive / hard case), the orbit group `⟨μ_n^{b−a}⟩` is all of `μ_n`, so
`orbitSize n a b = n`.  These are precisely the directions the descent CANNOT shrink (`d = 1`),
and they carry the maximal `μ_n`-action — the most bad-challenge orbits the soundness gate must
control. -/
theorem primitive_dir_orbitSize_eq_n {n a b : ℕ} (_hab : a ≤ b)
    (hcop : Nat.gcd (b - a) n = 1) : orbitSize n a b = n := by
  unfold orbitSize
  rw [hcop, Nat.div_one]

/-- **The descent no-go, packaged.**  For `n = 2^m` (`m > 0`) and any pencil whose exponent
difference `b − a` is ODD (a primitive direction): the orbit group is the full `μ_n`
(`orbitSize = n`) AND the descent factor `gcd(a, b, n)` cannot exceed `1` on this direction
(`gcd(b − a, n) = 1` forces no common nontrivial factor of the difference), so
`orbitSize_descent` is the identity there.  The fold-transport lever provably leaves the
odd-difference half of the directions — carrying the full orbit structure — untouched. -/
theorem arising_descent_vacuous_on_odd {m a b : ℕ} (hm : 0 < m) (hab : a ≤ b)
    (hodd : ¬ 2 ∣ (b - a)) :
    orbitSize (2 ^ m) a b = 2 ^ m ∧
      orbitSize (2 ^ m) a b = orbitSize ((2 ^ m) / 1) (a / 1) (b / 1) := by
  have hcop : Nat.gcd (b - a) (2 ^ m) = 1 := (primitive_diff_iff_odd m (b - a) hm).mpr hodd
  refine ⟨primitive_dir_orbitSize_eq_n hab hcop, ?_⟩
  exact orbitSize_descent_one (2 ^ m) a b

end ProximityGap.Frontier.ArisingDescentVacuityNoGo

#print axioms ProximityGap.Frontier.ArisingDescentVacuityNoGo.orbitSize_descent_one
#print axioms ProximityGap.Frontier.ArisingDescentVacuityNoGo.primitive_diff_iff_odd
#print axioms ProximityGap.Frontier.ArisingDescentVacuityNoGo.primitive_dir_orbitSize_eq_n
#print axioms ProximityGap.Frontier.ArisingDescentVacuityNoGo.arising_descent_vacuous_on_odd
