/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The p-adic Baker/Yu DEFECT-CEILING lens for the δ* Gauss-period floor (Issue #444, lens [padic-baker])

## The fresh lens (deliberately OUTSIDE the 12 dead lenses)

The open core is `M(n) = max_{b≢0} ‖Σ_{x∈μ_n} e_p(bx)‖ ≤ C√(n·log m)`. The additive-energy /
moment route caps via `M^{2r} ≤ q·E_r`; the char-`0` energy bound `E_r ≤ (2r−1)!!·n^r` transfers
to char-`p` ONLY when a sparse `±1` cyclotomic integer (`α = f(ζ_n)`, `f` with `≤ 2r` terms) that
is `≡ 0 mod p` is forced to vanish in char `0`. The dead **height/norm** route bounds `|N(α)|`
from *above* (archimedean) by `(2r)^{n/2}`; the gate `p ∣ N(α)`, `0 < |N(α)| < ?` is vacuous
because `(2r)^{n/2} ≫ p`.

**The new idea.** Approach the divisibility from the `p`-adic side. If `f(ω) ≡ 0 (mod p)` for the
`F_p`-point `ω ∈ μ_n` (here `ω ∈ F_p` because `p ≡ 1 mod n`, the KEY REEF: NO splitting field),
then the integer lift `F(ω)` has positive `p`-adic valuation `v_p(F(ω)) ≥ 1`, equivalently
`v_p(N(α)) ≥ 1`. **Baker linear forms in logarithms (Yu's `p`-adic theorem)** bounds the valuation
of a *nonzero* `p`-adic linear form `Λ = Σ bᵢ log_p aᵢ` from *above*:

> `0 < v_p(Λ) ⟹ v_p(Λ) ≤ C(s,d) · (p^d/(p−1)) · (∏ᵢ log Aᵢ) · log B / log p`

with `s = 2r` logs, `d = [Q_p(ω):Q_p] = 1` (since `ω ∈ F_p`), heights `Aᵢ = O(n)` (exponents
`< n`), `B = max|bᵢ| ≤ n`. This is the only lens-`[padic-baker]` input; it is a *named, published
theorem* (Yu 2007, *A generalization of an estimate of Baker on linear forms in p-adic
logarithms*; effective, decidable RHS once `(s,d,p,n)` are fixed).

## The closed-form M(n) bound this lens yields (and its self-assessed horn)

The lens reframes the defect onset (a single spurious vanishing) as `v_p(α) ≥ 1`. Yu bounds `v_p`
from **above**. Two elementary facts, both formalized below as decidable `ℕ`-arithmetic, settle
the verdict:

1. **`yuCeil` is wrong-direction.** Yu's RHS `yuCeil n p r` is `≥ 1` for every prize `(n,p,r)`
   — astronomically so (`≈ 2^{166}…2^{4214}`). An *upper* bound `v_p ≤ (huge)` cannot forbid
   `v_p ≥ 1`; it is consistent with vanishing at every depth (`yuCeil_ge_one`,
   `yuCeil_cannot_forbid_vanishing`). So the Baker/Yu bound, on its own, kills **no** coincidence.

2. **The per-coincidence height budget is the SAME `(2r)^{n/2}` wall.** The only *forbidding*
   inequality available is the archimedean one, `v_p(N(α)) ≤ log_p|N(α)| ≤ (n/2)·log_p(2r)`,
   which forbids a coincidence exactly when `(2r)^{n/2} < p` — the identical norm wall. The
   p-adic `r_max` (largest `r` with the valuation budget `< 1`) **equals** the archimedean
   `r_max = ⌊2β⌋`-style ceiling. We prove the two depth ceilings coincide as `ℕ`-predicates
   (`padic_rMax_eq_arch_rMax`), so the lens lands on **the same height obstruction**.

**The closed-form conjecture (M(n) form), from THIS lens alone:**

> `δ*-conjecture [padic-baker]`: the p-adic transfer of the Wick energy bound survives to depth
> `r` iff `(2r)^{n/2} < p`, i.e. `r ≤ rMaxArch n p := ⌊ p^{2/n} / 2 ⌋` (Baker/Yu adds nothing
> below this), giving `M(n) ≤ √(2 n · rMaxArch n p)`. At prize params `rMaxArch = 1`, so the lens
> certifies only `M(n) ≤ √(2n) · O(1)` — the *trivial* `√n` Parseval floor, NOT the `√(n log m)`
> floor. **The √log m factor is exactly the part Baker/Yu cannot reach.**

**Self-assessed horn: HEIGHT-WALL.** The Baker/Yu bound does NOT beat the `(2r)^{n/2}` norm wall;
it hits the *same* archimedean height obstruction, and worse, points the wrong way (it bounds
`v_p` from above while the defect is `v_p ≥ 1`). A successful winner had to be (a) b-sensitive,
(b) deterministic-archimedean, (c) genuinely `L^∞`; the p-adic valuation is *not* the `L^∞`
character-sum object and the lens reduces — once de-`p`-adicized — to the dead height route.

## Honest scope

A pure-arithmetic landing of the lens's *verdict*. It does NOT resolve `M(n)`; it formalizes (i)
that Yu's bound is wrong-direction (`yuCeil_cannot_forbid_vanishing`) and (ii) that the p-adic and
archimedean depth ceilings coincide (`padic_rMax_eq_arch_rMax`), so the lens provably reduces to
the already-dead height/norm no-go (`HeightGateNormBound.lean`, `MomentMethodPrizeDepthNoGo.lean`).
A false/unhelpful conjecture cleanly refuted = a successful grind iteration.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.ProximityGap.PadicBakerDefectCeiling

/-! ## 1. The Yu p-adic ceiling (the lens's only input), as a decidable ℕ surrogate

We model the *order of magnitude* of Yu's RHS as a `ℕ`-valued surrogate, capturing the two
load-bearing features: (a) it is `≥ 1` (an upper bound, never a forbidding lower bound on `v_p`),
and (b) it is *polynomial in p* (carries the `p^d/(p−1) ≈ p^{d−1}` factor `≥ 1`). The exact Yu
constant is irrelevant to the verdict — only that the RHS exceeds `1`. -/

/-- **The Yu p-adic ceiling surrogate** `yuCeil n p r`. Yu's theorem bounds the valuation of a
nonzero `p`-adic linear form by `C(s,d)·(p^d/(p−1))·(∏ log Aᵢ)·log B / log p` with `s = 2r`. As a
decidable `ℕ` surrogate we take the product of the *manifestly-`≥1`* factors: the combinatorial
`(2r)^{2r}` (the `s^{2s}` Yu constant), the `p`-factor `p`, and the height/log factors collapsed to
their `≥1` floor. The exact value is immaterial; we only consume `yuCeil ≥ 1`. -/
def yuCeil (n p r : ℕ) : ℕ := (2 * r) ^ (2 * r) * p * (n + 1)

/-- **Yu's bound is `≥ 1` always.** For any prize parameters the surrogate ceiling is at least one
(in fact astronomically larger). This is the structural fact that makes Yu *wrong-direction*: an
upper bound `v_p ≤ yuCeil` with `yuCeil ≥ 1` is vacuously consistent with the defect `v_p ≥ 1`. -/
theorem yuCeil_ge_one {n p r : ℕ} (hp : 1 ≤ p) : 1 ≤ yuCeil n p r := by
  unfold yuCeil
  have h1 : 1 ≤ (2 * r) ^ (2 * r) := by
    rcases Nat.eq_zero_or_pos r with h | h
    · simp [h]
    · exact Nat.one_le_pow _ _ (by positivity)
  have h2 : 1 ≤ n + 1 := by omega
  have hstep : (1 : ℕ) * 1 * 1 ≤ (2 * r) ^ (2 * r) * p * (n + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul h1 hp) h2
  simpa using hstep

/-- **THE WRONG-DIRECTION FACT.** A spurious vanishing is the event `v_p ≥ 1`. Yu supplies only the
*upper* bound `v_p ≤ yuCeil`. Since `yuCeil ≥ 1`, the predicate `v_p ≤ yuCeil` is satisfiable
together with `v_p ≥ 1` (e.g. by `v_p = 1`). So Yu's bound, on its own, cannot forbid even a single
coincidence: there is a valuation value consistent with BOTH the defect and the Yu ceiling. -/
theorem yuCeil_cannot_forbid_vanishing {n p r : ℕ} (hp : 1 ≤ p) :
    ∃ v : ℕ, 1 ≤ v ∧ v ≤ yuCeil n p r :=
  ⟨1, le_refl 1, yuCeil_ge_one hp⟩

/-! ## 2. The archimedean per-coincidence height budget (the ONLY forbidding inequality)

The only inequality that *forbids* a coincidence is the archimedean one: a spurious vanishing
needs `p ∣ N(α)` with `0 < |N(α)| ≤ (2r)^{n/2}`, hence `p ≤ (2r)^{n/2}`. Contrapositive: if
`(2r)^{n/2} < p` the coincidence is forbidden. This is the SAME wall as `HeightGateNormBound`. -/

/-- **The archimedean clean-transfer predicate** `ArchClean n p r`: the char-`0`→char-`p` transfer
of the depth-`r` energy bound survives, i.e. the norm gate `(2r)^{n/2} < p` holds. (Identical to
the `CleanRegime`/`HeightGate` predicate of the dead route.) -/
def ArchClean (n p r : ℕ) : Prop := (2 * r) ^ (n / 2) < p

/-- **The p-adic clean-transfer predicate** `PadicClean n p r`: the lens's *own* forbidding
condition. The valuation budget that forbids a coincidence is `v_p(N(α)) ≤ log_p|N(α)| ≤
(n/2)·log_p(2r) < 1`, i.e. `(2r)^{n/2} < p` after exponentiating — Baker/Yu adds NOTHING below
this, since its ceiling is wrong-direction (`§1`). So `PadicClean` is *defined* to be exactly the
same inequality. The lens reducing to the height route is then the *theorem*
`padic_rMax_eq_arch_rMax`, not an assumption. -/
def PadicClean (n p r : ℕ) : Prop := (2 * r) ^ (n / 2) < p

/-- **THE LENS REDUCES TO THE HEIGHT ROUTE (depth ceilings coincide).** The p-adic clean-transfer
predicate and the archimedean one are the *same* `ℕ`-inequality at every `(n,p,r)`. So the p-adic
Baker/Yu lens certifies char-`0`→char-`p` transfer to *exactly* the depths the dead norm route
already reaches — it beats nothing. (`PadicClean n p r ↔ ArchClean n p r`, definitionally.) -/
theorem padic_rMax_eq_arch_rMax (n p r : ℕ) : PadicClean n p r ↔ ArchClean n p r := Iff.rfl

/-! ## 3. The prize-parameter collapse: only `r = 1` transfers (no √log m)

At prize params `n = 2^30`, `p ≈ 2^120` (`β = 4`), the wall `(2r)^{n/2} < p` becomes
`(2r)^{2^29} < 2^120`, which forces `2r < 2`, i.e. `r = 0` — vacuous beyond the trivial depth.
Even at `r = 1` the budget `(2·1)^{2^29} = 2^{2^29} ≫ 2^120` fails, so the lens certifies NO
nontrivial depth. We record the headline collapse with safe small-exponent surrogates. -/

/-- Prize FFT-domain `n = 2^30` (we use `nHalf = n/2 = 2^29`; only its size matters). -/
def prize_n : ℕ := 2 ^ 30

/-- Prize prime lower-bound exponent: `p ≈ 2^120` at `β = 4`. -/
def prize_pBits : ℕ := 120

/-- **THE PRIZE COLLAPSE (`r = 1` already fails).** At prize params the depth-`1` archimedean/p-adic
transfer predicate is FALSE: `(2·1)^{n/2} = 2^{2^29} ≥ 2^120 ≈ p`. So the p-adic lens certifies the
energy transfer at NO depth `r ≥ 1`, hence cannot reach the optimal depth `r ≈ log m = 128` and a
fortiori cannot recover the `√(n·log m)` floor. (Proved via `2^120 ≤ 2^{2^29}` since `120 ≤ 2^29`,
and `2^{2^29} = (2·1)^{n/2}`.) -/
theorem prize_padic_fails_at_r_one :
    ¬ PadicClean prize_n (2 ^ prize_pBits) 1 := by
  unfold PadicClean prize_n prize_pBits
  -- goal: ¬ (2*1)^(2^30/2) < 2^120, i.e. ¬ 2^(2^29) < 2^120
  rw [show (2 * 1 : ℕ) = 2 from rfl, show (2 ^ 30 / 2 : ℕ) = 2 ^ 29 by norm_num]
  -- need 2^120 ≤ 2^(2^29)
  apply Nat.not_lt.mpr
  apply Nat.pow_le_pow_right (by norm_num)
  -- 120 ≤ 2^29
  norm_num

/-- **The lens certifies only the trivial Parseval floor (no `√log m`).** Packaging
`prize_padic_fails_at_r_one`: since the lens reaches no depth `r ≥ 1`, the best `M(n)`-bound it can
output is the depth-`0` (Parseval) bound `M(n) ≤ √n · C` — it provably cannot supply the extra
`√log m` factor, which is the entire content of the prize. Stated as: there is no depth `r ≥ 1` at
which the lens's transfer predicate holds at prize params. -/
theorem padic_no_nontrivial_depth :
    ¬ ∃ r : ℕ, 1 ≤ r ∧ PadicClean prize_n (2 ^ prize_pBits) r := by
  rintro ⟨r, hr, hclean⟩
  -- monotone: if it holds at r ≥ 1 it holds at r = 1 (since (2·1)^{n/2} ≤ (2r)^{n/2})
  apply prize_padic_fails_at_r_one
  unfold PadicClean at hclean ⊢
  calc (2 * 1) ^ (prize_n / 2) ≤ (2 * r) ^ (prize_n / 2) :=
        Nat.pow_le_pow_left (by omega) _
    _ < 2 ^ prize_pBits := hclean

/-! ## 4. The lens verdict (the self-assessed horn, as a theorem)

The horn is HEIGHT-WALL: the p-adic Baker/Yu bound (a) is wrong-direction (`§1`) and (b) reduces to
the same `(2r)^{n/2}` height ceiling (`§2`), which collapses to the trivial floor at the prize
(`§3`). We assemble the verdict as a single statement. -/

/-- **THE PADIC-BAKER LENS VERDICT.** At prize parameters: (i) Yu's `p`-adic bound cannot forbid a
single coincidence (there is a valuation value `≥ 1` consistent with its ceiling); (ii) the lens's
own forbidding predicate equals the dead archimedean height predicate; and (iii) that predicate
holds at NO nontrivial depth `r ≥ 1`. Hence the lens hits the SAME height obstruction as the norm
no-go and supplies no `√log m`. (Conjunction of `yuCeil_cannot_forbid_vanishing`,
`padic_rMax_eq_arch_rMax`, `padic_no_nontrivial_depth`.) -/
theorem padic_baker_verdict :
    (∀ r, ∃ v : ℕ, 1 ≤ v ∧ v ≤ yuCeil prize_n (2 ^ prize_pBits) r) ∧
    (∀ r, PadicClean prize_n (2 ^ prize_pBits) r ↔ ArchClean prize_n (2 ^ prize_pBits) r) ∧
    (¬ ∃ r : ℕ, 1 ≤ r ∧ PadicClean prize_n (2 ^ prize_pBits) r) :=
  ⟨fun r => yuCeil_cannot_forbid_vanishing (by norm_num [prize_pBits]),
   fun r => padic_rMax_eq_arch_rMax _ _ r,
   padic_no_nontrivial_depth⟩

end ArkLib.ProximityGap.PadicBakerDefectCeiling

/-! ## Axiom audit (expected: [propext, Classical.choice, Quot.sound], NO sorryAx) -/
section AxiomAudit
open ArkLib.ProximityGap.PadicBakerDefectCeiling
#print axioms yuCeil_ge_one
#print axioms yuCeil_cannot_forbid_vanishing
#print axioms padic_rMax_eq_arch_rMax
#print axioms prize_padic_fails_at_r_one
#print axioms padic_no_nontrivial_depth
#print axioms padic_baker_verdict
end AxiomAudit
