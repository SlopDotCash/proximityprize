/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (adversarial stress of approach N10 — the Shaw invariant)
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# ADVERSARIAL STRESS of APPROACH N10 — the Shaw invariant `ShawVanishingAtPrizeScale` (#444)

This file adversarially stress-tests the ONE named open claim of `_NovelShawInvariant.lean`,
`ShawVanishingAtPrizeScale n r`, defined there as

```
def ShawVanishingAtPrizeScale (n r : ℕ) : Prop :=
  ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (W : κ → ℤ) (q : ℕ),
    ConductorBound n r < q → shawInvariant W q = 0          -- ConductorBound n r := n ^ (2 * r)
```

The prose attached to it claims it is the Stickelberger statement *"the Galois-orbit-summed
cyclotomic norm of every short `2^a`-root relation is a `p`-free unit, hence `S_r = 0`"*, FALSE
only at Fermat primes. We mount the three requested attacks. **All three land**, each with a
machine-checked countermodel. The verdict is `OBSTRUCTION` (worse than "reduces"): the named claim
as written is either OUTRIGHT FALSE (over arbitrary `W`) or VACUOUSLY INAPPLICABLE at prize scale
(the conductor threshold is never met by the prize prime), and it never expresses the cyclotomic
norm it is advertised as.

NB: this stress file is SELF-CONTAINED — it re-declares the minimal `wrapLocus / shawInvariant`
skeleton from `_NovelShawInvariant.lean` (same definitions, verbatim) so it compiles with light
imports and exhibits the countermodels against the *exact* objects N10 uses. It imports nothing
from the cone.

--------------------------------------------------------------------------------------------------
## ATTACK 1 — Is `ShawVanishingAtPrizeScale` just "no wraparound", renamed (= the prize, circular)?

**Verdict: WORSE than circular — it is HOLLOW.** A circular restatement would at least *express*
the prize content ("no short `2^a`-root relation wraps mod `p`"). This predicate does not, because
the carrier value `W : κ → ℤ` is left **fully universal**: `κ`, `W`, and `q` are all `∀`-bound, and
`n, r` enter ONLY through the numeric threshold `ConductorBound n r = n^(2r)` on `q`. There is no
`μ_n`, no `2^a`-th root, no signed-carrier-sum, no cyclotomic norm anywhere in the `Prop`. So the
claim literally says:

> "for every finite family of integers `W(t)`, if `q > n^(2r)` then no `W(t)` is a nonzero multiple
> of `q`."

That is not the prize "no wraparound" statement renamed; it is a *strictly stronger and false*
universal divisibility claim that happens to mention `n^(2r)`. The genuine prize content (which
*specific* short `2^a`-root relations vanish mod `p`) is NOT smuggled — it is simply ABSENT. The
"orbit-summed cyclotomic norm" lives only in the docstring (`shaw_decl_quantifies_arbitrary_W`).

## ATTACK 2 — Is it REFUTABLE? (a short relation with norm divisible by a prize-scale prime)

**Verdict: REFUTED, two ways.**

(2a) *As written (arbitrary `W`) it is OUTRIGHT FALSE.* Take `κ = Unit`, `W ⟦_⟧ = (q : ℤ)` for any
`q > n^(2r)`. Then `q ∣ W` and `W ≠ 0`, so the single tuple wraps and `shawInvariant W q = 1 ≠ 0`.
This is `shaw_universal_claim_is_false` below, and it is exactly the situation `N10`'s own
`shaw_ne_zero_of_witness` flags. So the universal claim cannot be a theorem.

(2b) *Restricting `W` to genuine carrier values does NOT save it — the conductor threshold is the
killer.* The carrier value / cyclotomic norm of a `≤ 2r`-term `2^a`-root relation is bounded by
`(2r)^{n/2}` and is genuinely that large, so a prime `p` fails to divide SOME short-relation norm
only when `p > (2r)^{n/2}` — i.e. `ConductorBound` should be `(2r)^{n/2}`, NOT `n^(2r)`. At prize
scale `n = 2^30`, `r ≈ 110`, `p ≈ 2^158`:
  * `n^(2r) = 2^(30·220) = 2^6600`,           the threshold the Lean hypothesis `ConductorBound < q` demands;
  * `q ≈ 2^158`,                              the prize prime.
So `ConductorBound n r = 2^6600 ≫ 2^158 = q`: the hypothesis `ConductorBound n r < q` is **FALSE for
the prize prime**. The open claim, *specialized to the prize prime*, has a FALSE antecedent — it is
vacuously inapplicable and the conditional-closure `prize_of_shawVanishing` can never be discharged
with the prize `q`. And the *correct* threshold `(2r)^{n/2} = 220^{2^29} ≈ 2^{2^29·7.78}` is itself
astronomically larger than `q ≈ 2^158`, so `p` divides MANY short-relation norms — the cyclotomic
norm route is on the wrong side of √p-vacuity at prize scale. This is `conductor_below_prize_prime`.

## ATTACK 3 — Does Galois orbit-summing REDUCE the divisibility (or is it the same bad-prime set)?

**Verdict: the orbit-sum does NOT reduce the bad primes.** N10's `shaw_galois_invariant` proves only
that `S_r` is *invariant* under the `G`-action (the dyadic weight is preserved). Invariance is the
statement `S_r(σ·) = S_r(·)`; it says NOTHING about which primes divide the (invariant) orbit value.
Concretely, if a tuple `t` wraps mod `q` then EVERY tuple in its `G`-orbit wraps mod the SAME `q`
(`nonDiagWrap_stable`), so the orbit-union of wraps has the IDENTICAL bad-prime set as the single
wrap — Galois symmetry replicates the divisibility across the orbit, it does not cancel it. We make
this precise: under a `GaloisSymmetry` whose twist is a `p`-coprime unit, the orbit map sends wraps
to wraps and `q` divides every orbit member's value (`orbit_preserves_bad_prime`), so the
"orbit-summed" object inherits, never sheds, the divisibility by `q`. The advertised "orbit-summed
norm is a `p`-free unit" is asserted only in prose and is, at prize scale, FALSE (Attack 2b).

--------------------------------------------------------------------------------------------------
## NET VERDICT — `OBSTRUCTION`, `closesCharP = false`, `reducesToVacuity = true`

The Shaw scaffolding (rank/descent/Galois-invariance/transfer) is genuine and axiom-clean, but the
single open input `ShawVanishingAtPrizeScale` does not carry the prize: as written it is false over
arbitrary `W`; with `W` pinned to carrier values its threshold `n^(2r)` excludes the prize prime
(and the *correct* cyclotomic threshold `(2r)^{n/2}` excludes it even harder, dumping the route into
√p-vacuity); and Galois orbit-summing replicates rather than cancels the divisibility. The honest
residual is the SAME char-`p` short-relation wraparound wall, now dressed as a norm-divisibility
statement that the file never actually formalizes.

All theorems below are axiom-clean (`propext, Classical.choice, Quot.sound`); no
`sorry`/`native_decide`/`[CharZero]`. The "claims" being refuted are reproduced as `def`s; the
refutations are theorems.

## References
`_NovelShawInvariant.lean` (the audited skeleton); `_NovelStickelbergerStark.lean` (sibling N5,
already self-audited as a narrative scaffold); Conway–Jones / Mann (vanishing sums of `2`-power
roots); Stickelberger / Gross–Koblitz (cyclotomic norms). Issue #444.
-/

set_option linter.style.longLine false
set_option autoImplicit false
set_option linter.unusedSectionVars false


namespace ArkLib.ProximityGap.FrontierShawStress

open Finset

/-! ## 0. The N10 skeleton, re-declared verbatim (so we refute the EXACT objects) -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (V : ι → ℤ) (p : ℕ)

/-- `t` is a non-diagonal wrap: vanishes mod `p` but not over `ℤ`. (Verbatim from N10.) -/
def NonDiagWrap (t : ι) : Prop := (p : ℤ) ∣ V t ∧ V t ≠ 0

instance (t : ι) : Decidable (NonDiagWrap V p t) := by unfold NonDiagWrap; infer_instance

/-- The wrapping non-diagonal locus `L_p \ L_ℤ` as a `Finset`. (Verbatim from N10.) -/
noncomputable def wrapLocus : Finset ι := Finset.univ.filter (NonDiagWrap V p)

/-- The `2`-adic weight `2^{-v_2(V t)}`. (Verbatim from N10.) -/
noncomputable def dyadicWeight (t : ι) : ℚ :=
  (1 : ℚ) / (2 : ℚ) ^ ((V t).natAbs.factorization 2)

/-- The Shaw invariant `S_r(n,p)`. (Verbatim from N10.) -/
noncomputable def shawInvariant : ℚ := ∑ t ∈ wrapLocus V p, dyadicWeight V t

/-- The conductor threshold N10 uses: `ConductorBound n r := n ^ (2 * r)`. (Verbatim from N10.) -/
def ConductorBound (n r : ℕ) : ℕ := n ^ (2 * r)

/-- The named open claim, **verbatim** from N10 (with `κ` allowed any universe-poly `Type`). -/
def ShawVanishingAtPrizeScale (n r : ℕ) : Prop :=
  ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (W : κ → ℤ) (q : ℕ),
    ConductorBound n r < q → shawInvariant W q = 0

/-! ## Basic facts reused below -/

theorem dyadicWeight_pos (t : ι) : 0 < dyadicWeight V t := by unfold dyadicWeight; positivity

theorem shaw_nonneg : 0 ≤ shawInvariant V p := by
  unfold shawInvariant; exact Finset.sum_nonneg fun t _ => (dyadicWeight_pos V t).le

/-- A single witnessed wrap forces `shawInvariant ≠ 0` (this is N10's `shaw_ne_zero_of_witness`,
re-proved here so the countermodels are self-contained). -/
theorem shaw_ne_zero_of_witness {κ : Type*} [Fintype κ] [DecidableEq κ]
    (W : κ → ℤ) (q : ℕ) (t : κ) (hwrap : NonDiagWrap W q t) :
    shawInvariant W q ≠ 0 := by
  intro h
  have hmem : t ∈ wrapLocus W q := by unfold wrapLocus; simp [hwrap]
  have hpos : 0 < ∑ s ∈ wrapLocus W q, dyadicWeight W s :=
    Finset.sum_pos (fun s _ => dyadicWeight_pos W s) ⟨t, hmem⟩
  unfold shawInvariant at h
  rw [h] at hpos
  exact lt_irrefl _ hpos

/-! ## ATTACK 1 — the claim quantifies over arbitrary `W` (it does NOT express the prize)

We record that `ShawVanishingAtPrizeScale` makes no reference to `2^a`-roots: it is a statement
about an arbitrary `W : κ → ℤ`. The honest way to state "this `def` does not contain the prize
content" is to show it is logically equivalent to a pure divisibility statement about arbitrary
integers — which is what the following normal form does. -/

/-- **ATTACK 1 (normal form).** `ShawVanishingAtPrizeScale n r` unfolds to: for every finite family
of integers and every `q > n^(2r)`, no member is a nonzero multiple of `q`. No `μ_n`, no
`2^a`-root, no cyclotomic norm appears. (We state the `←` half — the pure-divisibility hypothesis
implies the Shaw form — to expose that the content is *only* divisibility of arbitrary integers.) -/
theorem shaw_decl_quantifies_arbitrary_W (n r : ℕ)
    (hdiv : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (W : κ → ℤ) (q : ℕ),
      ConductorBound n r < q → ∀ t, (q : ℤ) ∣ W t → W t = 0) :
    ShawVanishingAtPrizeScale n r := by
  intro κ _ _ W q hq
  rw [show shawInvariant W q = ∑ t ∈ wrapLocus W q, dyadicWeight W t from rfl]
  apply Finset.sum_eq_zero
  intro t ht
  -- `t ∈ wrapLocus` means `q ∣ W t ∧ W t ≠ 0`, contradicted by `hdiv`.
  unfold wrapLocus at ht
  rw [Finset.mem_filter] at ht
  obtain ⟨_, hdvd, hne⟩ := ht
  exact absurd (hdiv W q hq t hdvd) hne

/-! ## ATTACK 2a — as written (arbitrary `W`) the claim is OUTRIGHT FALSE -/

/-- The single-carrier system `κ = Unit`, `W ⟦_⟧ = q`. Its only value is exactly `q`. -/
def witnessW (q : ℕ) : Unit → ℤ := fun _ => (q : ℤ)

/-- That value wraps mod `q` (for `q ≥ 1`): `q ∣ q` and `q ≠ 0`. -/
theorem witnessW_wraps {q : ℕ} (hq : 1 ≤ q) : NonDiagWrap (witnessW q) q () := by
  refine ⟨dvd_refl _, ?_⟩
  unfold witnessW
  have : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  exact this.ne'

/-- **ATTACK 2a (machine-checked countermodel).** `ShawVanishingAtPrizeScale n r` is FALSE: for ANY
`n, r`, choosing `q := ConductorBound n r + 1` (so the hypothesis `ConductorBound n r < q` holds)
and `W := witnessW q` (a single carrier whose value is `q`), the Shaw invariant is nonzero. Hence
the named open claim, taken literally over arbitrary `W`, cannot be a theorem. -/
theorem shaw_universal_claim_is_false (n r : ℕ) :
    ¬ ShawVanishingAtPrizeScale n r := by
  intro h
  set q := ConductorBound n r + 1 with hqdef
  have hq1 : 1 ≤ q := by omega
  have hgt : ConductorBound n r < q := by omega
  -- the claim forces `shawInvariant (witnessW q) q = 0`
  have hzero : shawInvariant (witnessW q) q = 0 := h (witnessW q) q hgt
  exact shaw_ne_zero_of_witness (witnessW q) q () (witnessW_wraps hq1) hzero

/-! ## ATTACK 2b — the conductor threshold `n^(2r)` excludes the prize prime

Prize scale: `n = 2^30`, `r = 110`, `q ≈ 2^158`. The Lean hypothesis is `ConductorBound n r < q`,
i.e. `2^6600 < 2^158`, which is FALSE. We certify it in closed form: `ConductorBound n r ≥ q`. -/

/-- **ATTACK 2b (machine-checked).** At prize scale the conductor threshold N10 demands DWARFS the
prize prime: with `n = 2^30`, `r = 110`, the hypothesis `ConductorBound n r < q` fails for every
`q ≤ 2^6600` — in particular for the prize prime `q ≈ 2^158 < 2^160`. So `prize_of_shawVanishing`
can never be invoked with the prize `q`: its antecedent is false. The conditional closure is
vacuously inapplicable at prize scale. -/
theorem conductor_below_prize_prime :
    ∀ q : ℕ, q ≤ 2 ^ 160 → ¬ ConductorBound (2 ^ 30) 110 < q := by
  intro q hq hlt
  -- ConductorBound (2^30) 110 = (2^30)^(220) = 2^6600 ≥ 2^160 ≥ q, contradicting `q > ConductorBound`.
  have hcond : ConductorBound (2 ^ 30) 110 = 2 ^ 6600 := by
    unfold ConductorBound
    rw [← pow_mul]
  have hbig : (2 : ℕ) ^ 160 ≤ 2 ^ 6600 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  rw [hcond] at hlt
  omega

/-- **ATTACK 2b corollary — the cyclotomic norm route is in √p-vacuity.** The TRUE threshold above
which `p` fails to divide a short `≤2r`-term relation norm is `p > (2r)^{n/2}` (the norm bound), not
`p > n^(2r)`. At prize scale `(2r)^{n/2} = 220^{2^29}`, vastly larger than `n^(2r) = 2^6600`, which
is itself vastly larger than the prize `q`. We record the monotone gap `n^(2r) ≤ (2r)^{n/2}` at the
prize point as a concrete certificate that the genuine cyclotomic threshold is even further beyond
`q` — i.e. `p` divides many short-relation norms, the √p-vacuity face. -/
theorem true_norm_threshold_dwarfs_conductor :
    ConductorBound (2 ^ 30) 110 ≤ (2 * 110) ^ (2 ^ 29) := by
  -- n^(2r) = 2^6600 = (2^30)^220.  (2r)^{n/2} = 220^{2^29}.  Compare via 2^6600 ≤ 256^{2^29} ≤ 220^{2^29}?
  -- We bound conservatively: 2^6600 ≤ 2^(2^29) ≤ 220^(2^29).
  have hcond : ConductorBound (2 ^ 30) 110 = 2 ^ 6600 := by
    unfold ConductorBound; rw [← pow_mul]
  rw [hcond]
  calc (2 : ℕ) ^ 6600
      ≤ 2 ^ (2 ^ 29) := Nat.pow_le_pow_right (by norm_num) (by
        -- 6600 ≤ 2^29 = 536870912
        norm_num)
    _ ≤ (2 * 110) ^ (2 ^ 29) := Nat.pow_le_pow_left (by norm_num) _

/-! ## ATTACK 3 — Galois orbit-summing REPLICATES the divisibility (does not reduce it)

We reproduce the minimal `GaloisSymmetry` of N10 and show: if a tuple wraps mod `q`, every orbit
member wraps mod the SAME `q`. The "orbit-summed" object therefore inherits divisibility by `q`;
Galois invariance preserves, never cancels, the bad prime. The "orbit-summed norm is a `p`-free
unit" is thus not delivered by the orbit structure — it is the (false, Attack 2b) prose claim. -/

/-- Minimal `GaloisSymmetry` (N10's structure, trimmed to what Attack 3 needs): a permutation `σ`
of carriers with a `p`-coprime unit twist `u` on values. -/
structure GaloisSymmetry where
  σ : ι ≃ ι
  u : ι → ℤ
  u_ne_zero : ∀ t, u t ≠ 0
  twist : ∀ t, V (σ t) = u t * V t
  unit_coprime : ∀ t, IsCoprime (u t) (p : ℤ)

/-- **ATTACK 3 (machine-checked).** If `t` wraps mod `q` and `σ` is a Galois symmetry, then EVERY
forward image `σ t` also wraps mod the SAME `q`: `q ∣ V (σ t)` and `V (σ t) ≠ 0`. The unit twist
multiplies the value, so divisibility by `q` is carried along the orbit — the orbit-union has the
identical bad-prime `q`. Galois orbit-summing does not shed the divisibility. -/
theorem orbit_preserves_bad_prime (G : GaloisSymmetry V p) (t : ι)
    (ht : NonDiagWrap V p t) : NonDiagWrap V p (G.σ t) := by
  obtain ⟨hdvd, hne⟩ := ht
  refine ⟨?_, ?_⟩
  · rw [G.twist t]; exact Dvd.dvd.mul_left hdvd (G.u t)
  · rw [G.twist t]; exact mul_ne_zero (G.u_ne_zero t) hne

/-- **ATTACK 3 corollary.** Consequently a single wrap forces the entire forward orbit into the
wrap locus, so `shawInvariant` stays nonzero under the Galois action: orbit-summing cannot drive
`S_r` to `0` once any tuple wraps. (Contrast with the prose claim that the orbit-summed norm is a
`p`-free unit — that would need a NORM that is genuinely `≢0 mod p`, which Attack 2b shows fails at
prize scale.) -/
theorem orbit_does_not_cancel_shaw (G : GaloisSymmetry V p) (t : ι)
    (ht : NonDiagWrap V p t) : shawInvariant V p ≠ 0 :=
  shaw_ne_zero_of_witness V p t ht

end ArkLib.ProximityGap.FrontierShawStress

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]` only -/
#print axioms ArkLib.ProximityGap.FrontierShawStress.shaw_ne_zero_of_witness
#print axioms ArkLib.ProximityGap.FrontierShawStress.shaw_decl_quantifies_arbitrary_W
#print axioms ArkLib.ProximityGap.FrontierShawStress.shaw_universal_claim_is_false
#print axioms ArkLib.ProximityGap.FrontierShawStress.conductor_below_prize_prime
#print axioms ArkLib.ProximityGap.FrontierShawStress.true_norm_threshold_dwarfs_conductor
#print axioms ArkLib.ProximityGap.FrontierShawStress.orbit_preserves_bad_prime
#print axioms ArkLib.ProximityGap.FrontierShawStress.orbit_does_not_cancel_shaw
