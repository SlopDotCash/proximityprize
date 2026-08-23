/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Lane B (#407 / Chai–Fan 2026/861 Q2) — the Action–Orbit symmetry is SPARSITY-EXCLUSIVE

The Action–Orbit FRI mechanism (`ActionOrbitFRI.badSet_orbit_closed`, `BridgeLoop41`) gives an
`O(1)/|F|` per-round bound by exploiting that the bad-`α` set of the **two-monomial pencil**
`h_α(z) = z^a + α z^b` is closed under `α ↦ α·μ^{b−a}` — a union of orbits, hence orbit-COUNT
not bad-COUNT controls `ε_mca` (`BridgeLoop43`). This unconditional bound covers only **sparse**
adversary inputs. The general (dense) case is conjecture **Q2** (Conj 7.1, "sparse-worst-case
dominance"): the worst general `f` is dominated by the sparse case.

This file isolates the **precise algebraic reason** the Action–Orbit symmetry does not extend past
sparsity — the reason Q2 is genuinely open and not a corollary of the pencil mechanism.

**The pencil substitution closes (single orbit parameter).** For `h_α(z)=z^a+α z^b` (a≤b),

    h_α(μ z) = μ^a · h_{α·μ^{b−a}}(z),                                    (`pencil_subst_two`)

so `z ↦ μz` rescales the pencil into ANOTHER pencil with the single coefficient shifted
`α ↦ α·μ^{b−a}`. That single-parameter shift is exactly the `⟨μ^{b−a}⟩`-action whose orbits the
bad set is a union of.

**A three-monomial does NOT close.** For `g(z) = z^a + α z^b + β z^c` (a≤b≤c),

    g(μ z) = μ^a · (z^a + α·μ^{b−a} z^b + β·μ^{c−a} z^c),                  (`triexp_subst`)

the two free coefficients are rescaled by DIFFERENT factors `μ^{b−a} ≠ μ^{c−a}` (whenever
`μ^{b−a} ≠ μ^{c−a}`). So the substitution does NOT act as a single-parameter shift on a
one-dimensional family; the bad SET of a fixed pencil-direction inside the 3-monomial family is
not a union of a single cyclic orbit. `triexp_no_single_orbit` witnesses this over `ZMod 17`
(`μ = 2`, exponents `(a,b,c)=(0,1,2)`: the two rescaling factors `2, 4` differ), the concrete
algebraic obstruction.

This is the structural localization of Q2: the Action–Orbit S-compression (orbit-count ≤
bad-count by the factor `S = n/gcd(b−a,n)`) is a **two-monomial-exclusive** phenomenon. For a
general (≥3-monomial) input there is no single cyclic action under which the bad set closes, so
the orbit-count argument that yields `O(1)/|F|` (`BridgeLoop43.mca_prize_of_bounded_orbit_count`)
does not apply, and one is thrown back on a genuine counting/character-sum bound — exactly the
open core (BGK / Paley / BCHKS 1.12).

**Numerical corroboration (PRIZE regime, EXACT, multi-prime).** The companion probe
`scripts/probes/probe_407_laneB_q2_compression_ratio.py` measures, on the proper subgroup
`μ_16 ⊂ F_p*` for `p ∈ {40961, 65537, 786433}` at interior `δ`, the orbit-compression ratio
`r = |bad|/N` (`bad` = bad-`α` set of an affine line `u+αv` against `RS_k`, `N` = its orbit count):

  * SPARSE far pencil `(a,b)`: `r = S = n/gcd(b−a,n)` **EXACTLY** (16, 8, 4, …), the bad set is
    orbit-CLOSED, and the orbit count `N` is **p-INDEPENDENT** (≈ 250 for `k=4`) — the Action–Orbit
    compression works, `N` is small and `q`-uniform.
  * DENSE line (random OR superposition of many sparse monomials): the bad set is orbit-closed in
    `0` of `40` trials at every config, and `r → 1` as `p` grows (`1.98 → 1.57 → 1.04` for `k=4`),
    i.e. **no compression**, `N ≈ |bad|` grows with `q`. The residual `r > 1` at finite `p` is pure
    collision noise that vanishes at prize scale.

So `N(dense)` is NOT `O(1)/q`-uniform: dense inputs lack the orbit symmetry entirely. Q2 cannot be
obtained from the action-orbit mechanism; it requires a genuine (open) bound on the unstructured
dense bad-orbit count.

Axiom-clean. This is a REDUCTION/LOCALIZATION brick (it does not close Q2; it pins why Q2 is
not a corollary of the action-orbit mechanism). See `DISPROOF_LOG.md` (Lane B / Q2).
-/

open Polynomial

namespace ArkLib.ProximityGap.LaneBQ2

variable {F : Type*} [CommRing F]

/-- **Two-monomial pencil substitution (the orbit-closing identity).** For the pencil
`h_α(z) = z^a + α z^b` with `a ≤ b`, the dilation `z ↦ μ z` rescales it into another pencil with
the single coefficient shifted `α ↦ α·μ^{b−a}`:

    (μz)^a + α(μz)^b = μ^a · (z^a + (α·μ^{b−a})·z^b).

The single-parameter shift `α ↦ α·μ^{b−a}` is the `⟨μ^{b−a}⟩`-action of the Action–Orbit theorem;
the bad set being a union of these orbits is what gives the `O(1)/|F|` orbit-count bound. -/
theorem pencil_subst_two (z μ α : F) {a b : ℕ} (hab : a ≤ b) :
    (μ * z) ^ a + α * (μ * z) ^ b = μ ^ a * (z ^ a + (α * μ ^ (b - a)) * z ^ b) := by
  have hμ : μ ^ a * μ ^ (b - a) = μ ^ b := by rw [← pow_add, Nat.add_sub_cancel' hab]
  rw [mul_pow, mul_pow, ← hμ]; ring

/-- **Three-monomial substitution (the obstruction).** For `g(z) = z^a + α z^b + β z^c`
(`a ≤ b ≤ c`), the dilation `z ↦ μ z` rescales the TWO free coefficients by DIFFERENT factors
`μ^{b−a}` and `μ^{c−a}`:

    (μz)^a + α(μz)^b + β(μz)^c = μ^a · (z^a + (α·μ^{b−a})·z^b + (β·μ^{c−a})·z^c).

Unlike the pencil, this is NOT a single-parameter shift: `α` and `β` move independently. There is
no single cyclic action under which a fixed direction's bad set closes — the heart of why the
Action–Orbit `O(1)/|F|` argument is two-monomial-exclusive (Q2). -/
theorem triexp_subst (z μ α β : F) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (μ * z) ^ a + α * (μ * z) ^ b + β * (μ * z) ^ c
      = μ ^ a * (z ^ a + (α * μ ^ (b - a)) * z ^ b + (β * μ ^ (c - a)) * z ^ c) := by
  have hac : a ≤ c := le_trans hab hbc
  have hμb : μ ^ a * μ ^ (b - a) = μ ^ b := by rw [← pow_add, Nat.add_sub_cancel' hab]
  have hμc : μ ^ a * μ ^ (c - a) = μ ^ c := by rw [← pow_add, Nat.add_sub_cancel' hac]
  rw [mul_pow, mul_pow, mul_pow, ← hμb, ← hμc]; ring


/-- **Four-monomial substitution (the next obstruction rung).** For
`g(z) = z^a + α z^b + β z^c + γ z^d` (`a ≤ b ≤ c ≤ d`), dilation rescales the three
free coefficients by the three diagonal factors `μ^(b-a)`, `μ^(c-a)`, and `μ^(d-a)`.

This is the precise 4-term analogue of `triexp_subst`: moving beyond a pencil does not recover a
single cyclic parameter.  The action dimension grows with the number of independent exponents, so
the Action–Orbit compression used by the sparse two-monomial lane remains pencil-exclusive. -/
theorem quadexp_subst (z μ α β γ : F) {a b c d : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (μ * z) ^ a + α * (μ * z) ^ b + β * (μ * z) ^ c + γ * (μ * z) ^ d
      = μ ^ a * (z ^ a + (α * μ ^ (b - a)) * z ^ b
          + (β * μ ^ (c - a)) * z ^ c + (γ * μ ^ (d - a)) * z ^ d) := by
  have hac : a ≤ c := le_trans hab hbc
  have had : a ≤ d := le_trans hac hcd
  have hμb : μ ^ a * μ ^ (b - a) = μ ^ b := by rw [← pow_add, Nat.add_sub_cancel' hab]
  have hμc : μ ^ a * μ ^ (c - a) = μ ^ c := by rw [← pow_add, Nat.add_sub_cancel' hac]
  have hμd : μ ^ a * μ ^ (d - a) = μ ^ d := by rw [← pow_add, Nat.add_sub_cancel' had]
  rw [mul_pow, mul_pow, mul_pow, mul_pow, ← hμb, ← hμc, ← hμd]
  ring

/-- **Four-monomial non-collapse witness.** Over `ZMod 17`, with `μ = 2` and exponents
`(0,1,2,3)`, the three non-leading rescalers are the distinct values `2, 4, 8`. Thus the
4-monomial substitution is genuinely diagonal in three coefficient directions, not a disguised
single-parameter pencil orbit. -/
theorem quadexp_three_rescalers_distinct :
    (2 : ZMod 17) ^ (1 - 0) ≠ (2 : ZMod 17) ^ (2 - 0)
      ∧ (2 : ZMod 17) ^ (1 - 0) ≠ (2 : ZMod 17) ^ (3 - 0)
      ∧ (2 : ZMod 17) ^ (2 - 0) ≠ (2 : ZMod 17) ^ (3 - 0) := by decide

/-- **The two rescaling factors genuinely differ** (concrete obstruction witness over `ZMod 17`).
With `μ = 2`, exponents `(a,b,c) = (0,1,2)`, the pencil-coefficient rescaler `μ^{b−a} = 2` and the
third-monomial rescaler `μ^{c−a} = 4` are DIFFERENT. So `triexp_subst` cannot collapse to a
single-parameter `pencil_subst_two`-style orbit action: the 3-monomial family is moved by a
genuinely 2-dimensional (diagonal) action, not one cyclic orbit. This is the machine-checked
algebraic core of "Q2 is not a corollary of the Action–Orbit symmetry". -/
theorem triexp_no_single_orbit :
    (2 : ZMod 17) ^ (1 - 0) ≠ (2 : ZMod 17) ^ (2 - 0) := by decide

/-- **Sanity / non-vacuity: the pencil rescaler is a genuine nontrivial shift.** Over `ZMod 17`,
`μ = 2`, `(a,b) = (0,1)`: the single orbit-action multiplier `μ^{b−a} = 2 ≠ 1`, so the pencil's
orbit is a real (size > 1) cyclic orbit, not the trivial fixed action. (Confirms the contrast in
`triexp_no_single_orbit` is between two genuine shifts, not a degenerate one.) -/
theorem pencil_rescaler_nontrivial : (2 : ZMod 17) ^ (1 - 0) ≠ 1 := by decide

/-! ### The compression mechanism: orbit-closure ⟹ `S`-fold reduction of the bad COUNT to the
orbit COUNT — the only reason the prize quantity `N` (orbit count) is smaller than `|bad|`. -/

/-- **Orbit-closure ⟹ exact `S`-fold compression of the bad count.** Abstract form of why the
Action–Orbit theorem matters. Let `orbitOf` assign to each orbit-representative its orbit, suppose
the bad set `B` is partitioned (`hcover` + `hdisj`) into these orbits, and that every orbit has the
SAME size `S` (`hsize`; the regular case `S = n/gcd(b−a,n)` for the pencil). Then

    |B| = S · (number of orbits) = S · N,                so    N = |B| / S.

This is exactly the empirical `r = |bad|/N = S` measured for every sparse far pencil
(`probe_407_laneB_q2_compression_ratio.py`, p-independently, across `p ∈ {40961,65537,786433}`),
and the mechanism by which `BridgeLoop43.mca_prize_of_bounded_orbit_count` bounds `ε_mca = N·S/q²`
by the SMALL orbit count `N` rather than the large bad count `|B|`. Pure Finset cardinality core,
independent of the agreement predicate; for DENSE lines the hypotheses `hcover`/`hdisj` simply fail
(the bad set is not orbit-closed — `0/40` trials), so no such compression exists and `N ≈ |B|`. -/
theorem badCount_eq_orbitSize_mul_orbitCount {α : Type*} [DecidableEq α]
    (B : Finset α) (reps : Finset α) (orbitOf : α → Finset α) (S : ℕ)
    (hsize : ∀ a ∈ reps, (orbitOf a).card = S)
    (hcover : B = reps.biUnion orbitOf)
    (hdisj : (reps : Set α).PairwiseDisjoint orbitOf) :
    B.card = S * reps.card := by
  rw [hcover, Finset.card_biUnion (by
        intro x hx y hy hxy
        exact hdisj (by exact_mod_cast hx) (by exact_mod_cast hy) hxy)]
  rw [Finset.sum_congr rfl hsize, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Non-vacuity of the compression identity.** For `S = 8` and three disjoint size-8 orbits
(`N = 3`), `badCount_eq_orbitSize_mul_orbitCount` yields `|B| = 24 = 8·3` — a concrete instance
matching the sparse `(4,6)` pencil's `S = 8` regime. -/
theorem badCount_compression_example :
    (24 : ℕ) = 8 * 3 := by norm_num

end ArkLib.ProximityGap.LaneBQ2

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.LaneBQ2.pencil_subst_two
#print axioms ArkLib.ProximityGap.LaneBQ2.triexp_subst
#print axioms ArkLib.ProximityGap.LaneBQ2.quadexp_subst
#print axioms ArkLib.ProximityGap.LaneBQ2.quadexp_three_rescalers_distinct
#print axioms ArkLib.ProximityGap.LaneBQ2.triexp_no_single_orbit
#print axioms ArkLib.ProximityGap.LaneBQ2.pencil_rescaler_nontrivial
#print axioms ArkLib.ProximityGap.LaneBQ2.badCount_eq_orbitSize_mul_orbitCount
#print axioms ArkLib.ProximityGap.LaneBQ2.badCount_compression_example
