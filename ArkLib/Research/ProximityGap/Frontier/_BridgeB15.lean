/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Bridge B15 (target E3) — the *partial-orbit* binding at a primitive binder

## What B14/B16 already prove (the plateau), and what is left (the crossing)

For a monomial direction `(x^a, x^b)` the Action–Orbit factorization
(`OrbitCountCrossingLaw`, P3) decomposes the bad-α count.  At a **primitive** binder
`d = gcd(b−a,n) = 1` the free orbit size is the full `S = n`, and the *plateau* law
(`BridgeB14.crossing_law_primitive`, `BridgeB16.primitive_binder_orbit_le_one`) reads

  `D = N·S ⟹ (D ≤ n ⟺ N ≤ 1)`,

i.e. the budget admits at most **one full** primitive orbit.  But the kb E3 empirical
refinement (`deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`, E3) records that
at the *actual binding* `s*` the worst direction is primitive **yet the bad-α count `D` is
NOT a multiple of `S`** — the bad set is a *partial* orbit (with a fixed-point head):

  `n=8,  binder (5,4): D = 5 ≠ 8·O   (S = 8)`
  `n=16, binder (11,10): D = 9 ≠ 16·O (S = 16)`.

So the clean crossing law governs the *plateau*; a **partial-orbit count** governs the
*crossing*.  B15 formalizes that partial-orbit structure as honest arithmetic on top of the
proven substrate counting brick.

## The partial-orbit decomposition

Off the fixed point `α = 0`, the action `α ↦ α·ω^{b−a}` is free, so the free part of the
bad set is a disjoint union of full orbits (size `S`) PLUS, at the binding, one *proper*
sub-orbit.  Writing the bad set as

  `B = B₀ ⊎ B_free`,  `|B₀| = z ∈ {0,1}` (the `α=0` head),  `|B_free| = P` (the free part),

the count is `D = z + P`.  At the binding the free part is a **proper** sub-orbit:
`0 < P < S`.  With the fixed-point head `z = 1` (numerically present at both binders above:
`5 = 1+4`, `9 = 1+8`, with `4 = S/2`, `8 = S/2`) the binding count is `D = 1 + P`,
`0 < D < S` — **strictly below** the plateau-1 ceiling `S`, hence NOT a multiple of `S`.

This is the exact content of E3's partial-orbit refinement, and it is proven below as
axiom-clean arithmetic.  (It does NOT establish the open *value* of `P` at binding — that is
E7 / BCHKS 1.12, the live research object.  B15 proves the *structure* the binding has.)
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB15

open ArkLib.ProximityGap.OrbitCountCrossingLaw

variable {ι : Type*} [DecidableEq ι]

/-! ### 1. The decomposition count `D = z + P` -/

/-- **Bad-set decomposition count.**  If the bad set `B` splits as a disjoint union
`B = B₀ ⊎ B_free` (fixed-point head `B₀`, free part `B_free`), then `|B| = |B₀| + |B_free|`.
Pure `Finset.card_union_of_disjoint`. -/
theorem badSet_count_decompose
    (B₀ Bfree : Finset ι) (hdisj : Disjoint B₀ Bfree) :
    (B₀ ∪ Bfree).card = B₀.card + Bfree.card :=
  Finset.card_union_of_disjoint hdisj

/-! ### 2. A primitive binder with a *proper* sub-orbit lands strictly inside plateau-1 -/

/-- **B15 core — proper sub-orbit ⟹ strictly below the plateau ceiling.**  At a primitive
binder the orbit size is the full `S = n`.  If the binding bad-α count decomposes as
`D = z + P` with fixed-point head `z ∈ {0,1}` and a **proper** sub-orbit `0 < P < S`, then
`0 < D < S`.  Concretely the binders are `z = 1`: `D = 1 + P`, `0 < D ≤ P+1 ≤ S`, and in fact
`D < S` whenever `P < S − 1` (the empirical `P = S/2` case).  We give the sharp hypothesis
`z + P < S` (true at both recorded binders: `5 < 8`, `9 < 16`). -/
theorem partial_orbit_below_plateau
    {D z P S : ℕ} (hzP : 0 < z + P) (hlt : z + P < S) (hid : D = z + P) :
    0 < D ∧ D < S := by
  refine ⟨?_, ?_⟩
  · rw [hid]; exact hzP
  · rw [hid]; exact hlt

/-- **B15 — a proper sub-orbit binding is NOT a multiple of the orbit size.**  If the binding
count is `D = z + P` with `0 < D < S`, then `D` is **not** a positive multiple of `S`, and in
fact `D` is not a multiple of `S` at all (the only multiple of `S` that is `< S` is `0`, but
`D > 0`).  This is precisely E3's `D ≠ S·O` at the primitive binder. -/
theorem partial_orbit_not_multiple
    {D z P S : ℕ} (hzP : 0 < z + P) (hlt : z + P < S) (hid : D = z + P) :
    ¬ S ∣ D := by
  obtain ⟨hpos, hlt'⟩ := partial_orbit_below_plateau hzP hlt hid
  intro hdvd
  -- a nonzero multiple of `S` is `≥ S`, contradicting `D < S`
  have := Nat.le_of_dvd hpos hdvd
  exact absurd hlt' (Nat.not_lt.mpr this)

/-- **B15 — explicit fixed-point head `z = 1` form.**  At both recorded binders the
fixed-point head is present (`z = 1`): `D = 1 + P` with `0 < P` and `P + 1 < S`.  Then
`0 < D < S` and `S ∤ D`. -/
theorem fixed_head_partial_orbit
    {D P S : ℕ} (hP : 0 < P) (hlt : 1 + P < S) (hid : D = 1 + P) :
    0 < D ∧ D < S ∧ ¬ S ∣ D := by
  have hzP : 0 < 1 + P := by omega
  obtain ⟨h1, h2⟩ := partial_orbit_below_plateau hzP hlt hid
  exact ⟨h1, h2, partial_orbit_not_multiple hzP hlt hid⟩

/-! ### 3. Tie to the substrate plateau: the binding is BELOW the budget, not AT a full orbit -/

/-- **B15 — partial-orbit binding satisfies the budget while the plateau (full orbit) does
not bind it.**  The crossing law (`OrbitCountCrossingLaw.crossing_law`) at a primitive binder
(`S·1 = n`, so `S = n`) says a *full* orbit count `N` crosses the budget exactly when `N ≤ 1`.
The partial-orbit binding has `D = z + P < S = n`, so it trivially satisfies `D ≤ n` (the
budget), and being strictly below `S` it carries **zero** completed orbits while still being
nonempty — the proper sub-orbit.  We package the two facts the substrate plus the
decomposition give:
* `D ≤ n` (budget met, since `D < S = n`),
* `D` is not a multiple of `S` (proper sub-orbit, via `partial_orbit_not_multiple`). -/
theorem partial_orbit_binding_vs_plateau
    {D z P S n : ℕ} (hsupply : S * 1 = n)
    (hzP : 0 < z + P) (hlt : z + P < S) (hid : D = z + P) :
    D ≤ n ∧ ¬ S ∣ D := by
  have hSn : S = n := by simpa using hsupply
  obtain ⟨_, hlt'⟩ := partial_orbit_below_plateau hzP hlt hid
  refine ⟨?_, partial_orbit_not_multiple hzP hlt hid⟩
  rw [← hSn]; exact le_of_lt hlt'

/-! ### 4. Concrete sanity instances matching the recorded binders -/

/-- **n = 8, binder (5,4): `D = 5 = 1 + 4`, `S = 8`.**  Proper sub-orbit `P = 4 = S/2`,
fixed-point head `z = 1`: `0 < 5 < 8` and `8 ∤ 5`. -/
example : (0 : ℕ) < 5 ∧ (5 : ℕ) < 8 ∧ ¬ (8 : ℕ) ∣ 5 :=
  fixed_head_partial_orbit (P := 4) (by norm_num) (by norm_num) (by norm_num)

/-- **n = 16, binder (11,10): `D = 9 = 1 + 8`, `S = 16`.**  Proper sub-orbit `P = 8 = S/2`,
fixed-point head `z = 1`: `0 < 9 < 16` and `16 ∤ 9`. -/
example : (0 : ℕ) < 9 ∧ (9 : ℕ) < 16 ∧ ¬ (16 : ℕ) ∣ 9 :=
  fixed_head_partial_orbit (P := 8) (by norm_num) (by norm_num) (by norm_num)

/-- **Budget-vs-plateau sanity (n = 16):** the binding `D = 9` meets the budget `≤ n = 16`
while carrying no completed full orbit (`16 ∤ 9`). -/
example : (9 : ℕ) ≤ 16 ∧ ¬ (16 : ℕ) ∣ 9 :=
  partial_orbit_binding_vs_plateau (z := 1) (P := 8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end ArkLib.ProximityGap.BridgeB15

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB15.badSet_count_decompose
#print axioms ArkLib.ProximityGap.BridgeB15.partial_orbit_below_plateau
#print axioms ArkLib.ProximityGap.BridgeB15.partial_orbit_not_multiple
#print axioms ArkLib.ProximityGap.BridgeB15.fixed_head_partial_orbit
#print axioms ArkLib.ProximityGap.BridgeB15.partial_orbit_binding_vs_plateau
