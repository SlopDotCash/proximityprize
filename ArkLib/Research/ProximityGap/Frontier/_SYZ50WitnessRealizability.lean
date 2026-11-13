/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Research.ProximityGap.Frontier._SYZ49CyclotomicGcd

/-!
# SYZ50 — witness realizability: is the SYZ49 on-domain `ι = 2` witness band-realizable?

## Where this sits

SYZ49 exhibited an **on-domain** `ι = 2` witness over the *proper subgroup* `μ₁₂ ⊂ 𝔽₃₇^×`:
disjoint `(4,4,4)` sets `S_AC={1,8,27,29}`, `S_BC={6,10,11,31}`, `S_AB={14,23,26,36}` with the
constant syzygy `W_BC − 11·W_AC = −10·W_AB`.  It correctly concluded that the *cyclotomic
domain-membership* condition alone does **not** force `ι ≤ 1`, and relocated the shield to the
finer **band-realizability** (SYZ42 superadditive-union / SYZ27–28 Venn geometry).

This file executes that relocation head-on: it asks whether the SYZ49 witness — or its
degree profile — is *band-realizable* at rate exactly `1/2` (`n = 2k`), i.e. whether the three
disjoint pairwise-exclusive overlap sets can be the overlap regions of three band cores of an
actual over-budget stack.  The band Venn model (SYZ27/28/37/G172) forces, at rate `1/2`:

* **disjointness in the domain** `a + b + c + t ≤ n = 2k`
  (the three pairwise-exclusive regions `S_AB,S_AC,S_BC` — sizes `a,b,c` — and the triple region
  `T` of size `t` are mutually disjoint subsets of the `n`-point evaluation domain);
* **budget cap** `max(a,b,c) ≤ k − 1 − t` (SYZ37 uniform window, `t`-loaded interface);
* **interior slack** `a + b + c ≥ 2·(k − 1 − t) + 3` (G172).

## The decisive polytope verdict (probe `probe_syz50_witness_realizability.py`)

**Question A — is `{balanced interior} ∩ {band-realizable, rate 1/2}` empty?**  **NO — it is
NONEMPTY.**  Exhaustive integer enumeration (`k ≤ 40`) finds **65 982** balanced-interior
band-realizable profiles; the smallest is `n = 14`, `k = 7`, `(a,b,c) = (4,4,4)`, `t = 2`
(cores of size `s = a+b+t = 10`, radius `δ = 4/14 = 2/7 ∈ (1/4,1/3)`, i.e. the `2n/3 < s < 3n/4`
core band — but **below** the
Johnson radius `1 − √(1/2) ≈ 0.293`, so outside the decisive strip `(Johnson, 1/3)`).  **So the
counting/Venn overflow is *not* a global closing argument**: the balanced interior does meet the
realizable polytope at rate `1/2`.

**Question B — is the *specific* SYZ49 `μ₁₂` witness band-realizable?**  **NO.**  At `n = 12`,
`k = 6`, the band constraints *force* `t = 1` (slack ⟹ `t ≥ 1`, budget ⟹ `t ≤ 1`), but domain
disjointness then needs `a+b+c+t = 12+1 = 13 ≤ 12` — **impossible**.  The `μ₁₂` witness fills the
*entire proper subgroup* with its three `(4,4,4)` sets, leaving **no room** for the triple region
the band budget demands.  It is a domain-membership artifact of the whole-subgroup, **one domain
point short** of band-realizability: the general balanced law is `n ≥ 3d + 1`
(`balanced_profile_needs_domain`), and `μ_{3d}` (here `μ₁₂`, `d = 4`) misses it by exactly `1`.
Scope: this verdict is for the whole-subgroup domain `n = 12` only.  The same three disjoint root
sets also lie in `μ₁₂ ⊂ 𝔽₃₇^× = μ₃₆`, and at `n = 36, k = 18` the profile passes the `Realizable`
relaxation with `t = 13` (`mu12_profile_realizable_n36`) — though not `StrictBandCores`.

**Question C — do band-realizable configs carry *fresh* on-domain `ι = 2` witnesses?**  **YES.**
Over `μ₁₄ ⊂ 𝔽₂₉` the `(4,4,4)`, `t = 2` config yields **357** genuine constant-syzygy level-set
witnesses (three disjoint size-`4` sets with a size-`4` `R`-level set, `2` domain points left for
`T`).  So band-realizability *counting* does **not** close the interior either.

**Question D — the lift ceiling.**  Even on the realizable `n = 14` witness the pencil-yield
count is capped: `∑(n − sᵢ) = 3·(14 − 10) = 12 ≤ 13 = n − 1` (SYZ22/SYZ28 budget).  A full
bad-lift cannot outrun the budget — but *whether* the constant syzygy arises from a genuine
over-budget stack (the SYZ42 syndrome-configuration existence) is the unchanged open gate.

## Honest verdict

The polytope intersection is **nonempty**, so `ι ≤ 1` at rate `1/2` is **not** closed by a
pure counting/overflow argument.  What *is* newly pinned: on its whole-subgroup domain `n = 12` the
SYZ49 `μ₁₂` witness is **not** band-realizable (`n = 3d` short of the band's `n ≥ 3d + 1`; on a
larger domain such as `μ₃₆` the profile does pass the `Realizable` relaxation),
and the genuine gate is neither domain-membership (SYZ48/49) nor Venn-counting (this file) but
the **over-budget-stack lift** (SYZ42 existence core / SYZ28 pencil yield).  CORE remains OPEN /
ON-BGK — with the shield now correctly located one level deeper than SYZ49 left it.

## What is proved here (all axiom-clean, pure `ℕ`)
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ50

open ArkLib.ProximityGap.SYZ48 (BalancedInterior)

/-! ## 1. The band-realizability predicate at rate `1/2` -/

/-- **Band-realizable at rate `1/2`.**  Reduced degrees `(a,b,c)` (the sizes of the three
pairwise-exclusive overlap regions), triple-region size `t`, half-length `k` (domain size
`n = 2k`).  The three constraints the SYZ27/28/37/G172 Venn model imposes:

* `a,b,c ≥ 1` (nonempty overlap regions);
* **disjointness** `a + b + c + t ≤ 2k` (all four regions are disjoint domain subsets);
* **budget cap** `max(a,b,c) + 1 + t ≤ k`, i.e. `max(a,b,c) ≤ k − 1 − t` (SYZ37);
* **interior slack** `2k + 1 ≤ (a + b + c) + 2t`, i.e. `a+b+c ≥ 2(k−1−t)+3` (G172).

These are only **necessary** conditions (a relaxation): they do not guarantee three integer
cores in the strict band `2n/3 < |core| < 3n/4`.  `StrictBandCores` (§4b) adds the private
coordinate ownership, and `realizable_not_strictBandCores` shows the gap (audit finding L129).
Negative results about `Realizable` (such as `syz49_mu12_witness_not_realizable`) transfer to
strict-band cores; positive ones need `StrictBandCores`.

Subtraction-free `ℕ` phrasing so `omega` can drive everything. -/
def Realizable (a b c t k : ℕ) : Prop :=
  1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧
  a + b + c + t ≤ 2 * k ∧
  max a (max b c) + 1 + t ≤ k ∧
  2 * k + 1 ≤ a + b + c + 2 * t

/-! ## 2. The triple region is forced nonempty at rate `1/2` -/

/-- **Rate-`1/2` forces a nonempty triple region.**  Subtracting the disjointness bound
`a+b+c+t ≤ 2k` from the interior slack `2k+1 ≤ a+b+c+2t` gives `t ≥ 1`: every band-realizable
configuration at rate `1/2` has a nonempty triple overlap `T`.  This single fact is what the
whole-subgroup SYZ49 witness violates. -/
theorem realizable_forces_triple {a b c t k : ℕ} (h : Realizable a b c t k) : 1 ≤ t := by
  obtain ⟨_, _, _, hdisj, _, hslack⟩ := h; omega

/-- **Domain lower bound for a balanced profile.**  A balanced band-realizable profile
`(d,d,d)` at rate `1/2` needs `n = 2k ≥ 3d + 1`: the three size-`d` pairwise regions (`3d`
points) plus the forced nonempty triple region require at least `3d + 1` domain points.  Hence
the *whole proper subgroup* `μ_{3d}` (exactly `3d` points, `n = 3d`) is **one point short** of
band-realizability. -/
theorem balanced_profile_needs_domain {d t k : ℕ} (h : Realizable d d d t k) :
    3 * d + 1 ≤ 2 * k := by
  have ht : 1 ≤ t := realizable_forces_triple h
  obtain ⟨_, _, _, hdisj, _, _⟩ := h; omega

/-! ## 3. Question B — the SYZ49 `μ₁₂` witness is NOT band-realizable -/

/-- **The SYZ49 `μ₁₂` witness is band-non-realizable.**  At the prize domain size `n = 12`
(`k = 6`) no triple-region size `t` makes the balanced `(4,4,4)` profile band-realizable:
`balanced_profile_needs_domain` would require `3·4 + 1 = 13 ≤ 12`, false.  So the explicit
on-domain `ι = 2` witness of SYZ49 — living on the *whole* subgroup `μ₁₂ = μ_{3·4}` — is not the
overlap geometry of any band stack **on the domain `n = 12`**.  The statement fixes `k = 6`; it says
nothing about larger domains containing the same root sets (cf. `mu12_profile_realizable_n36`). -/
theorem syz49_mu12_witness_not_realizable : ¬ ∃ t : ℕ, Realizable 4 4 4 t 6 := by
  rintro ⟨t, h⟩
  have := balanced_profile_needs_domain h; omega

/-! ## 4. Question A — the polytope intersection is NONEMPTY -/

/-- **The smallest realizable balanced witness.**  `(a,b,c) = (4,4,4)`, `t = 2`, `k = 7`
(`n = 14`) is band-realizable: disjointness `14 ≤ 14`, budget `4+1+2 = 7 ≤ 7`, slack
`15 ≤ 12+4 = 16`.  The profile the `μ₁₂` witness *wanted* becomes realizable exactly one domain
point up, on `μ₁₄`. -/
theorem witness_realizable_n14 : Realizable 4 4 4 2 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`(4,4,4)` is balanced-interior** (`max + 1 = 5 < 6 = ⌊12/2⌋`): the SYZ47 floor does not
discharge it, so it is a genuine `ι ≤ 1` test case. -/
theorem witness_balanced_interior : BalancedInterior 4 4 4 := by
  unfold BalancedInterior; decide

/-- **DECISIVE POLYTOPE VERDICT — the intersection is nonempty.**  There is a profile that is
*both* balanced-interior (SYZ47 floor blind to it) *and* band-realizable at rate `1/2`, namely
`(4,4,4)`, `t = 2`, `k = 7`.  Therefore `ι ≤ 1` at rate `1/2` is **not** closed by a pure
counting/Venn-overflow argument: the balanced interior genuinely meets the realizable polytope.
The residual gate is the over-budget-stack lift, not the counting. -/
theorem balanced_interior_meets_realizable :
    ∃ a b c t k : ℕ, Realizable a b c t k ∧ BalancedInterior a b c :=
  ⟨4, 4, 4, 2, 7, witness_realizable_n14, witness_balanced_interior⟩

/-! ## 4b. Strict-band core ownership: `Realizable` is only a relaxation -/

/-- **Strict-band cores with private ownership.**  With pair regions `S_AB, S_AC, S_BC` of sizes
`a, b, c`, triple region `T` of size `t`, and private (single-core) regions of sizes
`pA, pB, pC`, the cores `S_AB ∪ S_AC ∪ T ∪ P_A`, `S_AB ∪ S_BC ∪ T ∪ P_B`,
`S_AC ∪ S_BC ∪ T ∪ P_C` all fit in the `n = 2k` domain and lie in the strict interior band
`2n/3 < s < 3n/4`, i.e. `4k + 1 ≤ 3s` and `4s + 1 ≤ 6k`. -/
def StrictBandCores (a b c t k : ℕ) : Prop :=
  Realizable a b c t k ∧ ∃ pA pB pC : ℕ,
    a + b + c + t + pA + pB + pC ≤ 2 * k ∧
    4 * k + 1 ≤ 3 * (a + b + t + pA) ∧ 4 * (a + b + t + pA) + 1 ≤ 6 * k ∧
    4 * k + 1 ≤ 3 * (a + c + t + pB) ∧ 4 * (a + c + t + pB) + 1 ≤ 6 * k ∧
    4 * k + 1 ≤ 3 * (b + c + t + pC) ∧ 4 * (b + c + t + pC) + 1 ≤ 6 * k

/-- **The relaxation is strictly weaker (audit finding L129).**  `(a,b,c,t,k) = (4,5,5,3,9)`
passes `Realizable`, but at `n = 18` each core needs at least `13` coordinates: the prescribed
regions give cores of sizes `12, 12, 13` and occupy `17` coordinates, leaving one coordinate for
the two private points that are needed. -/
theorem realizable_not_strictBandCores :
    Realizable 4 5 5 3 9 ∧ ¬ StrictBandCores 4 5 5 3 9 := by
  refine ⟨by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide, ?_⟩
  rintro ⟨_, pA, pB, pC, hdom, hA, _, hB, _, hC, _⟩
  omega

/-- **The `n = 14` witness profile has genuine strict-band cores** (no private coordinates:
all three cores have size `10`, and `28 < 30`, `40 < 42`). -/
theorem strictBandCores_n14 : StrictBandCores 4 4 4 2 7 :=
  ⟨witness_realizable_n14, 0, 0, 0, by decide⟩

/-- **The `n = 12` verdict is domain-specific (audit CW-B13-12).**  The SYZ49 root sets lie in
`μ₁₂ ⊂ 𝔽₃₇^× = μ₃₆`; at `n = 36` (`k = 18`) the balanced `(4,4,4)` profile with `t = 13` passes
`Realizable` (`25 ≤ 36`, `4+1+13 = 18 ≤ 18`, `37 ≤ 12+26`).  It does not, however, admit strict-band
cores with private ownership (each core would need `≥ 25` points, i.e. `≥ 4` private points apiece,
exceeding the `11` free coordinates). -/
theorem mu12_profile_realizable_n36 :
    Realizable 4 4 4 13 18 ∧ ¬ StrictBandCores 4 4 4 13 18 := by
  refine ⟨by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide, ?_⟩
  rintro ⟨_, pA, pB, pC, hdom, hA, _, hB, _, hC, _⟩
  omega

/-! ## 5. Question D — the pencil-yield lift ceiling on the realizable witness -/

/-- **Lift ceiling ≤ budget on the `n = 14` realizable witness.**  Each core hosts its two
pairwise regions plus the triple, size `s = a + b + t`; here `s = 4 + 4 + 2 = 10`, so the
pencil-yield count `∑(n − sᵢ) = 3·(14 − 10) = 12 ≤ 13 = n − 1` sits at-or-below the SYZ22
budget.  Even a maximal bad-lift on the realizable config cannot outrun the budget — consistent
with `δ*` untouched; the open content is *existence* of the stack, not its size. -/
theorem lift_ceiling_le_budget :
    3 * (14 - (4 + 4 + 2)) ≤ 14 - 1 := by decide

end ArkLib.ProximityGap.SYZ50

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ50.realizable_forces_triple
#print axioms ArkLib.ProximityGap.SYZ50.balanced_profile_needs_domain
#print axioms ArkLib.ProximityGap.SYZ50.syz49_mu12_witness_not_realizable
#print axioms ArkLib.ProximityGap.SYZ50.witness_realizable_n14
#print axioms ArkLib.ProximityGap.SYZ50.witness_balanced_interior
#print axioms ArkLib.ProximityGap.SYZ50.balanced_interior_meets_realizable
#print axioms ArkLib.ProximityGap.SYZ50.lift_ceiling_le_budget
#print axioms ArkLib.ProximityGap.SYZ50.realizable_not_strictBandCores
#print axioms ArkLib.ProximityGap.SYZ50.strictBandCores_n14
#print axioms ArkLib.ProximityGap.SYZ50.mu12_profile_realizable_n36
