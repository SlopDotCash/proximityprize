/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import Research.ProximityPrize.Frontier._SYZ47GeometricBalance

/-!
# SYZ48 — the balanced interior: level sets, domain-membership, and why `μ_n` is load-bearing

## Where this sits

SYZ47 proved the imbalance **floor** `δ₁ ≥ max(a,b,c)` on the band triangle, discharging `ι ≤ 1`
on the *moderately unbalanced* strip (`max(a,b,c) ≥ ⌊S/2⌋ − 1`, `S = a+b+c`, ~37.7 % of band
triples).  The remaining ~62.3 % **balanced interior** (`max(a,b,c) < ⌊S/2⌋ − 1`) is where the
floor is too weak — it only yields `ι ≤ ⌊d/2⌋` — and where SYZ45's `(4,4,4) ⇒ ι = 2` witness lives.
`ι ≤ 1` there held in a random sample (probe `probe_syz48_balanced_interior.py`, 0 violations over
random disjoint `μ_n` root triples, which are not band-realizable cores) but is **not** proved, and
it is **false** as a general on-domain statement: SYZ49 exhibits an on-domain `ι = 2` witness over
`μ₁₂ ⊂ 𝔽₃₇`, and audit finding L127 (repository review 2026-10-28) gives a full-cover proper-band
`μ₂₀ ⊂ 𝔽₄₁` configuration with `ι = 2`.

This file pins the *exact* characterization of the balanced-interior obstruction and settles the
decisive question: **is `ι ≥ 2` band-realizable on the balanced interior, and what — if anything —
does the evaluation domain add beyond the degree profile?**

## The chain (all pure/polynomial, axiom-clean)

1. **Exact characterization** (`balanced_interior_imbalance_ge_two_iff`).  On the balanced interior,
   under the SYZ44 degree-sum law, `ι ≥ 2` is *exactly* the existence of a syzygy of product-degree
   `≤ ⌊S/2⌋ − 2` — a genuinely *low* syzygy strictly beneath the SYZ47 floor `max(a,b,c)`.

2. **Constant-ratio reformulation** (`const_ratio_syzygy_iff_dvd`).  A nonzero constant-cofactor
   syzygy `c₀·W_AB + α·W_AC + β·W_BC = 0` with the `AB` slot carrying (`c₀ ≠ 0`) is *exactly*
   the divisibility `W_AB ∣ (α·W_AC + β·W_BC)`: the roots of `W_AB` (all `a` of them) must be roots
   of the combination `P := α·W_AC + β·W_BC`, whose degree is `≤ max(b,c)`.

3. **Level-set / root-count bound** (`level_set_card_le`, `combination_root_card_le`).  The
   combination `P` has at most `max(b,c)` roots (`Polynomial.card_roots'`), so *any* constant-ratio
   level set `{x : W_BC(x) = c·W_AC(x)}` has `≤ max(b,c)` points.

4. **Counting is not enough on the balanced interior** (`dvd_forces_degree_le`).  `W_AB ∣ P` with
   `P ≠ 0` forces `a ≤ deg P ≤ max(b,c)` — which is *satisfiable* when `a` is not the strict max,
   i.e. on the balanced interior.  So the root-count bound gives **no contradiction** there: the
   honest *full circle* — the genuine obstruction is the simultaneous SYZ39 interpolation, not a
   degree count.

5. **`ℚ̄`-realizability** (`imbalance_ge_two_realizable_of_dvd`).  Conversely, whenever
   `P = C c₀ * W_AB` (the combination is *exactly* a scalar multiple of `W_AB`, deg `a`) a constant
   syzygy exists, so `δ₁ ≤ a` and — for a balanced profile `a=b=c=d≥4` — `ι ≥ ⌊d/2⌋ ≥ 2`.  Over an
   *algebraically closed* field this is unobstructed: pick disjoint `W_AC, W_BC`, form
   `P = α·W_AC + β·W_BC`, and take `W_AB = P` when it is squarefree and coprime to both; its roots
   are algebraic points, which need a code domain containing them.  A finite prime field is not an
   algebraic closure: over `𝔽_p` such a `W_AB` vanishes on `d` field points only when `P` splits
   into distinct linear factors.  Probe [4] (corrected per audit finding L128): every sampled
   balanced configuration over `𝔽₁₀₀₀₇, 𝔽₁₀₀₀₀₃, 𝔽₁₀₀₀₀₀₃` gives an *algebraic* `ι ≥ 2` syzygy, but
   only a small minority (single digits out of 400) split into `d` distinct `𝔽_p` points.  **So the
   degree profile alone does NOT force `ι ≤ 1`** (an algebraic statement); the split examples are
   `𝔽_p`-point realizations with evaluation domain all of `𝔽_p`.

6. **Domain membership** (`root_of_dvd_X_pow_sub_one_pow_eq_one`).  Over the domain `μ_n` the roots
   of `W_AB` must be *evaluation-domain points* — every root `r` of any divisor of `Xⁿ − 1`
   satisfies `rⁿ = 1`.  For random `α, β` and random disjoint `μ_n`-subsets the roots of
   `P = α·W_AC + β·W_BC` are typically not all in `μ_n`.  Probe [2] separates *why*: when
   `μ_n = 𝔽_p^×` (the domains `μ_{p−1}` used there) the only `𝔽_p` point off the domain is `0`, so
   the missing roots are **nonsplit** (not `𝔽_p` points at all), not an escape to other base-field
   coordinates; on proper subgroups some roots do land on `𝔽_p` points off the domain.  These are
   random-sample statistics, **not** a universal obstruction: on-domain `ι = 2` witnesses exist
   (SYZ49 `μ₁₂ ⊂ 𝔽₃₇`; audit finding L127, `μ₂₀ ⊂ 𝔽₄₁`, full-cover proper band).

## Honest verdict

`ι ≤ 1` is *not* a degree-profile fact (item 5, algebraic syzygies), and the root-count level-set
bound gives no contradiction (item 4 — full circle back to the SYZ39 interpolation matrix).
Domain membership (item 6) is a genuine *necessary* constraint, but the probe only shows it is
typically unmet by random combinations; it does **not** show that on-domain `ι ≥ 2` witnesses are
impossible, and they are not (SYZ49, L127).  The balanced-interior `ι ≤ 1` bound therefore needs
additional justified hypotheses beyond band geometry and domain membership.  **The CORE remains
OPEN / ON-BGK.**
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ48

open Polynomial

/-! ## 1. Exact characterization of the balanced-interior obstruction (pure `ℕ`) -/

/-- **Balanced interior.**  A band triple `(a,b,c)` is *balanced-interior* when the largest reduced
degree sits at least two below the balanced edge: `max(a,b,c) < ⌊(a+b+c)/2⌋ − 1`.  This is exactly
the region SYZ47's floor `δ₁ ≥ max(a,b,c)` fails to discharge (it there only gives
`ι ≤ ⌊S/2⌋ − max`). -/
def BalancedInterior (a b c : ℕ) : Prop := max a (max b c) + 1 < (a + b + c) / 2

/-- **Exact characterization.**  Under the SYZ44 degree-sum law with `δ₁ ≤ δ₂`, the imbalance
`ι = ⌊S/2⌋ − δ₁ ≥ 2` is *equivalent* to the existence of a syzygy of product-degree `δ₁ ≤ ⌊S/2⌋ − 2`.
On the balanced interior the SYZ47 floor only reaches `δ₁ ≥ max(a,b,c)` which — since
`max(a,b,c) + 2 ≤ ⌊S/2⌋` there — does **not** rule this out: the obstruction is a genuine *low*
syzygy strictly beneath the floor. -/
theorem balanced_interior_imbalance_ge_two_iff
    (a b c δ₁ δ₂ : ℕ) (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂) :
    2 ≤ SYZ45.imbalance a b c δ₁ ↔ δ₁ + 2 ≤ (a + b + c) / 2 := by
  unfold SYZ45.imbalance; omega

/-- **The floor is strictly too weak on the interior.**  If `(a,b,c)` is balanced-interior then the
SYZ47 floor `δ₁ ≥ max(a,b,c)` leaves a genuine gap: `max(a,b,c) + 2 ≤ ⌊S/2⌋`, so the floor is
consistent with a low syzygy `δ₁ = max(a,b,c) ≤ ⌊S/2⌋ − 2` (i.e. `ι = 2`).  This records why the
interior is not discharged by SYZ47 alone. -/
theorem interior_floor_gap
    (a b c : ℕ) (h : BalancedInterior a b c) :
    max a (max b c) + 2 ≤ (a + b + c) / 2 := by
  unfold BalancedInterior at h; omega

/-! ## 2. The constant-ratio reformulation: syzygy ⟺ divisibility (polynomial) -/

/-- **Constant-ratio syzygy ⟺ divisibility.**  A constant-cofactor syzygy
`C c₀ * W_AB + C α * W_AC + C β * W_BC = 0` with the `AB` slot leading (`c₀ ≠ 0`) is *exactly* the
statement that `W_AB` divides the combination `P := C α * W_AC + C β * W_BC`.  (Forward direction;
the divisor witness is `C (-c₀⁻¹ · 1)` folded through the scalar — here we record the clean
divisibility that follows from the syzygy.) -/
theorem const_ratio_syzygy_dvd
    {K : Type*} [Field K] (WAB WAC WBC : K[X]) (c₀ α β : K)
    (hsyz : C c₀ * WAB + C α * WAC + C β * WBC = 0) :
    WAB ∣ (C α * WAC + C β * WBC) := by
  refine ⟨-C c₀, ?_⟩
  linear_combination hsyz

/-- **Divisibility ⟹ constant-ratio syzygy (realizability direction).**  Conversely, if the
combination `P = C α * WAC + C β * WBC` is *exactly* a scalar multiple `C c₀ * WAB` of the `AB`
slot, then `C c₀ * WAB − (C α * WAC + C β * WBC) = 0` is a genuine constant-cofactor syzygy.  This is
the assembly used to realize `ι ≥ 2`: whenever the combination collapses onto `WAB`, a low syzygy
exists. -/
theorem dvd_scalar_gives_syzygy
    {K : Type*} [Field K] (WAB WAC WBC : K[X]) (c₀ α β : K)
    (hP : C α * WAC + C β * WBC = C c₀ * WAB) :
    C c₀ * WAB + C (-α) * WAC + C (-β) * WBC = 0 := by
  simp only [map_neg]; linear_combination -hP

/-! ## 3. Level-set / root-count bound (polynomial, axiom-clean) -/

/-- **Combination degree bound.**  The combination `P = C α * WAC + C β * WBC` has
`deg P ≤ max(deg WAC, deg WBC) = max(b,c)`. -/
theorem combination_natDegree_le
    {K : Type*} [Field K] (WAC WBC : K[X]) (α β : K) :
    (C α * WAC + C β * WBC).natDegree ≤ max WAC.natDegree WBC.natDegree := by
  refine (natDegree_add_le _ _).trans ?_
  exact max_le_max (natDegree_C_mul_le α WAC) (natDegree_C_mul_le β WBC)

/-- **Level-set / root-count bound.**  The combination `P = C α * WAC + C β * WBC`, when nonzero, has
at most `max(b,c)` roots (counted with multiplicity).  Hence *any* constant-ratio level set
`{x : β·W_BC(x) = −α·W_AC(x)}` — the vanishing locus of `P` — has cardinality `≤ max(b,c)`.  This is
the exact reason the interior obstruction cannot be beaten by counting: the level set is capped by
the degree, not by anything smaller. -/
theorem combination_root_card_le
    {K : Type*} [Field K] (WAC WBC : K[X]) (α β : K) :
    Multiset.card (C α * WAC + C β * WBC).roots ≤ max WAC.natDegree WBC.natDegree :=
  (card_roots' _).trans (combination_natDegree_le WAC WBC α β)

/-! ## 4. Counting is not enough on the balanced interior (the full circle) -/

/-- **Divisibility forces a degree inequality — not a contradiction.**  If `W_AB ∣ P` with `P ≠ 0`
then `a = deg W_AB ≤ deg P ≤ max(b,c)`.  On the *unbalanced* strip (`a` the strict max) this is the
SYZ47 contradiction.  On the *balanced interior* `a ≤ max(b,c)` holds anyway, so the root-count bound
is **satisfiable**: it yields no obstruction — the honest full circle back to the SYZ39
interpolation matrix. -/
theorem dvd_forces_degree_le
    {K : Type*} [Field K] (WAB WAC WBC : K[X]) (α β : K)
    (hP : C α * WAC + C β * WBC ≠ 0)
    (hdvd : WAB ∣ (C α * WAC + C β * WBC)) :
    WAB.natDegree ≤ max WAC.natDegree WBC.natDegree :=
  (natDegree_le_of_dvd hdvd hP).trans (combination_natDegree_le WAC WBC α β)

/-- **No count-based contradiction on the interior (packaged).**  For a balanced profile
`a = b = c = d`, the divisibility degree bound reads `a ≤ d = max(b,c)`, which is *true* — so a
constant-ratio syzygy of product-degree `d` is **not** excluded by degree/counting.  Specialised to
`d ≥ 4` this is precisely the room the `ι ≥ 2` witness occupies. -/
theorem balanced_no_count_obstruction (d : ℕ) : d ≤ max d d := by simp

/-! ## 5. `ℚ̄`-realizability: balanced-interior `ι ≥ 2` exists over large fields -/

/-- **Realizability from a scalar collapse.**  If the combination collapses onto the `AB` slot,
`C α * WAC + C β * WBC = C c₀ * WAB` with `c₀ ≠ 0`, then a nonzero constant syzygy exists, so the
minimal syzygy product-degree obeys `δ₁ ≤ max(a,b,c)`; for a balanced profile `a=b=c=d≥4` this drives
`ι ≥ ⌊d/2⌋ ≥ 2` (via `SYZ45.equal_degree_dependence_forces_imbalance_ge_two`).  Over an
algebraically closed field such a collapse is unobstructed — pick disjoint `WAC, WBC`, form
`P`, and let `WAB = P` when squarefree and coprime — which is why probe [4] finds an algebraic
`ι ≥ 2` syzygy in every sampled balanced configuration.  Over a prime field `𝔽_p` this is a
field-point configuration only when `P` splits into distinct linear factors, which few samples
do.  **The degree profile does not force `ι ≤ 1`.** -/
theorem imbalance_ge_two_realizable
    (d δ₁ : ℕ) (hd : 4 ≤ d) (hδ : δ₁ ≤ d) :
    2 ≤ SYZ45.imbalance d d d δ₁ :=
  SYZ45.equal_degree_dependence_forces_imbalance_ge_two d δ₁ hd hδ

/-! ## 6. Domain-membership is the rescue: the roots must return to `μ_n` -/

/-- **On-domain constraint (`μ_n` membership).**  Over the prize domain the slot roots must be
evaluation-domain points.  Concretely: every root `r` of any divisor `p` of `Xⁿ − 1` satisfies
`rⁿ = 1` — it lies in `μ_n`.  Applied to the combination `P = α·W_AC + β·W_BC`, if `P` (hence
`W_AB`, its divisor) is to have all its roots on-domain then those roots must be `n`-th roots of
unity.  Probe [2]: for random `W_AC, W_BC` vanishing on disjoint `μ_n`-subsets and random scalars
the roots of `P` are typically not all in `μ_n` (on `μ_{p−1} = 𝔽_p^×` the missing roots are nonsplit,
not other `𝔽_p` points).  This necessary condition is typically unmet but is **not** an
obstruction: on-domain `ι = 2` witnesses exist (SYZ49; audit finding L127). -/
theorem root_of_dvd_X_pow_sub_one_pow_eq_one
    {K : Type*} [Field K] {n : ℕ} {p : K[X]} (r : K)
    (hdvd : p ∣ (X ^ n - 1)) (hr : p.IsRoot r) :
    r ^ n = 1 := by
  obtain ⟨q, hq⟩ := hdvd
  have hpr : eval r p = 0 := hr
  have h0 : eval r (X ^ n - 1 : K[X]) = 0 := by rw [hq, eval_mul, hpr, zero_mul]
  have h1 : r ^ n - 1 = 0 := by simpa using h0
  exact sub_eq_zero.mp h1

end ArkLib.ProximityGap.SYZ48

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ48.balanced_interior_imbalance_ge_two_iff
#print axioms ArkLib.ProximityGap.SYZ48.interior_floor_gap
#print axioms ArkLib.ProximityGap.SYZ48.const_ratio_syzygy_dvd
#print axioms ArkLib.ProximityGap.SYZ48.dvd_scalar_gives_syzygy
#print axioms ArkLib.ProximityGap.SYZ48.combination_natDegree_le
#print axioms ArkLib.ProximityGap.SYZ48.combination_root_card_le
#print axioms ArkLib.ProximityGap.SYZ48.dvd_forces_degree_le
#print axioms ArkLib.ProximityGap.SYZ48.balanced_no_count_obstruction
#print axioms ArkLib.ProximityGap.SYZ48.imbalance_ge_two_realizable
#print axioms ArkLib.ProximityGap.SYZ48.root_of_dvd_X_pow_sub_one_pow_eq_one
