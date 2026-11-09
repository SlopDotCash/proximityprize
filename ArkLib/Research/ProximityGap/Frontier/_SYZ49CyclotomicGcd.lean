/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Research.ProximityGap.Frontier._SYZ48BalancedInterior

/-!
# SYZ49 — the cyclotomic-GCD bedrock: max level set of `R = W_BC/W_AC` on `μ_n`

## Where this sits

SYZ48 pinned the balanced-interior kernel to a single on-domain question and *claimed* the
cyclotomic **domain-membership** condition (SYZ48 item 6: combination roots must return to `μ_n`)
is what rescues `ι ≤ 1` — the "domain is load-bearing". SYZ49 tests that claim head-on.

A constant-ratio (low) syzygy `c₀·W_AB + α·W_AC + β·W_BC = 0` with the `AB` slot carrying
(`c₀ ≠ 0`) is *exactly* `W_AB ∣ (α·W_AC + β·W_BC)` (SYZ48 `const_ratio_syzygy_dvd`). For the `AB`
slot to be band-realizable, `W_AB` must vanish on `a` points of `μ_n`, i.e.

  `deg gcd(α·W_AC + β·W_BC, Xⁿ − 1) ≥ a`.

Here `W_AC, W_BC` are the vanishing polynomials of **disjoint** `μ_n`-subsets `S_AC, S_BC` (sizes
`b, c`). The roots of `P := α·W_AC + β·W_BC` that lie in `μ_n` are *exactly* the `ω ∈ μ_n` **outside**
`S_AC ∪ S_BC` with `R(ω) := W_BC(ω)/W_AC(ω) = −α/β` — a single **level** of `R`. So

  `max_{α,β} deg gcd(α·W_AC + β·W_BC, Xⁿ − 1)  =  max level set of R on μ_n`.

## The decisive finding (probe `probe_syz49_cyclotomic_gcd.py`)

**The max level set REACHES `a`** — and *not only* via coset/binomial structure. Over the **proper**
subgroup `μ₁₂ ⊂ 𝔽₃₇^×` the exhaustive search finds **48** disjoint `(4,4,4)` triples with level set
`= 4 = a`, of which **42** are *not* single-coset (binomial). A verified explicit witness:

  `S_AC = {1,8,27,29}`, `S_BC = {6,10,11,31}`, `S_AB = {14,23,26,36}` ⊂ `μ₁₂ ⊂ 𝔽₃₇^×`,

pairwise-disjoint, squarefree, **none a coset**, with the genuine constant syzygy
`W_BC − 11·W_AC = −10·W_AB` (product-degree `4`). Ground-truth `min_syzygy_degree = 4`, so
`ι = ⌊12/2⌋ − 4 = 2` **on the prize domain**.

**Verdict (corrective).** The cyclotomic **domain-membership condition is NOT sufficient** to force
`ι ≤ 1`: an explicit on-`μ_n` `ι = 2` witness exists (proper subgroup, non-coset). SYZ48's probe [3]
found `0` violations only because it sampled *random* `μ_n` triples, which almost never carry a
constant syzygy — it never *constructed* `W_AB` from the level set. The true remaining gate is the
**full band-realizability** (SYZ42 superadditive-union / union-span geometry), **not** mere
domain-membership. The residual is unchanged in status (**CORE OPEN / ON-BGK**) but the shield is
now correctly located.

## The BGK correspondence (probe [D], identity verified)

Over `𝔽_p`, with `L =` discrete log base a primitive root,

  `L(R(ω)) = Σ_{s∈S_BC} L(ω − s) − Σ_{s∈S_AC} L(ω − s)  (mod p−1)`.

So `R` constant on a set `A` ⟺ this **additive discrete-log sum** is constant on `A` — literally an
additive-combinatorics / character-sum statement about `Σ ± L(ω − s)`. That is the **BGK wall shape**.
The two campaign walls (μ-basis imbalance and the BGK character-sum bound) meet here as *one* level-set
statement: the max level set of `R` is the max coincidence set of the additive log-phase.

## What is proved here (all axiom-clean, generic field)

1. `combination_isRoot_iff_ratio` — a domain point `ω` (with `W_AC(ω) ≠ 0`) is a root of
   `α·W_AC + β·W_BC` *iff* it sits on the level `R(ω) = −α/β`. The level-set reformulation, exactly.
2. `combination_mu_root_pow_eq_one` — every `μ_n`-membership fact for gcd roots (via SYZ48).
3. `gcd_natDegree_le_max` — the level-set / gcd cap `deg gcd(P, Xⁿ−1) ≤ max(b,c)`.
4. `full_split_gives_constant_syzygy` — if `P = C c₀ · W_AB` (all `deg P` roots return to the domain
   as `W_AB`'s roots) then a constant syzygy exists: the on-domain assembly, unobstructed by
   domain-membership.
5. `collapse_forces_imbalance_ge_two` — **the corrective implication**: if the combination
   collapses, `C α·W_AC + C β·W_BC = C c₀·W_AB` with `c₀ ≠ 0` and all three slots of degree `≤ d`,
   then every `δ₁` that lower-bounds the product-degree of all nonzero syzygies of the triple (in
   particular the minimal one) satisfies `δ₁ ≤ d`, hence `ι ≥ 2` for `d ≥ 4`.  The implication uses
   no domain-membership hypothesis, so membership cannot block it; that the collapse is realizable
   with all three slots dividing `Xⁿ−1` is the probe-verified `μ₁₂ ⊂ 𝔽₃₇` witness above (not
   kernel-checked in this file).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ49

open Polynomial

/-! ## 1. The level-set reformulation: domain root ⟺ ratio level -/

/-- **Root ⟺ level.**  For a field point `r` with `W_AC(r) ≠ 0` and `β ≠ 0`, `r` is a root of the
combination `P = C α * W_AC + C β * W_BC` *exactly* when it lies on the constant-ratio level
`R(r) = W_BC(r)/W_AC(r) = −α/β`.  This is the exact identity behind
`deg gcd(P, Xⁿ−1) = ` (size of the `R`-level set at `−α/β`): the `μ_n`-roots of `P` are precisely the
domain points on that one level. -/
theorem combination_isRoot_iff_ratio
    {K : Type*} [Field K] (WAC WBC : K[X]) (α β : K) (r : K)
    (hβ : β ≠ 0) (hac : WAC.eval r ≠ 0) :
    (C α * WAC + C β * WBC).IsRoot r ↔ WBC.eval r = (-α / β) * WAC.eval r := by
  unfold Polynomial.IsRoot
  rw [eval_add, eval_mul, eval_mul, eval_C, eval_C]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- **Domain membership of gcd roots (via SYZ48).**  Any root `r` of `gcd(P, Xⁿ−1)` — equivalently of
any divisor of `Xⁿ−1` — is an `n`-th root of unity, `rⁿ = 1`.  This is the on-domain constraint the
level set inherits: the `μ_n`-roots of `P` are the roots of `P` that also satisfy `rⁿ = 1`. -/
theorem gcd_root_pow_eq_one
    {K : Type*} [Field K] {n : ℕ} {p : K[X]} (r : K)
    (hdvd : p ∣ (X ^ n - 1)) (hr : p.IsRoot r) :
    r ^ n = 1 :=
  SYZ48.root_of_dvd_X_pow_sub_one_pow_eq_one r hdvd hr

/-! ## 2. The level-set / gcd cap -/

/-- **The gcd cap.**  Since `gcd(P, Xⁿ−1) ∣ P`, its degree is `≤ deg P ≤ max(b,c)`.  Hence the max
level set of `R` — equivalently `deg gcd(α·W_AC + β·W_BC, Xⁿ−1)` — is capped by `max(b,c)`.  For a
**balanced** band profile `b = c = a` this cap is exactly `a`: the level set can be as large as `a`,
and the probe shows it **is** (48 disjoint witnesses over `μ₁₂ ⊂ 𝔽₃₇^×`), so the cap is *tight* and
gives **no** exclusion. -/
theorem gcd_natDegree_le_max
    {K : Type*} [Field K] {n : ℕ} (WAC WBC : K[X]) (α β : K)
    (g : K[X]) (hg : g ∣ (C α * WAC + C β * WBC)) (hne : C α * WAC + C β * WBC ≠ 0) :
    g.natDegree ≤ max WAC.natDegree WBC.natDegree :=
  (natDegree_le_of_dvd hg hne).trans (SYZ48.combination_natDegree_le WAC WBC α β)

/-! ## 3. On-domain assembly: the constant syzygy is NOT obstructed by membership -/

/-- **Full split ⟹ constant syzygy.**  If the combination `P = C α · W_AC + C β · W_BC` collapses onto
`C c₀ · W_AB` (all of its `deg P` roots return to the domain as the roots of `W_AB`), then a nonzero
constant-cofactor syzygy exists.  This is SYZ48's `dvd_scalar_gives_syzygy` — recorded here as the
on-domain **assembly step**: when the level set reaches `a`, `W_AB` (deg `a`, roots in `μ_n`) *can* be
formed, and the syzygy follows.  Domain-membership does not stand in the way. -/
theorem full_split_gives_constant_syzygy
    {K : Type*} [Field K] (WAB WAC WBC : K[X]) (c₀ α β : K)
    (hP : C α * WAC + C β * WBC = C c₀ * WAB) :
    C c₀ * WAB + C (-α) * WAC + C (-β) * WBC = 0 :=
  SYZ48.dvd_scalar_gives_syzygy WAB WAC WBC c₀ α β hP

/-! ## 4. The corrective implication: a collapse forces `ι ≥ 2`, with no membership hypothesis -/

/-- **A collapse forces `ι ≥ 2` (the corrective implication).**  Suppose the balanced combination
collapses onto the `AB` slot, `C α · W_AC + C β · W_BC = C c₀ · W_AB` with `c₀ ≠ 0`, and all three
slots have degree `≤ d`.  Let `δ₁` be any lower bound for the product-degree
`max(deg(u·W_AB), deg(v·W_AC), deg(w·W_BC))` of every nonzero syzygy `(u, v, w)` of the triple —
in particular the minimal syzygy product-degree (`hmin`).  Then the constant syzygy
`(C c₀, C (-α), C (-β))` from `full_split_gives_constant_syzygy` has product-degree `≤ d`, so
`δ₁ ≤ d`, and for `d ≥ 4` the imbalance obeys `ι = ⌊3d/2⌋ − δ₁ ≥ 2`.

No domain-membership hypothesis (`W_• ∣ Xⁿ − 1`) is used: membership places no obstruction on this
implication.  That the collapse hypothesis is satisfiable with all three slots on the prize domain
is the probe-verified witness `S_AC={1,8,27,29}, S_BC={6,10,11,31}, S_AB={14,23,26,36} ⊂ μ₁₂ ⊂ 𝔽₃₇`
(non-coset) recorded in the module docstring; that witness is not kernel-checked here. -/
theorem collapse_forces_imbalance_ge_two
    {K : Type*} [Field K] (WAB WAC WBC : K[X]) (c₀ α β : K) (d δ₁ : ℕ)
    (hd : 4 ≤ d) (hc₀ : c₀ ≠ 0)
    (hdAB : WAB.natDegree ≤ d) (hdAC : WAC.natDegree ≤ d) (hdBC : WBC.natDegree ≤ d)
    (hP : C α * WAC + C β * WBC = C c₀ * WAB)
    (hmin : ∀ u v w : K[X], ¬ (u = 0 ∧ v = 0 ∧ w = 0) → u * WAB + v * WAC + w * WBC = 0 →
      δ₁ ≤ max (u * WAB).natDegree (max (v * WAC).natDegree (w * WBC).natDegree)) :
    2 ≤ SYZ45.imbalance d d d δ₁ := by
  have hsyz := full_split_gives_constant_syzygy WAB WAC WBC c₀ α β hP
  have hnz : ¬ (C c₀ = 0 ∧ C (-α) = 0 ∧ C (-β) = 0) := fun h => hc₀ (C_eq_zero.mp h.1)
  have hδ : δ₁ ≤ d :=
    (hmin _ _ _ hnz hsyz).trans <| max_le ((natDegree_C_mul_le _ _).trans hdAB) <|
      max_le ((natDegree_C_mul_le _ _).trans hdAC) ((natDegree_C_mul_le _ _).trans hdBC)
  exact SYZ48.imbalance_ge_two_realizable d δ₁ hd hδ

/-! ## 5. The reformulation packaged: gcd-degree = level-set size (statement of record) -/

/-- **Bedrock reformulation (record).**  The `μ_n`-roots of the combination `P = C α·W_AC + C β·W_BC`
are exactly the domain points `ω` (outside `S_AC ∪ S_BC`, where `W_AC(ω) ≠ 0`) on the single level
`R(ω) = −α/β`.  Combined with `gcd_natDegree_le_max`, the max over `(α,β)` of
`deg gcd(P, Xⁿ−1)` is the **max level set of `R` on `μ_n`**, capped by `max(b,c)` and — per the probe —
**attaining `a` on the balanced band**.  We record the pointwise equivalence (the count identity is
the finite sum over `μ_n` of this indicator). -/
theorem mu_root_iff_level
    {K : Type*} [Field K] {n : ℕ} (WAC WBC : K[X]) (α β : K) (r : K)
    (hβ : β ≠ 0) (hac : WAC.eval r ≠ 0) (hrn : r ^ n = 1) :
    (r ^ n = 1 ∧ (C α * WAC + C β * WBC).IsRoot r)
      ↔ (r ^ n = 1 ∧ WBC.eval r = (-α / β) * WAC.eval r) := by
  rw [combination_isRoot_iff_ratio WAC WBC α β r hβ hac]

end ArkLib.ProximityGap.SYZ49

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ49.combination_isRoot_iff_ratio
#print axioms ArkLib.ProximityGap.SYZ49.gcd_root_pow_eq_one
#print axioms ArkLib.ProximityGap.SYZ49.gcd_natDegree_le_max
#print axioms ArkLib.ProximityGap.SYZ49.full_split_gives_constant_syzygy
#print axioms ArkLib.ProximityGap.SYZ49.collapse_forces_imbalance_ge_two
#print axioms ArkLib.ProximityGap.SYZ49.mu_root_iff_level
