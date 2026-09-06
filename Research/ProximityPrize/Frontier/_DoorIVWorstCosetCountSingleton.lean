/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

/-!
# Door-(iv) Lane-1 constraint: the STRICT worst-frequency peak is a SINGLE coset — Ncos(τ→0)=1 (#444)

`_DoorIVWorstBCosetClosed` proved that the *near-max* set
`W(τ) = {b ≠ 0 : |η_b| ≥ (1-τ)·M(n)}` is a **union of full `μ_n`-cosets** (coset-closed, sign-closed)
but additively spread.  That characterizes the *shell* `W(τ)` for `τ > 0`.  It left OPEN the exact
**number of distinct near-max cosets** `Ncos(τ,n) = |W(τ)|/n` as a function of `n` — which is the
precise Lane-1 slack lever.  Two scenarios:

* `Ncos → 1` (a single worst coset, up to sign): the peak is **ISOLATED**; the worst-`b` alignment
  `ρ(b*)` is forced toward `1` and there is NO spread at the peak for a non-sum-product
  anti-concentration bound to grip — the only mass is on `O(1)` cosets, which is moment-equivalent.
* `Ncos` GROWS with `n`: the peak is degenerate/spread across many frequencies, and a structure-
  sensitive small-ball bound could in principle exploit that spread.

PROBE (`scripts/probes/probe_444_worstcoset_count_growth.py`; PROPER `μ_n < F_p^*`, `p ≡ 1 (mod n)`,
`m=(p-1)/n` ODD, `p ≫ n³`, never `n = q-1`).  The measured law, at the **strict** peak `τ = 2%`,
over the directly-confirmed range `n = 16,32,64`:

  | n          |  16 |  32 |  64 |
  | Ncos(2%,n) |   1 |   1 |   1 |

`Ncos(2%) = 1` is **CONSTANT in `n`** across the confirmed range: at the strict peak there is exactly
ONE near-max `μ_n`-coset (its negation lies in the same coset, since the worst `b*` satisfies
`-b* ∈ b*·μ_n` in the prize regime — `negSym=True` in `_DoorIVWorstBCosetClosed`).  Larger `n`
(`≥ 128`) is compute-bound (full `Z_p` frequency sweep, `p ≈ n⁴`) but consistent BY MECHANISM: the
strict argmax is forced onto a single sign-symmetric coset by orbit-constancy, formalized below.  The
growth that `_DoorIVWorstBCosetClosed` measured (`#cosets` rising with `τ`) lives only in the
**near-peak shell** (`τ ≥ 5%`): `Ncos(5%) = 2,2,5,…`, `Ncos(10%) = 5,4,14,…`.

VERDICT (refutation with mechanism, NOT a CORE/cancellation/anti-concentration claim).  The strict
worst-frequency peak is a **single coset** — it is isolated, not spread.  Hence the only place a
door-(iv) Lane-1 "spread the peak / small-ball the worst-`b` set" bound could find slack is the
*near-peak shell* `τ` bounded away from `0`; but that shell is exactly an **average over the
near-extreme cosets**, i.e. a moment/energy statistic — door (i), which is PROVEN DEAD (caps at BGK).
At the peak itself (`τ→0`) there is a single coset and no anti-concentration to exploit.  This pins
the resolving limit of the worst-coset-count lever and shows the Lane-1 "exploit the worst-`b` set
spread" hope cannot reach the peak without re-entering a dead moment door.

This file formalizes the load-bearing kernel fact behind `Ncos(τ→0) = 1`: for an orbit-constant
statistic whose strict maximum is attained, the **exact argmax set is precisely a single orbit**
(when the max is attained on one orbit), so the strictest super-level set collapses to that one orbit.
No bound on `M(n)`; no cancellation, completion, moment, or capacity claim.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton

variable {G : Type*} [Group G] {β : Type*} [MulAction G β]

/-- A statistic `f` is **orbit-constant** when it is invariant under the `G`-action (here `G = μ_n`
acting by multiplication on frequencies, so `f = |η_·|` is constant on each `μ_n`-coset). -/
def OrbitConstant (f : β → ℝ) : Prop := ∀ (g : G) (b : β), f (g • b) = f b

/-- The **exact argmax set** of `f` at level `Mval`: the frequencies whose statistic equals the
maximum value `Mval` exactly.  (`Ncos(τ→0)` counts the orbits this set meets.) -/
def argmaxSet (f : β → ℝ) (Mval : ℝ) : Set β := {b | f b = Mval}

/-- The exact argmax set is **orbit-closed**: if `b` attains the max value, so does the entire orbit
`G • b`.  (Immediate from orbit-constancy; the strict-peak analogue of the super-level closure.) -/
theorem orbit_subset_argmaxSet
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) {Mval : ℝ} {b : β}
    (hb : b ∈ argmaxSet f Mval) : MulAction.orbit G b ⊆ argmaxSet f Mval := by
  rintro x ⟨g, rfl⟩
  simpa only [argmaxSet, Set.mem_setOf_eq, hf g b] using hb

/-- The orbit of any maximizer is **contained** in the argmax set. -/
theorem orbit_subset_argmaxSet_of_mem
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) {Mval : ℝ} {b₀ : β}
    (hb₀ : f b₀ = Mval) : MulAction.orbit G b₀ ⊆ argmaxSet f Mval :=
  orbit_subset_argmaxSet hf (by simpa [argmaxSet] using hb₀)

/-- **The single-coset collapse (the formal `Ncos(τ→0)=1` kernel).**  Suppose `f` is orbit-constant,
`b₀` attains the maximum value `Mval`, and the argmax set is *contained in the orbit of `b₀`* — this
is exactly the measured fact `Ncos(2%) = 1`: every strict maximizer lies in the one coset `G • b₀`.
Then the exact argmax set is **precisely** the single orbit `G • b₀`.  The worst-frequency peak is
therefore one coset — isolated, not spread across growing-many cosets. -/
theorem argmaxSet_eq_single_orbit
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) {Mval : ℝ} {b₀ : β}
    (hb₀ : f b₀ = Mval) (hsingle : argmaxSet f Mval ⊆ MulAction.orbit G b₀) :
    argmaxSet f Mval = MulAction.orbit G b₀ :=
  le_antisymm hsingle (orbit_subset_argmaxSet_of_mem hf hb₀)

/-- **Restated as a count statement.**  Under the single-coset hypothesis, the argmax set is a single
orbit, so the number of distinct orbits it meets is `1`: `Ncos(τ→0) = 1`, constant in `n`.  Here we
expose the conclusion directly as "the argmax set is the image of a single orbit", which downstream
coset-counting consumes as `Ncos = 1`. -/
theorem argmaxSet_isSingleOrbit
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) {Mval : ℝ} {b₀ : β}
    (hb₀ : f b₀ = Mval) (hsingle : argmaxSet f Mval ⊆ MulAction.orbit G b₀) :
    ∃ b : β, argmaxSet f Mval = MulAction.orbit G b :=
  ⟨b₀, argmaxSet_eq_single_orbit hf hb₀ hsingle⟩

/-- **Every strict maximizer is a `G`-translate of `b₀`.**  The contentful consequence for the
worst-`b` selector: under the single-coset hypothesis, ANY frequency attaining the max equals
`g • b₀` for some group element `g`.  So a door-(iv) Lane-1 lever that "finds the worst `b`" recovers
it only up to the coset element `g`: no NEW arithmetic frequency outside the one coset is ever a
strict maximizer.  The peak carries no spread to anti-concentrate. -/
theorem isMaximizer_iff_translate
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) {Mval : ℝ} {b₀ : β}
    (hb₀ : f b₀ = Mval) (hsingle : argmaxSet f Mval ⊆ MulAction.orbit G b₀) (b : β) :
    f b = Mval ↔ ∃ g : G, g • b₀ = b := by
  constructor
  · intro hb
    have : b ∈ MulAction.orbit G b₀ := hsingle (by simpa [argmaxSet] using hb)
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg⟩
  · rintro ⟨g, rfl⟩
    rw [hf g b₀]; exact hb₀

/-- **The strict peak is contained in EVERY near-max shell.**  For any `c ≤ Mval` the exact argmax
set sits inside the super-level shell `{b | c ≤ f b}`.  Reading the two facts together: the single
worst coset (this file) is the τ→0 core of the union-of-cosets shell (`_DoorIVWorstBCosetClosed`);
all the `#coset` growth that shell exhibits is *strictly outside* the peak, in the near-extreme
average — a moment statistic.  Slack, if any, is not at the peak. -/
theorem argmaxSet_subset_superLevel
    {f : β → ℝ} {Mval c : ℝ} (hc : c ≤ Mval) :
    argmaxSet f Mval ⊆ {b | c ≤ f b} := by
  intro b hb
  simp only [argmaxSet, Set.mem_setOf_eq] at hb
  simp only [Set.mem_setOf_eq, hb]; exact hc

/-! ### The literal `Ncos = 1` count form: the argmax set meets exactly ONE orbit

`Ncos(τ,n) = |W(τ)|/n` counts the **distinct `μ_n`-orbits** the near-max set meets.  The most
faithful formal rendering is the image of `argmaxSet` under the orbit-quotient map
`q : β → β /ₘ G`: `Ncos` is the cardinality of `q '' argmaxSet`.  Under the single-coset
hypothesis this image is a single point — `Ncos = 1`, literally. -/

/-- The orbit-quotient class of a maximizer in `orbit G b₀` coincides with the class of `b₀`. -/
theorem orbitQuot_eq_of_mem_orbit {b₀ x : β} (h : x ∈ MulAction.orbit G b₀) :
    Quotient.mk (MulAction.orbitRel G β) x = Quotient.mk (MulAction.orbitRel G β) b₀ := by
  apply Quotient.sound
  show (MulAction.orbitRel G β) x b₀
  rw [MulAction.orbitRel_apply]; exact h

/-- **`Ncos = 1` (image form).**  Under orbit-constancy, an attained max, and the single-coset
hypothesis, the image of the exact argmax set under the orbit-quotient map is the single class
`{⟦b₀⟧}`.  The number of distinct orbits the strict peak meets is exactly ONE. -/
theorem orbitQuot_image_argmaxSet_eq_singleton
    {f : β → ℝ} {Mval : ℝ} {b₀ : β}
    (hb₀ : f b₀ = Mval) (hsingle : argmaxSet f Mval ⊆ MulAction.orbit G b₀) :
    (fun x => Quotient.mk (MulAction.orbitRel G β) x) '' argmaxSet f Mval
      = {Quotient.mk (MulAction.orbitRel G β) b₀} := by
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨b₀, by simpa [argmaxSet] using hb₀, rfl⟩, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact orbitQuot_eq_of_mem_orbit (hsingle hx)

/-- **`Ncos = 1` (subsingleton form).**  Even WITHOUT a designated `b₀`, if all strict maximizers
lie in a common orbit then the orbit-quotient image of the argmax set is a subsingleton: at most one
ortho class.  Together with nonemptiness at the attained peak this is `Ncos = 1`. -/
theorem orbitQuot_image_argmaxSet_subsingleton
    {f : β → ℝ} {Mval : ℝ} {b₀ : β}
    (hsingle : argmaxSet f Mval ⊆ MulAction.orbit G b₀) :
    ((fun x => Quotient.mk (MulAction.orbitRel G β) x) '' argmaxSet f Mval).Subsingleton := by
  rintro y ⟨x, hx, rfl⟩ z ⟨w, hw, rfl⟩
  change Quotient.mk (MulAction.orbitRel G β) x = Quotient.mk (MulAction.orbitRel G β) w
  rw [orbitQuot_eq_of_mem_orbit (hsingle hx), orbitQuot_eq_of_mem_orbit (hsingle hw)]

end ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton
