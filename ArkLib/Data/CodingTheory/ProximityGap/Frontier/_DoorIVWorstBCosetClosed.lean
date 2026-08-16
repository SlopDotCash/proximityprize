/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card

/-!
# Door-(iv) constraint: the worst-frequency SET is COSET-CLOSED — the b-selector is coset-blind (#444)

The prize is localized (`_DoorIVHalfMass*`) to the worst-frequency period magnitude
`M(n) = max_{b≠0} |η_b|`, where `η_b = Σ_{y∈μ_n} e_p(b·y)`.  A live door-(iv) hope (brief, Shaw-value
essay 2026-06-18, Lane 1) is to **exploit the arithmetic of the worst frequency `b`** — to find some
multiplicative/additive structure in the near-max set
`W(τ) = {b ≠ 0 : |η_b| ≥ (1-τ)·M(n)}` that a structure-sensitive (non-sum-product, non-moment)
anti-concentration bound could grip.

PROBE (`scripts/probes/probe_444_worstb_set_arithmetic.py`; proper `μ_n < F_p*`, `p ≫ n³`, structured
ODD-`m` primes, `n = 8..32`, `β ≈ 4–4.5`, never `n = q-1`).  The near-max set `W(τ)` is, in **every**
row:

* a **union of full `μ_n`-cosets** (`muOrbit = True`; `|W|` is always an exact multiple of `n`,
  `#cosets = |W|/n ∈ ℕ`).  Mechanism: `|η_b|` is constant on the coset `b·μ_n` because `μ_n` permutes
  itself, so every super-level set of `|η_b|` is a union of `μ_n`-cosets.
* **sign-symmetric** (`negSym = True`; `-b* ` is always near-max).  Mechanism: in the prize regime
  `μ_n` is closed under negation, so `η_{-b} = \overline{η_b}` and `|η_{-b}| = |η_b|`.

but is **additively SPREAD**: `|W+W|/|W|` *grows* with `n` (`7 → 16 → 43 …`), `longestAP ≤ 4`, `W` is
**not** a single multiplicative coset, **not** an AP, **not** a square-class.  So `W` is multiplicatively
structured (coset-closed + sign-closed) but carries **no finer additive structure**.

CONSEQUENCE (this file, axiom-clean).  We formalize the load-bearing fact: for **any** function
`f : β → ℝ` that is **constant on the orbits** of a group action `G ↷ β` (here `G = μ_n` acting by
multiplication, plus the negation involution), **every super-level set `{b : f b ≥ c}` is a union of
full orbits**, hence the near-max set is too; and if `f` additionally agrees under an involution `σ`
(here `σ = -·`), the super-level set is `σ`-closed.  Therefore the worst-`b` **selector is coset-blind
below coset granularity**: any "exploit the arithmetic of the worst `b`" lever can only resolve `b` up
to its `μ_n`-coset and its sign — and the probe shows there is **no** finer additive structure to
exploit (`W` is additively spread).  This bounds the resolving power of the entire door-(iv) Lane-1
"worst-`b` arithmetic" family.

This is a **refutation with mechanism** (a precisely-mapped resolution limit on the worst-`b` selector),
**not** a CORE/cancellation/anti-concentration claim: it does not bound `M(n)`; it shows the worst-`b`
set carries exactly the symmetries `f` already has (coset + sign) and the probe shows nothing finer.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed

open scoped Pointwise

variable {G : Type*} [Group G] {β : Type*} [MulAction G β]

/-- The **super-level set** of a real-valued frequency statistic `f` at threshold `c`:
the set of frequencies whose statistic is at least `c`.  (`W(τ)` is `superLevel f ((1-τ)·M)`.) -/
def superLevel (f : β → ℝ) (c : ℝ) : Set β := {b | c ≤ f b}

/-- A statistic `f` is **orbit-constant** (here: constant on each `μ_n`-coset `g • b`) when it is
invariant under the group action. -/
def OrbitConstant (f : β → ℝ) : Prop := ∀ (g : G) (b : β), f (g • b) = f b

/-- **Coset-closure of the super-level set.**  If `f` is orbit-constant, every super-level set is
closed under the action: `b` near-max ⟹ the whole coset `g • b` is near-max.  (Probe: `muOrbit=True`.) -/
theorem smul_mem_superLevel_of_orbitConstant
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) (c : ℝ) (g : G) {b : β}
    (hb : b ∈ superLevel f c) : g • b ∈ superLevel f c := by
  simpa only [superLevel, Set.mem_setOf_eq, hf g b] using hb

/-- The super-level set is a **union of full orbits**: it equals its own saturation under the
`G`-action.  (Probe: `|W|` is an exact multiple of `n`, `#cosets = |W|/n`.) -/
theorem superLevel_eq_smul_superLevel
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) (c : ℝ) (g : G) :
    superLevel f c = g • superLevel f c := by
  ext b
  constructor
  · intro hb
    refine ⟨g⁻¹ • b, ?_, by simp⟩
    have := smul_mem_superLevel_of_orbitConstant (G := G) hf c g⁻¹ hb
    simpa using this
  · rintro ⟨a, ha, rfl⟩
    exact smul_mem_superLevel_of_orbitConstant (G := G) hf c g ha

/-- The whole orbit of any near-max frequency stays near-max. -/
theorem orbit_subset_superLevel
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) (c : ℝ) {b : β}
    (hb : b ∈ superLevel f c) : MulAction.orbit G b ⊆ superLevel f c := by
  rintro x ⟨g, rfl⟩
  exact smul_mem_superLevel_of_orbitConstant (G := G) hf c g hb

/-- **Coset membership is exactly invariant.**  Multiplying a frequency by any group element neither
creates nor destroys near-max membership for an orbit-constant statistic.  Thus a worst-`b` selector
cannot distinguish points inside one multiplicative coset. -/
theorem smul_mem_superLevel_iff_of_orbitConstant
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) (c : ℝ) (g : G) {b : β} :
    g • b ∈ superLevel f c ↔ b ∈ superLevel f c := by
  constructor
  · intro hb
    have hback := smul_mem_superLevel_of_orbitConstant (G := G) hf c g⁻¹ hb
    simpa using hback
  · intro hb
    exact smul_mem_superLevel_of_orbitConstant (G := G) hf c g hb

/-- **Argmax membership is coset-blind.**  If `b` attains the supremum value `Mval` of `f`
(`f b = Mval` and `Mval` is an upper bound), then the ENTIRE coset `g • b` also attains it: the worst
frequency is never an isolated point, it is a full `μ_n`-coset.  (Probe: worst-`b` row is one coset.) -/
theorem smul_eq_of_isArgmax
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) {b : β} {Mval : ℝ}
    (hb : f b = Mval) (g : G) : f (g • b) = Mval := by
  rw [hf g b]; exact hb

/-! ### Sign-symmetry: the involution layer (`σ = -·`, `negSym = True`) -/

/-- An involution `σ : β → β` under which the statistic is invariant (here `σ = (-·)` and
`f (-b) = f b` because `μ_n` is closed under negation, so `|η_{-b}| = |η_b|`). -/
def InvolutionConstant (σ : β → β) (f : β → ℝ) : Prop :=
  Function.Involutive σ ∧ ∀ b, f (σ b) = f b

/-- **Sign-closure of the super-level set.**  Under an `f`-respecting involution, the near-max set is
involution-closed: `b` near-max ⟹ `σ b` (e.g. `-b`) near-max.  (Probe: `negSym=True`, `-b*` near-max.) -/
theorem sigma_mem_superLevel
    {f : β → ℝ} {σ : β → β} (hσ : InvolutionConstant σ f) (c : ℝ) {b : β}
    (hb : b ∈ superLevel f c) : σ b ∈ superLevel f c := by
  simpa only [superLevel, Set.mem_setOf_eq, hσ.2 b] using hb

/-- The super-level set is **mapped onto itself** by the `f`-respecting involution: `σ '' W = W`. -/
theorem image_sigma_superLevel
    {f : β → ℝ} {σ : β → β} (hσ : InvolutionConstant σ f) (c : ℝ) :
    σ '' superLevel f c = superLevel f c := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact sigma_mem_superLevel hσ c ha
  · intro hb
    exact ⟨σ b, sigma_mem_superLevel hσ c hb, hσ.1 b⟩

/-- **Sign-pair membership is exactly invariant.**  The involution layer is not just closed in one
direction: `b` is near-max exactly when `σ b` is near-max.  For the prize statistic this says `b` and
`-b` cannot be separated by a worst-frequency selector. -/
theorem sigma_mem_superLevel_iff
    {f : β → ℝ} {σ : β → β} (hσ : InvolutionConstant σ f) (c : ℝ) {b : β} :
    σ b ∈ superLevel f c ↔ b ∈ superLevel f c := by
  constructor
  · intro hb
    have hback := sigma_mem_superLevel hσ c hb
    simpa [hσ.1 b] using hback
  · intro hb
    exact sigma_mem_superLevel hσ c hb

/-- **The combined symmetry group of the worst-`b` set.**  Putting the two layers together: the
near-max set is closed under BOTH the `μ_n`-action AND the negation involution.  Any b-arithmetic lever
sees the worst frequency only through these symmetries (coset + sign); the probe shows there is no
finer additive structure (`W` additively spread, `|W+W|/|W|` grows, `longestAP ≤ 4`).  Hence the
worst-`b` selector is **coset-and-sign-blind** below this granularity — the door-(iv) Lane-1 limit. -/
theorem superLevel_smul_and_sigma_closed
    {f : β → ℝ} {σ : β → β} (hf : OrbitConstant (G := G) f) (hσ : InvolutionConstant σ f)
    (c : ℝ) :
    (∀ (g : G) (b : β), b ∈ superLevel f c → g • b ∈ superLevel f c) ∧
      (∀ (b : β), b ∈ superLevel f c → σ b ∈ superLevel f c) :=
  ⟨fun g _ hb => smul_mem_superLevel_of_orbitConstant hf c g hb,
   fun _ hb => sigma_mem_superLevel hσ c hb⟩

/-- **Coset-plus-sign membership is exactly invariant.**  If the statistic is constant on `G`-orbits
and under the involution `σ`, then applying any multiplicative coset move and then the sign involution
neither creates nor destroys near-max membership.  This is the direct selector-facing form of the
Lane-1 obstruction: the worst-`b` set cannot resolve points below the generated coset/sign fiber. -/
theorem sigma_smul_mem_superLevel_iff
    {f : β → ℝ} {σ : β → β} (hf : OrbitConstant (G := G) f) (hσ : InvolutionConstant σ f)
    (c : ℝ) (g : G) {b : β} :
    σ (g • b) ∈ superLevel f c ↔ b ∈ superLevel f c := by
  unfold superLevel
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hσ.2 (g • b), hf g b]

/-- Closure form of the combined coset/sign fiber: from one near-max frequency `b`, every signed
coset mate `σ (g • b)` is also near-max. -/
theorem sigma_smul_mem_superLevel_of_orbitConstant
    {f : β → ℝ} {σ : β → β} (hf : OrbitConstant (G := G) f) (hσ : InvolutionConstant σ f)
    (c : ℝ) (g : G) {b : β} (hb : b ∈ superLevel f c) :
    σ (g • b) ∈ superLevel f c :=
  (sigma_smul_mem_superLevel_iff hf hσ c g).mpr hb

/-- **The combined coset/sign map permutes every super-level set.**  The map
`b ↦ σ (g • b)` sends the near-max set onto itself, not merely into itself.  This is the set-level
form of the selector granularity wall: once orbit-constancy and sign-invariance are present, the
generated coset/sign fiber is an internal permutation of every threshold set, so no worst-`b` rule
based only on that statistic can choose a distinguished representative inside the fiber. -/
theorem image_sigma_smul_superLevel
    {f : β → ℝ} {σ : β → β} (hf : OrbitConstant (G := G) f) (hσ : InvolutionConstant σ f)
    (c : ℝ) (g : G) :
    (fun b : β => σ (g • b)) '' superLevel f c = superLevel f c := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact sigma_smul_mem_superLevel_of_orbitConstant hf hσ c g ha
  · intro hb
    have hsig : σ b ∈ superLevel f c := (sigma_mem_superLevel_iff hσ c).mpr hb
    have hpre : g⁻¹ • σ b ∈ superLevel f c :=
      (smul_mem_superLevel_iff_of_orbitConstant (G := G) hf c g⁻¹).mpr hsig
    refine ⟨g⁻¹ • σ b, hpre, ?_⟩
    simp [hσ.1 b]

/-- A threshold set containing a point with a genuinely different coset mate cannot be a singleton.
This is the finite selector obstruction in its sharpest local form: as soon as the action has a
nontrivial mate `g • b ≠ b`, any super-level set containing `b` also contains another point. -/
theorem superLevel_ne_singleton_of_nontrivial_smul
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) (c : ℝ) {b : β} (hb : b ∈ superLevel f c)
    {g : G} (hmove : g • b ≠ b) :
    superLevel f c ≠ ({b} : Set β) := by
  intro hsingle
  have hgb : g • b ∈ superLevel f c :=
    smul_mem_superLevel_of_orbitConstant (G := G) hf c g hb
  have hgb_mem_singleton : g • b ∈ ({b} : Set β) := by
    simpa [hsingle] using hgb
  exact hmove (by simpa using hgb_mem_singleton)

/-- Combined coset/sign singleton obstruction.  If the signed coset mate `σ (g • b)` is genuinely
different from `b`, then no super-level set containing `b` can be exactly `{b}`.  Thus a worst-`b`
rule cannot isolate a frequency unless the whole generated coset/sign fiber has collapsed to that
point. -/
theorem superLevel_ne_singleton_of_nontrivial_sigma_smul
    {f : β → ℝ} {σ : β → β} (hf : OrbitConstant (G := G) f) (hσ : InvolutionConstant σ f)
    (c : ℝ) {b : β} (hb : b ∈ superLevel f c) {g : G} (hmove : σ (g • b) ≠ b) :
    superLevel f c ≠ ({b} : Set β) := by
  intro hsingle
  have hgb : σ (g • b) ∈ superLevel f c :=
    sigma_smul_mem_superLevel_of_orbitConstant hf hσ c g hb
  have hgb_mem_singleton : σ (g • b) ∈ ({b} : Set β) := by
    simpa [hsingle] using hgb
  exact hmove (by simpa using hgb_mem_singleton)

/-! ### Finite cardinal floor: a near-max threshold contains a full free orbit -/

/-- Finite version of `superLevel`, used to state cardinal floors without quotient machinery. -/
noncomputable def superLevelFinset [Fintype β] (f : β → ℝ) (c : ℝ) : Finset β :=
  Finset.univ.filter fun b => c ≤ f b

/-- Membership in the finite super-level set is the same as membership in `superLevel`. -/
theorem mem_superLevelFinset [Fintype β] {f : β → ℝ} {c : ℝ} {b : β} :
    b ∈ superLevelFinset f c ↔ b ∈ superLevel f c := by
  classical
  simp [superLevelFinset, superLevel]

/-- **Orbit-size cardinal floor.**  In a finite free orbit, one near-max frequency forces at least
`|G|` near-max frequencies: the entire orbit injects into the finite super-level set.  This is the
cardinality form of the Door-IV worst-`b` coset-closure mechanism (`|W|` is forced to pay whole
cosets before any finer arithmetic selector can act). -/
theorem card_group_le_superLevelFinset_of_free_orbit
    [Fintype G] [Fintype β]
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) (c : ℝ) {b : β}
    (hb : b ∈ superLevel f c)
    (hfree : ∀ {g h : G}, g • b = h • b → g = h) :
    Fintype.card G ≤ (superLevelFinset f c).card := by
  classical
  let φ : G → β := fun g => g • b
  have hφinj : Function.Injective φ := by
    intro g h hgh
    exact hfree hgh
  have hsubset : (Finset.univ.image φ) ⊆ superLevelFinset f c := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨g, _hg, rfl⟩
    exact (mem_superLevelFinset (f := f) (c := c)).2
      (smul_mem_superLevel_of_orbitConstant (G := G) hf c g hb)
  calc
    Fintype.card G = (Finset.univ.image φ).card := by
      symm
      exact Finset.card_image_of_injective Finset.univ hφinj
    _ ≤ (superLevelFinset f c).card := Finset.card_le_card hsubset

/-- Combined coset/sign cardinal floor.  If the generated signed-coset map `g ↦ σ(g•b)` is
injective, then a threshold set containing `b` contains at least `|G|` signed coset mates.  Thus the
worst-frequency selector cannot be point-sized or sub-coset-sized unless this whole signed fiber
collapses. -/
theorem card_group_le_superLevelFinset_of_free_sigma_orbit
    [Fintype G] [Fintype β]
    {f : β → ℝ} {σ : β → β} (hf : OrbitConstant (G := G) f)
    (hσ : InvolutionConstant σ f) (c : ℝ) {b : β}
    (hb : b ∈ superLevel f c)
    (hfree : ∀ {g h : G}, σ (g • b) = σ (h • b) → g = h) :
    Fintype.card G ≤ (superLevelFinset f c).card := by
  classical
  let φ : G → β := fun g => σ (g • b)
  have hφinj : Function.Injective φ := by
    intro g h hgh
    exact hfree hgh
  have hsubset : (Finset.univ.image φ) ⊆ superLevelFinset f c := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨g, _hg, rfl⟩
    exact (mem_superLevelFinset (f := f) (c := c)).2
      (sigma_smul_mem_superLevel_of_orbitConstant hf hσ c g hb)
  calc
    Fintype.card G = (Finset.univ.image φ).card := by
      symm
      exact Finset.card_image_of_injective Finset.univ hφinj
    _ ≤ (superLevelFinset f c).card := Finset.card_le_card hsubset

/-- **Actual-orbit cardinal floor.**  Even without freeness, a near-max point forces the finite
super-level set to contain the whole image of its orbit map `g ↦ g • b`.  Thus any proposed
worst-frequency selector must pay the cardinality of the *actual* coset fiber; stabilizers are the only
way to shrink the coset bill below `|G|`. -/
theorem card_orbitImage_le_superLevelFinset
    [Fintype G] [Fintype β] [DecidableEq β]
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) (c : ℝ) {b : β}
    (hb : b ∈ superLevel f c) :
    (Finset.univ.image (fun g : G => g • b)).card ≤ (superLevelFinset f c).card := by
  classical
  apply Finset.card_le_card
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨g, _hg, rfl⟩
  exact (mem_superLevelFinset (f := f) (c := c)).2
    (smul_mem_superLevel_of_orbitConstant (G := G) hf c g hb)

/-- **Actual signed-fiber cardinal floor.**  With sign symmetry included, a near-max point forces the
finite super-level set to contain the full image of `g ↦ σ (g • b)`.  This is the non-free version of
the signed coset floor: any sub-fiber-sized selector must exhibit collisions in the signed orbit map,
not merely invoke the worst-`b` statistic. -/
theorem card_sigmaOrbitImage_le_superLevelFinset
    [Fintype G] [Fintype β] [DecidableEq β]
    {f : β → ℝ} {σ : β → β} (hf : OrbitConstant (G := G) f)
    (hσ : InvolutionConstant σ f) (c : ℝ) {b : β}
    (hb : b ∈ superLevel f c) :
    (Finset.univ.image (fun g : G => σ (g • b))).card ≤ (superLevelFinset f c).card := by
  classical
  apply Finset.card_le_card
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨g, _hg, rfl⟩
  exact (mem_superLevelFinset (f := f) (c := c)).2
    (sigma_smul_mem_superLevel_of_orbitConstant hf hσ c g hb)

/-- **Singleton selector collapse criterion.**  If a finite super-level set containing `b` is a
singleton, then the actual orbit image of `b` has cardinal one.  Equivalently, a point-sized worst-`b`
selector is possible only after the coset fiber has completely collapsed. -/
theorem orbitImage_card_eq_one_of_superLevelFinset_card_eq_one
    [Fintype G] [Fintype β] [DecidableEq β]
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) (c : ℝ) {b : β}
    (hb : b ∈ superLevel f c) (hcard : (superLevelFinset f c).card = 1) :
    (Finset.univ.image (fun g : G => g • b)).card = 1 := by
  classical
  have hle := card_orbitImage_le_superLevelFinset (G := G) hf c hb
  have hnonempty : 0 < (Finset.univ.image (fun g : G => g • b)).card := by
    exact Finset.card_pos.mpr ⟨(1 : G) • b, Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, rfl⟩⟩
  omega

/-- Signed singleton collapse criterion.  A singleton near-max set containing `b` forces the signed
coset image `g ↦ σ(g•b)` to have cardinal one.  Thus sign/coset symmetries cannot coexist with an
isolated worst frequency unless the entire signed fiber is degenerate. -/
theorem sigmaOrbitImage_card_eq_one_of_superLevelFinset_card_eq_one
    [Fintype G] [Fintype β] [DecidableEq β]
    {f : β → ℝ} {σ : β → β} (hf : OrbitConstant (G := G) f)
    (hσ : InvolutionConstant σ f) (c : ℝ) {b : β}
    (hb : b ∈ superLevel f c) (hcard : (superLevelFinset f c).card = 1) :
    (Finset.univ.image (fun g : G => σ (g • b))).card = 1 := by
  classical
  have hle := card_sigmaOrbitImage_le_superLevelFinset (G := G) hf hσ c hb
  have hnonempty : 0 < (Finset.univ.image (fun g : G => σ (g • b))).card := by
    exact Finset.card_pos.mpr ⟨σ ((1 : G) • b), Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, rfl⟩⟩
  omega

/-- Small-threshold contrapositive of the actual-orbit floor.  If a finite super-level set has
cardinality below the actual orbit image of `b`, then `b` cannot be near-max.  This is the sharp
selector audit hook when the action has a stabilizer: the required budget is the observed fiber size,
not the ambient group size. -/
theorem not_mem_superLevel_of_card_superLevelFinset_lt_orbitImage
    [Fintype G] [Fintype β] [DecidableEq β]
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) (c : ℝ) {b : β}
    (hcard : (superLevelFinset f c).card <
      (Finset.univ.image (fun g : G => g • b)).card) :
    ¬ b ∈ superLevel f c := by
  intro hb
  have hle := card_orbitImage_le_superLevelFinset (G := G) hf c hb
  exact (not_lt_of_ge hle) hcard

/-- Signed-fiber version of the sharp small-threshold contrapositive.  If the reported threshold set
is smaller than the actual signed-coset image of `b`, then `b` is not in that threshold set. -/
theorem not_mem_superLevel_of_card_superLevelFinset_lt_sigmaOrbitImage
    [Fintype G] [Fintype β] [DecidableEq β]
    {f : β → ℝ} {σ : β → β} (hf : OrbitConstant (G := G) f)
    (hσ : InvolutionConstant σ f) (c : ℝ) {b : β}
    (hcard : (superLevelFinset f c).card <
      (Finset.univ.image (fun g : G => σ (g • b))).card) :
    ¬ b ∈ superLevel f c := by
  intro hb
  have hle := card_sigmaOrbitImage_le_superLevelFinset (G := G) hf hσ c hb
  exact (not_lt_of_ge hle) hcard

/-- Small-threshold contrapositive of the orbit-size floor.  If a finite super-level set has cardinal
strictly smaller than `|G|`, then it contains no point whose `G`-orbit injects.  This is the audit form
for any proposed worst-`b` selector that advertises a sub-coset-sized near-max set. -/
theorem not_exists_free_orbit_mem_of_card_superLevelFinset_lt_group
    [Fintype G] [Fintype β]
    {f : β → ℝ} (hf : OrbitConstant (G := G) f) (c : ℝ)
    (hcard : (superLevelFinset f c).card < Fintype.card G) :
    ¬ ∃ b : β, b ∈ superLevel f c ∧ ∀ {g h : G}, g • b = h • b → g = h := by
  rintro ⟨b, hb, hfree⟩
  have hle := card_group_le_superLevelFinset_of_free_orbit (G := G) hf c hb hfree
  exact (not_lt_of_ge hle) hcard

/-- Signed-fiber small-threshold contrapositive.  A sub-`|G|` threshold set cannot contain a point whose
signed coset fiber `g ↦ σ(g•b)` injects.  Thus any genuinely free signed coset action forces the
near-max set to pay at least one whole signed fiber. -/
theorem not_exists_free_sigma_orbit_mem_of_card_superLevelFinset_lt_group
    [Fintype G] [Fintype β]
    {f : β → ℝ} {σ : β → β} (hf : OrbitConstant (G := G) f)
    (hσ : InvolutionConstant σ f) (c : ℝ)
    (hcard : (superLevelFinset f c).card < Fintype.card G) :
    ¬ ∃ b : β, b ∈ superLevel f c ∧ ∀ {g h : G}, σ (g • b) = σ (h • b) → g = h := by
  rintro ⟨b, hb, hfree⟩
  have hle := card_group_le_superLevelFinset_of_free_sigma_orbit (G := G) hf hσ c hb hfree
  exact (not_lt_of_ge hle) hcard

end ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed

#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.smul_mem_superLevel_iff_of_orbitConstant
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.sigma_mem_superLevel_iff
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.sigma_smul_mem_superLevel_iff
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.sigma_smul_mem_superLevel_of_orbitConstant
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.image_sigma_smul_superLevel
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.superLevel_ne_singleton_of_nontrivial_smul
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.superLevel_ne_singleton_of_nontrivial_sigma_smul
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.card_orbitImage_le_superLevelFinset
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.card_sigmaOrbitImage_le_superLevelFinset
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.orbitImage_card_eq_one_of_superLevelFinset_card_eq_one
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.sigmaOrbitImage_card_eq_one_of_superLevelFinset_card_eq_one
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.not_mem_superLevel_of_card_superLevelFinset_lt_orbitImage
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.not_mem_superLevel_of_card_superLevelFinset_lt_sigmaOrbitImage
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.card_group_le_superLevelFinset_of_free_orbit
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.card_group_le_superLevelFinset_of_free_sigma_orbit
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.not_exists_free_orbit_mem_of_card_superLevelFinset_lt_group
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCosetClosed.not_exists_free_sigma_orbit_mem_of_card_superLevelFinset_lt_group
