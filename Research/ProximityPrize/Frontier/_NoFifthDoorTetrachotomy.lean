/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# No-fifth-door tetrachotomy capstone for the proximity prize (#444, Lane 3)

Shaw's "Shaw Value" synthesis essay (#444, 2026-06-18) proves a *tetrachotomy with no fifth door*:
every conceivable mechanism for bounding the worst-frequency monomial-sum sup `M(n)` is one of

* **door (i)**   moment / symmetric-function  — caps at the BGK scale,
* **door (ii)**  `√q`-completion              — overshoots the BGK scale,
* **door (iii)** extreme-value / equidistribution — caps at the BGK scale,
* **door (iv)**  a genuinely new evaluation of the monomial sum (the only live door).

Doors (i)-(iii) are *proven dead*: each produces a certified bound no smaller than the **BGK scale**
`bgkScale n L = √(n·L)` (`L = log(p/n)`), which strictly exceeds the **prize scale**
`prizeScale n = √n` whenever the thinness index `L > 1` (the prize regime has `L = log(p/n) ≫ 1`).
Hence no door-(i)/(ii)/(iii) mechanism can certify the prize-scale bound `M = O(√n)`.

This module locks that prose into **kernel-checked statements**:

* `prizeScale_lt_bgkScale` — the strict scale separation `√n < √(n·L)` for `L > 1`, `n > 0`.
* `DoorType` / `Mechanism` — a finite classification of bound mechanisms by door.
* `Mechanism.OvershootsBGK` — the door-(i)/(ii)/(iii) obstruction: the certified bound is `≥ bgkScale`.
* `prizeScale_not_certified_of_overshoot` — an overshooting mechanism cannot certify a prize-scale
  bound: if it certifies `M ≤ certScale`, and `certScale ≥ bgkScale`, then it does **not** witness
  `M ≤ prizeScale` once `M` actually sits at the prize floor with slack, in the regime `L > 1`.
* `forces_doorIV` — **the no-fifth-door capstone.**  Any mechanism that certifies a prize-scale bound
  in the regime `L > 1` must be a door-(iv) mechanism; doors (i)-(iii) are excluded by overshoot.

Scope: this is the Lane-3 *tetrachotomy backbone*.  It proves the **separation + exclusion** that
makes "door (iv) is the only live door" a kernel-checked fact rather than prose.  It does **not**
prove the prize inequality, give any anti-concentration for the monomial phase set, or claim door
(iv) is achievable — door (iv) being the *only remaining* door is exactly the open problem.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy

open Real

/-- The BGK / symmetric-function scale `√(n·L)`.  Every door-(i)/(ii)/(iii) mechanism produces a
certified bound no smaller than this.  Here `n` is the subgroup size and `L` the logarithmic
thinness index (e.g. `log (p / n)`). -/
noncomputable def bgkScale (n L : ℝ) : ℝ := Real.sqrt (n * L)

/-- The prize target scale `√n` (square-root cancellation over the thin subgroup). -/
noncomputable def prizeScale (n : ℝ) : ℝ := Real.sqrt n

/-- Positivity of the prize scale. -/
theorem prizeScale_pos {n : ℝ} (hn : 0 < n) : 0 < prizeScale n :=
  Real.sqrt_pos.2 hn

/-- Positivity of the BGK scale. -/
theorem bgkScale_pos {n L : ℝ} (hn : 0 < n) (hL : 0 < L) : 0 < bgkScale n L :=
  Real.sqrt_pos.2 (mul_pos hn hL)

/-- **Scale separation.**  In the thin prize regime `L > 1`, the BGK scale strictly exceeds the prize
scale: `√n < √(n·L)`.  This is the quantitative core of "doors (i)-(iii) overshoot": a mechanism
capped at `bgkScale` is a strict `√L`-factor above the prize floor and so cannot reach `√n`. -/
theorem prizeScale_lt_bgkScale {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    prizeScale n < bgkScale n L := by
  unfold prizeScale bgkScale
  have h1 : n < n * L := by nlinarith [hn]
  exact Real.sqrt_lt_sqrt (le_of_lt hn) h1

/-- The closed ratio of the BGK scale to the prize scale is `√L`: a mechanism capped at `bgkScale`
is exactly a `√L` factor above the prize floor. -/
theorem bgkScale_div_prizeScale {n L : ℝ} (hn : 0 < n) (hL : 0 ≤ L) :
    bgkScale n L / prizeScale n = Real.sqrt L := by
  unfold bgkScale prizeScale
  rw [Real.sqrt_mul (le_of_lt hn)]
  have hsn : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
  field_simp

/-- The four doors of Shaw's tetrachotomy.  Doors (i)-(iii) are the *proven-dead* mechanism classes;
door (iv) is the only live door. -/
inductive DoorType
  /-- door (i): moment / symmetric-function bound (caps at BGK). -/
  | moment
  /-- door (ii): `√q`-completion (overshoots BGK). -/
  | completion
  /-- door (iii): extreme-value / equidistribution (caps at BGK). -/
  | extremeValue
  /-- door (iv): a genuinely new evaluation of the monomial sum (the only live door). -/
  | newEvaluation
  deriving DecidableEq, Repr

/-- A bound mechanism: its door class and the scale at which it certifies the worst-frequency sup.
`certScale` is the bound it produces, i.e. the mechanism certifies `M ≤ certScale`. -/
structure Mechanism where
  /-- which of the four doors the mechanism belongs to. -/
  door : DoorType
  /-- the scale of the certified bound: the mechanism witnesses `M ≤ certScale`. -/
  certScale : ℝ

/-- The door-(i)/(ii)/(iii) obstruction made into a predicate: the mechanism's certified scale is no
smaller than the BGK scale.  This is the formal content of Shaw's Lever refutations A-D (each named
non-door-(iv) lever was shown to bottom out at or above `bgkScale n L`); see the per-lever
obstruction theorems (`resonance_ceiling_below_prize_floor`, `coeff_route_loose`, etc.) in
`CampaignProvenIndex`. -/
def Mechanism.OvershootsBGK (m : Mechanism) (n L : ℝ) : Prop :=
  bgkScale n L ≤ m.certScale

/-- A door is *non-door-(iv)* exactly when it is one of moment / completion / extreme-value. -/
def DoorType.isClassical : DoorType → Prop
  | .moment => True
  | .completion => True
  | .extremeValue => True
  | .newEvaluation => False

/-- The finite tetrachotomy has an exact complement: a door is classical iff it is not the live
door `(iv)`. This packages the "no fifth door" bookkeeping as a kernel statement, so later capstones
can use `d.isClassical` and `d ≠ newEvaluation` interchangeably without re-case-splitting. -/
theorem DoorType.isClassical_iff_ne_newEvaluation (d : DoorType) :
    d.isClassical ↔ d ≠ DoorType.newEvaluation := by
  cases d <;> simp [DoorType.isClassical]

/-- Dual form of the finite tetrachotomy complement: the only non-classical door is door `(iv)`. -/
theorem DoorType.not_classical_iff_eq_newEvaluation (d : DoorType) :
    ¬ d.isClassical ↔ d = DoorType.newEvaluation := by
  rw [DoorType.isClassical_iff_ne_newEvaluation]
  constructor
  · exact Classical.not_not.mp
  · intro h hne
    exact hne h

/-- A mechanism is non-classical exactly when its door is the live door `(iv)`. -/
theorem Mechanism.not_classical_iff_doorIV (m : Mechanism) :
    ¬ m.door.isClassical ↔ m.door = DoorType.newEvaluation :=
  DoorType.not_classical_iff_eq_newEvaluation m.door

/-- **Overshoot ⇒ above the prize floor.**  In the regime `L > 1`, a mechanism whose certified scale
is at least the BGK scale has a certified scale strictly above the prize scale: it certifies only
`M ≤ certScale` with `certScale > √n`, never a prize-scale bound. -/
theorem certScale_gt_prizeScale_of_overshoot {m : Mechanism} {n L : ℝ}
    (hn : 0 < n) (hL : 1 < L) (hover : m.OvershootsBGK n L) :
    prizeScale n < m.certScale :=
  lt_of_lt_of_le (prizeScale_lt_bgkScale hn hL) hover

/-- **No classical door certifies a prize-scale bound.**  If a mechanism overshoots BGK (the proven
fate of every door-(i)/(ii)/(iii) lever) in the regime `L > 1`, then its certified scale cannot be
`≤ prizeScale n`: the prize-scale certificate is impossible through that mechanism. -/
theorem not_certifies_prizeScale_of_overshoot {m : Mechanism} {n L : ℝ}
    (hn : 0 < n) (hL : 1 < L) (hover : m.OvershootsBGK n L) :
    ¬ (m.certScale ≤ prizeScale n) := by
  intro hle
  exact absurd (lt_of_lt_of_le (certScale_gt_prizeScale_of_overshoot hn hL hover) hle)
    (lt_irrefl _)

/-- **No-fifth-door capstone.**  Suppose every classical door (moment / completion / extreme-value)
overshoots BGK in the regime `L > 1` (the proven Lever A-D refutations), and a mechanism `m`
certifies a prize-scale bound `m.certScale ≤ prizeScale n`.  Then `m` is **not** a classical door —
its door is `newEvaluation` (door (iv)).  Door (iv) is the only door through which a prize-scale
certificate can pass; there is no fifth door and no classical door survives. -/
theorem forces_doorIV {m : Mechanism} {n L : ℝ}
    (hn : 0 < n) (hL : 1 < L)
    (hclassicalOvershoots :
      ∀ m' : Mechanism, m'.door.isClassical → m'.OvershootsBGK n L)
    (hcert : m.certScale ≤ prizeScale n) :
    m.door = DoorType.newEvaluation := by
  -- if `m` were classical it would overshoot, contradicting the prize-scale certificate.
  have hnotClassical : ¬ m.door.isClassical := by
    intro hcl
    exact not_certifies_prizeScale_of_overshoot hn hL (hclassicalOvershoots m hcl) hcert
  cases hd : m.door with
  | moment => exact absurd (by rw [hd]; trivial) hnotClassical
  | completion => exact absurd (by rw [hd]; trivial) hnotClassical
  | extremeValue => exact absurd (by rw [hd]; trivial) hnotClassical
  | newEvaluation => rfl

/-- **No-fifth-door capstone, existential form.**  Under the same classical-overshoot hypothesis, any
mechanism certifying a prize-scale bound must come from the single live door (iv): the set of
prize-certifying mechanisms is contained in the door-(iv) mechanisms. -/
theorem prizeCertifying_subset_doorIV {n L : ℝ}
    (hn : 0 < n) (hL : 1 < L)
    (hclassicalOvershoots :
      ∀ m' : Mechanism, m'.door.isClassical → m'.OvershootsBGK n L) :
    ∀ m : Mechanism, m.certScale ≤ prizeScale n → m.door = DoorType.newEvaluation :=
  fun _ hcert => forces_doorIV hn hL hclassicalOvershoots hcert

/-! ## The door-(iv) target corridor `[√n, √(n·L)]`

The exclusion above says doors (i)-(iii) bottom out at the BGK ceiling `bgkScale n L = √(n·L)`, while
the Plancherel/RMS lower bound pins `prizeScale n = √n ≤ M` from below.  Hence the worst-frequency sup
`M` lives in the corridor `[√n, √(n·L)]`, and the *entire remaining door-(iv) content* is to shave the
multiplicative `√L` factor from the BGK ceiling down to the prize floor.  This differs from the trivial
`[√n, n]` Shaw-value bracket: here the ceiling is the BGK scale (what doors (i)-(iii) actually deliver),
not the trivial `n`. -/

/-- **Door-(iv) target corridor.**  Given the Plancherel floor `√n ≤ M` and any classical door's BGK
ceiling `M ≤ √(n·L)`, the worst-frequency sup `M` lies in the corridor `[prizeScale n, bgkScale n L]`.
The prize is exactly the lower endpoint; doors (i)-(iii) only reach the upper endpoint. -/
theorem mem_doorIV_corridor {M n L : ℝ}
    (hfloor : prizeScale n ≤ M) (hceil : M ≤ bgkScale n L) :
    prizeScale n ≤ M ∧ M ≤ bgkScale n L :=
  ⟨hfloor, hceil⟩

/-- **The corridor is genuinely nonempty with positive width** in the prize regime `L > 1`: the floor
is strictly below the ceiling (`√n < √(n·L)`), so the door-(iv) shave is a real `√L`-factor gap, not a
degenerate point. -/
theorem doorIV_corridor_width_pos {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    prizeScale n < bgkScale n L :=
  prizeScale_lt_bgkScale hn hL

/-- **The BGK ceiling is exactly the prize floor scaled by `√L`.**  Pins the door-(iv) obligation
quantitatively: door (iv) must remove precisely the factor `√L = √(log(p/n))` separating the BGK
ceiling that doors (i)-(iii) deliver from the prize floor.  (`bgkScale n L = √L · prizeScale n`.) -/
theorem bgkScale_eq_sqrtL_mul_prizeScale {n L : ℝ} (hn : 0 ≤ n) (hL : 0 ≤ L) :
    bgkScale n L = Real.sqrt L * prizeScale n := by
  unfold bgkScale prizeScale
  rw [Real.sqrt_mul hn, mul_comm]

/-! ## Discharging the door-(ii) (√q-completion) overshoot from the PROVEN completion ceiling

The abstract `OvershootsBGK` hypothesis is not a postulate for the completion door: it is *discharged*
by the proven √q-completion ceiling `M ≤ √q` (`worstPeriod_torsion_le_sqrt_card`, the classical
Polya-Vinogradov/Gauss-sum bound on each period over a torsion subgroup).  The completion mechanism
certifies the *scale* `completionScale q = √q`.  In the prize regime `q = n^β`, `β ≈ 4-5`, so
`q ≥ n·L` whenever `L ≤ q/n = n^{β-1}` (always true at the prize, where `L = log(p/n) ≪ n`).  Under that
regime fact the completion scale `√q` is `≥ bgkScale n L = √(n·L)`: door (ii) overshoots BGK, exactly
as the tetrachotomy claims, with NO extra assumption beyond the proven ceiling. -/

/-- The √q-completion scale that the door-(ii) mechanism certifies (`M ≤ √q`). -/
noncomputable def completionScale (q : ℝ) : ℝ := Real.sqrt q

/-- **Door-(ii) overshoot, discharged.**  In the prize regime, the field size dominates the BGK
argument: `n·L ≤ q` (since `q = n^β ≥ n² ≥ n·L` for `L ≤ n`).  Then the √q-completion scale that the
completion mechanism *provably* certifies dominates the BGK scale: `bgkScale n L ≤ completionScale q`.
This turns the `OvershootsBGK` hypothesis for door (ii) into a consequence of the proven completion
ceiling, not a postulate. -/
theorem completion_overshootsBGK_of_prizeRegime {n L q : ℝ}
    (hq : n * L ≤ q) :
    bgkScale n L ≤ completionScale q := by
  unfold bgkScale completionScale
  exact Real.sqrt_le_sqrt hq

/-- A `Mechanism` whose door is `completion` and whose certified scale is the proven `√q` ceiling,
in the prize regime, satisfies `OvershootsBGK` unconditionally (no extra hypothesis beyond the
regime fact `n·L ≤ q`). -/
theorem completionMechanism_overshootsBGK {n L q : ℝ} (hq : n * L ≤ q) :
    (⟨DoorType.completion, completionScale q⟩ : Mechanism).OvershootsBGK n L :=
  completion_overshootsBGK_of_prizeRegime hq

/-- **Door-(ii) cannot certify the prize.**  In the prize regime `L > 1`, `n·L ≤ q`, the √q-completion
mechanism's certified scale strictly exceeds the prize floor `√n`, so the completion door provably
fails to certify `M ≤ √n` — a discharged (not assumed) instance of the no-fifth-door exclusion. -/
theorem completion_not_certifies_prizeScale {n L q : ℝ}
    (hn : 0 < n) (hL : 1 < L) (hq : n * L ≤ q) :
    ¬ (completionScale q ≤ prizeScale n) :=
  not_certifies_prizeScale_of_overshoot hn hL (completionMechanism_overshootsBGK hq)

/-! ## Discharging the door-(i)/(iii) (moment / extreme-value) overshoot from the SOTA exponent wall

Doors (i) (moment / symmetric-function) and (iii) (extreme-value / equidistribution) both bottom out
at the BGK state of the art: a *guaranteed* per-frequency value `C·n^{1−δ}` with sub-prize exponent
`δ < 1/2` (the in-tree SOTA has `δ ≈ 0.011`, i.e. `n^{0.989}`).  This SOTA scale eventually DOMINATES
the BGK argument scale `bgkScale n L = √(n·L) = (√L)·n^{1/2}`, because the gap exponent `1/2 − δ > 0`
drives `n^{1/2−δ} → ∞` past the constant `√L`.  So any moment/EVT mechanism certifies a scale that
eventually exceeds `bgkScale`, i.e. it `OvershootsBGK` for all large `n` — a discharged consequence of
the SOTA exponent being `< 1/2`, not a postulate.  (This re-proves, self-contained, the eventual
domination at the heart of `_BGKSOTAInsufficiency.bgk_value_exceeds_prizeTarget_eventually`.) -/

open Filter Topology in
/-- **Moment/EVT SOTA scale eventually dominates BGK.**  For any SOTA constant `C > 0` and sub-prize
exponent `δ < 1/2`, and any thinness index `L ≥ 0`, there is a threshold `N₀` past which the SOTA
guaranteed value `C·n^{1−δ}` exceeds the BGK scale `√(n·L)`.  Hence the moment/extreme-value door's
certified scale `OvershootsBGK` for all large subgroups. -/
theorem momentEVT_scale_eventually_ge_bgkScale
    {C L δ : ℝ} (hC : 0 < C) (hL : 0 ≤ L) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, N₀ ≤ n → bgkScale n L ≤ C * n ^ (1 - δ) := by
  have hgap : 0 < 1 / 2 - δ := by linarith
  have htend : Tendsto (fun n : ℝ => C * n ^ (1 / 2 - δ)) atTop atTop :=
    Tendsto.const_mul_atTop hC (tendsto_rpow_atTop hgap)
  have hev : ∀ᶠ n : ℝ in atTop,
      Real.sqrt L < C * n ^ (1 / 2 - δ) ∧ (1 : ℝ) ≤ n :=
    (htend.eventually_gt_atTop (Real.sqrt L)).and (eventually_ge_atTop 1)
  obtain ⟨N₀, hN₀⟩ := hev.exists_forall_of_atTop
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨hgt, hn1⟩ := hN₀ n hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le one_pos hn1
  have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  -- bgkScale n L = (√L)·√n  and  C·n^{1−δ} = (C·n^{1/2−δ})·√n, compare coefficients.
  have hLHS : bgkScale n L = Real.sqrt L * Real.sqrt n := by
    unfold bgkScale; rw [Real.sqrt_mul hnpos.le]; ring
  have hrpow : n ^ (1 - δ) = n ^ (1 / 2 - δ) * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]; congr 1; ring
  have hRHS : C * n ^ (1 - δ) = (C * n ^ (1 / 2 - δ)) * Real.sqrt n := by
    rw [hrpow]; ring
  rw [hLHS, hRHS]
  exact le_of_lt (mul_lt_mul_of_pos_right hgt hsqrtn_pos)

/-- **Door-(i)/(iii) overshoot, discharged for large `n`.**  A moment/extreme-value mechanism whose
certified scale is the SOTA value `C·n^{1−δ}` (`δ < 1/2`) satisfies `OvershootsBGK` for every `n` past
the SOTA threshold `N₀`.  Combined with the strict scale separation, such a mechanism provably cannot
certify a prize-scale bound at those `n`. -/
theorem momentEVT_mechanism_overshootsBGK_eventually
    {C L δ : ℝ} (hC : 0 < C) (hL : 0 ≤ L) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, N₀ ≤ n →
      (⟨DoorType.moment, C * n ^ (1 - δ)⟩ : Mechanism).OvershootsBGK n L := by
  obtain ⟨N₀, hN₀⟩ := momentEVT_scale_eventually_ge_bgkScale hC hL hδ
  exact ⟨N₀, fun n hn => hN₀ n hn⟩

/-- **Door-(iii) overshoot, discharged for large `n`.**  The extreme-value/equidistribution door uses
that same SOTA scale `C·n^{1−δ}` as the moment door in this capstone model.  Hence it has the same
large-`n` BGK overshoot certificate, now named separately so the classical-side closure has an explicit
door-(iii) theorem rather than only a door-(i) representative. -/
theorem extremeValue_mechanism_overshootsBGK_eventually
    {C L δ : ℝ} (hC : 0 < C) (hL : 0 ≤ L) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, N₀ ≤ n →
      (⟨DoorType.extremeValue, C * n ^ (1 - δ)⟩ : Mechanism).OvershootsBGK n L := by
  obtain ⟨N₀, hN₀⟩ := momentEVT_scale_eventually_ge_bgkScale hC hL hδ
  exact ⟨N₀, fun n hn => hN₀ n hn⟩

/-! ## Classical side closed: doors (i)/(ii)/(iii) all FAIL the prize certificate at their proven scales

The three discharges above (`completion_not_certifies_prizeScale` for door (ii);
`momentEVT_mechanism_overshootsBGK_eventually` + the scale separation for doors (i)/(iii)) are bundled
here into a single citable statement: at the concrete proven certScales, NO classical door certifies a
prize-scale bound in the prize regime.  This is the unconditional classical side of the no-fifth-door
tetrachotomy — the `hclassicalOvershoots` hypothesis of `forces_doorIV` is no longer a postulate for
the completion / moment-EVT mechanisms, it is a theorem. -/

/-- **Classical side closed (concrete scales).**  In the prize regime `L > 1`:

* the √q-completion door (ii), at any field size with `n·L ≤ q`, fails the prize certificate; and
* the moment / extreme-value doors (i)/(iii), at the SOTA scale `C·n^{1−δ}` (`δ < 1/2`), fail the
  prize certificate for all `n` past the SOTA threshold.

No classical door reaches the prize floor `√n`; only door (iv) remains. -/
theorem classicalSide_closed
    {n L q C δ : ℝ} (hn : 0 < n) (hL : 1 < L)
    (hq : n * L ≤ q) (hC : 0 < C) (hLnn : 0 ≤ L) (hδ : δ < 1 / 2) :
    (¬ (completionScale q ≤ prizeScale n)) ∧
    (∃ N₀ : ℝ, ∀ m : ℝ, N₀ ≤ m →
        ¬ ((⟨DoorType.moment, C * m ^ (1 - δ)⟩ : Mechanism).certScale ≤ prizeScale m)) := by
  refine ⟨completion_not_certifies_prizeScale hn hL hq, ?_⟩
  obtain ⟨N₀, hN₀⟩ := momentEVT_mechanism_overshootsBGK_eventually hC hLnn hδ
  refine ⟨max N₀ 2, fun m hm => ?_⟩
  have hmN₀ : N₀ ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : (2 : ℝ) ≤ m := le_trans (le_max_right _ _) hm
  have hmpos : 0 < m := by linarith
  exact not_certifies_prizeScale_of_overshoot hmpos hL (hN₀ m hmN₀)

/-- **Classical side closed, all three doors named.**  This strengthens `classicalSide_closed` by
returning both the door-(i) moment obstruction and the door-(iii) extreme-value/equidistribution
obstruction at their common SOTA scale, alongside the door-(ii) completion obstruction.  It is a
bookkeeping capstone only: the conclusion is still that the named classical scales fail to certify the
prize floor; it supplies no new monomial-sum cancellation. -/
theorem classicalSide_closed_all
    {n L q C δ : ℝ} (hn : 0 < n) (hL : 1 < L)
    (hq : n * L ≤ q) (hC : 0 < C) (hLnn : 0 ≤ L) (hδ : δ < 1 / 2) :
    (¬ (completionScale q ≤ prizeScale n)) ∧
    (∃ N₀ : ℝ, ∀ m : ℝ, N₀ ≤ m →
        (¬ ((⟨DoorType.moment, C * m ^ (1 - δ)⟩ : Mechanism).certScale ≤ prizeScale m)) ∧
        (¬ ((⟨DoorType.extremeValue, C * m ^ (1 - δ)⟩ : Mechanism).certScale ≤ prizeScale m))) := by
  refine ⟨completion_not_certifies_prizeScale hn hL hq, ?_⟩
  obtain ⟨N₁, hN₁⟩ := momentEVT_mechanism_overshootsBGK_eventually hC hLnn hδ
  obtain ⟨N₂, hN₂⟩ := extremeValue_mechanism_overshootsBGK_eventually hC hLnn hδ
  refine ⟨max (max N₁ N₂) 2, fun m hm => ?_⟩
  have hmN₁ : N₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmN₂ : N₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm2 : (2 : ℝ) ≤ m := le_trans (le_max_right _ _) hm
  have hmpos : 0 < m := by linarith
  exact ⟨not_certifies_prizeScale_of_overshoot hmpos hL (hN₁ m hmN₁),
    not_certifies_prizeScale_of_overshoot hmpos hL (hN₂ m hmN₂)⟩

/-! ## Discharging the `forces_doorIV` quantifier from the proven ceilings (not a postulate)

The capstone `forces_doorIV` takes `hclassicalOvershoots : ∀ m', m'.door.isClassical →
m'.OvershootsBGK n L` as a *hypothesis*.  The discharges above (`completionMechanism_overshootsBGK`,
`momentEVT_mechanism_overshootsBGK_eventually`) prove overshoot only for the *specific* proven
certScales `√q` and `C·n^{1−δ}`.  They are not yet fed back into `forces_doorIV`, so the named-lever
capstone's docstring correctly flagged that the abstract quantifier was still open.

This section closes that gap *honestly*.  We cannot discharge overshoot for an *arbitrary* classical
`Mechanism` (its `certScale` field is unconstrained — a degenerate `Mechanism` with door `completion`
and `certScale = 0` does not overshoot, but it also violates the proven `M ≤ √q` *floor* on what a
completion mechanism can certify).  The physically meaningful subclass is the mechanisms that
*respect their proven ceiling*: a completion mechanism cannot certify anything below the proven `√q`
ceiling, and a moment/extreme-value mechanism cannot certify below the SOTA `C·n^{1−δ}` value.  For
that subclass overshoot is a **theorem**, and `forces_doorIV` then forces door (iv) **without** the
oversho­ot postulate. -/

/-- A classical `Mechanism` *respects its proven ceiling* at parameters `(q, C, δ, n)` when its
certified scale is at least the proven lower bound on what that door can certify:

* a `completion` mechanism certifies at least the proven `√q` completion ceiling `completionScale q`;
* a `moment`/`extremeValue` mechanism certifies at least the SOTA value `C·n^{1−δ}`;
* a `newEvaluation` mechanism is unconstrained (the live door).

This is the honest content of "the mechanism is a *real* instance of its door", as opposed to a
degenerate `Mechanism` value with an arbitrarily small `certScale` field. -/
def Mechanism.RespectsProvenScale (m : Mechanism) (q C δ n : ℝ) : Prop :=
  match m.door with
  | .completion => completionScale q ≤ m.certScale
  | .moment => C * n ^ (1 - δ) ≤ m.certScale
  | .extremeValue => C * n ^ (1 - δ) ≤ m.certScale
  | .newEvaluation => True

/-- **Fixed-field linear dominance is impossible.**  For any positive thinness index `L`, no fixed
field-size parameter `q` can dominate `n·L` for every real `n`.  This is the formal audit guard against
using a vacuous premise `∀ n, n·L ≤ q` to discharge the classical-door overshoot quantifier; the regime
witness must be threaded at the single conclusion index instead. -/
theorem not_forall_linear_le_fixed_field {L q : ℝ} (hL : 0 < L) :
    ¬ (∀ n : ℝ, n * L ≤ q) := by
  intro h
  have hq1 : ((q + 1) / L) * L ≤ q := h ((q + 1) / L)
  have hLne : L ≠ 0 := ne_of_gt hL
  have hcontr : q + 1 ≤ q := by
    simpa [div_mul_cancel₀ (q + 1) hLne] using hq1
  linarith

/-- **Every ceiling-respecting classical mechanism overshoots BGK** at a fixed `n` past the SOTA
threshold, in the prize regime.  This is the discharge of the `forces_doorIV` overshoot quantifier
restricted to the honest subclass: no postulate, only the proven `√q` and `C·n^{1−δ}` floors plus the
regime facts `n·L ≤ q` and `δ < 1/2`.  Returns the SOTA threshold `N₀`; at any single `n ≥ N₀` with its
own pointwise regime witness `n·L ≤ q`, the implication holds for *all* ceiling-respecting classical
mechanisms simultaneously.  The pointwise `n·L ≤ q` hypothesis is essential: a fixed finite `q` cannot
satisfy `∀ n, n·L ≤ q` in a nontrivial large-`n` statement. -/
theorem ceilingRespecting_classical_overshoots
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, N₀ ≤ n → n * L ≤ q → ∀ m : Mechanism,
      m.door.isClassical → m.RespectsProvenScale q C δ n → m.OvershootsBGK n L := by
  obtain ⟨N₀, hN₀⟩ := momentEVT_scale_eventually_ge_bgkScale (C := C) (L := L) (δ := δ) hC hLnn hδ
  refine ⟨N₀, fun n hn hq m hcl hresp => ?_⟩
  -- `OvershootsBGK` ⇔ `bgkScale n L ≤ m.certScale`; split on the door class.
  unfold Mechanism.OvershootsBGK
  unfold Mechanism.RespectsProvenScale at hresp
  cases hd : m.door with
  | completion =>
      rw [hd] at hresp
      -- proven completion floor: completionScale q ≤ certScale, and bgkScale ≤ completionScale q.
      exact le_trans (completion_overshootsBGK_of_prizeRegime hq) hresp
  | moment =>
      rw [hd] at hresp
      exact le_trans (hN₀ n hn) hresp
  | extremeValue =>
      rw [hd] at hresp
      exact le_trans (hN₀ n hn) hresp
  | newEvaluation =>
      -- not classical; the hypothesis `isClassical` is `False`.
      rw [hd] at hcl; exact absurd hcl (by simp [DoorType.isClassical])

/-- **No-fifth-door capstone, overshoot discharged.**  At a fixed `n` past the SOTA threshold, in the
prize regime (`L > 1`, `n·L ≤ q`, `C > 0`, `δ < 1/2`): if every classical mechanism *respects its
proven ceiling*, then **any** mechanism `m` certifying a prize-scale bound `m.certScale ≤ √n` must be
door (iv).  Unlike `forces_doorIV`, the overshoot of the classical doors is here a **theorem**
(`ceilingRespecting_classical_overshoots`), not a hypothesis — it is discharged from the proven `√q`
completion ceiling and the SOTA `C·n^{1−δ}` value.  The field-size dominance assumption is threaded at
the single conclusion index `n` as `n·L ≤ q`, avoiding the vacuous fixed-`q` premise `∀ n, n·L ≤ q`.
The only remaining hypothesis is the honest structural one that the classical mechanisms are *real*
instances of their door (respect their proven floor), not degenerate `Mechanism` values with an
arbitrarily small `certScale` field. -/
theorem forces_doorIV_ceilingRespecting
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, max N₀ 1 ≤ n → n * L ≤ q →
      (∀ m' : Mechanism, m'.door.isClassical → m'.RespectsProvenScale q C δ n) →
      ∀ m : Mechanism, m.certScale ≤ prizeScale n → m.door = DoorType.newEvaluation := by
  obtain ⟨N₀, hN₀⟩ := ceilingRespecting_classical_overshoots hLnn hC hδ
  refine ⟨N₀, fun n hn hq hrespAll m hcert => ?_⟩
  have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : (1 : ℝ) ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : 0 < n := lt_of_lt_of_le one_pos hn1
  -- discharge the abstract quantifier of `forces_doorIV` from the proven overshoot.
  refine forces_doorIV hnpos hL ?_ hcert
  intro m' hcl'
  exact hN₀ n hnN₀ hq m' hcl' (hrespAll m' hcl')

/-! ## Local contrapositive: a classical prize certificate must violate its proven ceiling

The previous theorem is the global, all-mechanisms form: if *every* classical mechanism respects its
proven scale, then a prize certificate is forced through door (iv).  For citations it is often cleaner
to use the pointwise contrapositive: at a fixed large `n`, a mechanism that certifies the prize is
either door (iv), or else it is a classical mechanism that has cheated its own proven scale.  This is
the precise formal guard against smuggling a classical door through a too-small `certScale` field. -/

/-- **Classical prize certificates violate their proven scale.**  Past the SOTA threshold, in the
prize regime, any *classical* mechanism that claims a prize-scale certificate `certScale ≤ √n` cannot
also respect the proven scale of its door (`√q` for completion, `C·n^{1−δ}` for moment/EVT).  Thus a
classical-looking prize certificate is necessarily a misclassified/degenerate mechanism, not a real
classical-door proof. -/
theorem classical_prize_certificate_violates_provenScale
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, max N₀ 1 ≤ n → n * L ≤ q → ∀ m : Mechanism,
      m.door.isClassical → m.certScale ≤ prizeScale n → ¬ m.RespectsProvenScale q C δ n := by
  obtain ⟨N₀, hN₀⟩ := ceilingRespecting_classical_overshoots hLnn hC hδ
  refine ⟨N₀, fun n hn hq m hcl hcert hresp => ?_⟩
  have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : (1 : ℝ) ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : 0 < n := lt_of_lt_of_le one_pos hn1
  exact not_certifies_prizeScale_of_overshoot hnpos hL (hN₀ n hnN₀ hq m hcl hresp) hcert

/-- **Local no-fifth-door alternative, no global premise.**  Past the SOTA threshold, in the prize
regime, any prize-scale certificate is either genuinely door (iv), or it violates the proven scale of
its own classical door.  This removes the global hypothesis that *all* classical mechanisms respect
their ceilings and replaces it by the sharp local dichotomy for the single mechanism under inspection. -/
theorem prize_certificate_doorIV_or_violates_provenScale
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, max N₀ 1 ≤ n → n * L ≤ q → ∀ m : Mechanism,
      m.certScale ≤ prizeScale n →
        m.door = DoorType.newEvaluation ∨ ¬ m.RespectsProvenScale q C δ n := by
  obtain ⟨N₀, hN₀⟩ := ceilingRespecting_classical_overshoots hLnn hC hδ
  refine ⟨N₀, fun n hn hq m hcert => ?_⟩
  by_cases hcl : m.door.isClassical
  · right
    intro hresp
    have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : (1 : ℝ) ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : 0 < n := lt_of_lt_of_le one_pos hn1
    exact not_certifies_prizeScale_of_overshoot hnpos hL (hN₀ n hnN₀ hq m hcl hresp) hcert
  · left
    exact (Mechanism.not_classical_iff_doorIV m).mp hcl

end ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy
