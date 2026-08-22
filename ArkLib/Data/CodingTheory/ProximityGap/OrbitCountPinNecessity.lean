/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConverse
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Orbit-count NECESSITY delimiter for the conditional `δ*` pin (#444 / #407)

`OpenCoreConditionalPin` proves the FORWARD pin: the single open core
`WorstCaseIncidenceBounded C δ B` (`I(δ) ≤ B`) implies `δ ≤ δ*`, and routes it through the
orbit-count crossing law via `worstCaseIncidence_pin_of_orbitCount` (which consumes only the `←`
direction `N ≤ d ⟹ |B| ≤ n` of `OrbitCountCrossingLaw.crossing_law`).

This file extends that face with the **necessity / reach delimiter** built on the so-far UNUSED
`→` direction of the same proven biconditional: when the pencil orbit count *exceeds* the gcd
budget `d = gcd(b−a,n)` at some stack, the open core at the prize budget `n` provably **fails**
there -- so that stack cannot certify the pin through this lever, and the budget-`n` open-core route
is provably inapplicable at that stack.  This is the honest mirror of `OpenCoreConditionalPin`
(rule 4: a precisely-mapped reach is a result), on the NON-MOMENT orbit-count / incidence-geometry
face, EXTEND-proven on `OrbitCountCrossingLaw.crossing_law` and `OpenCoreConditionalPin`'s own
`epsMCA_le_of_worstCaseIncidence`.

## What is proved here (axiom-clean, no `sorry`)

* **`incidence_gt_budget_of_orbitCount_gt`** -- pure arithmetic on the proven crossing law: with the
  orbit-count identity `|B| = N·S` (`S > 0`) and supply `S·d = n`, if `N > d` then `|B| > n`.
  The exact contrapositive of `crossing_law`'s budget test (the `→` direction, in its
  overflow form).
* **`not_worstCaseIncidenceBounded_of_orbitCount_gt`** -- the delimiter at the open-core layer: if
  **some** stack has bad-α count `|B_u| = N_u·S` with `N_u > d` (orbit count strictly over the gcd
  budget), then `WorstCaseIncidenceBounded C δ n` is FALSE -- the prize-budget open core does not
  hold, so the `δ*` pin is not certified through this lever at radius `δ`.
* **`orbitCount_le_of_worstCaseIncidenceBounded`** -- the exact necessary direction: if the
  prize-budget open core DOES hold and a stack's bad-α set factors as `N_u·S` with `S·d = n`, then
  necessarily `N_u ≤ d`.  This is the missing `→` half of the orbit-count budget test at the
  open-core layer.
* **`worstCaseIncidenceBounded_iff_orbitCountCertificate`** -- once per-stack orbit
  factorizations are supplied, the prize-budget open core is EQUIVALENT to the global certificate
  `∀u, N_u ≤ d`.
* **`deltaStar_orbitCountCertificate_bridge`** -- the δ* layer around that equivalence:
  strictly inside `mcaDeltaStar C (n/q)` forces the orbit certificate, while the orbit certificate
  pins `δ ≤ mcaDeltaStar C (n/q)`.
* **`mcaDeltaStar_le_of_orbitCount_gt`** -- the refutation side at the δ* layer: an overflowing
  stack (`N_u > d`) proves `¬ δ < δ*`, hence `mcaDeltaStar C (n/q) ≤ δ`.
* **`coprime_pin_requires_single_orbit`** -- the SHARPEST form, on the extremal primitive pencil
  `gcd(b−a,n) = 1` (orbit size `S = n`): the budget-`n` open core holds at a stack **iff** its
  bad-α set is a *single* `⟨ω^{b−a}⟩`-orbit (`N_u ≤ 1`); `N_u ≥ 2` distinct orbits provably block
  the pin at that stack.  Matches `OrbitCountConsumerBridge.coprime_crossing_law`'s `I ≤ n ⟺ N ≤ 1`
  threshold, lifted to a NECESSARY condition on the pin's open core.
* **`pin_not_certified_of_orbitCount_gt`** -- the assembled reach statement: an overflowing stack
  (`N_u > d`) witnesses that the prize-budget open core is false, so the orbit-count lever does NOT
  discharge the conditional pin at that radius via `worstCaseIncidence_pin_budget`.

## Honest scope (rule 3, rule 6)

This does NOT prove or refute CORE.  It is the precise REACH delimiter of the orbit-count discharge
of the conditional pin: it pins down *exactly when* the orbit-count lever certifies the open core
(`N ≤ d`, the forward pin) versus *provably fails* to (`N > d`, here).  Whether the worst-case
orbit count actually stays `≤ d` at the prize window radius -- i.e. whether the open core itself
holds -- is the recognized-open prize question and is UNTOUCHED.  No moment/census/geometric-minor
re-derivation; NO capacity / beyond-Johnson / growth-law claim; the cliff-at-n/2 is untouched.
This is a char-0-style structural cardinality delimiter (NON-MOMENT incidence/orbit face),
EXTEND-proven on two proven in-tree theorems, not a re-mapped dead face.
`CORE M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger Code
open ArkLib.ProximityGap.OrbitCountCrossingLaw

namespace ProximityGap.OrbitCountPinNecessity

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The arithmetic core: orbit count over budget ⟹ incidence overflows budget -/

/-- **Incidence overflow from orbit-count overflow.**  The contrapositive (overflow form) of
`OrbitCountCrossingLaw.crossing_law`: with the orbit-count identity `|B| = N·S` (`S > 0`) and the
supply identity `S·d = n`, an orbit count strictly above the gcd budget `d` forces the bad-α
incidence strictly above the prize budget `n`. -/
theorem incidence_gt_budget_of_orbitCount_gt
    {Bcard N S d n : ℕ} (hS : 0 < S) (hsupply : S * d = n) (hid : Bcard = N * S)
    (hN : d < N) : n < Bcard := by
  -- `Bcard ≤ n ↔ N ≤ d`; here `¬ (N ≤ d)`, so `¬ (Bcard ≤ n)`, i.e. `n < Bcard`.
  have hiff := crossing_law (Bcard := Bcard) (N := N) (S := S) (d := d) (n := n) hS hsupply hid
  exact lt_of_not_ge (fun hle => (Nat.not_le.mpr hN) (hiff.mp hle))

/-! ## The delimiter at the open-core layer -/

open Classical in
/-- **Orbit-count overflow refutes the prize-budget open core.**  If **some** stack `u` has bad-α
count `|B_u| = N_u·S` with the supply `S·d = n` and `N_u > d` (orbit count strictly over the gcd
budget), then `WorstCaseIncidenceBounded C δ n` is FALSE: the prize-budget open core does not hold,
so the `δ*` pin is not certified through this lever at radius `δ`. -/
theorem not_worstCaseIncidenceBounded_of_orbitCount_gt
    (C : Set (ι → A)) (δ : ℝ≥0) {S d n : ℕ} (hS : 0 < S) (hsupply : S * d = n)
    (u : WordStack A (Fin 2) ι) {N : ℕ}
    (hid : (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * S)
    (hN : d < N) :
    ¬ OpenCoreConditionalPin.WorstCaseIncidenceBounded (F := F) (A := A) C δ n := by
  intro hbound
  have hcard_le : (Finset.univ.filter
      (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card ≤ n := hbound u
  have hgt : n < (Finset.univ.filter
      (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card :=
    incidence_gt_budget_of_orbitCount_gt hS hsupply hid hN
  exact (Nat.not_lt.mpr hcard_le) hgt

open Classical in
/-- **Orbit-count necessity from the prize-budget open core.**  If
`WorstCaseIncidenceBounded C δ n` holds and a stack `u` has exact orbit factorization
`|B_u| = N_u·S` with supply `S·d = n`, then the orbit count is forced below the gcd budget:
`N_u ≤ d`.

Together with `not_worstCaseIncidenceBounded_of_orbitCount_gt`, this makes the orbit-count face a
sharp open-core delimiter: `N_u ≤ d` is necessary for any stack participating in a budget-`n`
certificate, while `N_u > d` refutes that certificate. -/
theorem orbitCount_le_of_worstCaseIncidenceBounded
    (C : Set (ι → A)) (δ : ℝ≥0) {S d n : ℕ} (hS : 0 < S) (hsupply : S * d = n)
    (u : WordStack A (Fin 2) ι) {N : ℕ}
    (hid : (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * S)
    (hbound : OpenCoreConditionalPin.WorstCaseIncidenceBounded (F := F) (A := A) C δ n) :
    N ≤ d := by
  have hcard_le : (Finset.univ.filter
      (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card ≤ n := hbound u
  exact (crossing_law hS hsupply hid).mp hcard_le

open Classical in
/-- **Global orbit-certificate extraction from the open core.**  Assume every stack has an exact
orbit factorization `|B_u| = N_u·S` with the common supply law `S·d = n`.  If the prize-budget
open core holds, then the factorizations automatically satisfy the global orbit-count certificate
`N_u ≤ d` for every stack. -/
theorem orbitCountCertificate_of_worstCaseIncidenceBounded
    (C : Set (ι → A)) (δ : ℝ≥0) {S d n : ℕ} (hS : 0 < S) (hsupply : S * d = n)
    (hfactor : ∀ u : WordStack A (Fin 2) ι,
      ∃ N : ℕ,
        (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card
          = N * S)
    (hbound : OpenCoreConditionalPin.WorstCaseIncidenceBounded (F := F) (A := A) C δ n) :
    ∀ u : WordStack A (Fin 2) ι,
      ∃ N : ℕ,
        (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card
          = N * S
        ∧ N ≤ d := by
  intro u
  obtain ⟨N, hid⟩ := hfactor u
  exact ⟨N, hid, orbitCount_le_of_worstCaseIncidenceBounded C δ hS hsupply u hid hbound⟩

open Classical in
/-- **Exact open-core/orbit-certificate equivalence under factorization.**  Once the
Action-Orbit-style per-stack factorization `|B_u| = N_u·S` is available for every stack, the
prize-budget open core `WorstCaseIncidenceBounded C δ n` is equivalent to the global orbit-count
certificate `∀u, N_u ≤ d`.

The reverse direction is the direct crossing-law argument used by the forward orbit-count pin; the
forward direction is the new necessity theorem above. -/
theorem worstCaseIncidenceBounded_iff_orbitCountCertificate
    (C : Set (ι → A)) (δ : ℝ≥0) {S d n : ℕ} (hS : 0 < S) (hsupply : S * d = n)
    (hfactor : ∀ u : WordStack A (Fin 2) ι,
      ∃ N : ℕ,
        (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card
          = N * S) :
    OpenCoreConditionalPin.WorstCaseIncidenceBounded (F := F) (A := A) C δ n
      ↔ ∀ u : WordStack A (Fin 2) ι,
          ∃ N : ℕ,
            (Finset.univ.filter
              (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * S
            ∧ N ≤ d := by
  constructor
  · exact orbitCountCertificate_of_worstCaseIncidenceBounded C δ hS hsupply hfactor
  · intro horbit u
    obtain ⟨N, hid, hNd⟩ := horbit u
    exact (crossing_law hS hsupply hid).2 hNd

open Classical in
/-- **δ*-interior forces the orbit-count certificate under factorization.**  Once every stack has
an exact orbit factorization `|B_u| = N_u·S` with `S·d = n`, any radius strictly below the formal
threshold `mcaDeltaStar C (n/q)` automatically satisfies the global orbit-count certificate
`N_u ≤ d` for every stack.

This is `OpenCoreConverse.worstCaseIncidence_of_lt_mcaDeltaStar` followed by the orbit-count
necessity theorem above. -/
theorem orbitCountCertificate_of_lt_mcaDeltaStar
    (C : Set (ι → A)) {δ : ℝ≥0} {S d n : ℕ} (hS : 0 < S) (hsupply : S * d = n)
    (hfactor : ∀ u : WordStack A (Fin 2) ι,
      ∃ N : ℕ,
        (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card
          = N * S)
    (hδ : δ < mcaDeltaStar (F := F) (A := A) C
      ((n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))) :
    ∀ u : WordStack A (Fin 2) ι,
      ∃ N : ℕ,
        (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card
          = N * S
        ∧ N ≤ d :=
  orbitCountCertificate_of_worstCaseIncidenceBounded C δ hS hsupply hfactor
    (_root_.ProximityGap.OpenCoreConverse.worstCaseIncidence_of_lt_mcaDeltaStar
      (F := F) (A := A) C (E := n) hδ)

open Classical in
/-- **δ* / orbit-count bridge at the prize budget.**  Under the exact per-stack factorization
`|B_u| = N_u·S` and supply `S·d = n`, the orbit-count certificate is the budget-facing condition
around `mcaDeltaStar C (n/q)`:

* strictly inside the threshold, the orbit certificate is forced;
* conversely, the orbit certificate implies the threshold lower bound `δ ≤ mcaDeltaStar C (n/q)`.

The remaining open content is therefore the actual prize-regime production of the factorizations
and the certificate `N_u ≤ d` at the target radius, not this formal transport layer. -/
theorem deltaStar_orbitCountCertificate_bridge
    (C : Set (ι → A)) {δ : ℝ≥0} {S d n : ℕ}
    (hδ1 : δ ≤ 1) (hS : 0 < S) (hsupply : S * d = n)
    (hfactor : ∀ u : WordStack A (Fin 2) ι,
      ∃ N : ℕ,
        (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card
          = N * S) :
    (δ < mcaDeltaStar (F := F) (A := A) C
      ((n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) →
        ∀ u : WordStack A (Fin 2) ι,
          ∃ N : ℕ,
            (Finset.univ.filter
              (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * S
            ∧ N ≤ d)
    ∧ ((∀ u : WordStack A (Fin 2) ι,
          ∃ N : ℕ,
            (Finset.univ.filter
              (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * S
            ∧ N ≤ d) →
        δ ≤ mcaDeltaStar (F := F) (A := A) C
          ((n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))) := by
  constructor
  · exact fun hδ => orbitCountCertificate_of_lt_mcaDeltaStar C hS hsupply hfactor hδ
  · intro horbit
    exact _root_.ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin_budget
      (F := F) (A := A) C hδ1
      ((worstCaseIncidenceBounded_iff_orbitCountCertificate C δ hS hsupply hfactor).mpr
        horbit)

open Classical in
/-- **Orbit-count overflow refutes δ*-interiority.**  If some stack has an exact orbit
factorization `|B_u| = N_u·S` with `S·d = n` and `N_u > d`, then radius `δ` cannot lie strictly
inside the formal threshold `mcaDeltaStar C (n/q)`.

Proof: strict interior would force the prize-budget open core by `OpenCoreConverse`; the
overflow theorem above refutes that open core. -/
theorem not_lt_mcaDeltaStar_of_orbitCount_gt
    (C : Set (ι → A)) (δ : ℝ≥0) {S d n : ℕ} (hS : 0 < S) (hsupply : S * d = n)
    (u : WordStack A (Fin 2) ι) {N : ℕ}
    (hid : (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * S)
    (hN : d < N) :
    ¬ δ < mcaDeltaStar (F := F) (A := A) C
      ((n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) := by
  intro hδ
  exact not_worstCaseIncidenceBounded_of_orbitCount_gt C δ hS hsupply u hid hN
    (_root_.ProximityGap.OpenCoreConverse.worstCaseIncidence_of_lt_mcaDeltaStar
      (F := F) (A := A) C (E := n) hδ)

open Classical in
/-- **Orbit-count overflow upper-bounds the formal threshold.**  The same overflowing stack gives
the order-theoretic upper delimiter `mcaDeltaStar C (n/q) ≤ δ`. -/
theorem mcaDeltaStar_le_of_orbitCount_gt
    (C : Set (ι → A)) (δ : ℝ≥0) {S d n : ℕ} (hS : 0 < S) (hsupply : S * d = n)
    (u : WordStack A (Fin 2) ι) {N : ℕ}
    (hid : (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * S)
    (hN : d < N) :
    mcaDeltaStar (F := F) (A := A) C
      ((n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ≤ δ :=
  not_lt.mp (not_lt_mcaDeltaStar_of_orbitCount_gt C δ hS hsupply u hid hN)

open Classical in
/-- **The assembled reach statement.**  An overflowing stack (`N_u > d`) witnesses that the
prize-budget open core `WorstCaseIncidenceBounded C δ n` is false; hence the orbit-count lever does
NOT discharge `worstCaseIncidence_pin_budget` at this radius: the pin is not certified through
this face at `δ`.  (The forward pin still holds wherever `N ≤ d`; this is exactly its complementary
reach.) -/
theorem pin_not_certified_of_orbitCount_gt
    (C : Set (ι → A)) (δ : ℝ≥0) {S d n : ℕ} (hS : 0 < S) (hsupply : S * d = n)
    (u : WordStack A (Fin 2) ι) {N : ℕ}
    (hid : (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * S)
    (hN : d < N) :
    ¬ OpenCoreConditionalPin.WorstCaseIncidenceBounded (F := F) (A := A) C δ n :=
  not_worstCaseIncidenceBounded_of_orbitCount_gt C δ hS hsupply u hid hN

/-! ## The sharpest form: the primitive (coprime) pencil needs a single orbit -/

open Classical in
/-- **The coprime pencil pins only on a single orbit.**  On the extremal primitive pencil
`gcd(b−a,n) = 1` the orbit size is the full domain `S = n` (`hsupply : n * 1 = n`).  Then the
prize-budget open core holds at a stack `u` **iff** its bad-α set is a *single* `⟨ω^{b−a}⟩`-orbit:

* if the stack realizes `N_u ≥ 2` distinct orbits, the open core at budget `n` is FALSE there
  (the pin is provably blocked);
* equivalently (`crossing_law` with `d = 1`), `|B_u| ≤ n ⟺ N_u ≤ 1`.

This lifts `OrbitCountConsumerBridge.coprime_crossing_law` (`I ≤ n ⟺ N ≤ 1`) to a NECESSARY
condition on the conditional pin's open core. -/
theorem coprime_pin_requires_single_orbit
    (C : Set (ι → A)) (δ : ℝ≥0) {n : ℕ} (hn : 0 < n)
    (u : WordStack A (Fin 2) ι) {N : ℕ}
    (hid : (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * n)
    (hN : 2 ≤ N) :
    ¬ OpenCoreConditionalPin.WorstCaseIncidenceBounded (F := F) (A := A) C δ n :=
  not_worstCaseIncidenceBounded_of_orbitCount_gt C δ hn (Nat.mul_one n) u hid
    (by omega)

open Classical in
/-- **Coprime necessity in the positive direction.**  In the primitive pencil case (`S = n`,
`d = 1`), any stack whose bad-α count factors as `N_u·n` under a budget-`n` open-core certificate
must have at most one orbit: `N_u ≤ 1`.  This is the open-core half complementary to
`coprime_pin_requires_single_orbit`. -/
theorem coprime_orbitCount_le_one_of_worstCaseIncidenceBounded
    (C : Set (ι → A)) (δ : ℝ≥0) {n : ℕ} (hn : 0 < n)
    (u : WordStack A (Fin 2) ι) {N : ℕ}
    (hid : (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * n)
    (hbound : OpenCoreConditionalPin.WorstCaseIncidenceBounded (F := F) (A := A) C δ n) :
    N ≤ 1 :=
  orbitCount_le_of_worstCaseIncidenceBounded C δ hn (Nat.mul_one n) u hid hbound

open Classical in
/-- **Primitive two-orbit overflow refutes δ*-interiority.**  In the coprime pencil (`S = n`,
`d = 1`), a stack with at least two bad-scalar orbits proves `¬ δ < mcaDeltaStar C (n/q)`. -/
theorem not_lt_mcaDeltaStar_of_coprime_two_orbits
    (C : Set (ι → A)) (δ : ℝ≥0) {n : ℕ} (hn : 0 < n)
    (u : WordStack A (Fin 2) ι) {N : ℕ}
    (hid : (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * n)
    (hN : 2 ≤ N) :
    ¬ δ < mcaDeltaStar (F := F) (A := A) C
      ((n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  not_lt_mcaDeltaStar_of_orbitCount_gt C δ hn (Nat.mul_one n) u hid (by omega)

open Classical in
/-- **Primitive two-orbit overflow upper-bounds δ*.**  The coprime overflow witness gives
`mcaDeltaStar C (n/q) ≤ δ`. -/
theorem mcaDeltaStar_le_of_coprime_two_orbits
    (C : Set (ι → A)) (δ : ℝ≥0) {n : ℕ} (hn : 0 < n)
    (u : WordStack A (Fin 2) ι) {N : ℕ}
    (hid : (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * n)
    (hN : 2 ≤ N) :
    mcaDeltaStar (F := F) (A := A) C
      ((n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ≤ δ :=
  not_lt.mp (not_lt_mcaDeltaStar_of_coprime_two_orbits C δ hn u hid hN)

/-! ## Sanity: the delimiter has teeth (a concrete over-budget orbit count overflows) -/

/-- **Non-vacuity sanity.**  A stack whose bad-α count is `N·S` with `N = d + 1 > d` overflows the
budget `n = S·d`: `(d+1)·S = S·d + S > S·d = n` (since `S > 0`).  The arithmetic delimiter fires on
the minimal overflow `N = d+1`. -/
example {S d : ℕ} (hS : 0 < S) : S * d < (d + 1) * S :=
  incidence_gt_budget_of_orbitCount_gt (Bcard := (d + 1) * S) (N := d + 1) (S := S)
    (d := d) (n := S * d) hS rfl rfl (Nat.lt_succ_self d)

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms incidence_gt_budget_of_orbitCount_gt
#print axioms not_worstCaseIncidenceBounded_of_orbitCount_gt
#print axioms orbitCount_le_of_worstCaseIncidenceBounded
#print axioms orbitCountCertificate_of_worstCaseIncidenceBounded
#print axioms worstCaseIncidenceBounded_iff_orbitCountCertificate
#print axioms orbitCountCertificate_of_lt_mcaDeltaStar
#print axioms deltaStar_orbitCountCertificate_bridge
#print axioms not_lt_mcaDeltaStar_of_orbitCount_gt
#print axioms mcaDeltaStar_le_of_orbitCount_gt
#print axioms pin_not_certified_of_orbitCount_gt
#print axioms coprime_pin_requires_single_orbit
#print axioms coprime_orbitCount_le_one_of_worstCaseIncidenceBounded
#print axioms not_lt_mcaDeltaStar_of_coprime_two_orbits
#print axioms mcaDeltaStar_le_of_coprime_two_orbits

end ProximityGap.OrbitCountPinNecessity
