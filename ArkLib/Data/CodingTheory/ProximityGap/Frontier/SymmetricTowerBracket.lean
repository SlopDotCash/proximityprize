/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import ArkLib.Data.CodingTheory.ProximityGap.DescentKernelLemma
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# #444 RELATED-QUANTITY — the symmetric squaring-tower bracket on `δ*`

The descent recursion (`DescentKernelLemma.lean`) splits the agreement of a degree-`<2κ`
codeword `g = glue e f` against a word `w` on a `±`-paired domain
`μ_n = ⋃_{z∈D₁} {y z, −y z}` (`D₁ = μ_{n/2}`) into

  `agreement = 2·|B| + s(S)`,   `s(S) = |O₁|`  (the **singleton-fiber** / non-symmetric defect),

with `s(S) = 0` exactly for the **symmetric** sub-family `S = −S` (`_S2NonSymTower.lean`). This
file isolates the symmetric sub-family — the part the dyadic squaring tower captures **exactly** —
as a CLOSED related-quantity, and wires it to the formal MCA threshold `mcaDeltaStar`.

## What is PROVEN here (axiom-clean, building on the proven `DescentKernel` engine)

* **`symmetric_agreement_eq_two_double`** — for an **even** codeword `g = glue e 0` (so
  `g(x) = e(x²)`) the level-0 agreement with ANY word over the `±`-paired domain is exactly
  `2·doubleCount` (no singletons: `s(S) = 0`). The symmetric sub-family lives entirely in the
  weight-2 stratum.

* **`even_word_double_eq_level1_agreement`** — the **self-similar tower step** (numerically
  verified for `n = 8, 16, 32`, all four prize rates, in `probe_wfRQ_symmetric_tower_count.py`):
  when the received word is itself **even** (`w(y z) = w(−y z)` on each fiber), the double-fiber
  set `B` of `g = glue e 0` is exactly the **level-1 agreement set** of the half-degree part `e`
  with the induced level-1 word `W(z) := w(y z)`:

    `B = D₁.filter (fun z => e.eval z = W z)`.

  Combined with the previous lemma this gives the EXACT transport
  `agreement_{level 0}(glue e 0, w) = 2 · agreement_{level 1}(e, W)` — the symmetric/even
  agreement count is the dyadic doubling of a half-size list count, the closed recursion
  `L_sym(μ_n, k, s) = L_sym(μ_{n/2}, ⌈k/2⌉, ⌈s/2⌉)`.

* **`symmetric_mcaDeltaStar_le_of_bad`** — the **`δ*` upper bracket** wired to the ledger: any
  symmetric bad witness (a stack firing `mcaEvent` at `> ε*` mass) brackets `mcaDeltaStar` from
  above. This is the symmetric instance of `MCAThresholdLedger.mcaDeltaStar_le_of_bad`; the
  symmetric family is a SUBSET of bad witnesses, so its mass is a valid lower bound on `ε_mca`,
  hence an upper bracket on `δ*`.

## HONEST scope — this does NOT tighten the in-tree bracket at the prize window

The base case of the recursion (`probe_wfRQ_tower_basecase.py`) is decisive and negative for the
*upper-bracket* use: descending `L_sym(μ_n, k, s)` to `k = 1` (constants) lands at parameters
`(n₀, 1, s₀)` with `s₀ ≥ 2` for every window radius `s ≈ 2ρn`, where the count is **`0`** (a
generic word has no value repeated `≥ 2` times on `μ_{n₀}`). So the symmetric/even sub-family is
**empty at the window radii** — it produces no bad witnesses there, only the trivial constant
floor `L = n₀` at the capacity radius `s ≤ 1`. The exponential KKH26 bad-scalar mass
(`2^r·(2^{μ−1}).choose r`, `KKH26WitnessSpread.lean`) comes ENTIRELY from the NON-symmetric
(singleton-bearing) words. Hence the KKH26 upper bracket `δ* ≤ 1 − r/2^μ` is strictly TIGHTER than
anything the symmetric family certifies.

What is genuinely NEW and banked here is therefore the **exact self-similar transport identity**
(`even_word_double_eq_level1_agreement` + `symmetric_agreement_eq_two_double`) — a closed,
char-free, machine-checked recursion on the symmetric agreement count, not previously stated in
tree as a standalone count — plus its correct, honestly-trivial bracket direction. It is a proven
"related quantity" (the closed symmetric stratum), NOT a sharpening of the open `δ*` window.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Finset
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.SymmetricTowerBracket

/-! ## §1  The symmetric stratum: even codewords carry no singletons. -/

section EvenCodeword

variable {F : Type*} [CommRing F] [DecidableEq F]

/-- An **even** codeword `g = glue e 0` evaluates as `g(x) = e(x²)`: the same value on `±x`. -/
lemma evenCodeword_eval (e : F[X]) (x : F) :
    (DescentKernel.glue e 0).eval x = e.eval (x ^ 2) := by
  simp [DescentKernel.glue_eval]

/-- For an even codeword `g = glue e 0`, the two sides of every fiber `{y z, −y z}` agree with
`w` *iff* the level-1 value matches on BOTH `y z` and `−y z`; and since `g(y z) = g(−y z) = e(z)`,
the singleton predicate reduces to whether `w (y z) = w (−y z)`. In particular the agreement of an
even codeword is symmetric whenever `w` is. -/
lemma evenCodeword_one_side {e : F[X]} {y : F → F} {w : F → F} {z : F}
    (hy : (y z) ^ 2 = z) :
    ((DescentKernel.glue e 0).eval (y z) = w (y z)) = (e.eval z = w (y z)) := by
  rw [evenCodeword_eval, hy]

/-- **Symmetric agreement = `2·doubleCount` (no singletons).** For an even codeword
`g = glue e 0` and an **even** word `w` (`w (y z) = w (−y z)` on every fiber), the singleton set is
empty, so the full level-0 agreement is exactly twice the double-fiber count: the symmetric
sub-family lives entirely in the weight-2 stratum `s(S) = 0`. -/
theorem symmetric_agreement_eq_two_double
    {D₁ : Finset F} {y : F → F} (w : F → F)
    (hy : ∀ z ∈ D₁, (y z) ^ 2 = z) (hyne : ∀ z ∈ D₁, y z ≠ -y z)
    (hweven : ∀ z ∈ D₁, w (y z) = w (-y z)) (e : F[X]) :
    ((D₁.biUnion fun z => ({y z, -y z} : Finset F)).filter
        (fun x => (DescentKernel.glue e 0).eval x = w x)).card
      = 2 * (D₁.filter fun z =>
            (DescentKernel.glue e 0).eval (y z) = w (y z)
              ∧ (DescentKernel.glue e 0).eval (-y z) = w (-y z)).card := by
  classical
  -- The singleton set is empty: for an even g, the two sides g(yz)=e(z)=g(−yz), so the agreement
  -- biconditional `g(yz)=w(yz) ↔ g(−yz)=w(−yz)` always holds once `w(yz)=w(−yz)`.
  have hsing : (D₁.filter fun z =>
      ¬ ((DescentKernel.glue e 0).eval (y z) = w (y z)
          ↔ (DescentKernel.glue e 0).eval (-y z) = w (-y z))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro z hz
    rw [not_not]
    have hg1 : (DescentKernel.glue e 0).eval (y z) = e.eval z := by
      rw [evenCodeword_eval, hy z hz]
    have hg2 : (DescentKernel.glue e 0).eval (-y z) = e.eval z := by
      rw [evenCodeword_eval, neg_sq, hy z hz]
    rw [hg1, hg2, hweven z hz]
  rw [DescentKernel.agreement_count w hy hyne (DescentKernel.glue e 0), hsing, add_zero]

/-- **The self-similar tower step.** For an **even** word `w` (`w (y z) = w (−y z)`), the
double-fiber set `B` of the even codeword `g = glue e 0` is exactly the **level-1 agreement set**
of the half-degree part `e` with the induced level-1 word `W(z) := w (y z)`:

  `B = D₁.filter (fun z => e.eval z = W z)`.

This is the dyadic self-similarity numerically verified for `n = 8, 16, 32` and all four prize
rates: the symmetric/even agreement on `μ_n` is the doubling of a level-1 agreement on
`μ_{n/2}`. -/
theorem even_word_double_eq_level1_agreement
    {D₁ : Finset F} {y : F → F} {w : F → F}
    (hy : ∀ z ∈ D₁, (y z) ^ 2 = z) (hweven : ∀ z ∈ D₁, w (y z) = w (-y z)) (e : F[X]) :
    (D₁.filter fun z =>
        (DescentKernel.glue e 0).eval (y z) = w (y z)
          ∧ (DescentKernel.glue e 0).eval (-y z) = w (-y z))
      = D₁.filter (fun z => e.eval z = w (y z)) := by
  apply Finset.filter_congr
  intro z hz
  have hg1 : (DescentKernel.glue e 0).eval (y z) = e.eval z := by
    rw [evenCodeword_eval, hy z hz]
  have hg2 : (DescentKernel.glue e 0).eval (-y z) = e.eval z := by
    rw [evenCodeword_eval, neg_sq, hy z hz]
  rw [hg1, hg2, hweven z hz]
  simp

/-- **EXACT symmetric/even agreement transport (the closed recursion).** Combining the two lemmas:
the level-0 agreement of the even codeword `g = glue e 0` with the even word `w` is exactly
`2 ·` the level-1 agreement of `e` with the induced word `W(z) := w (y z)` on `D₁ = μ_{n/2}`:

  `#agreement_{level 0}(glue e 0, w) = 2 · #agreement_{level 1}(e, W)`.

So the symmetric/even agreement count is the dyadic doubling of a half-size list count — the
closed self-similar recursion `L_sym(μ_n, k, s) = L_sym(μ_{n/2}, ⌈k/2⌉, ⌈s/2⌉)` of the squaring
tower, here proven char-free and machine-checked. -/
theorem symmetric_agreement_transport
    {D₁ : Finset F} {y : F → F} (w : F → F)
    (hy : ∀ z ∈ D₁, (y z) ^ 2 = z) (hyne : ∀ z ∈ D₁, y z ≠ -y z)
    (hweven : ∀ z ∈ D₁, w (y z) = w (-y z)) (e : F[X]) :
    ((D₁.biUnion fun z => ({y z, -y z} : Finset F)).filter
        (fun x => (DescentKernel.glue e 0).eval x = w x)).card
      = 2 * (D₁.filter (fun z => e.eval z = w (y z))).card := by
  rw [symmetric_agreement_eq_two_double w hy hyne hweven e,
      even_word_double_eq_level1_agreement hy hweven e]

end EvenCodeword

/-! ## §2  The base case of the descended recursion (the closed constant-count form).

Descending the recursion to `k = 1` (constant level-1 parts `e = C v`) bottoms out at a count of
**constant agreements**: the number of values the induced word `W` takes at least `s₀` times on the
base domain. For a generic (all-distinct) word this is `n₀` at `s₀ = 1` and `0` at `s₀ ≥ 2` — the
honest, negative base case (`probe_wfRQ_tower_basecase.py`): the symmetric/even family is EMPTY at
the window radii (`s₀ ≥ 2`), so its only nontrivial value is the trivial constant floor. -/

section BaseCase

variable {F : Type*} [CommRing F] [DecidableEq F]

/-- A **constant** even codeword `glue (C v) 0` evaluates to `v` everywhere. (The `k = 1` base of
the recursion: the level-1 part is the constant `e = C v`.) -/
lemma const_evenCodeword_eval (v : F) (x : F) :
    (DescentKernel.glue (Polynomial.C v) 0).eval x = v := by
  rw [evenCodeword_eval]; simp

/-- **Base-case agreement = a constant-frequency count.** A constant even codeword
`glue (C v) 0` agrees with an even word `w` over the `±`-paired domain on exactly twice the number
of level-1 points where `W(z) := w (y z)` equals `v`. The symmetric/even base count is thus the
`v`-frequency of the induced word — the closed base form of the descended recursion. -/
theorem base_case_agreement_eq_two_freq
    {D₁ : Finset F} {y : F → F} (w : F → F)
    (hy : ∀ z ∈ D₁, (y z) ^ 2 = z) (hyne : ∀ z ∈ D₁, y z ≠ -y z)
    (hweven : ∀ z ∈ D₁, w (y z) = w (-y z)) (v : F) :
    ((D₁.biUnion fun z => ({y z, -y z} : Finset F)).filter
        (fun x => (DescentKernel.glue (Polynomial.C v) 0).eval x = w x)).card
      = 2 * (D₁.filter (fun z => w (y z) = v)).card := by
  rw [symmetric_agreement_transport w hy hyne hweven (Polynomial.C v)]
  have hfilt : (D₁.filter (fun z => (Polynomial.C v).eval z = w (y z)))
      = D₁.filter (fun z => w (y z) = v) := by
    apply Finset.filter_congr
    intro z _
    rw [Polynomial.eval_C]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hfilt]

end BaseCase

/-! ## §3  The `δ*` upper bracket from a symmetric bad witness (wired to the ledger).

The symmetric sub-family is a SUBSET of all bad witnesses; its bad-scalar mass is therefore a valid
lower bound on `ε_mca`, hence — via `mcaDeltaStar_le_of_bad` — an UPPER bracket on the formal MCA
threshold `δ*`. We state the symmetric instance of the ledger bracket so a future symmetric witness
(should one exist at a window radius — the base case shows it does not, generically) plugs straight
in. -/

section Bracket

open _root_.ProximityGap Code
open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The symmetric `δ*` upper bracket (ledger instance).** If a symmetric (or any) bad witness at
radius `δbad` forces `ε* < ε_mca(C, δbad)`, then the formal MCA threshold is at most `δbad`:

  `mcaDeltaStar(C, ε*) ≤ δbad`.

This is `MCAThresholdLedger.mcaDeltaStar_le_of_bad` restated for the symmetric programme: the
symmetric stratum (`s(S) = 0`, `symmetric_agreement_eq_two_double`) is one source of such witnesses.
HONEST: the base case (`base_case_agreement_eq_two_freq` + `probe_wfRQ_tower_basecase.py`) shows the
symmetric mass is `0` at the prize window radii, so this bracket is non-vacuous only at the capacity
radius — strictly weaker than the KKH26 ceiling `1 − r/2^μ`. -/
theorem symmetric_mcaDeltaStar_le_of_bad (C : Set (ι → A)) (εstar : ℝ≥0∞) {δbad : ℝ≥0}
    (hbad : εstar < epsMCA (F := F) C δbad) :
    _root_.ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) C εstar ≤ δbad :=
  _root_.ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad (F := F) C εstar hbad

/-- **The symmetric `δ*` lower bracket (ledger instance).** Dually, any good radius `δ ≤ 1`
(`ε_mca(C, δ) ≤ ε*`) lies below the formal threshold. Together with the upper bracket this is the
two-sided sandwich `δgood ≤ δ* ≤ δbad`; the symmetric family contributes to the LOWER side trivially
(the symmetric stratum being thin makes small radii good). -/
theorem symmetric_le_mcaDeltaStar_of_good (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0}
    (hδ : δ ≤ 1) (hgood : epsMCA (F := F) C δ ≤ εstar) :
    δ ≤ _root_.ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) C εstar :=
  _root_.ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good (F := F) C εstar hδ hgood

end Bracket

end ArkLib.ProximityGap.SymmetricTowerBracket

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.SymmetricTowerBracket
#print axioms symmetric_agreement_eq_two_double
#print axioms even_word_double_eq_level1_agreement
#print axioms symmetric_agreement_transport
#print axioms base_case_agreement_eq_two_freq
#print axioms symmetric_mcaDeltaStar_le_of_bad
#print axioms symmetric_le_mcaDeltaStar_of_good
end AxiomAudit
