/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CodewordHeavyScalar
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS

/-!
# The bounded spread-excess law (#466 lane W1): pencil caps + the conjecture

Successor to the REFUTED windowed `SumsetExtremal` (DISPROOF_LOG tag
`466-r1-windowed-extremal-spread-beats`; note
`docs/kb/deltastar-466-p5-replication-2026-07-01.md`): in the prize window, 2-Fourier-component
(spread) directions strictly beat every monomial direction's worst-offset bad-scalar count.
The surviving replacement is the **bounded spread-excess law**: the spread advantage is a
bounded constant `C ≤ 2`, not an order-of-growth phenomenon.

## What is PROVEN here (axiom-clean)

The probe `scripts/probes/probe_466_spread_excess.py` (symmetric search effort per direction
class) shows the winners' bad-scalar sets decompose into FEW *pencils*: for a fixed `k`-subset
`p`, every witness codeword along the line `w_γ = u₀ + γ·u₁` through `p` has the form
`c_γ = I_p(u₀) + γ·I_p(u₁)` — an affine pencil `c₀ + γ·c₁` in the code.  This file proves the
per-pencil cap the probe measures as SATURATED:

* `agreeSet_pencil_line` — the shift identity: agreement of the pencil word `c₀ + γ·c₁` with
  the line word `u₀ + γ·u₁` is agreement of the fixed word `c₀` with the shifted line
  `u₀ + γ·(u₁ − c₁)`.
* `pencilHeavyScalars_card_le` — **the pencil cap**: the scalars `γ` whose line word agrees
  with the pencil word on `≥ a` points number at most `supp(u₁ − c₁) / (a − z)`, where `z`
  counts coordinates on which the pencil is locked to the line for every `γ`
  (`u₁ = c₁` and `u₀ = c₀`).  This is the `codeword_heavy_scalar` bound transported along the
  shift identity — the "2-dim intersection constant" of the pencil mechanism.
* `bad_card_le_of_pencil_cover` — the cover consequence: a bad-scalar set covered by `m`
  pencils of locked-agreement `≤ zBar < a` has size `≤ m · (n / (a − zBar))`.

Mechanism finding (probe, n=8 boundary a=4, both primes 4129/4153): the spread winner's 12 bad
scalars are covered by 3 pencils, the largest saturating its cap `5 = supp/(a−z) = 5/1` via the
maximal locked count `z = a−1 = 3`; monomial directions cap at `z = 2`, per-pencil cap 3, worst
9.  The spread excess is *pencil concentration*: 2-component directions admit pencils with more
locked coordinates (extra zeros of `u₁ − I_p(u₁)` beyond the `k` interpolation points).

## What is CONJECTURED here (honest label — NOT proven)

`SpreadExcessLaw C` (`C = 2` intended): for far 2-component directions in the window
(`k + 2 ≤ a`, `a² ≤ n·k`), the worst-offset bad-scalar count is at most `C` times the worst
monomial-direction count.  Measured ratios (symmetric effort, exact counts, witnesses
brute-verified, ≥ 2 primes per scale): n=8 boundary 4/3; n=16 values in
`scripts/probes/_out_466_spread_excess.txt`.  Refuting it (ratio growing with `n` or `q`) would
also be decisive — see the kill condition in the lane brief.

What is missing for a proof: a bound on the number of pencils a worst-offset stack can
concentrate on (the min-cover measured by the probe) — this is the same counting surface as
the line-list production obligations (dossier v3 §6 Tier-1 item 2), NOT closed here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Frontier.SpreadExcess

open ProximityGap.SpikeFloor ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## The pencil shift identity and the per-pencil cap (PROVEN) -/

/-- **Shift identity.** Agreement of the pencil word `c₀ + γ·c₁` with the line word
`u₀ + γ·u₁` is agreement of the fixed word `c₀` with the direction-shifted line
`u₀ + γ·(u₁ − c₁)`. -/
theorem agreeSet_pencil_line (c₀ c₁ u₀ u₁ : Fin n → F) (γ : F) :
    agreeSet (fun i => c₀ i + γ • c₁ i) (fun i => u₀ i + γ • u₁ i)
      = agreeSet c₀ (fun i => u₀ i + γ • (u₁ i - c₁ i)) := by
  ext i
  simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and, smul_eq_mul]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

open Classical in
/-- The scalars `γ` at which the pencil word `c₀ + γ·c₁` is `a`-heavy against the line
`w_γ = u₀ + γ·u₁`. -/
noncomputable def pencilHeavyScalars (c₀ c₁ u₀ u₁ : Fin n → F) (a : ℕ) : Finset F :=
  (Finset.univ : Finset F).filter
    (fun γ => a ≤ (agreeSet (fun i => c₀ i + γ • c₁ i) (fun i => u₀ i + γ • u₁ i)).card)

open Classical in
/-- **The pencil cap** (the probe's per-pencil provable bound, measured saturated).
If the locked coordinates (where `u₁ = c₁` AND `u₀ = c₀`, so the pencil agrees with the
line for every `γ`) number `z < a`, then the pencil is `a`-heavy for at most
`supp(u₁ − c₁) / (a − z)` scalars. -/
theorem pencilHeavyScalars_card_le (a : ℕ) (c₀ c₁ u₀ u₁ : Fin n → F)
    (hz : (directionZeroAgreementSet c₀ u₀ (fun i => u₁ i - c₁ i)).card < a) :
    (pencilHeavyScalars c₀ c₁ u₀ u₁ a).card
      ≤ (directionSupportSet (fun i => u₁ i - c₁ i)).card
          / (a - (directionZeroAgreementSet c₀ u₀ (fun i => u₁ i - c₁ i)).card) := by
  have hset : pencilHeavyScalars c₀ c₁ u₀ u₁ a
      = (Finset.univ : Finset F).filter
          (fun γ => a ≤ (agreeSet c₀ (fun i => u₀ i + γ • (u₁ i - c₁ i))).card) := by
    unfold pencilHeavyScalars
    refine Finset.filter_congr fun γ _ => ?_
    rw [agreeSet_pencil_line]
  rw [hset]
  exact codeword_heavy_scalar_card_le_support_div_sub_zeroAgreement a c₀ u₀
    (fun i => u₁ i - c₁ i) hz

/-- The direction support is at most the block length. -/
theorem directionSupportSet_card_le (d : Fin n → F) :
    (directionSupportSet d).card ≤ n := by
  classical
  calc (directionSupportSet d).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (by
        intro i _; exact Finset.mem_univ i)
    _ = n := by rw [Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **Cover consequence.** A set of scalars covered by `m` pencils, each with locked-agreement
count `≤ zBar < a`, has size at most `m · (n / (a − zBar))`.  This is the proven half of the
spread-excess mechanism: what remains open is bounding the pencil count `m` itself. -/
theorem bad_card_le_of_pencil_cover (a : ℕ) (u₀ u₁ : Fin n → F)
    (S : Finset F) (P : Finset ((Fin n → F) × (Fin n → F))) (zBar : ℕ) (hza : zBar < a)
    (hcover : S ⊆ P.biUnion (fun p => pencilHeavyScalars p.1 p.2 u₀ u₁ a))
    (hzp : ∀ p ∈ P,
      (directionZeroAgreementSet p.1 u₀ (fun i => u₁ i - p.2 i)).card ≤ zBar) :
    S.card ≤ P.card * (n / (a - zBar)) := by
  have hstep : ∀ p ∈ P, (pencilHeavyScalars p.1 p.2 u₀ u₁ a).card ≤ n / (a - zBar) := by
    intro p hp
    set z : ℕ := (directionZeroAgreementSet p.1 u₀ (fun i => u₁ i - p.2 i)).card with hzdef
    have hz : z < a := lt_of_le_of_lt (hzp p hp) hza
    have h1 : (pencilHeavyScalars p.1 p.2 u₀ u₁ a).card
        ≤ (directionSupportSet (fun i => u₁ i - p.2 i)).card / (a - z) :=
      pencilHeavyScalars_card_le a p.1 p.2 u₀ u₁ (by rw [← hzdef]; exact hz)
    have h2 : (directionSupportSet (fun i => u₁ i - p.2 i)).card / (a - z)
        ≤ n / (a - z) :=
      Nat.div_le_div_right (directionSupportSet_card_le _)
    have h3 : n / (a - z) ≤ n / (a - zBar) := by
      refine Nat.div_le_div_left ?_ ?_
      · exact Nat.sub_le_sub_left (hzp p hp) a
      · exact Nat.sub_pos_of_lt hza
    exact le_trans h1 (le_trans h2 h3)
  calc S.card
      ≤ (P.biUnion (fun p => pencilHeavyScalars p.1 p.2 u₀ u₁ a)).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ p ∈ P, (pencilHeavyScalars p.1 p.2 u₀ u₁ a).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, n / (a - zBar) := Finset.sum_le_sum hstep
    _ = P.card * (n / (a - zBar)) := by rw [Finset.sum_const, smul_eq_mul]

/-! ## The conjecture (HONEST LABEL: open, not proven; refutable by probe) -/

/-- A direction that is `a`-far from the code (not `a`-close to any codeword); the
non-degeneracy condition for bad-scalar counting (a direction `a`-close to the code has all
`q` scalars bad — the below-window degeneracy repaired by `SumsetExtremalityGuard`). -/
def FarDirection (dom : Fin n ↪ F) (k a : ℕ) (u₁ : Fin n → F) : Prop :=
  ∀ c : Fin n → F, c ∈ rsCode dom k → (agreeSet c u₁).card < a

open Classical in
/-- The bad scalars of the stack `(u₀, u₁)` at agreement level `a`: scalars `γ` for which
some codeword agrees with `w_γ = u₀ + γ·u₁` on at least `a` coordinates. -/
noncomputable def lineBadScalars (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    Finset F :=
  (Finset.univ : Finset F).filter
    (fun γ => ∃ c : Fin n → F, c ∈ rsCode dom k ∧
      a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)

open Classical in
/-- The worst-offset bad-scalar count of a direction. -/
noncomputable def worstBad (dom : Fin n ↪ F) (k a : ℕ) (u₁ : Fin n → F) : ℕ :=
  (Finset.univ : Finset (Fin n → F)).sup
    (fun u₀ => (lineBadScalars dom k a u₀ u₁).card)

/-- A monomial direction. -/
def monoDir (dom : Fin n ↪ F) (j : ℕ) : Fin n → F := fun i => dom i ^ j

/-- A 2-Fourier-component (spread) direction `x^j + c·x^{j'}`. -/
def spread2Dir (dom : Fin n ↪ F) (j j' : ℕ) (c : F) : Fin n → F :=
  fun i => dom i ^ j + c * dom i ^ j'

open Classical in
/-- The monomial baseline: the worst-offset count over `a`-far monomial directions. -/
noncomputable def monoBaseline (dom : Fin n ↪ F) (k a : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter
      (fun jm : Fin n => FarDirection dom k a (monoDir dom (jm : ℕ)))).sup
    (fun jm : Fin n => worstBad dom k a (monoDir dom (jm : ℕ)))

/-- **CONJECTURE (the bounded spread-excess law) — OPEN, NOT PROVEN.**
For window-interior agreement (`k + 2 ≤ a`, `a² ≤ n·k`, i.e. at or above the Johnson boundary
`δ ≤ 1 − √ρ` — the levels where direction discrimination has content per round-1 (D)), the
worst-offset bad-scalar count of any `a`-far 2-component direction is at most `C` times the
monomial baseline.

⚠️ **`C = 2` is REFUTED in evidence** (P5 referee audit,
`docs/kb/deltastar-466b-p5-referee-2026-07-01.md`): at n=16, k=4, a=7, q ∈ {65617, 65633} the
spread `x⁴+x¹⁴` has brute-verified worst ≥ 21 vs monomial baseline 9 — ratio ≥ 21/9 ≈ 2.33
(guards satisfied: k+2 = 6 ≤ 7, a² = 49 ≤ 64 = n·k, direction 7-far).  The live constant is
`C = 3` (nothing measured exceeds it: 4/3 at n=8/a=4; ≥2.33 with heuristic-search monomial
baseline at n=16/a=7).  The un-bounded alternative (ratio growing with `n` or `q`) would
refute the Prop at every constant; nothing here asserts its truth at any `C`. -/
def SpreadExcessLaw (C : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) [NeZero n] (dom : Fin n ↪ F) (k a j j' : ℕ) (c : F),
    k + 2 ≤ a → a * a ≤ n * k →
    FarDirection dom k a (spread2Dir dom j j' c) →
    worstBad dom k a (spread2Dir dom j j' c) ≤ C * monoBaseline dom k a

/-- Monotonicity of the law in the constant (proven glue: a law at `C` gives the law at any
`C' ≥ C`). -/
theorem spreadExcessLaw_mono {C C' : ℕ} (hCC : C ≤ C') (h : SpreadExcessLaw C) :
    SpreadExcessLaw C' := by
  intro F _ _ _ n _ dom k a j j' c ha hw hfar
  exact le_trans (h F n dom k a j j' c ha hw hfar)
    (Nat.mul_le_mul hCC le_rfl)

/-! ## Source audit -/

#print axioms agreeSet_pencil_line
#print axioms pencilHeavyScalars_card_le
#print axioms directionSupportSet_card_le
#print axioms bad_card_le_of_pencil_cover
#print axioms spreadExcessLaw_mono

end ProximityGap.Frontier.SpreadExcess
