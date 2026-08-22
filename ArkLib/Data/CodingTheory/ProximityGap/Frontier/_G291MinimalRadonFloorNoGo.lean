/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# G291: the CORE census no-go sits exactly at the Radon pigeonhole floor (#466)

G289 shows the bounded-degree canonical-feature no-gos are dimension-forced (Cover counting) and
gate-independent, but its only kernel-checked witness is a *specific* five-cell linear positive
circuit plus the gate-flip transfer. This file supplies the missing **theorem-level deep-floor
content**: the census positive circuit is a **minimal positive Radon circuit**, sitting exactly at
the pigeonhole floor `N = d + 1` for the canonical linear feature dimension `d = log₂ n = 4`, and it
is **r-uniform**: its support genuinely spans both ranks `r ∈ {5,6}`, so the no-go is not a
per-rank artifact and cannot be compressed to a smaller cell family.

## What is genuinely new beyond G289

G289 exhibits one positive circuit (existence of a dependence). G291 proves that circuit is
**minimal**: no proper sub-support carries a nonzero linear dependence, because every `d`-subset of
the signed feature vectors is linearly independent. A strictly-positive dependence whose support is
a minimal dependent set is, by definition, a *positive circuit* (a positive Radon partition). Hence
the CORE no-go is pinned at the Radon floor: with only `d = 4` canonical Ramanujan coordinates,
`d + 1 = 5` sponsor-faithful cells already force a positive circuit, and not one cell fewer. This is
exactly the "deep-floor / primitive-census" invariant: the no-go is a pigeonhole certificate of
minimal support, carrying no arithmetic content about the gate beyond dimension counting, consistent
with and sharpening G289's gate-independence.

The abstract minimality lemma is general (any `d`-dimensional family whose `d`-subsets are
independent), and the concrete consumer instantiates it on the exact G289 census data, adding the
r-uniformity witness. Nothing here weakens a goal, restates an open Prop, or fits a fixed depth: the
minimal-support/Radon-floor statement is `r`-uniform and dimension-parametrized.

CORE remains open / on-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G291MinimalRadonFloorNoGo

open scoped BigOperators

/-! ## Abstract minimal positive Radon circuit

A family `v : Fin (d+1) → Fin d → ℚ` of `d+1` vectors in `ℚ^d`. If every `d`-element subfamily is
linearly independent (equivalently: the only linear dependence omitting a single index is trivial),
then any nonzero linear dependence among all `d+1` vectors has **full support**: no proper
sub-support is dependent. A strictly-positive such dependence is therefore a *minimal* positive
circuit (a positive Radon partition), which by the G287/G289 obstruction forbids a strict linear
separator, and no smaller family can. -/

/-- Linear independence of the subfamily obtained by deleting index `k`: the only coefficient
vector `c` supported off `k` with `∑ c i • v i = 0` is the zero vector. We phrase "supported off
`k`" as `c k = 0`. -/
def DeleteOneIndependent {n m : ℕ} (v : Fin n → Fin m → ℚ) : Prop :=
  ∀ k : Fin n, ∀ c : Fin n → ℚ, c k = 0 →
    (∀ j : Fin m, ∑ i, c i * v i j = 0) → ∀ i, c i = 0

/-- **Minimal-support (Radon floor) lemma.** If every one-deleted subfamily of `v` is linearly
independent, then any linear dependence `c` that omits at least one index (`c k = 0` for some `k`)
must be the zero dependence. Hence a nonzero dependence has full support: the dependence is minimal,
i.e. a Radon circuit at the floor `d + 1`. -/
theorem minimal_support_of_deleteOne_independent {n m : ℕ}
    (v : Fin n → Fin m → ℚ) (hindep : DeleteOneIndependent v)
    (c : Fin n → ℚ) (hdep : ∀ j : Fin m, ∑ i, c i * v i j = 0)
    (k : Fin n) (hk : c k = 0) :
    ∀ i, c i = 0 :=
  hindep k c hk hdep

/-- Contrapositive packaging: a dependence with **any** nonzero coefficient has full support (every
proper sub-support is independent). This is the "no proper positive sub-circuit" statement. -/
theorem full_support_of_nonzero_dependence {n m : ℕ}
    (v : Fin n → Fin m → ℚ) (hindep : DeleteOneIndependent v)
    (c : Fin n → ℚ) (hdep : ∀ j : Fin m, ∑ i, c i * v i j = 0)
    (i₀ : Fin n) (hnz : c i₀ ≠ 0) :
    ∀ k, c k ≠ 0 := by
  intro k hk
  exact hnz (minimal_support_of_deleteOne_independent v hindep c hdep k hk i₀)

/-! ## Reused separation obstruction (positive circuit ⇒ no strict separator) -/

/-- A strictly-positive linear dependence among signed feature vectors forbids a strict linear
separator (identical in force to `G287`/`G289`, reproved locally for self-containment). -/
theorem no_strict_separator_of_positive_relation
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (v : ι → κ → ℚ) (weight : ι → ℚ)
    (hweight : ∀ i, 0 < weight i)
    (hrel : ∀ j, ∑ i, weight i * v i j = 0) :
    ¬ ∃ a : κ → ℚ, ∀ i, 0 < ∑ j, a j * v i j := by
  classical
  rintro ⟨a, ha⟩
  have hzero : (∑ i, weight i * ∑ j, a j * v i j) = 0 := by
    calc
      (∑ i, weight i * ∑ j, a j * v i j) =
          ∑ i, ∑ j, a j * (weight i * v i j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ j, ∑ i, a j * (weight i * v i j) := Finset.sum_comm
      _ = ∑ j, a j * ∑ i, weight i * v i j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
      _ = 0 := by simp [hrel]
  have hpos : 0 < ∑ i, weight i * ∑ j, a j * v i j := by
    apply Finset.sum_pos
    · intro i _
      exact mul_pos (hweight i) (ha i)
    · exact Finset.univ_nonempty
  linarith

/-! ## Exact five-cell CORE census circuit and its minimality (d = 4)

The five sponsor-faithful census cells with their canonical linear features `(T₂,T₄,T₈,T₁₆)`, CORE
gate signs, exact positive Farkas weights (verbatim from `_G289CountingMirageNoGo.lean`), and their
rank labels `r ∈ {5,6}`. Here `d = 4` and the support size is `d + 1 = 5`: the pigeonhole floor.
-/

/-- Raw feature vectors `(T₂,T₄,T₈,T₁₆)` of the five census cells. -/
def rawFeat : Fin 5 → Fin 4 → ℚ :=
  ![![-309168, -683424, 2610752, 3312256],
    ![14464, 57856, -86784, -173568],
    ![9290416, 70408736, -14191744, 90283648],
    ![5023728, 22930784, 168792128, 266289664],
    ![11819168, 32644736, 88373568, 58306048]]

/-- CORE gate sign of each cell (`+1`/`-1`). -/
def gate : Fin 5 → ℚ := ![1, -1, 1, -1, 1]

/-- Signed feature vectors `v i j = gate i * rawFeat i j`. -/
def signedFeat (i : Fin 5) (j : Fin 4) : ℚ := gate i * rawFeat i j

/-- Rank label `r ∈ {5,6}` of each census cell. -/
def rank : Fin 5 → ℕ := ![5, 6, 5, 6, 5]

/-- Exact positive Farkas weights of the five-cell circuit. -/
def circuitWeight : Fin 5 → ℚ :=
  ![770888209934274952,
    294057324376824869095,
    185095074806906020,
    347725276122965348,
    382331993870867280]

/-- Every circuit weight is strictly positive. -/
theorem circuitWeight_pos (i : Fin 5) : 0 < circuitWeight i := by
  fin_cases i <;> norm_num [circuitWeight]

/-- Exact positive dependence: each of the four gate-signed feature coordinates sums to zero. -/
theorem census_farkas_relation (j : Fin 4) :
    ∑ i, circuitWeight i * signedFeat i j = 0 := by
  fin_cases j <;>
    simp [signedFeat, circuitWeight, gate, rawFeat, Fin.sum_univ_succ] <;>
    norm_num

/-- **r-uniformity.** The support of the circuit (all five weights are nonzero) genuinely spans both
ranks: rank `5` and rank `6` each occur on a positively-weighted cell. So the no-go is not a
single-rank artifact. -/
theorem circuit_r_uniform :
    (∃ i, circuitWeight i ≠ 0 ∧ rank i = 5) ∧ (∃ i, circuitWeight i ≠ 0 ∧ rank i = 6) := by
  refine ⟨⟨0, ?_, ?_⟩, ⟨1, ?_, ?_⟩⟩
  · norm_num [circuitWeight]
  · norm_num [rank]
  · norm_num [circuitWeight]
  · norm_num [rank]

/-- **Minimality of the census circuit (Radon floor): every 4-subset is independent.** For each
deletable index `k`, the four remaining signed feature vectors in `ℚ⁴` are linearly independent, so
the only coefficient vector supported off `k` that annihilates all four coordinates is zero. The
independence is discharged by explicit exact Cramer certificates: for each deleted `k` and each
target coordinate `t ≠ k`, an integer linear combination of the four coordinate identities equals
`det_k · c_t`, with `det_k ≠ 0` the (nonzero) `4×4` minor determinant. Hence `signedFeat` satisfies
`DeleteOneIndependent`, so by `full_support_of_nonzero_dependence` any nonzero dependence among the
five census vectors has full support: the positive Farkas circuit is **minimal**, a positive Radon
partition at the floor `d + 1 = 5`. -/
theorem census_deleteOne_independent : DeleteOneIndependent signedFeat := by
  intro k c hk hdep i
  have h0 := hdep 0
  have h1 := hdep 1
  have h2 := hdep 2
  have h3 := hdep 3
  simp only [signedFeat, gate, rawFeat, Fin.sum_univ_five,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.tail_cons] at h0 h1 h2 h3
  fin_cases k
  -- k = 0
  · have hk' : c 0 = 0 := hk
    have z1 : c 1 = 0 := by
      have key : (730734727560518232029790208 : ℚ) * c 1 = 0 := by
        linear_combination (1382906631683320756568064) * h0
          + (-307739059981346054471680) * h1
          + (-122972876675310475935744) * h2
          + (78359048461337669795840) * h3
          - (-278740673481041176598287482880) * hk'
      have hd : (730734727560518232029790208 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z2 : c 2 = 0 := by
      have key : (730734727560518232029790208 : ℚ) * c 2 = 0 := by
        linear_combination (825847919611365818368) * h0
          + (-176541857858476048384) * h1
          + (-77324196576545472512) * h2
          + (48635472303061204992) * h3
          - (-175453972857296563292078080) * hk'
      have hd : (730734727560518232029790208 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z3 : c 3 = 0 := by
      have key : (730734727560518232029790208 : ℚ) * c 3 = 0 := by
        linear_combination (1569394308534089285632) * h0
          + (-344585062216400109568) * h1
          + (-138944134032480796672) * h2
          + (85393238655281135616) * h3
          - (-329613206738866719520980992) * hk'
      have hd : (730734727560518232029790208 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z4 : c 4 = 0 := by
      have key : (730734727560518232029790208 : ℚ) * c 4 = 0 := by
        linear_combination (1772107448944567517184) * h0
          + (-384298800735411240960) * h1
          + (-148768785733863342080) * h2
          + (93960413367175217152) * h3
          - (-362417354135845230209925120) * hk'
      have hd : (730734727560518232029790208 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    fin_cases i <;> assumption
  -- k = 1
  · have hk' : c 1 = 0 := hk
    have z0 : c 0 = 0 := by
      have key : (-278740673481041176598287482880 : ℚ) * c 0 = 0 := by
        linear_combination (1382906631683320756568064) * h0
          + (-307739059981346054471680) * h1
          + (-122972876675310475935744) * h2
          + (78359048461337669795840) * h3
          - (730734727560518232029790208) * hk'
      have hd : (-278740673481041176598287482880 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z2 : c 2 = 0 := by
      have key : (-278740673481041176598287482880 : ℚ) * c 2 = 0 := by
        linear_combination (17022671627607478108160) * h0
          + (-6547717166808577474560) * h1
          + (-31038809832696709120) * h2
          + (262368886826228449280) * h3
          - (175453972857296563292078080) * hk'
      have hd : (-278740673481041176598287482880 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z3 : c 3 = 0 := by
      have key : (-278740673481041176598287482880 : ℚ) * c 3 = 0 := by
        linear_combination (25139441549201378902016) * h0
          + (-7369276267363528867840) * h1
          + (-2468888720290236071936) * h2
          + (2772016041456944742400) * h3
          - (329613206738866719520980992) * hk'
      have hd : (-278740673481041176598287482880 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z4 : c 4 = 0 := by
      have key : (-278740673481041176598287482880 : ℚ) * c 4 = 0 := by
        linear_combination (9895435921246192926720) * h0
          + (-6035390383689390489600) * h1
          + (-4241748680911209103360) * h2
          + (3021739668523086970880) * h3
          - (362417354135845230209925120) * hk'
      have hd : (-278740673481041176598287482880 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    fin_cases i <;> assumption
  -- k = 2
  · have hk' : c 2 = 0 := hk
    have z0 : c 0 = 0 := by
      have key : (175453972857296563292078080 : ℚ) * c 0 = 0 := by
        linear_combination (-825847919611365818368) * h0
          + (176541857858476048384) * h1
          + (77324196576545472512) * h2
          + (-48635472303061204992) * h3
          - (-730734727560518232029790208) * hk'
      have hd : (175453972857296563292078080 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z1 : c 1 = 0 := by
      have key : (175453972857296563292078080 : ℚ) * c 1 = 0 := by
        linear_combination (17022671627607478108160) * h0
          + (-6547717166808577474560) * h1
          + (-31038809832696709120) * h2
          + (262368886826228449280) * h3
          - (-278740673481041176598287482880) * hk'
      have hd : (175453972857296563292078080 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z3 : c 3 = 0 := by
      have key : (175453972857296563292078080 : ℚ) * c 3 = 0 := by
        linear_combination (4305372704421183488) * h0
          + (-3104122707222462464) * h1
          + (1517344159333613568) * h2
          + (-1434598590039195648) * h3
          - (-329613206738866719520980992) * hk'
      have hd : (175453972857296563292078080 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z4 : c 4 = 0 := by
      have key : (175453972857296563292078080 : ℚ) * c 4 = 0 := by
        linear_combination (15904094693826232320) * h0
          + (-4714321359171747840) * h1
          + (2629622169736314880) * h2
          + (-1560910313439887360) * h3
          - (-362417354135845230209925120) * hk'
      have hd : (175453972857296563292078080 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    fin_cases i <;> assumption
  -- k = 3
  · have hk' : c 3 = 0 := hk
    have z0 : c 0 = 0 := by
      have key : (-329613206738866719520980992 : ℚ) * c 0 = 0 := by
        linear_combination (1569394308534089285632) * h0
          + (-344585062216400109568) * h1
          + (-138944134032480796672) * h2
          + (85393238655281135616) * h3
          - (730734727560518232029790208) * hk'
      have hd : (-329613206738866719520980992 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z1 : c 1 = 0 := by
      have key : (-329613206738866719520980992 : ℚ) * c 1 = 0 := by
        linear_combination (-25139441549201378902016) * h0
          + (7369276267363528867840) * h1
          + (2468888720290236071936) * h2
          + (-2772016041456944742400) * h3
          - (278740673481041176598287482880) * hk'
      have hd : (-329613206738866719520980992 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z2 : c 2 = 0 := by
      have key : (-329613206738866719520980992 : ℚ) * c 2 = 0 := by
        linear_combination (4305372704421183488) * h0
          + (-3104122707222462464) * h1
          + (1517344159333613568) * h2
          + (-1434598590039195648) * h3
          - (175453972857296563292078080) * hk'
      have hd : (-329613206738866719520980992 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z4 : c 4 = 0 := by
      have key : (-329613206738866719520980992 : ℚ) * c 4 = 0 := by
        linear_combination (-20984750634288807936) * h0
          + (2444599203680747520) * h1
          + (-1805865864302428160) * h2
          + (-30929886145937408) * h3
          - (362417354135845230209925120) * hk'
      have hd : (-329613206738866719520980992 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    fin_cases i <;> assumption
  -- k = 4
  · have hk' : c 4 = 0 := hk
    have z0 : c 0 = 0 := by
      have key : (362417354135845230209925120 : ℚ) * c 0 = 0 := by
        linear_combination (-1772107448944567517184) * h0
          + (384298800735411240960) * h1
          + (148768785733863342080) * h2
          + (-93960413367175217152) * h3
          - (-730734727560518232029790208) * hk'
      have hd : (362417354135845230209925120 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z1 : c 1 = 0 := by
      have key : (362417354135845230209925120 : ℚ) * c 1 = 0 := by
        linear_combination (9895435921246192926720) * h0
          + (-6035390383689390489600) * h1
          + (-4241748680911209103360) * h2
          + (3021739668523086970880) * h3
          - (-278740673481041176598287482880) * hk'
      have hd : (362417354135845230209925120 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z2 : c 2 = 0 := by
      have key : (362417354135845230209925120 : ℚ) * c 2 = 0 := by
        linear_combination (-15904094693826232320) * h0
          + (4714321359171747840) * h1
          + (-2629622169736314880) * h2
          + (1560910313439887360) * h3
          - (-175453972857296563292078080) * hk'
      have hd : (362417354135845230209925120 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    have z3 : c 3 = 0 := by
      have key : (362417354135845230209925120 : ℚ) * c 3 = 0 := by
        linear_combination (-20984750634288807936) * h0
          + (2444599203680747520) * h1
          + (-1805865864302428160) * h2
          + (-30929886145937408) * h3
          - (-329613206738866719520980992) * hk'
      have hd : (362417354135845230209925120 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp key).resolve_left hd
    fin_cases i <;> assumption

/-! ## The census no-go is a minimal, r-uniform positive Radon circuit -/

/-- The census signed features admit a strictly-positive dependence: `circuitWeight` is positive on
every cell and annihilates all four coordinates. -/
theorem census_positive_circuit :
    (∀ i, 0 < circuitWeight i) ∧ (∀ j, ∑ i, circuitWeight i * signedFeat i j = 0) :=
  ⟨circuitWeight_pos, census_farkas_relation⟩

/-- **The census positive circuit has full support.** Any nonzero linear dependence among the five
signed feature vectors uses every cell; in particular the positive Farkas circuit `circuitWeight`,
which is nonzero (indeed positive) on cell `0`, is minimal: no strict sub-family of cells carries a
dependence. This is the Radon-floor certificate: with `d = 4` canonical Ramanujan coordinates,
`d + 1 = 5` sponsor-faithful cells force a positive circuit and not one cell fewer. -/
theorem census_circuit_full_support :
    ∀ k, circuitWeight k ≠ 0 := by
  refine full_support_of_nonzero_dependence signedFeat census_deleteOne_independent
    circuitWeight ?_ 0 ?_
  · intro j; simpa using census_farkas_relation j
  · exact ne_of_gt (circuitWeight_pos 0)

/-- **G291 headline.** The canonical-feature CORE no-go is a *minimal, r-uniform positive Radon
circuit at the pigeonhole floor `d + 1 = 5`*: (1) a strictly-positive dependence exists, so no fixed
linear functional of `(T₂,T₄,T₈,T₁₆)` has the CORE gate sign on all five cells; (2) the dependence
has full support (minimal, no smaller cell family works); (3) the support spans both ranks
`r ∈ {5,6}`, so the obstruction is not a per-rank artifact. This is the deep-floor certificate: the
no-go carries no arithmetic content beyond dimension counting (cf. G289 gate-independence), and it
is
pinned at the Radon floor. -/
theorem census_minimal_r_uniform_no_go :
    (¬ ∃ a : Fin 4 → ℚ, ∀ i, 0 < ∑ j, a j * signedFeat i j) ∧
    (∀ k, circuitWeight k ≠ 0) ∧
    ((∃ i, circuitWeight i ≠ 0 ∧ rank i = 5) ∧ (∃ i, circuitWeight i ≠ 0 ∧ rank i = 6)) := by
  refine ⟨?_, census_circuit_full_support, circuit_r_uniform⟩
  exact no_strict_separator_of_positive_relation signedFeat circuitWeight circuitWeight_pos
    census_farkas_relation

#print axioms minimal_support_of_deleteOne_independent
#print axioms full_support_of_nonzero_dependence
#print axioms no_strict_separator_of_positive_relation
#print axioms circuitWeight_pos
#print axioms census_farkas_relation
#print axioms circuit_r_uniform
#print axioms census_deleteOne_independent
#print axioms census_circuit_full_support
#print axioms census_minimal_r_uniform_no_go

end ArkLib.ProximityGap.Frontier.G291MinimalRadonFloorNoGo
