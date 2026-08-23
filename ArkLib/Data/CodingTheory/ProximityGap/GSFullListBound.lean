/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GSHasseMultiplicity
import ArkLib.Data.CodingTheory.ProximityGap.GSYDegreeListCap

/-!
# Issue #232 — the FULL multiplicity-`m` Guruswami–Sudan list bound, assembled

The capstone of the GS formalization arc.  `GSHasseMultiplicity.gs_decoder_pipeline` produces one
nonzero weighted-degree-bounded `Q` such that every degree-`< k` polynomial with `m·agree ≥ D`
yields a factor `(Y − f) ∣ Q`; `GSYDegreeListCap.card_le_natDegreeY_of_sub_C_dvd` caps any such
factor family by `deg_Y Q`.  This file welds them and bounds `deg_Y Q ≤ (D−1)/(k−1)` from the
weighted-degree constraint, giving:

* `gs_full_list_bound` — for any field `F`, any `n` distinct points, any received word, any
  multiplicity `m`: if `n·C(m+1,2) < #gsSupport(D,k)` and `D ≤ m·t`, then every finite set of
  degree-`≤ k−1` polynomials with `≥ t` agreements has size `≤ (D−1)/(k−1)`.

This subsumes `SudanListBound` (the `m = 1` case) and is the machine whose parameter optimization
approaches the Johnson radius as `m → ∞` (and, by `GSJohnsonWall`/`GSExactCountWall`, provably never
passes it).

## The multiplicity ladder (concrete, `n = 50`, `k = 2`; integer Johnson floor `t = 8 ≈ √50`)

The gain from multiplicity, machine-checked at `n = 50` (`#gsSupport(D,2) = D(D+1)/2`):

| m | constraints `50·C(m+1,2)` | minimal `D` | certified `t ≥ ⌈D/m⌉` | list cap `(D−1)/(k−1)` |
|---|---|---|---|---|
| 1 | 50  | 10 (`55 > 50`)   | **10** | 9  |
| 2 | 150 | 17 (`153 > 150`) | **9**  | 16 |
| 4 | 500 | 32 (`528 > 500`) | **8**  | 31 |

`t = 8` is the integer Johnson floor at `n = 50, k = 2` (`√(n(k−1)) = √50 ≈ 7.07`): multiplicity 4
certifies a finite list exactly down to it, where Sudan (`m = 1`) needs `t = 10`.  Per the walls,
no multiplicity certifies `t ≤ 7`.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open Polynomial

namespace ArkLib.CodingTheory.GSFullListBound

open GSHasse

variable {F : Type*} [Field F]

/-- The `Y`-degree of any polynomial satisfying the `(1, k−1)`-weighted-degree bound `< D` is at
most `(D−1)/(k−1)` (for `k ≥ 2`): the leading `Y`-coefficient is a nonzero polynomial, whose own
leading coefficient witnesses `(k−1)·deg_Y ≤ i + (k−1)·deg_Y < D`. -/
theorem natDegreeY_le_of_wdeg {Q : Polynomial (Polynomial F)} {k D : ℕ} (hk : 2 ≤ k)
    (hQ : Q ≠ 0) (hwdeg : ∀ i j : ℕ, (Q.coeff j).coeff i ≠ 0 → i + (k - 1) * j < D) :
    Q.natDegree ≤ (D - 1) / (k - 1) := by
  set j := Q.natDegree with hj
  have hcj : Q.coeff j ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hi : (Q.coeff j).coeff (Q.coeff j).natDegree ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hcj
  have h := hwdeg _ j hi
  have hc : 0 < k - 1 := by omega
  rw [Nat.le_div_iff_mul_le hc, Nat.mul_comm]
  omega

/-- **The full multiplicity-`m` Guruswami–Sudan list bound (the capstone).**
For any field `F`, distinct evaluation points `α : Fin n → F`, received word `w`, degree bound
`k ≥ 2`, multiplicity `m`, weighted-degree budget `D`, and agreement threshold `t`:

* `n · C(m+1, 2) < #gsSupport(D, k)` (the order-`m` interpolant exists), and
* `D ≤ m · t` (the multiplicity-weighted root order beats the degree budget),

imply that **every** finite set `L` of polynomials of degree `≤ k−1`, each agreeing with `w` on at
least `t` points, satisfies `L.card ≤ (D−1)/(k−1)`.

`m = 1` recovers the Sudan bound; larger `m` certifies smaller `t` (approaching the Johnson radius,
never passing it per `GSJohnsonWall`/`GSExactCountWall`). -/
theorem gs_full_list_bound [DecidableEq F] (k D m t n : ℕ) (hk : 2 ≤ k) (hD : 0 < D)
    (α w : Fin n → F) (hinj : Function.Injective α)
    (hcount : n * (m + 1).choose 2 < (gsSupport D k).card)
    (hDt : D ≤ m * t)
    (L : Finset (Polynomial F))
    (hdeg : ∀ f ∈ L, f.natDegree ≤ k - 1)
    (hagree : ∀ f ∈ L, t ≤ (Finset.univ.filter fun s : Fin n => f.eval (α s) = w s).card) :
    L.card ≤ (D - 1) / (k - 1) := by
  obtain ⟨Q, hQ0, hwdeg, hfac⟩ := gs_decoder_pipeline k D m n hD α w hinj hcount
  have hdvd : ∀ f ∈ L, (X - C f) ∣ Q := by
    intro f hf
    refine hfac f (hdeg f hf) ?_
    calc D ≤ m * t := hDt
      _ ≤ m * (Finset.univ.filter fun s : Fin n => f.eval (α s) = w s).card :=
          Nat.mul_le_mul_left m (hagree f hf)
  calc L.card ≤ Q.natDegree := R14.card_le_natDegreeY_of_sub_C_dvd Q hQ0 L hdvd
    _ ≤ (D - 1) / (k - 1) := natDegreeY_le_of_wdeg hk hQ0 hwdeg

/-! ## The multiplicity ladder at `n = 50, k = 2` — machine-checked feasibility at each rung.

`#gsSupport(D, 2) = ∑_{j<D}(D−j) = D(D+1)/2` (`gsSupport_card`).  The integer Johnson floor is
`t = 8` (`√50 ≈ 7.07`). -/

/-- `m = 1` (Sudan) is feasible at `t = 10` with `D = 10`: `50·1 = 50 < 55` and `10 ≤ 1·10`. -/
theorem ladder_m1 : 50 * (1 + 1).choose 2 < (gsSupport 10 2).card ∧ 10 ≤ 1 * 10 := by
  constructor
  · rw [gsSupport_card]; decide
  · norm_num

/-- `m = 2` is feasible at `t = 9` with `D = 17`: `50·3 = 150 < 153` and `17 ≤ 2·9 = 18` —
one agreement BELOW Sudan's reach. -/
theorem ladder_m2 : 50 * (2 + 1).choose 2 < (gsSupport 17 2).card ∧ 17 ≤ 2 * 9 := by
  constructor
  · rw [gsSupport_card]; decide
  · norm_num

/-- `m = 4` is feasible at `t = 8` — **the integer Johnson floor** — with `D = 32`:
`50·10 = 500 < 528` and `32 ≤ 4·8 = 32`. Multiplicity climbs the ladder all the way to Johnson. -/
theorem ladder_m4 : 50 * (4 + 1).choose 2 < (gsSupport 32 2).card ∧ 32 ≤ 4 * 8 := by
  constructor
  · rw [gsSupport_card]; decide
  · norm_num

/-- **The ladder, instantiated end-to-end over a real field** (`F = ZMod 53`, the 50 distinct points
`0,…,49`): at the Johnson-floor agreement `t = 8` with multiplicity `m = 4`, every finite list of
lines-or-constants (`deg ≤ 1`) with `≥ 8` agreements has size `≤ 31`.  (The hypotheses are inhabited:
`ladder_m4` + the injectivity of `Fin 50 → ZMod 53`.) -/
instance primeFact_GSFullListBound_1 : Fact (Nat.Prime 53) := ⟨by norm_num⟩

theorem ladder_m4_instance (w : Fin 50 → ZMod 53) (L : Finset (Polynomial (ZMod 53)))
    (hdeg : ∀ f ∈ L, f.natDegree ≤ 1)
    (hagree : ∀ f ∈ L,
      8 ≤ (Finset.univ.filter fun s : Fin 50 => f.eval ((s : ℕ) : ZMod 53) = w s).card) :
    L.card ≤ 31 := by
  have hinj : Function.Injective (fun s : Fin 50 => ((s : ℕ) : ZMod 53)) := by
    intro a b hab
    have hab' : ((a : ℕ) : ZMod 53) = ((b : ℕ) : ZMod 53) := hab
    have ha : ((a : ℕ) : ZMod 53).val = (a : ℕ) := ZMod.val_natCast_of_lt (by omega)
    have hb : ((b : ℕ) : ZMod 53).val = (b : ℕ) := ZMod.val_natCast_of_lt (by omega)
    have hv : ((a : ℕ) : ZMod 53).val = ((b : ℕ) : ZMod 53).val := by rw [hab']
    rw [ha, hb] at hv
    exact Fin.ext hv
  have h := gs_full_list_bound (F := ZMod 53) 2 32 4 8 50 (by norm_num) (by norm_num)
    (fun s => ((s : ℕ) : ZMod 53)) w hinj
    (ladder_m4.1) (ladder_m4.2) L hdeg hagree
  simpa using h

end ArkLib.CodingTheory.GSFullListBound

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.GSFullListBound.natDegreeY_le_of_wdeg
#print axioms ArkLib.CodingTheory.GSFullListBound.gs_full_list_bound
#print axioms ArkLib.CodingTheory.GSFullListBound.ladder_m1
#print axioms ArkLib.CodingTheory.GSFullListBound.ladder_m2
#print axioms ArkLib.CodingTheory.GSFullListBound.ladder_m4
#print axioms ArkLib.CodingTheory.GSFullListBound.ladder_m4_instance
