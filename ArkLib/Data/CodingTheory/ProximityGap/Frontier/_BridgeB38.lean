/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Nat.Lattice

/-!
# Bridge B38 — converse of binding: incidence over budget ⟹ below the crossing (target X, #444)

**Claim (spec B38).** *Bad-side converse of the crossing.* If at some over-determination depth
`m` there is a far direction whose far-line incidence exceeds the budget, then `m` lies strictly
below the binding depth `m*`. This is the contrapositive of the *definition* of binding: `m*` is
the **shallowest** depth at which every far direction is within budget, so any budget violation at
`m` certifies `m < m*` (`m` is on the bad side of the crossing).

## Set-up (self-contained; no character-sum substrate consumed)

We use the abstract data the empirical-formula programme `E1..E7` attaches to a window:

* a finite, nonempty index set `Dir` of *far directions* (the monomial pencils
  `γ : s₀ + γ s₁ ∈ G`);
* a *far-line incidence* `D : ℕ → Dir → ℕ` (depth `m`, direction `d`), the count
  `#{γ : the far line meets the period spectrum}`, assumed **antitone in `m`** — deeper
  over-determination can only *cut* incidence (`D_antitone`), the structural monotonicity behind
  the crossing law `E6`;
* a `budget : ℕ` (the prize budget `⌊q·ε*⌋ ≈ n`).

The **worst-case incidence at depth `m`** is `Dstar D m = sup_d D m d` (a finite `Finset.sup`).
The window is *admissible at depth `m`* iff `Dstar D m ≤ budget`. Under antitonicity the admissible
set is an up-closed initial segment `[m*, ∞)`, and the **binding depth** is its shallow edge

  `mStar = sInf { m : Dstar D m ≤ budget }`

— the crossing point `m*` of `E6/E7` (capacity − δ* = (m*−1)/n).

## What is proven (all axiom-clean)

* `Dstar_apply_le` / `exists_Dstar_eq` — `Dstar` is the achieved finite max over directions.
* `Dstar_antitone` — worst-case incidence inherits antitonicity in `m`.
* `over_budget_dir_imp_over_budget` — a single over-budget direction makes the window
  inadmissible (`budget < Dstar D m`), i.e. `m ∉ Admissible`.
* **`over_budget_imp_lt_mStar` (target X).** If some far direction has incidence `> budget` at
  depth `m`, then `m < mStar` — *provided the binding depth exists*, i.e. some admissible depth
  exists (`(Admissible D budget).Nonempty`). Antitonicity makes the admissible set up-closed, so an
  inadmissible `m` is strictly below its shallow edge `sInf = mStar`.
* **`mStar_admissible`** — the shallow edge is itself admissible (`Dstar D mStar ≤ budget`): the
  crossing is *attained*, so `m*` is a genuine first-crossing depth.
* **`lt_mStar_iff_over_budget`** — the sharp converse/forward equivalence under antitonicity:
  for the up-closed admissible segment, `m < mStar ↔ budget < Dstar D m` (`m` below the crossing
  ⟺ `m` is over budget). The B38 target is the `→`-free `mpr` direction packaged from incidence.

The mathematical content is the order skeleton of the binding/crossing definition; the hard
analytic input (whether incidence actually stays `≤ budget` from `m*` on) is the open core of
`OpenCoreConditionalPin` and is **not** touched here.

Issue #444.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB38

variable {Dir : Type*} [Fintype Dir] [Nonempty Dir]

/-- **Worst-case far-line incidence at depth `m`**: the finite maximum over far directions. -/
def Dstar (D : ℕ → Dir → ℕ) (m : ℕ) : ℕ := Finset.univ.sup (fun d => D m d)

/-- Every direction's incidence is `≤` the worst case. -/
theorem Dstar_apply_le (D : ℕ → Dir → ℕ) (m : ℕ) (d : Dir) : D m d ≤ Dstar D m :=
  Finset.le_sup (f := fun d => D m d) (Finset.mem_univ d)

/-- The worst case is achieved (`Dir` finite, nonempty): `Dstar D m = D m d₀` for some `d₀`. -/
theorem exists_Dstar_eq (D : ℕ → Dir → ℕ) (m : ℕ) : ∃ d, Dstar D m = D m d := by
  classical
  obtain ⟨d, _, hd⟩ :=
    Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun d => D m d)
  exact ⟨d, hd⟩

/-- If a window is admissible (`Dstar ≤ budget`) then every direction is within budget. -/
theorem le_budget_of_admissible {D : ℕ → Dir → ℕ} {m budget : ℕ}
    (h : Dstar D m ≤ budget) (d : Dir) : D m d ≤ budget :=
  le_trans (Dstar_apply_le D m d) h

/-- **A single over-budget direction makes the window inadmissible at that depth.** -/
theorem over_budget_dir_imp_over_budget {D : ℕ → Dir → ℕ} {m budget : ℕ} {d : Dir}
    (h : budget < D m d) : budget < Dstar D m :=
  lt_of_lt_of_le h (Dstar_apply_le D m d)

/-- `Dstar` inherits antitonicity in `m` from the per-direction incidence. -/
theorem Dstar_antitone {D : ℕ → Dir → ℕ} (hD : ∀ d, Antitone (fun m => D m d)) :
    Antitone (Dstar D) := by
  intro a b hab
  refine Finset.sup_le (fun d _ => ?_)
  exact le_trans (hD d hab) (Dstar_apply_le D a d)

/-- The set of **admissible depths**: those whose worst-case incidence is within budget. -/
def Admissible (D : ℕ → Dir → ℕ) (budget : ℕ) : Set ℕ := {m | Dstar D m ≤ budget}

@[simp] theorem mem_Admissible {D : ℕ → Dir → ℕ} {budget m : ℕ} :
    m ∈ Admissible D budget ↔ Dstar D m ≤ budget := Iff.rfl

/-- The **binding depth** `m*`: the shallowest admissible depth (crossing point of the up-closed
admissible segment under antitonicity). -/
noncomputable def mStar (D : ℕ → Dir → ℕ) (budget : ℕ) : ℕ :=
  sInf (Admissible D budget)

/-- The binding depth is admissible whenever the admissible set is nonempty: the crossing is
*attained*. -/
theorem mStar_admissible {D : ℕ → Dir → ℕ} {budget : ℕ}
    (hne : (Admissible D budget).Nonempty) :
    Dstar D (mStar D budget) ≤ budget :=
  Nat.sInf_mem hne

/-- **Target X — converse of binding.**

If at depth `m` some far direction `d` has far-line incidence strictly above the budget, then `m`
is below the binding depth: `m < mStar`. The only hypotheses are antitonicity of the per-direction
incidence (the structural monotonicity of the crossing law) and existence of *some* admissible
depth (so the binding depth `m* = sInf` exists). -/
theorem over_budget_imp_lt_mStar {D : ℕ → Dir → ℕ} {m budget : ℕ} {d : Dir}
    (hD : ∀ d, Antitone (fun m => D m d))
    (hover : budget < D m d)
    (hne : (Admissible D budget).Nonempty) :
    m < mStar D budget := by
  have hAnti : Antitone (Dstar D) := Dstar_antitone hD
  -- `m` is inadmissible.
  have hm_bad : budget < Dstar D m := over_budget_dir_imp_over_budget hover
  -- The binding depth is admissible.
  have hadm : Dstar D (mStar D budget) ≤ budget := mStar_admissible hne
  -- If `mStar ≤ m`, antitonicity would force `m` admissible — contradiction.
  by_contra hle
  push_neg at hle  -- mStar ≤ m
  have : Dstar D m ≤ Dstar D (mStar D budget) := hAnti hle
  exact absurd (le_trans this hadm) (not_le.mpr hm_bad)

/-- **Sharp equivalence (under antitonicity, with attained crossing).** For the up-closed
admissible segment, a depth is below the binding depth **iff** its worst-case incidence is over
budget. The B38 converse is the `mpr` (over-budget ⟹ below crossing); the forward direction is the
*definition* of admissibility above the crossing. -/
theorem lt_mStar_iff_over_budget {D : ℕ → Dir → ℕ} {m budget : ℕ}
    (hD : ∀ d, Antitone (fun m => D m d))
    (hne : (Admissible D budget).Nonempty) :
    m < mStar D budget ↔ budget < Dstar D m := by
  constructor
  · -- below the crossing ⟹ inadmissible: `m < sInf` means `m ∉ Admissible`.
    intro hlt
    have : m ∉ Admissible D budget := Nat.notMem_of_lt_sInf hlt
    simpa [Admissible, not_le] using this
  · -- over budget ⟹ below the crossing, via the worst-case direction realizing `Dstar`.
    intro hover
    obtain ⟨d, hd⟩ := exists_Dstar_eq D m
    exact over_budget_imp_lt_mStar hD (by rw [← hd]; exact hover) hne

end ArkLib.ProximityGap.BridgeB38

-- Axiom audit (expected: propext, Classical.choice, Quot.sound)
#print axioms ArkLib.ProximityGap.BridgeB38.Dstar_antitone
#print axioms ArkLib.ProximityGap.BridgeB38.over_budget_imp_lt_mStar
#print axioms ArkLib.ProximityGap.BridgeB38.lt_mStar_iff_over_budget
