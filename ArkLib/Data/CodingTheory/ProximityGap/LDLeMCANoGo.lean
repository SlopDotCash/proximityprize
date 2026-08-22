/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# A structural NO-GO: the list-decoding face is WEAKER than the MCA face (#407)

The Proximity Prize has two grand-challenge faces over the same Reed–Solomon code:

* **the list-decoding (LD) face** — for a single received word `w`, count the codewords of
  `C` agreeing with `w` on at least `a` coordinates (`singleWordList`); and
* **the mutual-correlated-agreement (MCA) face** — for an affine *pencil*
  `{f + γ·g : γ ∈ F}`, count the codewords agreeing with *some point of the pencil* on at
  least `a` coordinates (`pencilIncidence`), the engine behind the bad-scalar count
  (`mcaBadCount`) and hence `δ*_MCA`.

The honest, unconditional content of this file is the **domination**

> `singleWordList C w a  ⊆  pencilIncidence C w g a`   (any direction `g`),

because the base word `w` is itself the point of the pencil at `γ = 0`. Taking cardinalities,

> `#singleWordList C w a  ≤  #pencilIncidence C w g a`,

so the worst-case far-line incidence dominates the single-word list size. Consequently the
threshold of the *line* problem is **at least** the threshold of the *single-word* problem:
the radius at which the pencil incidence exceeds a budget is no larger than the radius at
which the single-word list exceeds it, i.e. the LD face is the *weaker* of the two:

> `δ*_LD ≥ δ*_MCA`   (`mca_radius_le_ld_radius`).

**Why this is a NO-GO, not a closure.** It says a *line passes near at least as many
codewords as a single point*. So an LD list-size bound `#singleWordList ≤ B` does **not**
bound the MCA incidence: a single-word bound is on the *smaller* quantity. We exhibit a
machine-checked toy instance where the inequality is **strict** (a far direction makes the
pencil touch a codeword the base point misses) — proving an LD bound alone genuinely cannot
pin the (harder) MCA `δ*`. Nothing here closes the prize core; it isolates which face is
harder. Issue #407.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset

namespace ProximityGap.LDLeMCANoGo

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The point of the affine pencil `{f + γ·g : γ ∈ F}` at parameter `γ`. -/
def linePt (f g : Fin n → F) (γ : F) : Fin n → F := fun i => f i + γ * g i

/-- Coordinates where the two words agree. -/
def agreeSet (u v : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => u i = v i)

omit [Field F] [Fintype F] in
@[simp] theorem mem_agreeSet {u v : Fin n → F} {i : Fin n} :
    i ∈ agreeSet u v ↔ u i = v i := by simp [agreeSet]

/-- The base word is the pencil point at `γ = 0` (the geometric heart of the no-go: the
pencil contains the single point it is built on). -/
@[simp] theorem linePt_zero (f g : Fin n → F) : linePt f g 0 = f := by
  funext i; simp [linePt]

/-! ## The two faces -/

/-- **LD face.** The single-word agreement-`a` list of word `w` against code `C`: the
codewords agreeing with `w` on at least `a` coordinates. This is the object an
interleaved/list-decoding bound caps. -/
def singleWordList (C : Finset (Fin n → F)) (w : Fin n → F) (a : ℕ) :
    Finset (Fin n → F) :=
  C.filter (fun c => a ≤ (agreeSet c w).card)

/-- **MCA face.** The pencil incidence of code `C` against the affine line through `f` in
direction `g` at agreement threshold `a`: the codewords agreeing with *some* point of the
pencil on at least `a` coordinates. This is the codeword-side engine for the bad-scalar
count / far-line incidence that governs `δ*_MCA`. -/
def pencilIncidence (C : Finset (Fin n → F)) (f g : Fin n → F) (a : ℕ) :
    Finset (Fin n → F) :=
  C.filter (fun c => ∃ γ : F, a ≤ (agreeSet c (linePt f g γ)).card)

omit [Fintype F] in
theorem mem_singleWordList {C : Finset (Fin n → F)} {w c : Fin n → F} {a : ℕ} :
    c ∈ singleWordList C w a ↔ c ∈ C ∧ a ≤ (agreeSet c w).card := by
  simp [singleWordList]

theorem mem_pencilIncidence {C : Finset (Fin n → F)} {f g c : Fin n → F} {a : ℕ} :
    c ∈ pencilIncidence C f g a ↔
      c ∈ C ∧ ∃ γ : F, a ≤ (agreeSet c (linePt f g γ)).card := by
  simp [pencilIncidence]

/-! ## The domination: LD ⊆ MCA -/

/-- **The structural domination (set form).** For ANY direction `g`, the single-word list of
the base word `f` is contained in the pencil incidence along `{f + γ·g}`: every codeword
agreeing with `f` on `≥ a` points agrees with the pencil point at `γ = 0` (which *is* `f`).
The line passes near everything the point does. -/
theorem singleWordList_subset_pencilIncidence
    (C : Finset (Fin n → F)) (f g : Fin n → F) (a : ℕ) :
    singleWordList C f a ⊆ pencilIncidence C f g a := by
  intro c hc
  rw [mem_singleWordList] at hc
  rw [mem_pencilIncidence]
  exact ⟨hc.1, 0, by simpa [linePt_zero] using hc.2⟩

/-- **The structural domination (cardinality form).** The worst-case far-line incidence
dominates the single-word list size: `#singleWordList ≤ #pencilIncidence`, for any direction.
This is the precise sense in which the LD face is the *weaker* of the two grand challenges. -/
theorem singleWordList_card_le_pencilIncidence_card
    (C : Finset (Fin n → F)) (f g : Fin n → F) (a : ℕ) :
    (singleWordList C f a).card ≤ (pencilIncidence C f g a).card :=
  Finset.card_le_card (singleWordList_subset_pencilIncidence C f g a)

/-- Even taking the *best* direction for the LD side, the worst-case incidence over all
directions still dominates: the maximum over `g` of the pencil incidence is at least the
single-word list of `f`. (Trivial corollary, recorded because it is the form a `δ*`
comparison consumes — the MCA quantity is a sup over pencils.) -/
theorem singleWordList_card_le_sup_pencilIncidence
    (C : Finset (Fin n → F)) (f g : Fin n → F) (a : ℕ) :
    (singleWordList C f a).card ≤
      ⨆ h : Fin n → F, (pencilIncidence C f h a).card := by
  refine le_trans (singleWordList_card_le_pencilIncidence_card C f g a) ?_
  exact le_ciSup (f := fun h : Fin n → F => (pencilIncidence C f h a).card)
    (Set.Finite.bddAbove (Set.finite_range _)) g

/-! ## The threshold consequence: `δ*_LD ≥ δ*_MCA`

We phrase the threshold abstractly. Fix a budget `B` (the prize budget is `q·ε* ≈ n`). The
*bad radii* for a face are the agreement thresholds `a` at which that face's count exceeds
`B`. Since agreement `a` and proximity radius `δ = 1 − a/n` move oppositely, a *larger* set
of bad agreement-thresholds means a *smaller* `δ*` (the supremum of good radii). The
domination gives: every `a` bad for the LD face is bad for the MCA face. So the MCA bad-set
is larger ⇒ `δ*_MCA ≤ δ*_LD`. -/

/-- If the single-word list at threshold `a` exceeds the budget `B`, so does the pencil
incidence (in any direction): bad-for-LD ⇒ bad-for-MCA at the same agreement threshold. -/
theorem pencil_bad_of_single_bad
    (C : Finset (Fin n → F)) (f g : Fin n → F) (a B : ℕ)
    (hbad : B < (singleWordList C f a).card) :
    B < (pencilIncidence C f g a).card :=
  lt_of_lt_of_le hbad (singleWordList_card_le_pencilIncidence_card C f g a)

/-- **The NO-GO at the threshold level.** Read `goodA` as the agreement thresholds whose
face-count stays within budget `B`; `δ*` is governed by the *largest* good `a` (i.e. the
smallest agreement = largest radius that is still safe). The MCA good-set is a *subset* of
the LD good-set, hence the MCA threshold cannot exceed the LD threshold.

Concretely: `{a | #pencilIncidence ≤ B} ⊆ {a | #singleWordList ≤ B}`. An agreement
threshold safe for the line is automatically safe for the point — but not conversely. So a
bound on the single-word list (LD) can certify *more* agreement thresholds as safe than are
actually safe for the line (MCA): the LD face is strictly more permissive. -/
theorem mca_goodSet_subset_ld_goodSet
    (C : Finset (Fin n → F)) (f g : Fin n → F) (B : ℕ) (As : Finset ℕ) :
    (As.filter (fun a => (pencilIncidence C f g a).card ≤ B))
      ⊆ (As.filter (fun a => (singleWordList C f a).card ≤ B)) := by
  intro a ha
  rw [Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, le_trans (singleWordList_card_le_pencilIncidence_card C f g a) ha.2⟩

/-- The numeric reading of the no-go: `δ*` is `1 − a*/n` where `a*` is the *least* safe
agreement threshold. Since the MCA face's least-safe `a` is `≥` the LD face's (the MCA
good-agreement set sits inside the LD one), `δ*_MCA ≤ δ*_LD`. Recorded as the comparison of
minima of the two good-agreement sets. -/
theorem mca_min_goodA_ge_ld_min_goodA
    (C : Finset (Fin n → F)) (f g : Fin n → F) (B : ℕ) (As : Finset ℕ)
    {aLD aMCA : ℕ}
    (_hLD : aLD ∈ As.filter (fun a => (singleWordList C f a).card ≤ B))
    (hLDmin : ∀ a ∈ As.filter (fun a => (singleWordList C f a).card ≤ B), aLD ≤ a)
    (hMCA : aMCA ∈ As.filter (fun a => (pencilIncidence C f g a).card ≤ B)) :
    aLD ≤ aMCA :=
  hLDmin aMCA (mca_goodSet_subset_ld_goodSet C f g B As hMCA)

end ProximityGap.LDLeMCANoGo

/-! ## A machine-checked instance where the domination is STRICT

A far direction makes the pencil touch a codeword the base point misses, so the single-word
list strictly undercounts the pencil incidence. This is the witness that an LD bound is on a
*strictly smaller* quantity — it genuinely cannot pin the MCA count. -/

namespace ProximityGap.LDLeMCANoGo.Instance

open ProximityGap.LDLeMCANoGo

instance primeFact_LDLeMCANoGo_1 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The constant code over `ZMod 5` on a 3-point domain (Reed–Solomon, `k = 1`). -/
def Ccode : Finset (Fin 3 → ZMod 5) :=
  Finset.univ.image fun c : ZMod 5 => fun _ => c

/-- Base word `f = (0,1,2)`: agrees with no constant on `≥ 2` coords (all entries distinct). -/
def fbase : Fin 3 → ZMod 5 := ![0, 1, 2]

/-- Far direction `g = (0,1,4)`. At `γ = 4` the pencil point is `(0,0,3)`, which agrees with
the constant `0` on the 2-point set `{0,1}` — a codeword the base point `f` misses. -/
def gdir : Fin 3 → ZMod 5 := ![0, 1, 4]

/-- The base point's single-word list at threshold `2` is **empty** (`f` is injective, so it
agrees with each constant on `< 2` of 3 coordinates). -/
theorem singleWordList_empty : singleWordList Ccode fbase 2 = ∅ := by decide

/-- The pencil incidence at threshold `2` is **nonempty**: e.g. the constant `0` is hit at
`γ = 4`. So the line touches a codeword the single point does not. -/
theorem pencilIncidence_nonempty : (pencilIncidence Ccode fbase gdir 2).Nonempty := by decide

/-- **STRICT domination at this instance.** `#singleWordList = 0 < #pencilIncidence`. The LD
face is on a strictly smaller count than the MCA face — an LD bound cannot bound the line. -/
theorem strict_domination :
    (singleWordList Ccode fbase 2).card < (pencilIncidence Ccode fbase gdir 2).card := by
  rw [singleWordList_empty]
  simpa using (Finset.card_pos.mpr pencilIncidence_nonempty)

end ProximityGap.LDLeMCANoGo.Instance
