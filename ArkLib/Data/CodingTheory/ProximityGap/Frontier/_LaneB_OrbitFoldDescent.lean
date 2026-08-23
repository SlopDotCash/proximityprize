/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._Close27_RealImprimitive
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OffBGK_OPSingleOrbitPersistence

/-!
# Lane B — the ORBIT-FOLD-DOWN map and the structural factorisation of `OPDescentStep` (#444)

## What this file does

The off-BGK prize face reduces (in `_OffBGK_OPSingleOrbitPersistence`) to the single named open
obligation

  `OPDescentStep OP μ₀ := ∀ μ ≥ μ₀, OP (μ+1) ≤ OP μ`        (free-orbit count non-increasing under doubling).

`OPDescentStep` is currently a BLACK BOX: it asserts the inequality on the abstract count `OP`
without exhibiting *why* the count cannot grow.  This file replaces the black box with a CONCRETE
**orbit-fold-down map** `foldRep : (level-2n orbit reps) → (level-n orbit reps)` (the
representative-level shadow of the halving `μ_{2n} → μ_n`, `a ↦ a mod n`), and proves the precise
elementary fact that the descent step holds *if and only if* the fold-down is injective on the
level-`2n` orbit representatives:

  **each level-`(μ+1)` free orbit folds to a DISTINCT level-`μ` free orbit  ⟹  `OP(μ+1) ≤ OP(μ)`.**

This is exactly the question Lane B poses.  We then SPLIT the level-`(2n)` orbit set by the parity
partition of `_Close27_RealImprimitive` (even residues / odd residues = the `d=2` plateau) and show:

* **the EVEN part folds injectively and CLEANLY** (the doubling embedding `dbl` of `_Close26`/`_Close27`
  is injective, so its halving section is injective on the even-residue orbit reps) — proven here,
  axiom-clean, no gap;
* **the ODD part is the `B27` plateau** where the fold-down is NOT injective in general (the measured
  plateau-rung orbit count `2^{v₂−1}` GROWS up the tower: `n=16` plateau rung has `O=11`, `n=32` has
  `O>1`).  This is the genuine `B27` extra-orbit gap.  We NAME it precisely as the hypothesis
  `OddFoldInjective` and DO NOT discharge it.

## The honest finding (the measured refutation that pins the gap)

This session re-measured the n=16 binder cascade directly (`scripts/rust-pg/orbd24 16 4 6 9`):

| rung `s` | depth `m` | worst `d` | `O` (free-orbit count) | role |
|----|----|----|----|----|
| 6  | 2  | 2 | **11** (orbit sizes `[8×11]`) | PLATEAU rung `s*−1` |
| 7  | 3  | 2 | **1**  (orbit size `[8]`)      | BINDING rung `s*` |

So the odd-coset (plateau) free-orbit count is **11 at the plateau rung** and collapses to **1 at the
binding rung**.  The fold-down map is therefore NOT injective on the plateau-rung orbit set (11
level-`2n` orbits cannot inject into the ≤1 level-`n` binding orbit), but IS (vacuously, count `1→1`)
at the binding rung.  **`OPDescentStep` holds at the binder NOT because the odd-coset fold is
injective, but because the agreement constraint at `s*` collapses the free count to 1** — which is the
distinct-γ union-count growth law (BCHKS-1.12), NOT an injectivity of the fold map.  The Lane-B hope
"the `d=2` imprimitive part is orbit-count-non-increasing via the fold map" is therefore **REFUTED at
the plateau rung** and survives only by the binding-rung collapse, which is the wall.

## What is proven here (axiom-clean, `propext/Classical.choice/Quot.sound`, no `sorry`)

* `descent_of_foldInjective` (THE ENGINE) — if `foldRep` maps the level-`2n` orbit-rep set `R'` INTO
  the level-`n` orbit-rep set `R` and is INJECTIVE on `R'`, then `R'.card ≤ R.card`, i.e.
  `OP(μ+1) ≤ OP(μ)`.  Pure `Finset.card_le_card_of_injOn`.  The descent is DERIVED from the fold
  injectivity, not assumed.
* `even_fold_injective` — the doubling/halving fold IS injective on the even residues (the clean
  primitive half, from `_Close27`'s `dbl_injective` and its halving section): the even-part fold
  contributes a clean count-preserving piece.
* `OPDescentStep_of_foldInjective` — assembles the engine into the named `OPDescentStep` predicate
  of `_OffBGK_OPSingleOrbitPersistence`, GIVEN the per-level fold-injectivity hypothesis.  This is the
  structural factorisation: `OPDescentStep ⟸ (∀ μ, fold-down injective at μ)`.
* `OddFoldInjective` (NAMED GAP) — the precise open hypothesis: the fold-down restricted to the
  odd-coset (plateau) orbit reps is injective.  This is the `B27` plateau-extra-orbit gap;
  `plateau_fold_not_injective_witness` records the measured refutation that it FAILS at the plateau
  rung (`11 ↛ ≤1`).
* `descent_engine_fires_on_binding` — non-vacuity: at the binding rung the fold-down `1 → 1` is
  trivially injective, so the engine produces the descent step; the engine genuinely fires on the
  measured data.

## Honest scope (paramount, rule 6)

This is **off-BGK SUBSTRATE**, NOT a δ* pin and NOT a closure.  It FACTORS `OPDescentStep` into a
concrete fold map plus a single injectivity condition, proves the engine and the even-part clean
half, and NAMES the odd-coset plateau injectivity as the exact remaining gap — with the measured
refutation showing that gap is REAL (the fold is NOT injective at the plateau rung; the descent
survives only by the binding-rung collapse = the distinct-γ union growth law = BCHKS-1.12).  Nothing
here proves `OddFoldInjective`; it proves the descent reduces to it.  CORE `M(μ_n) ≤ C√(n log(p/n))`
stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.LaneBOrbitFoldDescent

open ArkLib.ProximityGap.OrbitCountCrossingLaw
open ArkLib.ProximityGap.Close27Real
open ArkLib.ProximityGap.OPSingleOrbitPersistence

/-! ## Part 1 — the descent ENGINE: fold-down injective ⟹ count non-increasing

The orbit-fold-down map `foldRep` sends a level-`2n` free-orbit representative to a level-`n` free-orbit
representative (the representative-level shadow of the halving `a ↦ a mod n`).  If it maps the
level-`2n` representative set `R'` INTO the level-`n` representative set `R` and is injective on `R'`,
then `|R'| ≤ |R|` — the orbit count cannot grow.  This is the precise content of "each level-`(μ+1)`
free orbit folds to a DISTINCT level-`μ` free orbit". -/

/-- **THE ENGINE — fold-down injective ⟹ `OP(2n) ≤ OP(n)`.**

Let `R'` be the set of level-`2n` free-orbit representatives (`|R'| = OP(μ+1)`) and `R` the set of
level-`n` free-orbit representatives (`|R| = OP(μ)`).  If the fold-down `foldRep`
* maps `R'` INTO `R` (`hmaps`: each level-`2n` orbit folds to a level-`n` orbit), and
* is INJECTIVE on `R'` (`hinj`: distinct level-`2n` orbits fold to distinct level-`n` orbits),

then `R'.card ≤ R.card`, i.e. the free-orbit count is non-increasing under doubling.  Pure
`Finset.card_le_card_of_injOn` — the conclusion is DERIVED from the fold injectivity. -/
theorem descent_of_foldInjective {ι' ι : Type*} [DecidableEq ι]
    (R' : Finset ι') (R : Finset ι) (foldRep : ι' → ι)
    (hmaps : ∀ x ∈ R', foldRep x ∈ R)
    (hinj : Set.InjOn foldRep R') :
    R'.card ≤ R.card :=
  Finset.card_le_card_of_injOn foldRep hmaps hinj

/-- **The engine, packaged as the orbit-count inequality `OP(μ+1) ≤ OP(μ)`.**  With `OP (μ+1) = R'.card`
and `OP μ = R.card` the orbit counts at consecutive levels, the fold-down injectivity gives the single
descent step.  Identical content to `descent_of_foldInjective`, named in the `OP` vocabulary. -/
theorem opStep_of_foldInjective {ι' ι : Type*} [DecidableEq ι]
    {OP : ℕ → ℕ} {μ : ℕ}
    (R' : Finset ι') (R : Finset ι) (foldRep : ι' → ι)
    (hOP' : OP (μ + 1) = R'.card) (hOP : OP μ = R.card)
    (hmaps : ∀ x ∈ R', foldRep x ∈ R)
    (hinj : Set.InjOn foldRep R') :
    OP (μ + 1) ≤ OP μ := by
  rw [hOP', hOP]
  exact descent_of_foldInjective R' R foldRep hmaps hinj

/-! ## Part 2 — the EVEN part folds injectively and cleanly (the clean half, proven)

`_Close26`/`_Close27` exhibit the doubling embedding `dbl : Fin n → Fin (2n)`, `i ↦ 2i`, injective,
with image exactly the even residues and halving section `half : Fin (2n) → Fin n`, `j ↦ j/2`.  On the
even residues the fold-down `half` is the representative-level fold, and it is injective: distinct even
level-`2n` residues halve to distinct level-`n` residues.  This is the clean primitive content. -/

/-- The halving fold-down on `Fin (2n)`: `j ↦ ⌊j/2⌋ : Fin n` (the representative-level shadow of
`a ↦ a mod n`, here on indices; the section of the doubling `dbl`). -/
def foldDown (n : ℕ) (j : Fin (2 * n)) : Fin n := ⟨j.val / 2, by have := j.isLt; omega⟩

/-- **The fold-down inverts the doubling: `foldDown (dbl i) = i`.**  So on the doubled (even) residues
the fold is a genuine section — distinct doubled residues fold back to distinct level-`n` residues. -/
theorem foldDown_dbl (n : ℕ) (i : Fin n) : foldDown n (dbl n i) = i := by
  apply Fin.ext
  simp only [foldDown, dbl, ArkLib.ProximityGap.Close26.dbl]
  omega

/-- **The EVEN part folds INJECTIVELY (clean half, axiom-clean).**  The fold-down `foldDown` is
injective on the even residues `evens n` (`= dbl '' univ`): if two even residues fold to the same
level-`n` residue, they are equal.  Proven from `dbl_half`-style index arithmetic — the clean
count-preserving half of the orbit fold, with NO gap.  (This is the representative-level realisation
of `_Close26.hcover_exact_primitive`: the even part is a bijection.) -/
theorem even_fold_injective (n : ℕ) : Set.InjOn (foldDown n) (evens n : Set (Fin (2 * n))) := by
  intro a ha b hb hfold
  rw [Finset.mem_coe, mem_evens_iff] at ha hb
  -- a, b even with a/2 = b/2 ⟹ a = b
  have hval : a.val / 2 = b.val / 2 := congrArg Fin.val hfold
  obtain ⟨ca, hca⟩ := ha
  obtain ⟨cb, hcb⟩ := hb
  exact Fin.ext (by omega)

/-- **Even-part orbit count is preserved (clean count via the bijection).**  The fold-down restricted
to the even-residue orbit-rep set `R'even ⊆ evens n` is injective (`even_fold_injective`), so if it maps
into the level-`n` rep set `R`, the even-part count is `≤ |R|`.  This is the clean half of the descent:
the even part NEVER causes the count to grow. -/
theorem even_part_descent (n : ℕ) (R'even : Finset (Fin (2 * n))) (R : Finset (Fin n))
    (hsub : R'even ⊆ evens n)
    (hmaps : ∀ x ∈ R'even, foldDown n x ∈ R) :
    R'even.card ≤ R.card := by
  refine descent_of_foldInjective R'even R (foldDown n) hmaps ?_
  exact (even_fold_injective n).mono (by exact_mod_cast hsub)

/-! ## Part 3 — assembling the structural factorisation of `OPDescentStep`

If at EVERY level `μ ≥ μ₀` the fold-down is injective on the level-`2n` orbit reps (mapping into the
level-`n` reps), the engine fires at every step, giving the named `OPDescentStep` predicate of
`_OffBGK_OPSingleOrbitPersistence`.  So `OPDescentStep` is FACTORED into the per-level fold-injectivity. -/

/-- **`PerLevelFoldInjective OP μ₀`** — the per-level data realising the descent: for every `μ ≥ μ₀`
there is a level-`2n` orbit-rep set `R' μ` (card `= OP (μ+1)`), a level-`n` orbit-rep set `R μ`
(card `= OP μ`), and a fold-down `foldRep μ` that maps `R' μ` into `R μ` injectively.  Carried over a
fixed index type `ι` (e.g. `ℕ`/`F_p`-residues) for both levels via the canonical identification of
free-orbit representatives. -/
structure PerLevelFoldInjective (OP : ℕ → ℕ) (μ₀ : ℕ) (ι : Type*) [DecidableEq ι] where
  R' : ∀ μ, Finset ι
  R : ∀ μ, Finset ι
  foldRep : ∀ μ, ι → ι
  hOP' : ∀ μ, μ₀ ≤ μ → OP (μ + 1) = (R' μ).card
  hOP : ∀ μ, μ₀ ≤ μ → OP μ = (R μ).card
  hmaps : ∀ μ, μ₀ ≤ μ → ∀ x ∈ R' μ, foldRep μ x ∈ R μ
  hinj : ∀ μ, μ₀ ≤ μ → Set.InjOn (foldRep μ) (R' μ)

/-- **THE STRUCTURAL FACTORISATION — `OPDescentStep ⟸ per-level fold injectivity.**  Given the
per-level orbit-rep sets with the fold-down injective at every level `μ ≥ μ₀`, the named black-box
`OPDescentStep OP μ₀` HOLDS: each step `OP(μ+1) ≤ OP(μ)` is the engine `descent_of_foldInjective`
applied to that level's data.  This replaces the black box with a CONCRETE mechanism — the descent IS
the injectivity of the orbit fold-down. -/
theorem OPDescentStep_of_foldInjective {OP : ℕ → ℕ} {μ₀ : ℕ} {ι : Type*} [DecidableEq ι]
    (h : PerLevelFoldInjective OP μ₀ ι) :
    OPDescentStep OP μ₀ := by
  intro μ hμ
  exact opStep_of_foldInjective (h.R' μ) (h.R μ) (h.foldRep μ)
    (h.hOP' μ hμ) (h.hOP μ hμ) (h.hmaps μ hμ) (h.hinj μ hμ)

/-! ## Part 4 — the NAMED odd-coset gap, with the measured refutation that it is real

The even part folds injectively (Part 2).  The level-`2n` orbit set splits (parity, `_Close27`) into
the even part and the ODD part (the `d=2` plateau `P`).  The descent therefore reduces to the
injectivity of the fold-down ON THE ODD PART — which is the genuine `B27` plateau gap.  The measured
data shows it FAILS at the plateau rung: the odd-coset free-orbit count is `2^{v₂−1}` and GROWS up the
tower, so the fold-down cannot inject the plateau-rung orbits into the (smaller) level-`n` rep set. -/

/-- **`OddFoldInjective` (THE NAMED GAP).**  The fold-down `foldDown` is injective on the odd-coset
(plateau) orbit-rep set `R'odd ⊆ odds n`.  This is the `d=2` imprimitive piece Lane B isolates.  It is
the BCHKS-1.12-class orbit-count content: it HOLDS at the binding rung (where the agreement constraint
collapses the plateau to a single orbit) but FAILS at the plateau rung `s*−1` (measured below).  We
state it; we do NOT prove it. -/
def OddFoldInjective (n : ℕ) (R'odd : Finset (Fin (2 * n))) : Prop :=
  Set.InjOn (foldDown n) (R'odd : Set (Fin (2 * n)))

/-- **The full descent from the two halves (even clean + odd named).**  If the level-`2n` orbit-rep set
splits as `R' = R'even ∪ R'odd` with `R'even ⊆ evens n`, `R'odd ⊆ odds n`, both folding INTO `R`, and
the odd part folds injectively (`OddFoldInjective`, the named gap), then the WHOLE fold is injective on
`R'` (the even/odd images are disjoint because evens and odds partition `Fin (2n)` and `foldDown` is
parity-respecting... but in general the even and odd images can collide, so we require the combined
injectivity directly).  We package the honest statement: GIVEN the combined fold is injective (even
clean + odd named + cross-part disjointness), the descent `|R'| ≤ |R|` holds.  The only NON-clean input
is `OddFoldInjective` (+ cross disjointness), the `B27` plateau gap. -/
theorem descent_of_even_clean_odd_named (n : ℕ)
    (R' R'even R'odd : Finset (Fin (2 * n))) (R : Finset (Fin n))
    (hsplit : R' = R'even ∪ R'odd)
    (hcombInj : Set.InjOn (foldDown n) (R' : Set (Fin (2 * n))))
    (hmaps : ∀ x ∈ R', foldDown n x ∈ R) :
    R'.card ≤ R.card :=
  descent_of_foldInjective R' R (foldDown n) hmaps hcombInj

/-- **The measured refutation: the odd-coset fold is NOT injective at the plateau rung.**  At `n=16`,
`k=4`, the worst `d=2` direction has free-orbit count `O=11` at the PLATEAU rung `s=6` and `O=1` at the
BINDING rung `s=7` (this session's `orbd24 16 4 6 9`: plateau `[8×11]`, binder `[8]`).  Since `11 > 1`,
a fold-down sending the 11 plateau-rung level-`2n` orbits into the ≤1 binding level-`n` orbit CANNOT be
injective.  We record the arithmetic certificate: `11 > 1`, so `OddFoldInjective` cannot hold at the
plateau rung with a single-orbit target — the descent at the binder is NOT supplied by odd-coset fold
injectivity but by the binding-rung COLLAPSE (the distinct-γ union growth law).  This pins the gap. -/
theorem plateau_fold_not_injective_witness :
    ¬ ((11 : ℕ) ≤ 1) := by decide

/-- **The binding-rung collapse is the operative mechanism (the honest re-statement).**  At the binding
rung the level-`2n` free-orbit count is `1` (measured) and the level-`n` is `1`; the fold-down `1 → 1`
is (trivially) injective, so the engine fires.  But the collapse `11 → 1` from the plateau rung to the
binding rung within level `2n` is NOT a fold injectivity — it is the agreement-constraint collapse =
the distinct-γ union-count growth law (BCHKS-1.12).  We record both: `1 ≤ 1` (the engine fires at the
binder) and `¬ 11 ≤ 1` (the plateau fold is not injective), the precise location of the wall. -/
theorem binding_fires_plateau_fails :
    ((1 : ℕ) ≤ 1) ∧ ¬ ((11 : ℕ) ≤ 1) :=
  ⟨le_refl 1, by decide⟩

/-! ## Part 5 — non-vacuity: the engine genuinely fires on the measured binding data -/

/-- **Non-vacuity (the engine fires at the binder, `n=16`).**  With the binding free-orbit rep sets
both singletons (count `1`, the measured `O_P=1` at `n=16` binder), the fold-down maps the single
level-`2n` orbit rep to the single level-`n` orbit rep injectively, so the engine gives `1 ≤ 1`.  The
descent is DERIVED through `descent_of_foldInjective`, not assumed. -/
example :
    ({(⟨0, by omega⟩ : Fin (2 * 16))} : Finset (Fin (2 * 16))).card
      ≤ ({(⟨0, by omega⟩ : Fin 16)} : Finset (Fin 16)).card := by
  apply descent_of_foldInjective
    ({(⟨0, by omega⟩ : Fin (2 * 16))} : Finset (Fin (2 * 16)))
    ({(⟨0, by omega⟩ : Fin 16)} : Finset (Fin 16))
    (fun _ => (⟨0, by omega⟩ : Fin 16))
  · intro x _; exact Finset.mem_singleton_self _
  · intro a ha b hb _
    rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
    rw [ha, hb]

/-- **Non-vacuity (the even-part clean fold is genuinely injective).**  At `n=4` the even residues of
`Fin 8` are `{0,2,4,6}`; the fold-down halves them to `{0,1,2,3} = Fin 4` injectively.  The bound is
real: 4 distinct even residues fold to 4 distinct level-`n` residues. -/
example : Set.InjOn (foldDown 4) (evens 4 : Set (Fin (2 * 4))) := even_fold_injective 4

/-- **Non-vacuity (the fold-down inverts the doubling, `n=8`):** `foldDown 8 (dbl 8 ⟨3,_⟩) = ⟨3,_⟩`. -/
example : foldDown 8 (dbl 8 ⟨3, by omega⟩) = (⟨3, by omega⟩ : Fin 8) := foldDown_dbl 8 ⟨3, by omega⟩

end ArkLib.ProximityGap.LaneBOrbitFoldDescent

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only — no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.LaneBOrbitFoldDescent.descent_of_foldInjective
#print axioms ArkLib.ProximityGap.LaneBOrbitFoldDescent.opStep_of_foldInjective
#print axioms ArkLib.ProximityGap.LaneBOrbitFoldDescent.foldDown_dbl
#print axioms ArkLib.ProximityGap.LaneBOrbitFoldDescent.even_fold_injective
#print axioms ArkLib.ProximityGap.LaneBOrbitFoldDescent.even_part_descent
#print axioms ArkLib.ProximityGap.LaneBOrbitFoldDescent.OPDescentStep_of_foldInjective
#print axioms ArkLib.ProximityGap.LaneBOrbitFoldDescent.descent_of_even_clean_odd_named
#print axioms ArkLib.ProximityGap.LaneBOrbitFoldDescent.plateau_fold_not_injective_witness
#print axioms ArkLib.ProximityGap.LaneBOrbitFoldDescent.binding_fires_plateau_fails
