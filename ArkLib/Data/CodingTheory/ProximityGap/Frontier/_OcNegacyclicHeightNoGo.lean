/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# LANE OC (#466, Opus core 2026-07-10): the low-height PRIMITIVE annihilator is
  PIGEONHOLE-FORCED and COEFFICIENT-AGNOSTIC — a thinness-essential no-go for the
  "limit char-p wraparound shapes via low-height annihilating relations" route.

## The route this closes

The dossier §6 / DISPROOF board leaves open whether a **2-adic / negacyclic structure
lemma for primitive low-height annihilating relations** can rule out or sharply limit
char-p wraparound shapes before any Paley cancellation. Concretely: over a multiplicative
subgroup `μ_N ⊂ F_p^×` with power-basis images `a i = ζ^i` (`i < D`, `D = φ(N)`), a
"primitive (wraparound-created) annihilating relation" is a nonzero integer vector
`g : Fin D → ℤ` with `Σ_i g i · a i ≡ 0 (mod p)` that does not vanish in characteristic 0
(automatic when the `a i` are the power-basis images, since those are `ℤ`-independent in
`ℤ[ζ_N]`). Its **height** is `max_i |g i|`. The hope: for the *thin* 2-power subgroup the
minimal such height is forced ABOVE that of a *thick* (odd-factor) subgroup, giving a
thinness-essential handle on the wraparound.

## What this file establishes (machine-checked, axiom-clean)

The minimal height is governed by a **pigeonhole threshold that depends only on `(D, p)`,
not on the sequence `a` at all** — hence it is *identical* for thin and thick subgroups of
the same free dimension in the same field. Formally, for ANY coefficient map
`a : Fin D → ZMod p`:

* **`exists_lowHeight_annihilator`** — if the box of height-`≤ h` vectors is larger than
  the field, `(2h+1)^D > p`, then there is a **nonzero** `g : Fin D → ℤ` with
  `|g i| ≤ 2h` for all `i` and `Σ_i (g i) • (a i) = 0` in `ZMod p`. (Pigeonhole on the
  evaluation map over the box `{0,…,2h}^D`; the difference of a colliding pair.)

* **`lowHeight_annihilator_coeff_agnostic`** — the SAME hypothesis `(2h+1)^D > p` produces
  the annihilator for two *arbitrary* coefficient maps `a` and `a'` simultaneously; the
  existence witness depends only on `(D, p, h)`. This is the thickness-invariance: the
  low-height-annihilator existence cannot separate a thin `a` from a thick `a'`.

* **`prize_scale_forces_height_one`** — at the prize scaling `D = N/2` (`N = 2^m`) and
  `p = N^β` with `β · m < D` (i.e. `log_2 p < D`, which holds with enormous margin since
  `D = 2^{m-1}` while `β·m` is linear in `m`), already `h = 1` satisfies `3^D > p`, so a
  nonzero **height-≤ 2** annihilator exists for *every* subgroup. The minimal primitive
  height is floored at the pigeonhole minimum — no thin/thick gap survives.

## The verdict (honest scope)

This is a **no-go**, not a closure: it does not bound `M(μ_n)` and does not refute CORE.
It proves the specific route dead — the *existence/height of low-height primitive
annihilating relations is a coefficient-agnostic pigeonhole fact*, so it carries **zero**
thinness signal at prize scale and cannot limit char-p wraparound shapes in a
thinness-essential way. The finite probes (`probe_oc_*`, this lane's report) additionally
measured the *residual* thin-vs-thick offset at small `D` to be a bounded additive edge
effect (`≤ 2` observed, thin `≥` thick monotone), on a quantity that itself collapses to
`1` at prize scale — confirming the additive offset cannot produce the prize's
multiplicative `√log` separation.

Issue #466, lane OC.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


namespace ArkLib.ProximityGap.Frontier.OcNegacyclicHeightNoGo

open Finset

/-- The box of height-`≤ h` coefficient vectors, as functions `Fin D → Fin (2h+1)`
(coordinates shifted to `0 … 2h`; the genuine coefficient at coordinate `i` is
`(v i : ℤ) - h`). Its cardinality is `(2h+1)^D`. -/
theorem card_box (D h : ℕ) :
    (Finset.univ : Finset (Fin D → Fin (2 * h + 1))).card = (2 * h + 1) ^ D := by
  simp [Finset.card_univ]

/-- The evaluation map `v ↦ Σ_i ((v i : ℤ) - h) • a i` in `ZMod p`, sending a shifted box
vector to its annihilator residue. -/
noncomputable def evalShift {D : ℕ} (p : ℕ) (a : Fin D → ZMod p) (h : ℕ)
    (v : Fin D → Fin (2 * h + 1)) : ZMod p :=
  ∑ i, (((v i : ℤ) - h : ℤ) : ZMod p) * a i

/-- **The pigeonhole core.** If the height-`≤ h` box is strictly larger than `ZMod p`
(`(2h+1)^D > p`), two distinct shifted box vectors collide under `evalShift`. -/
theorem exists_collision {D : ℕ} {p : ℕ} [NeZero p] (a : Fin D → ZMod p) {h : ℕ}
    (hbig : p < (2 * h + 1) ^ D) :
    ∃ u v : Fin D → Fin (2 * h + 1), u ≠ v ∧ evalShift p a h u = evalShift p a h v := by
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin D → Fin (2 * h + 1)) := by
    rw [ZMod.card p, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    simpa using hbig
  obtain ⟨u, v, hne, huv⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (evalShift p a h) hcard
  exact ⟨u, v, hne, huv⟩

/-- **`exists_lowHeight_annihilator`.** For ANY coefficient map `a : Fin D → ZMod p`, if
`(2h+1)^D > p` then there is a NONZERO integer vector `g : Fin D → ℤ` of height `≤ 2h`
(`|g i| ≤ 2h` for all `i`) that annihilates: `Σ_i (g i : ZMod p) * a i = 0`.

The witness is the difference `g i = (u i : ℤ) - (v i : ℤ)` of a colliding pair; the shift
`-h` cancels in the difference, and `|g i| ≤ 2h`. This existence depends only on `(D, p, h)`
through the hypothesis `(2h+1)^D > p` — never on the *values* of `a`. -/
theorem exists_lowHeight_annihilator {D : ℕ} {p : ℕ} [NeZero p] (a : Fin D → ZMod p) {h : ℕ}
    (hbig : p < (2 * h + 1) ^ D) :
    ∃ g : Fin D → ℤ, g ≠ 0 ∧ (∀ i, |g i| ≤ 2 * h) ∧
      (∑ i, ((g i : ZMod p)) * a i) = 0 := by
  obtain ⟨u, v, hne, hcol⟩ := exists_collision a hbig
  refine ⟨fun i => (u i : ℤ) - (v i : ℤ), ?_, ?_, ?_⟩
  · -- nonzero, since u ≠ v
    intro hzero
    apply hne
    funext i
    have : ((u i : ℤ) - (v i : ℤ)) = 0 := congrFun hzero i
    have hcoe : (u i : ℤ) = (v i : ℤ) := by linarith
    exact Fin.ext (by exact_mod_cast hcoe)
  · -- height bound: |(u i) - (v i)| ≤ 2h
    intro i
    change |((u i : ℤ) - (v i : ℤ))| ≤ 2 * h
    have hu : ((u i : ℕ) : ℤ) ≤ 2 * (h : ℤ) := by
      have := (u i).is_lt
      omega
    have hv : ((v i : ℕ) : ℤ) ≤ 2 * (h : ℤ) := by
      have := (v i).is_lt
      omega
    have hu0 : (0 : ℤ) ≤ ((u i : ℕ) : ℤ) := by positivity
    have hv0 : (0 : ℤ) ≤ ((v i : ℕ) : ℤ) := by positivity
    rw [abs_le]
    constructor <;> omega
  · -- annihilation: unfold the collision
    have := hcol
    simp only [evalShift] at this
    -- Σ ((u i - h) - (v i - h)) a i = Σ (u i - h)a i - Σ (v i - h)a i = 0
    have key : (∑ i, ((((u i : ℤ) - (v i : ℤ) : ℤ) : ZMod p)) * a i) =
        (∑ i, (((u i : ℤ) - h : ℤ) : ZMod p) * a i)
          - (∑ i, (((v i : ℤ) - h : ℤ) : ZMod p) * a i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    rw [key, this, sub_self]

/-- **`lowHeight_annihilator_coeff_agnostic`** (the thickness-invariance no-go). The single
hypothesis `(2h+1)^D > p` produces a low-height annihilator for BOTH a "thin" coefficient
map `a` and a "thick" map `a'` — the existence and the height bound are *identical*,
depending only on `(D, p, h)`. Hence low-height-primitive-annihilator existence cannot
distinguish thin from thick, and carries no thinness signal. -/
theorem lowHeight_annihilator_coeff_agnostic {D : ℕ} {p : ℕ} [NeZero p]
    (a a' : Fin D → ZMod p) {h : ℕ} (hbig : p < (2 * h + 1) ^ D) :
    (∃ g : Fin D → ℤ, g ≠ 0 ∧ (∀ i, |g i| ≤ 2 * h) ∧
        (∑ i, ((g i : ZMod p)) * a i) = 0) ∧
    (∃ g : Fin D → ℤ, g ≠ 0 ∧ (∀ i, |g i| ≤ 2 * h) ∧
        (∑ i, ((g i : ZMod p)) * a' i) = 0) :=
  ⟨exists_lowHeight_annihilator a hbig, exists_lowHeight_annihilator a' hbig⟩

/-- **`prize_scale_forces_height_one`.** At prize scale the free dimension `D` dominates
`log_2 p`, so even `h = 1` clears the pigeonhole (`3^D > p`) and a nonzero height-`≤ 2`
annihilator exists for EVERY coefficient map. Stated abstractly: if `p < 3 ^ D` then such
an annihilator exists. (Prize instance: `D = 2^{m-1}`, `p = 2^{β m}`, and
`2^{β m} < 3^{2^{m-1}}` for `m ≥ 6` with astronomical margin — the minimal primitive height
is floored at the pigeonhole minimum, thin and thick alike.) -/
theorem prize_scale_forces_height_one {D : ℕ} {p : ℕ} [NeZero p] (a : Fin D → ZMod p)
    (hbig : p < 3 ^ D) :
    ∃ g : Fin D → ℤ, g ≠ 0 ∧ (∀ i, |g i| ≤ 2) ∧
      (∑ i, ((g i : ZMod p)) * a i) = 0 := by
  have h3 : (3 : ℕ) = 2 * 1 + 1 := rfl
  have := exists_lowHeight_annihilator (h := 1) a (by simpa [h3] using hbig)
  simpa using this

/-- Honest scope marker: this file is a NO-GO. It does not bound the prize object
`M(μ_n)` and does not refute CORE; it proves that low-height primitive annihilator
existence is coefficient-agnostic (thickness-invariant), closing the "limit wraparound
shapes via low-height annihilating relations" route as thin-blind. -/
def isPrizeClosure : Prop := False

theorem not_prizeClosure : ¬ isPrizeClosure := id

#print axioms exists_lowHeight_annihilator
#print axioms lowHeight_annihilator_coeff_agnostic
#print axioms prize_scale_forces_height_one
#print axioms not_prizeClosure

end ArkLib.ProximityGap.Frontier.OcNegacyclicHeightNoGo
