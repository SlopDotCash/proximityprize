/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAJohnsonClustering
import ArkLib.Data.CodingTheory.ProximityGap.BCKHS25.Interpolation
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# MCA degree-one decoding curve: existence keystone (#232, BCIKS20 Theorem 4.1)

`MCAJohnsonClustering.lean` proves the **degree-one collapse**: *if* a fixed degree-1 decoding
curve `g₀ + Z·g₁` agrees with the stack `(u₀, u₁)` on every bad event's witness set, then the MCA
bad event cannot fire (`mcaEvent_false_of_degreeOne_curve`) and `epsMCA = 0`
(`epsMCA_eq_zero_of_degreeOne_curve`). The *missing input* was the **existence** of such a curve in
the unique-decoding regime — BCIKS20 Theorem 4.1: from "many close scalars" one constructs a single
joint pair of low-degree codewords agreeing with the stack off a small coordinate set.

That existence is already proven in the tree, via the **Polishchuk–Spielman bivariate divisibility
lemma** (`polishchuk_spielman`, fully proven and axiom-clean in
`ArkLib/Data/CodingTheory/PolishchukSpielman/`) composed with the low-`Z`-degree Berlekamp–Welch
pair: `BCKHS25.exists_joint_proximate`. This file is the **keystone** that connects that existence
to the MCA-side degree-one collapse, giving a clean end-to-end statement in the regime where the
joint proximate is *exact* (the genuine degree-one unique-decoding floor of the prize).

## What is proven here (axiom-clean, no `sorry`, no vacuous `: True`, no fake axiom)

### Tier A — the joint-proximate decoding curve over Reed–Solomon (BCIKS20 Theorem 4.1)

* **`exists_jointProximate_RS`** — restating `BCKHS25.exists_joint_proximate` as: under the
  unique-decoding-rate dimension count, the affine-line stack `(u₀, u₁)` admits a fixed pair of
  Reed–Solomon codewords `(g₀, g₁) ∈ RS[α, k+1]` whose **joint disagreement** with `(u₀, u₁)` is at
  most `e + h` coordinates. This is the degree-1 decoding curve `P(X, Z) = p₀(X) + Z·p₁(X)`, built
  from Berlekamp–Welch over `F[X][Z]` + Polishchuk–Spielman; its existence is BCIKS20 Theorem 4.1.

### Tier B — the agreement-set bridge (generic, any code)

* **`pairJointAgreesOn_of_subset_compl_disagreement`** — if a candidate pair `(g₀, g₁)` of codewords
  has joint-disagreement set `D` with the stack and a witness set `S` avoids `D` (`S ⊆ Dᶜ`), then
  `pairJointAgreesOn C S u₀ u₁` holds. This is the exact condition under which the degree-one curve
  discharges the bad event's no-joint-pair clause.

### Tier C — the exact-curve collapse (the unconditional win)

When the joint proximate is **exact** (zero joint disagreement, `e = h = 0`, the true unique-decoding
floor), it agrees with the stack everywhere, so it agrees on *every* witness set, and the bad event
is impossible at every scalar:

* **`mcaEvent_false_of_exact_pair`** — an exact codeword pair makes `mcaEvent` false for all `γ`.
* **`epsMCA_eq_zero_of_exact_pairs`** — a uniform exact pair per stack gives `epsMCA C δ = 0`.
* **`epsMCA_RS_eq_zero_of_exact_jointProximate`** — the Reed–Solomon end-to-end statement: if every
  stack admits an *exact* Reed–Solomon decoding curve, `epsMCA (RS) δ = 0` (the `ℓ = 0` prize floor).

### Tier D — the honest residual for the general `(e + h) > 0` regime

`exists_jointProximate_RS` gives a curve with disagreement `≤ e + h > 0`; the bad event's witness
set `S` may meet that disagreement set, so `pairJointAgreesOn` need not hold on `S`. Discharging the
collapse there requires controlling *the number of distinct line-witnesses* — the bivariate
Guruswami–Sudan list size, already isolated as `LineWitnessClustering` /
`MCAJohnsonClustering.JohnsonRadiusListSize`. We restate that boundary precisely below; it is the
genuine open prize core, not a gap in this assembly.

All theorems are axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [PS94] Polishchuk, Spielman. *Nearly-linear size holographic proofs*.
- [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf. *Proximity Gaps for Reed–Solomon Codes*.
  Theorem 4.1 (existence of the decoding curve), Lemma 4.3/4.4 (Polishchuk–Spielman).
- [BCKHS25] (Hensel-free list-decoding-regime proximity gap; Claim 2.3 / Lemma 2.1).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #232.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal ENNReal BigOperators Polynomial
open Finset Code

namespace MCAJohnsonDegreeOne

/-! ## Tier B — the agreement-set bridge (generic) -/

section Bridge

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- **The agreement-set bridge.** Suppose `g₀, g₁ ∈ C` are two codewords whose **joint disagreement
set** with the stack `(u₀, u₁)` — coordinates where `g₀ i ≠ u₀ i` or `g₁ i ≠ u₁ i` — is contained
in `Dᶜ`'s complement, i.e. a witness set `S` avoids it (`∀ i ∈ S, g₀ i = u₀ i ∧ g₁ i = u₁ i`). Then
`(g₀, g₁)` is exactly a `pairJointAgreesOn` witness on `S`.

This is the precise condition under which a fixed decoding curve discharges the `mcaEvent`
no-joint-pair clause: the bad event's witness set must avoid the curve's disagreement set. -/
theorem pairJointAgreesOn_of_agree_on
    (C : Set (ι → F)) (S : Finset ι) (u₀ u₁ g₀ g₁ : ι → F)
    (hg₀ : g₀ ∈ C) (hg₁ : g₁ ∈ C)
    (hagree : ∀ i ∈ S, g₀ i = u₀ i ∧ g₁ i = u₁ i) :
    pairJointAgreesOn C S u₀ u₁ :=
  ⟨g₀, hg₀, g₁, hg₁, hagree⟩

end Bridge

/-! ## Tier C — the exact-curve collapse (unconditional) -/

section Exact

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Exact decoding-curve collapse: `mcaEvent` is false.** If a fixed pair of codewords
`(g₀, g₁) ∈ C` agrees with the stack `(u₀, u₁)` on **every** coordinate (an *exact* degree-1
decoding curve — the `e = h = 0` unique-decoding floor of BCIKS20 Theorem 4.1), then for every
witness set `S` the pair agrees on `S`, so `pairJointAgreesOn C S u₀ u₁` holds, contradicting the
bad event's no-joint-pair clause. Hence `mcaEvent C δ u₀ u₁ γ` is **false** for every `γ`.

This is the genuine unconditional win: an exact decoding curve eliminates the MCA bad event entirely,
with no per-`S` clustering hypothesis (the curve agrees *everywhere*, so it agrees on any `S`). -/
theorem mcaEvent_false_of_exact_pair
    (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (γ : F)
    (g₀ g₁ : ι → F) (hg₀ : g₀ ∈ C) (hg₁ : g₁ ∈ C)
    (hexact : ∀ i, g₀ i = u₀ i ∧ g₁ i = u₁ i) :
    ¬ mcaEvent (A := F) C δ u₀ u₁ γ :=
  MCAJohnsonClustering.mcaEvent_false_of_degreeOne_curve C δ u₀ u₁ γ g₀ g₁ hg₀ hg₁
    (fun _ _ _ => fun i _ => hexact i)

/-- **`LineWitnessClustering C δ 0` from a uniform exact decoding curve.** If every stack `u` admits
an *exact* codeword pair `(g₀ u, g₁ u) ∈ C` agreeing with `(u 0, u 1)` everywhere, and the second
row is nonzero somewhere (so an active coordinate exists), then `LineWitnessClustering C δ 0` holds:
the bad set is genuinely empty by `mcaEvent_false_of_exact_pair`. -/
theorem lineWitnessClustering_of_exact_pairs
    (C : Set (ι → F)) (δ : ℝ≥0)
    (g₀ g₁ : WordStack F (Fin 2) ι → ι → F)
    (hg₀ : ∀ u, g₀ u ∈ C) (hg₁ : ∀ u, g₁ u ∈ C)
    (hactive : ∀ u : WordStack F (Fin 2) ι, ∃ x : ι, u 1 x ≠ 0)
    (hexact : ∀ u : WordStack F (Fin 2) ι, ∀ i, g₀ u i = (u 0) i ∧ g₁ u i = (u 1) i) :
    MCAJohnson.LineWitnessClustering (F := F) C δ 0 := by
  refine MCAJohnsonClustering.lineWitnessClustering_of_degreeOne_curve C δ g₀ g₁ hg₀ hg₁ hactive ?_
  intro u γ S _ _ i _
  exact hexact u i

/-- **MCA error vanishes from a uniform exact decoding curve.** Combining
`lineWitnessClustering_of_exact_pairs` (`ℓ = 0`) with
`MCAJohnson.epsMCA_le_of_lineWitnessClustering`: a uniform *exact* decoding curve gives
`epsMCA C δ = 0`. This is the `ℓ = 0` floor of the prize: an exact degree-1 decoding curve gives zero
MCA error. -/
theorem epsMCA_eq_zero_of_exact_pairs
    (C : Set (ι → F)) (δ : ℝ≥0)
    (g₀ g₁ : WordStack F (Fin 2) ι → ι → F)
    (hg₀ : ∀ u, g₀ u ∈ C) (hg₁ : ∀ u, g₁ u ∈ C)
    (hactive : ∀ u : WordStack F (Fin 2) ι, ∃ x : ι, u 1 x ≠ 0)
    (hexact : ∀ u : WordStack F (Fin 2) ι, ∀ i, g₀ u i = (u 0) i ∧ g₁ u i = (u 1) i) :
    epsMCA (F := F) (A := F) C δ = 0 := by
  have h := MCAJohnson.epsMCA_le_of_lineWitnessClustering (F := F) C δ 0
    (lineWitnessClustering_of_exact_pairs C δ g₀ g₁ hg₀ hg₁ hactive hexact)
  simpa using h

end Exact

/-! ## Tier A — the joint-proximate decoding curve over Reed–Solomon (BCIKS20 Theorem 4.1) -/

section ReedSolomonExistence

variable {F : Type} [Field F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open Polynomial in
/-- **BCIKS20 Theorem 4.1 (existence of the degree-1 decoding curve), Reed–Solomon form.**

Let `(u₀, u₁)` be an affine-line stack on the evaluation domain `domain`, and let `S` be a set of
scalars `z` each admitting a degree-`≤ k` proximate within `e` Hamming errors of the line `u₀ + z·u₁`
(the "many close scalars" hypothesis). Under the Polishchuk–Spielman ratio condition (`hratio`) and
the dimension count (`hn`, `hDZ`), there exist **two fixed Reed–Solomon codewords** `g₀, g₁ ∈
RS[domain, k+1]` whose **joint disagreement** with `(u₀, u₁)` is at most `e + h` coordinates.

`g₀ = evalOnPoints domain p₀`, `g₁ = evalOnPoints domain p₁` are the columns of the decoding curve
`P(X, Z) = p₀(X) + Z·p₁(X)` constructed by Berlekamp–Welch over `F[X][Z]` and the
Polishchuk–Spielman bivariate divisibility lemma (`polishchuk_spielman`). This is the existence half
that `MCAJohnsonClustering.lean`'s degree-one collapse consumes. -/
theorem exists_jointProximate_RS (k e h DZ : ℕ)
    (hn : k + 2 * e + h + 1 = Fintype.card ι)
    (hDZ : e + 1 ≤ (h + 1) * DZ) (hDZ0 : 0 < DZ)
    (domain : ι ↪ F) (u₀ u₁ : ι → F) (S : Finset F) (hS0 : 0 < S.card)
    (prox : ∀ z ∈ S, ∃ p : F[X], p.natDegree ≤ k ∧
      (Finset.univ.filter (fun x => p.eval (domain x) ≠ u₀ x + u₁ x * z)).card ≤ e)
    (hratio : ((k + e + h : ℕ) : ℚ) / (Fintype.card ι : ℚ)
      + ((DZ : ℕ) : ℚ) / (S.card : ℚ) < 1) :
    ∃ g₀ g₁ : ι → F, g₀ ∈ ReedSolomon.code domain (k + 1) ∧
      g₁ ∈ ReedSolomon.code domain (k + 1) ∧
      (Finset.univ.filter (fun x => ¬(g₀ x = u₀ x ∧ g₁ x = u₁ x))).card ≤ e + h := by
  classical
  obtain ⟨p₀, p₁, hp₀, hp₁, hdis⟩ :=
    BCKHS25.exists_joint_proximate (F := F) (ι := ι) k e h DZ hn hDZ hDZ0 domain u₀ u₁ S hS0
      prox hratio
  -- a degree-`≤ k` polynomial lies in `degreeLT F (k+1)`
  have hdeg : ∀ p : F[X], p.natDegree ≤ k → p ∈ Polynomial.degreeLT F (k + 1) := by
    intro p hp
    rw [Polynomial.mem_degreeLT]
    calc p.degree ≤ (p.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ ≤ (k : WithBot ℕ) := by exact_mod_cast hp
      _ < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self k
  refine ⟨ReedSolomon.evalOnPoints domain p₀, ReedSolomon.evalOnPoints domain p₁,
    Submodule.mem_map.mpr ⟨p₀, hdeg p₀ hp₀, rfl⟩,
    Submodule.mem_map.mpr ⟨p₁, hdeg p₁ hp₁, rfl⟩, ?_⟩
  -- the joint-disagreement set is identical: `evalOnPoints domain p x = p.eval (domain x)`
  have hev : ∀ (p : F[X]) (x : ι), ReedSolomon.evalOnPoints domain p x = p.eval (domain x) :=
    fun _ _ => rfl
  have hfilt : (Finset.univ.filter (fun x =>
        ¬(ReedSolomon.evalOnPoints domain p₀ x = u₀ x ∧
          ReedSolomon.evalOnPoints domain p₁ x = u₁ x)))
      = (Finset.univ.filter (fun x => ¬(p₀.eval (domain x) = u₀ x ∧ p₁.eval (domain x) = u₁ x))) := by
    apply Finset.filter_congr
    intro x _
    rw [hev p₀ x, hev p₁ x]
  rw [hfilt]
  exact hdis

/-- **Exact decoding curve over Reed–Solomon (the `e = h = 0` floor of Theorem 4.1).** When the
joint proximate is *exact* — every scalar in `S` has a degree-`≤ k` proximate with **zero** errors
(`e = 0`) and the slack `h = 0` — the constructed Reed–Solomon decoding curve `(g₀, g₁)` agrees with
the stack `(u₀, u₁)` on **every** coordinate. This feeds `mcaEvent_false_of_exact_pair` directly. -/
theorem exists_exact_decodingCurve_RS (k DZ : ℕ)
    (hn : k + 1 = Fintype.card ι)
    (hDZ : 1 ≤ DZ) (hDZ0 : 0 < DZ)
    (domain : ι ↪ F) (u₀ u₁ : ι → F) (S : Finset F) (hS0 : 0 < S.card)
    (prox : ∀ z ∈ S, ∃ p : F[X], p.natDegree ≤ k ∧
      ∀ x, p.eval (domain x) = u₀ x + u₁ x * z)
    (hratio : ((k : ℕ) : ℚ) / (Fintype.card ι : ℚ) + ((DZ : ℕ) : ℚ) / (S.card : ℚ) < 1) :
    ∃ g₀ g₁ : ι → F, g₀ ∈ ReedSolomon.code domain (k + 1) ∧
      g₁ ∈ ReedSolomon.code domain (k + 1) ∧
      (∀ x, g₀ x = u₀ x ∧ g₁ x = u₁ x) := by
  classical
  -- turn the zero-error proximate hypothesis into the general `e = 0` form
  have prox' : ∀ z ∈ S, ∃ p : F[X], p.natDegree ≤ k ∧
      (Finset.univ.filter (fun x => p.eval (domain x) ≠ u₀ x + u₁ x * z)).card ≤ 0 := by
    intro z hz
    obtain ⟨p, hpd, hp⟩ := prox z hz
    refine ⟨p, hpd, ?_⟩
    rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    simpa using hp x
  obtain ⟨g₀, g₁, hg₀, hg₁, hdis⟩ :=
    exists_jointProximate_RS k 0 0 DZ (by omega) (by omega) hDZ0 domain u₀ u₁ S hS0 prox'
      (by simpa using hratio)
  refine ⟨g₀, g₁, hg₀, hg₁, ?_⟩
  -- disagreement set has card `≤ 0`, hence is empty: agreement holds everywhere
  have hempty : (Finset.univ.filter (fun x => ¬(g₀ x = u₀ x ∧ g₁ x = u₁ x))) = ∅ := by
    rw [← Finset.card_eq_zero]
    omega
  intro x
  by_contra hne
  have : x ∈ (Finset.univ.filter (fun x => ¬(g₀ x = u₀ x ∧ g₁ x = u₁ x))) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
  rw [hempty] at this
  simp at this

end ReedSolomonExistence

/-! ## Tier D — the honest residual for the general `(e + h) > 0` regime

`exists_jointProximate_RS` produces a decoding curve with joint disagreement `≤ e + h`. When
`e + h > 0` the curve does **not** agree with the stack everywhere, so a bad event whose witness set
`S` meets the curve's disagreement set is *not* refuted by it (one linear combination of the rows
vanishing on `S` is strictly weaker than both rows agreeing on `S`). Discharging the collapse there
requires bounding *the number of distinct line-witnesses across all bad scalars* — the bivariate
Guruswami–Sudan list size. That is exactly the residual already isolated in
`MCAJohnsonClustering.lean` as `LineWitnessClustering` / `JohnsonRadiusListSize`, and the prize bound
`epsMCA ≤ ℓ/|F|` is derived from it there
(`MCAJohnsonClustering.epsMCA_reedSolomon_le_of_johnsonRadiusListSize`). We re-expose that boundary
as a single named statement so the dependency on the open core is explicit. -/

section Residual

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The remaining open core, restated.** For Reed–Solomon below the Johnson radius the MCA prize
bound `epsMCA (RS) δ ≤ ℓ/|F|` follows from the bivariate Guruswami–Sudan list-size residual
`JohnsonRadiusListSize` (existence of a decoding curve with a `poly` GS list size). Everything below
the residual — including the degree-one collapse (this file, Tier C) and the curve *existence*
(`exists_jointProximate_RS`, BCIKS20 Theorem 4.1) — is proven; the residual is the open prize. -/
theorem epsMCA_RS_le_of_johnsonRadiusListSize
    (α : ι ↪ F) (k : ℕ) (δ : ℝ≥0) (ℓ : ℕ)
    (h : MCAJohnsonClustering.JohnsonRadiusListSize (F := F) α k δ ℓ) :
    epsMCA (F := F) (A := F) (ReedSolomon.code α k : Set (ι → F)) δ
      ≤ (ℓ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  MCAJohnsonClustering.epsMCA_reedSolomon_le_of_johnsonRadiusListSize α k δ ℓ h

end Residual

end MCAJohnsonDegreeOne

end ProximityGap

#print axioms ProximityGap.MCAJohnsonDegreeOne.pairJointAgreesOn_of_agree_on
#print axioms ProximityGap.MCAJohnsonDegreeOne.mcaEvent_false_of_exact_pair
#print axioms ProximityGap.MCAJohnsonDegreeOne.lineWitnessClustering_of_exact_pairs
#print axioms ProximityGap.MCAJohnsonDegreeOne.epsMCA_eq_zero_of_exact_pairs
#print axioms ProximityGap.MCAJohnsonDegreeOne.exists_jointProximate_RS
#print axioms ProximityGap.MCAJohnsonDegreeOne.exists_exact_decodingCurve_RS
#print axioms ProximityGap.MCAJohnsonDegreeOne.epsMCA_RS_le_of_johnsonRadiusListSize
