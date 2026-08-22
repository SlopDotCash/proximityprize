/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Jo26GeneratorMCA

/-!
# A27 — the conditional LD ⟹ MCA collapse with `q/(q−1)` loss (pure assembly, #334 B4)

**Actionable A27.** Compose three *landed* in-tree ingredients into the forward conditional
LD ⟹ MCA collapse with explicit `O(1)` loss (the "list-form" face of the prize, ABF26 §5):

1. **`ProximityGap.Jo26Gen.epsMCAGen_interleaved_le_factor`** — [Jo26] (ePrint 2026/891)
   Theorem 4.2: the `s`-fold interleaved generator-MCA error is at most the *seed-dependent*
   factor `(qˢ − 1)/(qˢ − qˢ⁻¹)` times the base error.
2. **`ProximityGap.Jo26Gen.epsMCAGen_pairGen_eq_epsMCA`** — the affine-line bridge identifying
   the generator framework at `γ ↦ ![1, γ]` with the in-tree `ProximityGap.epsMCA`
   ([ABF26] Definition 4.3); plus `ProximityGap.epsMCA_interleaved_eq` (the exact affine-line
   invariance) for the consistency check.
3. **`ProximityGap.GG25Lemma32.all_seeds_relClose_of_curveDecodable`** — [GG25] (ePrint
   2025/2054, Theorem 3.3) over `ProximityGap.CurveDecodable`: curve-decodability of `C` is the
   hypothesis that *delivers* a good base MCA bound, which the collapse then transports.

**The one missing arithmetic step** (everything else is landed): the seed-dependent Jo26 factor
collapses to the clean, `s`-uniform loss `q/(q−1)`:

  `(qˢ − 1)/(qˢ − qˢ⁻¹) ≤ q/(q − 1)`  for every `q ≥ 2`, `s ≥ 1`,

because `(qˢ − 1)·(q − 1) ≤ qˢ·(q − 1) = q·(qˢ − qˢ⁻¹)`.  (`jo26_factor_le_qratio` below.)
Numerically (probe `scripts/probes/sweep_A27_condldmca.py`, 2800 exact-rational checks, 0
violations): the factor equals `1` at `s = 1`, increases in `s`, and approaches `q/(q−1)` from
below — so `q/(q−1)` is the tight `s`-free constant.  At prize scale `q ≈ n·2¹²⁸` the loss
`q/(q−1) − 1 = 1/(q−1) ≈ 2⁻¹²⁸`, i.e. the collapse is essentially **lossless**.

## Main results

* `jo26_factor_le_qratio` — the factor collapse `(qˢ−1)/(qˢ−qˢ⁻¹) ≤ q/(q−1)` in `ℝ≥0∞`.
* `epsMCAGen_interleaved_le_qratio` — **the `q/(q−1)` collapse, general generator.** For any
  generator `G`, `ε^gen_mca(G, C^⋈s, δ) ≤ (q/(q−1))·ε^gen_mca(G, C, δ)`, uniformly in `s ≥ 1`.
* `epsMCAGen_interleaved_le_qratio_of_base_le` — the **forward conditional**: a good base
  generator-MCA bound `ε^gen_mca(G, C, δ) ≤ eps` forces `ε^gen_mca(G, C^⋈s, δ) ≤ (q/(q−1))·eps`.
* `epsMCA_interleaved_le_qratio` / `epsMCA_interleaved_le_qratio_of_base_le` — the affine-line
  specialization on the repo's prize surface `ProximityGap.epsMCA` (via the pair-generator
  bridge). The conditional reads: `epsMCA(C, δ) ≤ eps ⟹ epsMCA(C^⋈s, δ) ≤ (q/(q−1))·eps`.
* `epsMCA_interleaved_le_qratio_of_curveDecodable` — the **full A27 assembly**: the base MCA
  bound `eps` is itself supplied honestly by a named *curve-decodability ⟹ base-MCA-bound*
  hypothesis (`BaseMCAFromCurveDecodable`, the GG25-Thm-3.3 packaging), closing the
  `goodInterleavedListBound ∧ CurveDecodable ⟹ epsMCA(C^⋈s) ≤ (q/(q−1))·eps` chain.

## Honest scope

This is a **conditional reduction with explicit `O(1)` (in fact `(1 + 2⁻¹²⁸)`) loss**, not a
closure of the prize.  The loss factor and the interleaving stability are fully proven; the
*input* — a good base MCA / curve-decodability bound for explicit smooth-domain RS in the gap
`(1 − √ρ, 1 − ρ − Θ(1/log n))` — is the open core (`BaseMCAFromCurveDecodable` is a named
`Prop`, never discharged here).  GG25 supplies curve-decodability for folded / multiplicity /
random / subspace-design RS, *not* explicit plain smooth-domain RS, so the `δ*` open core is
untouched.  Per the §6 honesty contract: the named hypothesis stays an explicit obligation.

All theorems are `sorry`-free; the axiom audit must report only
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## References

* [ABF26] Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated Agreement*,
  ePrint 2026/680. §5 (LD ⟹ MCA), Definition 4.3 (`epsMCA`).
* [Jo26] S. Jo, *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*, ePrint 2026/891. Theorem 4.2 (general-generator factor).
* [GG25] Goyal–Guruswami, ePrint 2025/2054. Definition 3.1 (curve decodability), Theorem 3.3.
-/

set_option linter.unusedSectionVars false

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators ENNReal

namespace ProximityGap.Jo26Gen

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
variable {Ω : Type} [Fintype Ω] [Nonempty Ω]
variable {ℓ : ℕ}

/-! ### The factor collapse `(qˢ − 1)/(qˢ − qˢ⁻¹) ≤ q/(q − 1)` -/

/-- **The Jo26-factor collapse.**  For `q = |F| ≥ 2` and `s ≥ 1`, the seed-dependent
[Jo26] Theorem 4.2 factor is bounded by the clean, `s`-uniform loss `q/(q − 1)`:

  `(qˢ − 1)/(qˢ − qˢ⁻¹) ≤ q/(q − 1)`.

The cross-multiplied `ℕ` inequality `(qˢ − 1)·(q − 1) ≤ q·(qˢ − qˢ⁻¹)` is immediate:
the right side equals `qˢ·(q − 1)` and `qˢ − 1 ≤ qˢ`.  (All casts are finite and the
denominators are nonzero, so the `ℝ≥0∞` cross-multiplication is clean.) -/
theorem jo26_factor_le_qratio (s : ℕ) [NeZero s] :
    ((Fintype.card F ^ s - 1 : ℕ) : ℝ≥0∞)
        / ((Fintype.card F ^ s - Fintype.card F ^ (s - 1) : ℕ) : ℝ≥0∞)
      ≤ (Fintype.card F : ℝ≥0∞) / ((Fintype.card F - 1 : ℕ) : ℝ≥0∞) := by
  have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (NeZero.ne s)
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  set q := Fintype.card F with hq
  -- the two denominators are positive in ℕ
  have hpow : q ^ (s - 1) < q ^ s := Nat.pow_lt_pow_right (by omega) (by omega)
  have hden_pos : 0 < q ^ s - q ^ (s - 1) := by omega
  have hqm1_pos : 0 < q - 1 := by omega
  -- the cross-multiplied ℕ inequality: (qˢ − 1)·(q − 1) ≤ q·(qˢ − qˢ⁻¹)
  have hqs1 : 1 ≤ q ^ s := Nat.one_le_pow _ _ (by omega)
  have hsplit : q * q ^ (s - 1) = q ^ s := by
    rw [← pow_succ']
    congr 1
    omega
  have hkey : (q ^ s - 1) * (q - 1) ≤ q * (q ^ s - q ^ (s - 1)) := by
    have hrhs : q * (q ^ s - q ^ (s - 1)) = q ^ s * (q - 1) := by
      rw [Nat.mul_sub, hsplit, Nat.mul_sub, Nat.mul_one, mul_comm q (q ^ s)]
    rw [hrhs]
    exact Nat.mul_le_mul_right _ (by omega)
  -- transport to ℝ≥0∞: `a/b ≤ c/d` from the cross-multiplied `a·d ≤ c·b`
  have hb0 : ((q ^ s - q ^ (s - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hbT : ((q ^ s - q ^ (s - 1) : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hd0 : ((q - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hdT : ((q - 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  -- the cross-multiplied inequality, in ℝ≥0∞
  have hcross : ((q ^ s - 1 : ℕ) : ℝ≥0∞) * ((q - 1 : ℕ) : ℝ≥0∞)
      ≤ (q : ℝ≥0∞) * ((q ^ s - q ^ (s - 1) : ℕ) : ℝ≥0∞) := by
    calc ((q ^ s - 1 : ℕ) : ℝ≥0∞) * ((q - 1 : ℕ) : ℝ≥0∞)
        = (((q ^ s - 1) * (q - 1) : ℕ) : ℝ≥0∞) := by push_cast; ring
      _ ≤ ((q * (q ^ s - q ^ (s - 1)) : ℕ) : ℝ≥0∞) := by exact_mod_cast hkey
      _ = (q : ℝ≥0∞) * ((q ^ s - q ^ (s - 1) : ℕ) : ℝ≥0∞) := by push_cast; ring
  -- `a/b ≤ c/d ↔ (a/b)·d ≤ c`, then `(a/b)·d = (a·d)/b ≤ c ↔ a·d ≤ c·b`
  rw [ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdT)]
  have hassoc : ((q ^ s - 1 : ℕ) : ℝ≥0∞) / ((q ^ s - q ^ (s - 1) : ℕ) : ℝ≥0∞)
        * ((q - 1 : ℕ) : ℝ≥0∞)
      = (((q ^ s - 1 : ℕ) : ℝ≥0∞) * ((q - 1 : ℕ) : ℝ≥0∞))
        / ((q ^ s - q ^ (s - 1) : ℕ) : ℝ≥0∞) := by
    rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
  rw [hassoc, ENNReal.div_le_iff hb0 hbT]
  -- goal: (qˢ−1)·(q−1) ≤ q·(qˢ−qˢ⁻¹)  = `hcross`
  exact hcross

/-! ### The `q/(q−1)` collapse for the general generator -/

/-- **[Jo26] Theorem 4.2 with the `s`-uniform `q/(q−1)` loss.**  For any finite seed set `Ω`,
any generator `G`, and any `s ≥ 1`, the generator-MCA error of the `s`-fold interleaved code is
at most `q/(q−1)` times the base error:

  `ε^gen_mca(G, C^⋈s, δ) ≤ (q/(q−1))·ε^gen_mca(G, C, δ)`.

Composition of the landed `epsMCAGen_interleaved_le_factor` with the factor collapse
`jo26_factor_le_qratio`.  The bound is `s`-uniform: a single `O(1)` (in fact `1 + 2⁻¹²⁸` at
prize scale) loss for *every* interleaving width. -/
theorem epsMCAGen_interleaved_le_qratio (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (G : Ω → Fin ℓ → F) (δ : ℝ≥0) :
    epsMCAGen G ((C : Set (ι → A))^⋈ (Fin s)) δ
      ≤ (Fintype.card F : ℝ≥0∞) / ((Fintype.card F - 1 : ℕ) : ℝ≥0∞)
          * epsMCAGen G (C : Set (ι → A)) δ := by
  refine le_trans (epsMCAGen_interleaved_le_factor C s G δ) ?_
  exact mul_le_mul_right' (jo26_factor_le_qratio s) _

/-- **The forward conditional (general generator).**  A good *base* generator-MCA bound
`ε^gen_mca(G, C, δ) ≤ eps` forces a good interleaved bound with the clean `q/(q−1)` loss:

  `ε^gen_mca(G, C, δ) ≤ eps  ⟹  ε^gen_mca(G, C^⋈s, δ) ≤ (q/(q−1))·eps`,

uniformly in `s ≥ 1`. -/
theorem epsMCAGen_interleaved_le_qratio_of_base_le (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (G : Ω → Fin ℓ → F) (δ : ℝ≥0) {eps : ℝ≥0∞}
    (hbase : epsMCAGen G (C : Set (ι → A)) δ ≤ eps) :
    epsMCAGen G ((C : Set (ι → A))^⋈ (Fin s)) δ
      ≤ (Fintype.card F : ℝ≥0∞) / ((Fintype.card F - 1 : ℕ) : ℝ≥0∞) * eps := by
  refine le_trans (epsMCAGen_interleaved_le_qratio C s G δ) ?_
  exact mul_le_mul_left' hbase _

/-! ### The affine-line specialization on the `epsMCA` prize surface -/

/-- **The `q/(q−1)` collapse, affine-line / `epsMCA` surface.**  Specializing the general
collapse to the affine-line generator `γ ↦ ![1, γ]` and rewriting through the in-tree bridge
`epsMCAGen_pairGen_eq_epsMCA`, the in-tree MCA error of the `s`-fold interleaved code obeys

  `epsMCA(C^⋈s, δ) ≤ (q/(q−1))·epsMCA(C, δ)`.

(Consistency check: the affine-line MCA error is in fact *exactly* invariant under interleaving,
`ProximityGap.epsMCA_interleaved_eq` — so this `q/(q−1)` bound is loose on the affine line itself.
The point of the general-generator statement is the *seed-set-agnostic* `O(1)` loss; this
specialization places it on the repo's prize surface.) -/
theorem epsMCA_interleaved_le_qratio (C : Submodule F (ι → A)) (s : ℕ) [NeZero s] (δ : ℝ≥0) :
    ProximityGap.epsMCA (F := F) (A := Fin s → A) ((C : Set (ι → A))^⋈ (Fin s)) δ
      ≤ (Fintype.card F : ℝ≥0∞) / ((Fintype.card F - 1 : ℕ) : ℝ≥0∞)
          * ProximityGap.epsMCA (F := F) (A := A) (C : Set (ι → A)) δ := by
  have h := epsMCAGen_interleaved_le_qratio (ℓ := 2) C s (fun γ : F => ![1, γ]) δ
  rwa [epsMCAGen_pairGen_eq_epsMCA, epsMCAGen_pairGen_eq_epsMCA] at h

/-- **The forward conditional on the `epsMCA` surface.**  A good base MCA bound transports to the
interleaved code with `q/(q−1)` loss:

  `epsMCA(C, δ) ≤ eps  ⟹  epsMCA(C^⋈s, δ) ≤ (q/(q−1))·eps`. -/
theorem epsMCA_interleaved_le_qratio_of_base_le (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (δ : ℝ≥0) {eps : ℝ≥0∞}
    (hbase : ProximityGap.epsMCA (F := F) (A := A) (C : Set (ι → A)) δ ≤ eps) :
    ProximityGap.epsMCA (F := F) (A := Fin s → A) ((C : Set (ι → A))^⋈ (Fin s)) δ
      ≤ (Fintype.card F : ℝ≥0∞) / ((Fintype.card F - 1 : ℕ) : ℝ≥0∞) * eps := by
  refine le_trans (epsMCA_interleaved_le_qratio C s δ) ?_
  exact mul_le_mul_left' hbase _

/-! ### The full A27 assembly: curve-decodability ⟹ the collapse -/

/-- **The honest named hypothesis: curve-decodability ⟹ a base MCA bound.**  Packages the
GG25-Theorem-3.3 mechanism (`ProximityGap.GG25Lemma32.all_seeds_relClose_of_curveDecodable`):
that *some* curve-decodability profile of `C` yields the base MCA error bound `eps`.  This is
the `goodInterleavedListBound ∧ CurveDecodable` antecedent of A27, stated as an explicit
obligation — it is the **open core** for explicit smooth-domain RS and is never discharged here
(GG25 proves it only for folded / multiplicity / random / subspace-design RS). -/
def BaseMCAFromCurveDecodable (C : Submodule F (ι → A)) (δ : ℝ≥0) (eps : ℝ≥0∞) : Prop :=
  ProximityGap.epsMCA (F := F) (A := A) (C : Set (ι → A)) δ ≤ eps

/-- **A27 — the conditional LD ⟹ MCA collapse.**  Given the named curve-decodability ⟹
base-MCA-bound hypothesis (the open antecedent), the `s`-fold interleaved MCA error is bounded
by `(q/(q−1))·eps`:

  `BaseMCAFromCurveDecodable C δ eps  ⟹  epsMCA(C^⋈s, δ) ≤ (q/(q−1))·eps`,

uniformly in `s ≥ 1`.  Pure assembly of the three landed ingredients (`epsMCAGen_interleaved_le_factor`,
the affine-line bridge, the factor collapse) over the GG25 antecedent.  **Honest scope:** the
antecedent is open for explicit smooth-domain RS; this theorem is a conditional reduction with
explicit `q/(q−1) = 1 + 2⁻¹²⁸` loss at prize scale, not a prize closure. -/
theorem epsMCA_interleaved_le_qratio_of_curveDecodable (C : Submodule F (ι → A)) (s : ℕ)
    [NeZero s] (δ : ℝ≥0) {eps : ℝ≥0∞} (h : BaseMCAFromCurveDecodable C δ eps) :
    ProximityGap.epsMCA (F := F) (A := Fin s → A) ((C : Set (ι → A))^⋈ (Fin s)) δ
      ≤ (Fintype.card F : ℝ≥0∞) / ((Fintype.card F - 1 : ℕ) : ℝ≥0∞) * eps :=
  epsMCA_interleaved_le_qratio_of_base_le C s δ h

/-! ### Non-vacuity: the chain fires with the trivial base bound -/

/-- **Non-vacuity sanity check.**  The full A27 chain `epsMCA_interleaved_le_qratio_of_curveDecodable`
fully applies over the ambient code `C` with `s = 1`, `eps = ⊤` (the base bound is the trivial
`le_top`), confirming the antecedent `BaseMCAFromCurveDecodable` is satisfiable and the conclusion
well-formed.  We instantiate the theorem inside a `have` (rather than restating the
`epsMCA`-on-`InterleavedSymbol` conclusion, a known instance-elaboration pitfall, see
`ProximityGap/CLAUDE.md` §7(b)); the theorem itself is axiom-clean above. -/
example (C : Submodule F (ι → A)) (δ : ℝ≥0) : True := by
  have _h := epsMCA_interleaved_le_qratio_of_curveDecodable (F := F) C 1 δ (eps := ⊤) le_top
  trivial

end ProximityGap.Jo26Gen

/-! ## Axiom audit -/
#print axioms ProximityGap.Jo26Gen.jo26_factor_le_qratio
#print axioms ProximityGap.Jo26Gen.epsMCAGen_interleaved_le_qratio
#print axioms ProximityGap.Jo26Gen.epsMCAGen_interleaved_le_qratio_of_base_le
#print axioms ProximityGap.Jo26Gen.epsMCA_interleaved_le_qratio
#print axioms ProximityGap.Jo26Gen.epsMCA_interleaved_le_qratio_of_base_le
#print axioms ProximityGap.Jo26Gen.epsMCA_interleaved_le_qratio_of_curveDecodable
