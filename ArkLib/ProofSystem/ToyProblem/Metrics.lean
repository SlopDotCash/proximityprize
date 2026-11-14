/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Extensions.ProofSystem.ToyProblem.SoundnessBounds
import ArkLib.ToMathlib.ToyProblemViolation
import ArkLib.ToMathlib.KoalaBearCode
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Proximity-Prize "bits of security" leaderboard (ABF26 §6)

This retained model uses the existential-encoding relations from the downstream Definitions
module. Its instance and ratio APIs live in `ToyProblem.ExistentialEncoding`, and
`winningSetSoundness` is their combinatorial supremum. Canonical `winningSetDensity` instead
pins one encoder. References below to the soundness error mean the retained scalar; identifying
it with a concrete protocol-game error requires additional coupling theorems. No equality with
the canonical fixed-encoder quantity is asserted.

A machine-checked **leaderboard contract** for the soundness of the §6 toy
protocol (Construction 6.2 / its simplified IOR Construction 6.9). The
Ethereum Foundation Proximity Prize (proximityprize.org) asks for the gap
between the *provable* security of small-field hash-based SNARGs and the
*best known attack*; at the KoalaBear-sextic regime (`ρ = 1/2`, `t = 128`)
this is the ≈64-vs-≈116-bit frontier (ABF26 §6.3 Tables 2–5, and the
standalone attack of Fenzi–Sanso, eprint 2025/2197).

This file states that frontier as two opposing Lean structures over **one
common quantity**, `winningSetSoundness`: the soundness scalar of the
simplified IOR `T'[C]` (Construction 6.9, the §6.4 attack target), computed in
the in-tree **existential-encoding** language `ToyProblem.relaxedRelation`.
The scalar gap between the two structures is meaningful *for that scalar*;
see the status section below for why that scalar is not the paper's
soundness error.

* `SecurityLowerBound p` — an inhabitant is a proof "we can *prove* `≥ bits`
  bits of security": `soundnessError ≤ 2^(-bits)`. The proof routes through
  the full-protocol round-by-round (RBR) upper bound `toySoundnessError`
  (Lemmas 6.10 / 6.6 / 6.8).
* `SecurityUpperBound p` — an inhabitant is a proof "no analysis can prove
  `> bits` bits": `soundnessError ≥ 2^(-bits)`. The intended witness is the
  winning-set attack of Lemmas 6.12 / 6.13 (in the existential-encoding model
  the constraint degeneracy also supplies witnesses; see the status section).
* `securityGap lo hi := hi.bits - lo.bits` — the scalar contestants minimise.
  `SecurityLowerBound.bits_le_of` proves `lo.bits ≤ hi.bits` (so the gap is
  `≥ 0`) directly from the two inequalities, axiom-cleanly.

## Status: the existential-encoding scalar is degenerate (audit 2026-10-28, L33)

`winningSetSoundness` is **not** the paper's soundness error of `T'[C]`. The
paper's relation uses the code's fixed encoding, while `relaxedRelation` lets
every instance pick its own linear encoder into `C`. For one row this makes the
linear constraint vacuous (`ToyProblem.mem_winningSet_iff_exists_agree`, for
`k ≥ 2`, `v ≠ 0` and a code closed under scaling), so a violating two-row
instance whose folds are all close to `C` wins **every** challenge. At the
anchor `koalaIRS` such an instance is `ArkLib.KoalaBearAttack.attackInstance`
(`ArkLib/ToMathlib/KoalaBearAttackInstance.lean`), and there:

* `koalaIRS.soundnessError = 1`
  (`ArkLib.KoalaBearAttack.koalaIRS_soundnessError_eq_one`);
* every `SecurityLowerBound koalaIRS` has `bits ≤ 0`, and the 64-bit lower
  residual `arklib_lowerBound_irs_t128_residual` is **false**
  (`ArkLib.KoalaBearAttack.not_arklib_lowerBound_irs_t128_residual`), so
  `arklib_lowerBound_irs_t128` can never be applied and
  `securityGap_koalaIRS_anchors` is vacuous;
* the 116-bit attack residuals hold, but only through this degeneracy
  (`ArkLib.KoalaBearAttack.fenziSanso_upperBound_attack_concrete_residual_holds`).
  They are not evidence for the Fenzi–Sanso list-decoding attack, which has no
  large lists at this length-4 carrier.

This refutes the existential-encoding model's reading of the anchors, not the
paper, the prize, or the fixed-encoding protocol. The fixed-encoding scalar
is the canonical `winningSetDensity` (over `RelaxedRelationFor`, in
`ToyProblem/SoundnessBounds.lean`); the correlated-agreement attack is transferred to it
below
(`epsCA_le_winningSetDensity`). Re-pointing `ToyParams.soundnessError`,
the two leaderboard structures and the anchors to the fixed encoding is still
open (issue #18 encoder alignment).

## The common quantity (central design decision)

The two sides **must** bound the same quantity or the gap is meaningless.
The trap: `toySoundnessError` (the full-protocol RBR max) is an *upper* bound,
while the attack lemmas L6.12/6.13 *lower* bound. So `attack ≤ error ≤
toySoundnessError`. We make the leaderboard quantity the **simplified-IOR
soundness error** `winningSetSoundness` — per `winningSet`'s Definition 6.11,
the worst-case winning-challenge fraction `|Ω|/|F|` over *violating* instances.
In the paper, with the fixed encoding, this is the object the §6.4 attacks
directly lower-bound and Lemma 6.10 upper-bounds; for the existential-encoding
scalar used here see the status section above.

* the X side proves `soundnessError ≤ toySoundnessError ≤ 2^(-bits)`
  (`toySoundnessError` is the *vehicle*, not the leaderboard quantity);
* the Y side proves `soundnessError ≥ winningSet.ncard/|F| ≥ 2^(-bits)`.

**Why `winningSetSoundness` is `t`-independent (no `(1-δ)^t` term).** `T'[C]`
is single-round; its soundness error is *exactly* the winning fraction. The
spot-check term `(1-δ)^t` belongs to the *full* protocol C6.2, and at the
prize regime (`t=128`, `δ≈1-1/√2`) it equals `2^(-64)` — which alone exceeds
the attack target `2^(-116)`. Folding it into the common quantity would
collapse the attack side to a triviality (and, at a smaller `δ`, make the
provable side a *falsehood*). It therefore lives only in `toySoundnessError`,
where it correctly caps the *provable* security at 64 bits (ABF26 §6.3, `.tex`
2819–2823: the soundness is `max(2^(-71.5), 2^(-64))`, spot-check-dominated).

Stating the upper-bound structure against `soundnessError` (not
`toySoundnessError`) is what keeps the leaderboard faithful: a contestant
cannot "win" by inflating the RBR bound — they must exhibit a violating
instance with many winning challenges. In the existential-encoding language
that instance can come from the constraint degeneracy instead of a paper
attack (status section above).

The Phase-1 grand-challenge framework
(`ProximityGap.GrandChallenges`) feeds the X side: a tighter
`MCALowerWitness` shrinks the `ε_mca` term inside `toySoundnessError`, which
raises the provable lower bound `X`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.2 Lemmas 6.6/6.8; §6.4 Lemmas 6.10, 6.12,
  6.13; Definition 6.11; §6.3 Tables 2–5).
* Fenzi, G., Sanso, A., *Small-field hash-based SNARGs are less sound than
  conjectured*, eprint 2025/2197 (Construction 4.2 ≈ C6.2; Lemma 4.4 is a
  similar observation to Lemma 6.12, per ABF26 §6.4.1).
-/

-- Several plumbing lemmas use only a subset of the `ι`/`F` typeclass instances in their
-- types; suppress the noisy `unused...InType` / `unusedSectionVars` warnings file-wide,
-- matching the idiom in `ProximityGap/GrandChallenges.lean`.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ToyProblem

open Code InterleavedCode ListDecodable ProximityGap ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]

/-! ## The soundness scalar (Definition 6.11 reading, existential encoding)

`winningSetSoundness` is the Definition 6.11 supremum, over instances
`(v, μ₁, μ₂, f₁, f₂)` that *violate* the relaxed relation `R̃_{C,δ}^2`, of the
winning-challenge fraction `|Ω| / |F|`, with both relations taken in the
existential-encoding form `ToyProblem.relaxedRelation`. The violating
constraint is essential — over *all* inputs a valid instance has `Ω = F`
(fraction `1`), so the unrestricted sup is the trivial `1`. It is not enough
here, though: since `relaxedRelation` ignores a single row's constraint
(`ToyProblem.mem_winningSet_iff_exists_agree`), violating instances with
`Ω = F` exist as well, and the supremum is `1` at the KoalaBear anchor
(`ArkLib.KoalaBearAttack.koalaIRS_soundnessError_eq_one`). The paper's
fixed-encoding scalar is the canonical `winningSetDensity`. -/

/-- An instance of the simplified IOR whose stack `(v, μ₁, μ₂, f₁, f₂)`
violates the existential-encoding relaxed relation `R̃_{C,δ}^2`
(`ToyProblem.relaxedRelation`). This is the index of the worst-case
supremum `winningSetSoundness`. Violating the existential relation is a
stronger requirement than violating the fixed-encoding one
(`ToyProblem.not_relaxedRelationFor_of_not_relaxedRelation`). -/
structure ExistentialEncoding.ViolatingInstance (C : Set (ι → F)) (δ : ℝ≥0) (k : ℕ) where
  /-- The linear-constraint vector. -/
  v : Fin k → F
  /-- First constraint value. -/
  μ₁ : F
  /-- Second constraint value. -/
  μ₂ : F
  /-- First input word. -/
  f₁ : ι → F
  /-- Second input word. -/
  f₂ : ι → F
  /-- The instance violates the relaxed two-row relation `R̃_{C,δ}^2`. -/
  violates : ¬ relaxedRelation (ℓ := 2) C δ v ![μ₁, μ₂] ![f₁, f₂]

/-- The winning-challenge fraction `|Ω^{f₁,f₂}_{v,μ₁,μ₂}| / |F|` of a
violating instance. Always in `[0, 1]` (`winningSet ⊆ F`). -/
noncomputable def ExistentialEncoding.winningSetRatio {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (x : ExistentialEncoding.ViolatingInstance C δ k) : ℝ≥0 :=
  ((winningSet C δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-- **Definition 6.11 of [ABF26]** (soundness error of the simplified IOR), in
the in-tree existential-encoding language.

The worst-case winning-challenge fraction over violating instances:
`sup_{(v,μ₁,μ₂,f₁,f₂) violating R̃²} |Ω| / |F|`, with `R̃` and `Ω` the
existential-encoding `relaxedRelation` and `winningSet`. This is the common
quantity the leaderboard's two sides bound from opposite directions. It is
**not** the protocol's soundness error after the combination-randomness round:
that uses the code's fixed encoding (`winningSetDensity`). The existential
scalar is degenerate; it equals `1` at the KoalaBear anchor
(`ArkLib.KoalaBearAttack.koalaIRS_soundnessError_eq_one`). -/
noncomputable def winningSetSoundness {k : ℕ} (C : Set (ι → F)) (δ : ℝ≥0) : ℝ≥0 :=
  ⨆ x : ExistentialEncoding.ViolatingInstance C δ k, ExistentialEncoding.winningSetRatio x

/-- The winning-challenge fraction never exceeds `1` (`winningSet ⊆ F`). -/
theorem ExistentialEncoding.winningSetRatio_le_one {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (x : ExistentialEncoding.ViolatingInstance C δ k) : ExistentialEncoding.winningSetRatio x ≤ 1 := by
  haveI : Nonempty F := ⟨0⟩
  have hpos : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  rw [ExistentialEncoding.winningSetRatio, div_le_one hpos]
  have hle : (winningSet C δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard ≤ Fintype.card F := by
    have := Set.ncard_le_ncard (Set.subset_univ
      (winningSet C δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂)) (Set.finite_univ)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  exact_mod_cast hle

/-- The family of winning-challenge fractions is bounded above (by `1`), so
its supremum is well-behaved in the conditionally complete order `ℝ≥0`. -/
theorem ExistentialEncoding.bddAbove_winningSetRatio {k : ℕ} (C : Set (ι → F)) (δ : ℝ≥0) :
    BddAbove (Set.range (fun x : ExistentialEncoding.ViolatingInstance C δ k ↦ ExistentialEncoding.winningSetRatio x)) := by
  refine ⟨1, ?_⟩
  rintro r ⟨x, rfl⟩
  exact ExistentialEncoding.winningSetRatio_le_one x

/-- Each violating instance's winning fraction is a lower bound on the
soundness error of [ABF26] Definition 6.11 — the backbone of the attack (Y)
side: an explicit attack witness lower-bounds `winningSetSoundness`. -/
theorem winningSetRatio_le_winningSetSoundness {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (x : ExistentialEncoding.ViolatingInstance C δ k) :
    ExistentialEncoding.winningSetRatio x ≤ winningSetSoundness (k := k) C δ :=
  le_ciSup (ExistentialEncoding.bddAbove_winningSetRatio C δ) x

/-- The simplified-IOR soundness scalar is a genuine probability bound: it is at most `1`. -/
theorem winningSetSoundness_le_one {k : ℕ} (C : Set (ι → F)) (δ : ℝ≥0) :
    winningSetSoundness (k := k) C δ ≤ 1 := by
  exact ciSup_le' fun x : ExistentialEncoding.ViolatingInstance C δ k => ExistentialEncoding.winningSetRatio_le_one x

/-- **Violation certificate for the correlated-agreement attack.** In the
non-trivial branch of `epsCA` (`¬ jointProximity`), the zero-constraint two-row
instance `(0, 0, 0, u 0, u 1)` violates the existential relaxed relation. This is
the contrapositive of the in-tree bridge `relaxedRelation_two_zero_imp_jointProximity`,
so (unlike an honest-zero witness) it is a genuine violation certificate. -/
theorem not_relaxedRelation_two_zero_of_not_jointProximity {k : ℕ} [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0) (u : WordStack F (Fin 2) ι)
    (hjp : ¬ jointProximity C (u := u) δ) :
    ¬ relaxedRelation (k := k) (ℓ := 2) C δ (0 : Fin k → F) ![0, 0] ![u 0, u 1] := by
  intro hrel
  -- `![u 0, u 1]` and `u` agree as `WordStack`s, so the bridge yields `jointProximity`.
  have hu_eq : (![u 0, u 1] : WordStack F (Fin 2) ι) = u := by
    funext i j; fin_cases i <;> rfl
  have := ToyProblem.relaxedRelation_two_zero_imp_jointProximity (k := k) C δ
    (![u 0, u 1] : WordStack F (Fin 2) ι) hrel
  rw [hu_eq] at this
  exact hjp this

/-- **Per-word-stack core of the correlated-agreement attack.** For a code with a
linear parametrization and `δ < 1`, the probability that the fold `u 0 + γ • u 1`
is `δ`-close to `C` is at most the zero-constraint winning fraction
`|winningSet C δ 0 0 0 (u 0) (u 1)| / |F|`. Shared by
`epsCA_le_winningSetSoundness` and `epsCA_le_winningSetDensity`. -/
theorem prob_relClose_le_winningSet_zero_ratio {k : ℕ} [Nonempty ι] (C : Set (ι → F))
    (δ : ℝ≥0) (hδlt : δ < 1)
    (hClin : ∃ enc : (Fin k → F) →ₗ[F] (ι → F), Set.range enc = C)
    (u : WordStack F (Fin 2) ι) :
    Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ] ≤
      ((((winningSet (k := k) C δ (0 : Fin k → F) 0 0 (u 0) (u 1)).ncard : ℝ≥0) /
        (Fintype.card F : ℝ≥0) : ℝ≥0) : ENNReal) := by
  classical
  obtain ⟨enc, hencC⟩ := hClin
  -- `enc`'s image is `C`: membership and surjectivity (for the `relation`-from-membership bridge).
  have hEnc_mem : ∀ m, enc m ∈ C := by
    intro m; rw [← hencC]; exact Set.mem_range_self m
  have hEnc_surj : ∀ c ∈ C, ∃ m, enc m = c := by
    intro c hc; rw [← hencC] at hc; exact hc
  -- `relation`-from-membership bridge (cf. `simplified_iop_soundness_ca_lb` `hrel_of_mem`).
  have hrel_of_mem : ∀ c : ι → F, c ∈ C →
      relation (k := k) (ℓ := 1) C (0 : Fin k → F) (fun _ ↦ (0 : F)) (fun _ ↦ c) := by
    intro c hc
    obtain ⟨m, hm⟩ := hEnc_surj c hc
    exact ⟨fun _ ↦ m, ⟨enc, hEnc_mem, fun _ ↦ hm.symm⟩, by intro i; simp⟩
  -- `Pr[…] = |S| / |F|` and `S ⊆ winningSet`, so `Pr[…] ≤ |winningSet| / |F|` in ENNReal.
  set S : Finset F := Finset.univ.filter
    (fun γ => δᵣ(u 0 + γ • u 1, C) ≤ δ) with hS_def
  have hPr : Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ] =
      (((S.card : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ENNReal) := by
    rw [prob_uniform_eq_card_filter_div_card (F := F)
      (P := fun γ => δᵣ(u 0 + γ • u 1, C) ≤ δ)]
    norm_cast
  -- `S ⊆ winningSet C δ 0 0 0 (u 0) (u 1)`.
  have hsub : ↑S ⊆ winningSet (k := k) C δ (0 : Fin k → F) 0 0 (u 0) (u 1) := by
    intro γ hγ
    simp only [hS_def, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hγ
    rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at hγ
    obtain ⟨c, hc_mem, hc_dist⟩ := hγ
    refine ⟨fun _ => c, ?_, ?_⟩
    · simpa using hrel_of_mem c hc_mem
    · rw [relCloseToWord_iff_exists_agreementCols] at hc_dist
      obtain ⟨T, hT_card, hT_agree⟩ := hc_dist
      refine ⟨T, ?_, ?_⟩
      · have hcomp := (relDist_floor_bound_iff_complement_bound (Fintype.card ι) T.card δ).mp
          hT_card
        have hδle : δ ≤ 1 := le_of_lt hδlt
        have hcompR : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤ (T.card : ℝ) := by
          have := (NNReal.coe_le_coe.mpr hcomp)
          rwa [NNReal.coe_mul, NNReal.coe_natCast] at this
        rwa [NNReal.coe_sub hδle, NNReal.coe_one] at hcompR
      · intro i j hj
        have := (hT_agree j).1 hj
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  -- `|S| ≤ |winningSet|`.
  have hwin_fin : (winningSet (k := k) C δ (0 : Fin k → F) 0 0 (u 0) (u 1)).Finite :=
    Set.toFinite _
  have hcard_le : (S.card : ℕ) ≤
      (winningSet (k := k) C δ (0 : Fin k → F) 0 0 (u 0) (u 1)).ncard := by
    rw [← Set.ncard_coe_finset S]
    exact Set.ncard_le_ncard hsub hwin_fin
  rw [hPr]
  have hdiv : ((S.card : ℝ≥0) / (Fintype.card F : ℝ≥0)) ≤
      ((winningSet (k := k) C δ (0 : Fin k → F) 0 0 (u 0) (u 1)).ncard : ℝ≥0) /
        (Fintype.card F : ℝ≥0) := by
    gcongr ?_ / _
    exact_mod_cast hcard_le
  exact ENNReal.coe_le_coe.mpr hdiv

/-- **The correlated-agreement attack lower-bounds the simplified-IOR soundness
scalar** (the §6.4.2 attack chain, end-to-end and machine-checked). For a linear
code `C`, the existential-encoding scalar `winningSetSoundness` is at least the
correlated agreement error `ε_ca(C, δ)`. This is **Lemma 6.13 of [ABF26]**
(`simplified_iop_soundness_ca_lb`) packaged as an `ExistentialEncoding.ViolatingInstance` and pushed
through `winningSetRatio_le_winningSetSoundness`: the attack witness's winning
fraction `|Ω|/|F| ≥ ε_ca` is a genuine lower bound on the worst-case scalar.

The witnesses are zero-constraint instances carrying a genuine violation
certificate (`not_relaxedRelation_two_zero_of_not_jointProximity`). At `v = 0` the
encoding is irrelevant, so the same bound holds for the fixed-encoding scalar
(`epsCA_le_winningSetDensity`). **CLOSED (2026-06), axiom-clean**
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`). A
`SecurityUpperBound` of `b` bits at a code with `ε_ca ≥ 2^(-b)` follows
immediately; that numeric `ε_ca` bound at the KoalaBear code is not proved. (At
`koalaIRS` the existential attack residual is instead discharged by the constraint
degeneracy, `ArkLib.KoalaBearAttack.fenziSanso_upperBound_attack_residual_holds`,
which is not a correlated-agreement attack.) -/
theorem epsCA_le_winningSetSoundness {k : ℕ} [Nonempty ι] (C : Set (ι → F)) (δ : ℝ≥0)
    (hδpos : (0 : ℝ≥0) < δ) (hδlt : δ < 1)
    (hClin : ∃ enc : (Fin k → F) →ₗ[F] (ι → F), Set.range enc = C) :
    epsCA (F := F) (A := F) C δ δ ≤ (winningSetSoundness (k := k) C δ : ENNReal) := by
  classical
  -- Bound the `epsCA` supremum per word stack `u`; in the non-trivial (`¬ jointProximity`)
  -- branch the zero-constraint instance is a genuine `ExistentialEncoding.ViolatingInstance`.
  rw [show epsCA (F := F) (A := F) C δ δ
        = ⨆ u : WordStack F (Fin 2) ι,
            if jointProximity C (u := u) δ then (0 : ENNReal)
            else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ] from epsCA_eq_pmf C δ δ]
  refine iSup_le (fun u => ?_)
  by_cases hjp : jointProximity C (u := u) δ
  · -- Trivial branch: the term is `0`.
    simp only [hjp, ite_true]; positivity
  · -- Non-trivial branch: `Pr[…] ≤ |Ω|/|F| = winningSetRatio x ≤ winningSetSoundness`.
    simp only [hjp, ite_false]
    let x : ExistentialEncoding.ViolatingInstance C δ k :=
      { v := 0, μ₁ := 0, μ₂ := 0, f₁ := u 0, f₂ := u 1,
        violates := not_relaxedRelation_two_zero_of_not_jointProximity C δ u hjp }
    exact le_trans (prob_relClose_le_winningSet_zero_ratio C δ hδlt hClin u)
      (ENNReal.coe_le_coe.mpr (winningSetRatio_le_winningSetSoundness x))

/-! ## The fixed-encoding soundness scalar (the paper's Definition 6.11)

The paper's simplified IOR `T'[C]` uses the code's **fixed** encoding. Its soundness
scalar is the canonical `ToyProblem.winningSetDensity` (the supremum of
`ToyProblem.winningSetRatio` over `ToyProblem.ViolatingInstance`, built on
`RelaxedRelationFor` / `winningSetFor`, in `ToyProblem/SoundnessBounds.lean`). It is
the target for re-pointing the leaderboard; `ToyParams.soundnessError` and the two
leaderboard structures still use the existential scalar above. The
correlated-agreement attack transfers to it (`epsCA_le_winningSetDensity`) through the
violation transport `not_relaxedRelationFor_of_not_relaxedRelation` and the
zero-constraint bridge `winningSetFor_zero_eq`. No general inequality between
`winningSetDensity` and `winningSetSoundness` is claimed: the fixed language has more
violating instances, but smaller winning sets. -/

/-- **The correlated-agreement attack lower-bounds the fixed-encoding soundness
scalar.** If `encode` parametrizes `C` (`Set.range encode = C`), then
`ε_ca(C, δ) ≤ winningSetDensity encode δ`. The witnesses are the
zero-constraint instances of `epsCA_le_winningSetSoundness`: their existential
violation certificate transports to the fixed encoding
(`not_relaxedRelationFor_of_not_relaxedRelation`), and at `v = 0` their
fixed-encoding and existential winning sets coincide (`winningSetFor_zero_eq`). -/
theorem epsCA_le_winningSetDensity {k : ℕ} [Nonempty ι] (C : Set (ι → F))
    (δ : ℝ≥0) (hδlt : δ < 1) (encode : (Fin k → F) →ₗ[F] (ι → F))
    (hrange : Set.range encode = C) :
    epsCA (F := F) (A := F) C δ δ ≤ (winningSetDensity encode δ : ENNReal) := by
  classical
  have hmem : ∀ m, encode m ∈ C := fun m ↦ by rw [← hrange]; exact Set.mem_range_self m
  rw [show epsCA (F := F) (A := F) C δ δ
        = ⨆ u : WordStack F (Fin 2) ι,
            if jointProximity C (u := u) δ then (0 : ENNReal)
            else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ] from epsCA_eq_pmf C δ δ]
  refine iSup_le (fun u => ?_)
  by_cases hjp : jointProximity C (u := u) δ
  · -- Trivial branch: the term is `0`.
    simp only [hjp, ite_true]; positivity
  · -- Non-trivial branch: the zero-constraint instance violates the fixed relation too.
    simp only [hjp, ite_false]
    let x : ViolatingInstance encode δ :=
      { v := 0, μ₁ := 0, μ₂ := 0, f₁ := u 0, f₂ := u 1,
        violates := not_relaxedRelationFor_of_not_relaxedRelation hmem
          (not_relaxedRelation_two_zero_of_not_jointProximity C δ u hjp) }
    have hratio : winningSetRatio x =
        ((winningSet (k := k) C δ (0 : Fin k → F) 0 0 (u 0) (u 1)).ncard : ℝ≥0) /
          (Fintype.card F : ℝ≥0) := by
      show ((winningSetFor encode δ (0 : Fin k → F) 0 0 (u 0) (u 1)).ncard : ℝ≥0) /
          (Fintype.card F : ℝ≥0) = _
      rw [winningSetFor_zero_eq hrange]
    refine le_trans (prob_relClose_le_winningSet_zero_ratio C δ hδlt ⟨encode, hrange⟩ u) ?_
    rw [← hratio]
    exact ENNReal.coe_le_coe.mpr (winningSetRatio_le_winningSetDensity x)

/-! ## What the leaderboard quantity is, and is NOT

The common quantity is **`winningSetSoundness`** — the Definition 6.11 soundness
scalar of the *simplified IOR* `T'[C]` (Construction 6.9, the §6.4 attack
target), computed with the existential-encoding relations. In the paper, with the
code's fixed encoding, this object is what the §6.4 attacks (Lemmas 6.12/6.13)
*directly* lower-bound and the §6.4 soundness analysis (Lemma 6.10) upper-bounds.
It is **not** that fixed-encoding error (`winningSetDensity`), and it is
degenerate (`= 1`) at the KoalaBear anchor; see the module status section.

It is deliberately **t-independent**: `T'[C]` is single-round, so its soundness
error is exactly the worst-case winning fraction (no spot-check term). Folding a
`(1-δ)^t` term into this quantity would be unfaithful — it would (i) belong to
the *full* protocol C6.2, not C6.9, and (ii) at the prize regime `t = 128`,
`δ ≈ 1-1/√2`, the spot-check term is `(1/√2)^128 = 2^(-64)`, which alone
exceeds the attack target `2^(-116)` and dominates the provable target
`2^(-64)` — collapsing the attack side to a triviality and the provable side to
a falsehood. The `(1-δ)^t` round lives only in the X-side *vehicle*
`toySoundnessError` (the full-protocol RBR bound, below), where it correctly
caps the *provable* security at 64 bits (ABF26 §6.3, `.tex` lines 2819–2823:
the spot-check term dominates `max(2^(-71.5), 2^(-64))`). -/

/-! ## The RBR upper-bound vehicle (full protocol C6.2; Lemmas 6.6 / 6.8)

`toySoundnessError` reuses the per-round error terms of ABF26 Lemmas 6.6 / 6.8
(the error terms of the canonical `Spec.oracleVerifier_knowledgeSoundness_winningSetUpperBound` /
`Spec.oracleVerifier_rbrKnowledgeSoundnessWorstCase`): the `γ`-round error
`ε_mca(C,δ) + |Λ(C^{≡2},δ)| / |F|` and the spot-check error `(1-δ)^t`. In the
paper, Lemma 6.10 makes the `γ`-round error an upper bound on the fixed-encoding
simplified-IOR error, so this is the X-side vehicle. For the existential scalar
`winningSetSoundness` that step is only the explicit residual
`winningSetSoundness_le_toySoundnessError_mcaSafe_residual` below, which cannot
hold at the KoalaBear anchor together with the numeric 64-bit cap (see
`arklib_lowerBound_irs_t128_residual`). -/

/-- The round-by-round soundness upper bound of **Lemmas 6.6 / 6.8 of [ABF26]**
(the *full* protocol C6.2): the `max` of the combination-randomness error
`ε_mca(C,δ) + |Λ(C^{≡2},δ)| / |F|` and the spot-check error `(1-δ)^t`. These are
the per-round terms of the paper's Lemmas 6.6 / 6.8. It bounds the
simplified-IOR soundness from above only through ABF26 Lemma 6.10 (the explicit
residual `winningSetSoundness_le_toySoundnessError_mcaSafe_residual` for the
existential scalar); the `(1-δ)^t` branch is what caps provable security at
64 bits at the prize regime. -/
noncomputable def toySoundnessError (C : Set (ι → F)) (δ : ℝ≥0) (t : ℕ) : ℝ≥0 :=
  max ((epsMCA (F := F) (A := F) C δ).toNNReal +
        ((ListDecodable.Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
          / (Fintype.card F : ℝ≥0))
      ((1 - δ) ^ t)

/-
STATUS (DISPROVEN + NEEDS_CLASSICAL). This bound is the soundness analysis of
Construction 6.9 (ABF26 Lemma 6.10): `winningSetSoundness ≤ ε_mca + |Λ|/|F|`.
Its `ε_mca` term is the *mutual correlated agreement* error, whose provable
size hinges on the proximity radius `δ` one is allowed to take. The
up-to-capacity reading (correlated-agreement / mutual-correlated-agreement /
list-decodability with `BStar = ρ`) was DISPROVEN in 2025 (Crites–Stewart;
Ben-Sasson–Carmon–Haback–Kopparty–Saraf; Diamond–Gruen;
eprint.iacr.org/2025/2046): it is FALSE for some Reed–Solomon families, so any
placeholder discharged at capacity would be discharging a false statement. The
provable replacement is the Johnson-radius variant (`BStar = √ρ`). Even the
Johnson-radius bound is NEEDS_CLASSICAL: discharging it requires classical
coding-theory results (Johnson bound / Guruswami–Sudan / Reed–Solomon
list-decoding) that are NOT yet in mathlib (no Reed–Solomon, list-decoding, or
Johnson API upstream) — a genuine ground-up formalization, not a port. See
research/formal/arklib-proof-research-2026-06.md. There is no `sorry` here: the
formerly executable hole is now the explicit residual proposition
`winningSetSoundness_le_toySoundnessError_mcaSafe_residual`; callers must
provide it.

STATUS (EXISTENTIAL ENCODING, audit 2026-10-28 L33). The paper's Lemma 6.10 is
about the fixed-encoding relation. The residual below is stated for the
existential-encoding scalar `winningSetSoundness`, which equals `1` at the
KoalaBear anchor (`ArkLib.KoalaBearAttack.koalaIRS_soundnessError_eq_one`), so
there it would force `ε_mca + |Λ|/|F| ≥ 1`; together with the numeric 64-bit cap
it is refuted (`ArkLib.KoalaBearAttack.not_arklib_lowerBound_irs_t128_residual`).
-/
/-- Residual content of ABF26 Lemma 6.10, stated for the **existential-encoding**
scalar: the simplified-IOR winning-set soundness `winningSetSoundness` is bounded
by the first (`γ`-round) branch of `toySoundnessError`. This is an explicit
proposition, not a Lean proof hidden behind a hole. The paper proves Lemma 6.10
for the fixed-encoding relation; for the existential scalar this residual is not
justified by the paper and is incompatible, at the KoalaBear anchor, with the
numeric 64-bit cap (see `arklib_lowerBound_irs_t128_residual`). -/
def winningSetSoundness_le_toySoundnessError_mcaSafe_residual {k : ℕ} [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (hEnc : ∃ encode : (Fin k → F) →ₗ[F] (ι → F),
      (∀ m, encode m ∈ C) ∧ ∀ c ∈ C, ∃ m, encode m = c) :
    Prop :=
  δ < (minRelHammingDistCode C : ℝ≥0) →
  winningSetSoundness (k := k) C δ ≤
    (epsMCA (F := F) (A := F) C δ).toNNReal +
      ((ListDecodable.Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
        / (Fintype.card F : ℝ≥0)

/-- **Conditional adapter: the simplified-IOR scalar is below the full-protocol
RBR bound, given the Lemma 6.10 residual.** `winningSetSoundness ≤
toySoundnessError` follows from `hResidual` (the existential-encoding statement of
**Lemma 6.10 of [ABF26]**, `γ`-round error `ε_mca + |Λ|/|F|`) because that error
is the first branch of the `max`. The X side routes through this to turn an
`ε_mca`/`Λ` bound (and the `(1-δ)^t` spot-check cap) into a lower bound on
provable security. The adapter is valid; its hypothesis carries all of the
content and is not proved (see the residual's docstring). -/
theorem winningSetSoundness_le_toySoundnessError {k : ℕ} [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0) (t : ℕ)
    (hEnc : ∃ encode : (Fin k → F) →ₗ[F] (ι → F),
      (∀ m, encode m ∈ C) ∧ ∀ c ∈ C, ∃ m, encode m = c)
    (hResidual : winningSetSoundness_le_toySoundnessError_mcaSafe_residual (k := k) C δ hEnc)
    (hδ : δ < (minRelHammingDistCode C : ℝ≥0)) :
    winningSetSoundness (k := k) C δ ≤ toySoundnessError C δ t := by
  exact le_trans (hResidual hδ) (le_max_left _ _)

/-! ## Bits of security -/

/-- Provable security in bits of a soundness error `e`: `-log₂ e`. At `e = 0`
(perfect soundness) `Real.logb 2 0 = 0`, so `bitsOfSecurity 0 = 0`; callers
exhibiting genuine perfect soundness should special-case it. For the prize
regime `e ∈ (0, 1)` so `bitsOfSecurity e > 0`. -/
noncomputable def bitsOfSecurity (e : ℝ≥0) : ℝ := -Real.logb 2 (e : ℝ)

/-- A positive soundness error bounded by `1` has nonnegative bits of security. -/
theorem bitsOfSecurity_nonneg {e : ℝ≥0} (hpos : 0 < e) (hle : e ≤ 1) :
    0 ≤ bitsOfSecurity e := by
  rw [bitsOfSecurity, le_neg]
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hpos)]
  simpa using (NNReal.coe_le_coe.mpr hle)

/-! ## Parameter record (KoalaBear-sextic regime)

`ToyParams` bundles the ambient field/index and interpreted code (the
universe-pinned bridge — `epsMCA`/`Λ` need their code at `Type 0`) together
with the plain-data numeric regime (KoalaBear field size `q`, sextic
extension, rate `ρ`, and `s, n, k, t, δ, η`). The leaderboard anchor now uses
the genuine KoalaBear-sextic carrier and RS code (at block length `4`). At that
anchor the existential-encoding scalar equals `1`: the cardinality residual of
the attack side holds through the constraint degeneracy, and the RBR residual of
the provable side is refuted (module status section). `ToyParams` carries no
encoder, so the fixed-encoding scalar `winningSetDensity` is not yet wired
into it. -/

/-- The KoalaBear-sextic parameter regime plus its code interpretation. The
operational fields `(F, ι, C, δ, t, k)` feed `soundnessError`; the documentary
fields `(q, ext, ρ, s, n, η)` record the §6.3 numeric regime for Phase 5 and
the wiki. All carrier types are pinned to `Type 0`. -/
structure ToyParams where
  /-- Ambient field (`Type 0`; KoalaBear sextic at Phase 5). -/
  F : Type
  /-- Codeword index type (`Type 0`; `Fin n`). -/
  ι : Type
  [field : Field F]
  [fintypeF : Fintype F]
  [decEqF : DecidableEq F]
  [fintypeι : Fintype ι]
  /-- The interpreted base code `C ⊆ (ι → F)`. -/
  C : Set (ι → F)
  /-- Proximity radius `δ`. -/
  δ : ℝ≥0
  /-- Number of spot-check repetitions `t`. -/
  t : ℕ
  /-- Constraint dimension `k` (gives `winningSet`'s `v : Fin k → F`). -/
  k : ℕ
  /-- Documentary: field characteristic-prime size `q` (KoalaBear: `2^31 - 2^24 + 1`). -/
  q : ℕ := 2 ^ 31 - 2 ^ 24 + 1
  /-- Documentary: extension degree (KoalaBear sextic: `6`). -/
  ext : ℕ := 6
  /-- Documentary: rate `ρ = k/n` (prize regime `1/2`). -/
  ρ : ℝ≥0 := 1 / 2
  /-- Documentary: interleaving / codeword symbol size `s`. -/
  s : ℕ := 1
  /-- Documentary: intended block length `n` (the intended rate is `ρ = k/n`).
  Need not equal `|ι|` for stand-in parameters. -/
  n : ℕ := 0
  /-- Documentary: Johnson slack `η`. -/
  η : ℝ≥0 := 0

attribute [instance] ToyParams.field ToyParams.fintypeF ToyParams.decEqF ToyParams.fintypeι

/-- The leaderboard's common quantity at a parameter point: the simplified-IOR
(Construction 6.9 / Definition 6.11) soundness scalar `winningSetSoundness` in
the **existential-encoding** language, projected onto the bundled carrier. It is
not the paper's fixed-encoding soundness error and equals `1` at `koalaIRS`
(`ArkLib.KoalaBearAttack.koalaIRS_soundnessError_eq_one`). -/
noncomputable def ToyParams.soundnessError (p : ToyParams) : ℝ≥0 :=
  winningSetSoundness (k := p.k) p.C p.δ

/-- The bundled simplified-IOR soundness error is bounded by `1`. -/
theorem ToyParams.soundnessError_le_one (p : ToyParams) :
    p.soundnessError ≤ 1 :=
  _root_.ToyProblem.winningSetSoundness_le_one (k := p.k) p.C p.δ

/-- The bundled simplified-IOR soundness error lies in the probability interval `[0, 1]`. -/
theorem ToyParams.soundnessError_mem_Icc (p : ToyParams) :
    p.soundnessError ∈ Set.Icc 0 1 :=
  ⟨by positivity, p.soundnessError_le_one⟩

/-- Real-valued form of `ToyParams.soundnessError_mem_Icc`. -/
theorem ToyParams.coe_soundnessError_mem_Icc (p : ToyParams) :
    (p.soundnessError : ℝ) ∈ Set.Icc 0 1 :=
  ⟨NNReal.coe_nonneg _, by exact_mod_cast p.soundnessError_le_one⟩

/-- The true bits-of-security of a positive bundled soundness error is nonnegative. -/
theorem ToyParams.bitsOfSecurity_nonneg (p : ToyParams) (hpos : 0 < p.soundnessError) :
    0 ≤ bitsOfSecurity p.soundnessError :=
  _root_.ToyProblem.bitsOfSecurity_nonneg hpos p.soundnessError_le_one

/-- A positive bundled soundness error has true bits-of-security in `[0, ∞)`. -/
theorem ToyParams.bitsOfSecurity_mem_Ici (p : ToyParams) (hpos : 0 < p.soundnessError) :
    bitsOfSecurity p.soundnessError ∈ Set.Ici 0 :=
  p.bitsOfSecurity_nonneg hpos

/-- The full-protocol RBR upper-bound vehicle (Lemmas 6.6 / 6.8) at a parameter
point. -/
noncomputable def ToyParams.toySoundnessError (p : ToyParams) : ℝ≥0 :=
  _root_.ToyProblem.toySoundnessError p.C p.δ p.t

/-- `soundnessError ≤ toySoundnessError` at a parameter point, conditional on
the explicit Lemma 6.10 residual for that parameter point. -/
theorem ToyParams.soundnessError_le_toySoundnessError (p : ToyParams) [Nonempty p.ι]
    (hEnc : ∃ encode : (Fin p.k → p.F) →ₗ[p.F] (p.ι → p.F),
      (∀ m, encode m ∈ p.C) ∧ ∀ c ∈ p.C, ∃ m, encode m = c)
    (hResidual :
      winningSetSoundness_le_toySoundnessError_mcaSafe_residual (k := p.k) p.C p.δ hEnc)
    (hδ : p.δ < (minRelHammingDistCode p.C : ℝ≥0)) :
    p.soundnessError ≤ p.toySoundnessError :=
  _root_.ToyProblem.winningSetSoundness_le_toySoundnessError (k := p.k) p.C p.δ p.t
    hEnc hResidual hδ

/-! ## The two leaderboard interfaces

Both are stated against the **same** common quantity `p.soundnessError`, the
existential-encoding scalar. A submission is an *inhabitant*. At `koalaIRS` that
scalar is `1`, so every `SecurityLowerBound koalaIRS` has `bits ≤ 0` and every
`bits ≥ 0` is a `SecurityUpperBound koalaIRS`
(`ArkLib.KoalaBearAttack.koalaIRS_securityLowerBound_bits_nonpos`,
`ArkLib.KoalaBearAttack.zeroBitUpperBound`). -/

/-- **Provable security lower bound** at parameter point `p`: a number `bits`
and a proof that the bundled simplified-IOR soundness scalar is `≤ 2^(-bits)` —
i.e. "we can *prove* at least `bits` bits of security" for the
existential-encoding model. The intended proof route is
`soundnessError ≤ toySoundnessError ≤ 2^(-bits)` via [ABF26] Lemmas 6.10 / 6.6.
`bits : ℝ` because the security level *is* `bitsOfSecurity e = -log₂ e`, a real for
any soundness error `e ∈ (0,1)` (almost never an integer); the §6.3 figures the
anchors quote are themselves fractional (the attack is `2^(-116.49)`, the C6.9 MCA
branch `≈ 2^(-71.5)`, the spot-check `(1-δ)^128 ≈ 2^(-65.9)`). -/
structure SecurityLowerBound (p : ToyParams) where
  /-- The provable security level, in bits. -/
  bits : ℝ
  /-- The bundled (existential-encoding) soundness scalar is at most `2^(-bits)`. -/
  proof : p.soundnessError ≤ (2 : ℝ≥0) ^ (-bits)

/-- **Provable security upper bound** at parameter point `p`: a number `bits`
and a proof that the bundled soundness scalar is `≥ 2^(-bits)` — i.e. "no
analysis can prove *more* than `bits` bits of security" for the
existential-encoding model. The intended witness is a winning-set attack in the
style of [ABF26] Lemmas 6.12 / 6.13 (`soundnessError ≥ |Ω|/|F| ≥ 2^(-bits)`);
in this model the constraint degeneracy also supplies witnesses, which are not
paper attacks. -/
structure SecurityUpperBound (p : ToyParams) where
  /-- The provable security ceiling, in bits. -/
  bits : ℝ
  /-- The bundled (existential-encoding) soundness scalar is at least `2^(-bits)`. -/
  proof : p.soundnessError ≥ (2 : ℝ≥0) ^ (-bits)

/-! ## The leaderboard metric -/

/-- **The leaderboard metric.** The scalar gap `Y − X` between the best known
attack (`hi`) and the best provable security (`lo`). Contestants minimise this.
The paper's KoalaBear-sextic figure is the ≈116 − 64 = 52-bit frontier; the Lean
anchors at `koalaIRS` do not certify it (module status section). -/
def securityGap {p : ToyParams} (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) : ℝ :=
  hi.bits - lo.bits

/-- **The [ABF26] §6 prize gap is honest** (`lo.bits ≤ hi.bits`, so
`securityGap ≥ 0`). Proved
directly from the two inequalities: `2^(-hi.bits) ≤ soundnessError ≤
2^(-lo.bits)`, and `x ↦ 2^(-x)` is strictly antitone, so `lo.bits ≤ hi.bits`.
No degenerate `error = 0` case arises: the two `2^(-·)` terms are positive and
are chained transitively, never divided by the error. Axiom-clean. -/
theorem SecurityLowerBound.bits_le_of {p : ToyParams}
    (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) :
    lo.bits ≤ hi.bits := by
  -- `2^(-hi.bits) ≤ soundnessError ≤ 2^(-lo.bits)` in `ℝ≥0`.
  have hchain : (2 : ℝ≥0) ^ (-hi.bits) ≤ (2 : ℝ≥0) ^ (-lo.bits) :=
    le_trans hi.proof lo.proof
  -- Cast to `ℝ` and use strict monotonicity of `2^(·)`.
  have hchainR : (2 : ℝ) ^ (-hi.bits) ≤ (2 : ℝ) ^ (-lo.bits) := by
    have := (NNReal.coe_le_coe.mpr hchain)
    rwa [NNReal.coe_rpow, NNReal.coe_rpow, NNReal.coe_ofNat] at this
  have hexp : -hi.bits ≤ -lo.bits :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hchainR
  linarith

/-- `securityGap` is non-negative. -/
theorem securityGap_nonneg {p : ToyParams}
    (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) :
    0 ≤ securityGap lo hi := by
  have := lo.bits_le_of hi
  simp only [securityGap]; linarith

/-! ### The `bits` interpretation

A `SecurityLowerBound`/`SecurityUpperBound` `bits` field is exactly a bound on
the bits-of-security `bitsOfSecurity soundnessError` of the bundled
(existential-encoding) scalar; "true" below means the value for that scalar.
Together these read: `lo.bits ≤ bitsOfSecurity (soundnessError) ≤ hi.bits`
(when the error is positive), i.e. the certified provable level sits below the
true level, which sits below the attack ceiling. -/

/-- A provable lower bound's `bits` is at most the true bits-of-security
(equivalently to `lo.proof`, when the soundness error is positive). -/
theorem SecurityLowerBound.le_bitsOfSecurity {p : ToyParams} (lo : SecurityLowerBound p)
    (h : 0 < p.soundnessError) : lo.bits ≤ bitsOfSecurity p.soundnessError := by
  rw [bitsOfSecurity, le_neg, Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast h)]
  have := NNReal.coe_le_coe.mpr lo.proof
  rwa [NNReal.coe_rpow, NNReal.coe_ofNat] at this

/-- A provable upper bound's `bits` is at least the true bits-of-security
(equivalently to `hi.proof`, when the soundness error is positive). -/
theorem SecurityUpperBound.bitsOfSecurity_le {p : ToyParams} (hi : SecurityUpperBound p)
    (h : 0 < p.soundnessError) : bitsOfSecurity p.soundnessError ≤ hi.bits := by
  rw [bitsOfSecurity, neg_le, Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast h)]
  have := NNReal.coe_le_coe.mpr hi.proof
  rwa [NNReal.coe_rpow, NNReal.coe_ofNat] at this

/-- Two-sided bracket for the true bits-of-security certified by a lower/upper
leaderboard pair. This packages the common downstream use of
`SecurityLowerBound.le_bitsOfSecurity` and
`SecurityUpperBound.bitsOfSecurity_le`. -/
theorem bitsOfSecurity_mem_Icc_of_bounds {p : ToyParams}
    (lo : SecurityLowerBound p) (hi : SecurityUpperBound p)
    (h : 0 < p.soundnessError) :
    bitsOfSecurity p.soundnessError ∈ Set.Icc lo.bits hi.bits :=
  ⟨lo.le_bitsOfSecurity h, hi.bitsOfSecurity_le h⟩

/-! ## Anchor parameter point and the two current entries

`koalaIRS` fixes the genuine KoalaBear-sextic regime (`q = 2^31 - 2^24 + 1`,
sextic extension, `ρ = 1/2`, `t = 128`) over the concrete rate-`1/2`
Reed-Solomon code `KoalaBear.rsCodeSet`.

The two anchors below are conditional on explicit residual propositions rather than
hidden proof holes. The field and code are no longer opaque stand-ins. For the
existential-encoding scalar they bound, the residuals are now settled, but not by the
intended §6 content: the provable side's residual `arklib_lowerBound_irs_t128_residual` is
**false** (`ArkLib.KoalaBearAttack.not_arklib_lowerBound_irs_t128_residual`), and the attack
side's residual `fenziSanso_upperBound_attack_residual` is **true** by the constraint
degeneracy (`ArkLib.KoalaBearAttack.fenziSanso_upperBound_attack_residual_holds`), not by a
Fenzi–Sanso winning-set construction. -/

/-- The Proximity-Prize anchor parameter point: the genuine KoalaBear-sextic regime
(`q = 2^31 - 2^24 + 1`, sextic extension, `ρ = 1/2`, `t = 128`) over the real field
`F_{p^6}` and the genuine rate-`1/2` Reed-Solomon code, at block length `n = 4`. The proximity
radius is set near capacity,
`δ = 3/10` (just above `1 - 1/√2 ≈ 0.293`), so the full-protocol spot-check term
`(1-δ)^128 ≈ 2^(-65.9) ≤ 2^(-64)` is consistent with the headline 64-bit provable ceiling
(cf. ABF26 §6.3, `.tex` 2819–2823). The existential-encoding soundness scalar is `1` here
(`ArkLib.KoalaBearAttack.koalaIRS_soundnessError_eq_one`). -/
noncomputable def koalaIRS : ToyParams where
  F := KoalaBear.Sextic
  ι := Fin 4
  C := KoalaBear.rsCodeSet
  δ := 3 / 10
  t := 128
  k := 2
  q := 2 ^ 31 - 2 ^ 24 + 1
  ext := 6
  ρ := 1 / 2
  s := 1
  n := 4
  η := 1 / 16

/-
STATUS (OPEN_PRIZE). This anchor is the *provable-security* (X) side of the
EF Proximity Prize / ABF26 §6 Grand Challenge: how many bits of soundness can
one actually *prove* for the toy protocol at the KoalaBear-sextic rate regime
(target `ε* = 2^-128` at rates `1/2 .. 1/16`). Maximising this provable `bits`
is the open research problem the prize poses — it is an unsolved research
problem, not a closeable Lean obligation. The `64`-bit value here is a
placeholder anchor, and the proof route moreover inherits the
DISPROVEN/NEEDS_CLASSICAL status of `winningSetSoundness_le_toySoundnessError`
(the up-to-capacity `ε_mca` term, disproven 2025; the Johnson-radius
replacement needs absent mathlib coding-theory API). Do not attempt to close
this residual by pretending those imports exist. See
research/formal/arklib-proof-research-2026-06.md.

STATUS (REFUTED for the existential scalar, audit 2026-10-28 L33). The residual
`arklib_lowerBound_irs_t128_residual` is false: the existential-encoding scalar is `1`
at `koalaIRS`, so no positive-bit `SecurityLowerBound koalaIRS` exists
(`ArkLib.KoalaBearAttack.not_arklib_lowerBound_irs_t128_residual`,
`ArkLib.KoalaBearAttack.koalaIRS_securityLowerBound_bits_nonpos`). The 64-bit figure
remains the paper's spot-check-limited ceiling for the fixed-encoding protocol.
-/
/-- `koalaIRS` has a nonempty index type (`Fin 4`). -/
instance : Nonempty koalaIRS.ι := ⟨(0 : Fin 4)⟩

/-- The genuine KoalaBear-sextic Reed–Solomon code is the range of a linear encoder. -/
theorem koalaIRS_linear_encoder :
    ∃ encode : (Fin koalaIRS.k → koalaIRS.F) →ₗ[koalaIRS.F] (koalaIRS.ι → koalaIRS.F),
      (∀ m, encode m ∈ koalaIRS.C) ∧ ∀ c ∈ koalaIRS.C, ∃ m, encode m = c := by
  rcases KoalaBear.rsCode_isLinear with ⟨enc, henc⟩
  exact ⟨enc, by
    intro m
    change enc m ∈ KoalaBear.rsCodeSet
    rw [← henc]
    exact Set.mem_range_self m, by
    intro c hc
    change c ∈ KoalaBear.rsCodeSet at hc
    rw [← henc] at hc
    exact hc⟩

/-- Explicit residual assumptions for the 64-bit Koala anchor: ABF26 Lemma 6.10 at
`koalaIRS` (stated for the existential-encoding scalar), the proximity-below-distance
condition, and the §6.3 numeric evaluation of the RBR bound.

**This conjunction is false**
(`ArkLib.KoalaBearAttack.not_arklib_lowerBound_irs_t128_residual`): together the
conjuncts give `koalaIRS.soundnessError ≤ 2^(-64)`, while that scalar is `1`. The second
conjunct is proved (`ToyProblem.koalaIRS_delta_lt_minRelHammingDist`), so the first and
third cannot both hold. -/
def arklib_lowerBound_irs_t128_residual : Prop :=
  winningSetSoundness_le_toySoundnessError_mcaSafe_residual
      (k := koalaIRS.k) koalaIRS.C koalaIRS.δ koalaIRS_linear_encoder ∧
  koalaIRS.δ < (minRelHammingDistCode koalaIRS.C : ℝ≥0) ∧
  koalaIRS.toySoundnessError ≤ (2 : ℝ≥0) ^ (-(64 : ℝ))

/-- **Conditional 64-bit lower-bound anchor at the IRS/KoalaBear/`t=128` point.**
Cites **Lemmas 6.10 / 6.6 / 6.8 of [ABF26]**: in the paper the fixed-encoding
simplified-IOR soundness error is bounded by the full-protocol RBR error
`max (ε_mca + |Λ|/|F|) ((1-δ)^t)`, which evaluates to ≈`2^(-64)` at the §6.3
Table 2–3 numerics — the spot-check branch `(1-δ)^128 = (1/√2)^128 = 2^(-64)`
is the binding cap (`.tex` 2819–2823; the `ε_mca + |Λ|/|F|` branch is the even
tighter ≈`2^(-71.5)`). The construction routes `soundnessError ≤ toySoundnessError ≤
2^(-64)` and is conditional on `arklib_lowerBound_irs_t128_residual`.

That hypothesis is **refuted**
(`ArkLib.KoalaBearAttack.not_arklib_lowerBound_irs_t128_residual`): the bundled
existential-encoding scalar is `1` at `koalaIRS`, so this anchor can never be applied
and 64 is **not** a provable bound on `winningSetSoundness`. -/
noncomputable def arklib_lowerBound_irs_t128
    (h : arklib_lowerBound_irs_t128_residual) : SecurityLowerBound koalaIRS where
  bits := 64
  proof := by
    haveI : Nonempty koalaIRS.ι := inferInstance
    exact le_trans
      (koalaIRS.soundnessError_le_toySoundnessError koalaIRS_linear_encoder h.1 h.2.1)
      h.2.2

/-- Explicit residual for the 116-bit attack anchor: the bundled existential-encoding
scalar at `koalaIRS` is at least `2^(-116)`.

It is **true**, but only because that scalar is `1`
(`ArkLib.KoalaBearAttack.fenziSanso_upperBound_attack_residual_holds`, via the constraint
degeneracy of the existential encoding). This is not the Fenzi–Sanso / ABF26 Lemma 6.12
list-decoding attack, which has no large lists at this length-4 carrier. -/
def fenziSanso_upperBound_attack_residual : Prop :=
  koalaIRS.soundnessError ≥ (2 : ℝ≥0) ^ (-(116 : ℝ))

/-- **Winning-set attack upper bound (≈116 bits) at the IRS/KoalaBear/`t=128`
point.** Cites **Lemma 6.12 of [ABF26]** (§6.4.1; a similar observation appears
in Fenzi–Sanso, eprint 2025/2197, Lemma 4.4): in the paper, at KoalaBear-sextic
`ρ = 1/2, t = 128` and real block lengths, the winning challenge set is large enough
that the simplified-IOR soundness error is `≥ ≈2^(-116)` (ABF26 §6.3, `.tex` 2925:
`2^(-116.49)`). This backward-compatible anchor is conditional on the explicit
proposition `fenziSanso_upperBound_attack_residual`; the concrete carrier below
refines it to a KoalaBear winning-set cardinality witness. Both residuals are proved
in `ArkLib/ToMathlib/KoalaBearAttackInstance.lean`, but by the existential-encoding
degeneracy rather than by the paper's attack, so the 116-bit ceiling it certifies is
an artifact of the model (the scalar is `1`, a `0`-bit ceiling). -/
noncomputable def fenziSanso_upperBound_attack
    (h : fenziSanso_upperBound_attack_residual) : SecurityUpperBound koalaIRS where
  bits := 116
  proof := h

/-- **Arithmetic readoff of the two conditional anchors.** In the paper's
KoalaBear-sextic regime the provable security is ≈64 bits and the best known attack is
≈116 bits, a `116 − 64 = 52`-bit gap (see [ABF26] §6.3 Tables 2–5). This theorem only
reads that difference off the two `bits` fields.

It is **vacuous**: its hypothesis `hLo` is refuted
(`ArkLib.KoalaBearAttack.not_arklib_lowerBound_irs_t128_residual`), so it certifies no
frontier at `koalaIRS`. The anchor-independent, axiom-clean guarantee is the metric
lemma `bits_le_of`. -/
theorem securityGap_koalaIRS_anchors :
    ∀ (hLo : arklib_lowerBound_irs_t128_residual)
      (hHi : fenziSanso_upperBound_attack_residual),
      securityGap (arklib_lowerBound_irs_t128 hLo) (fenziSanso_upperBound_attack hHi) = 52 := by
  intro hLo hHi
  simp only [securityGap, arklib_lowerBound_irs_t128, fenziSanso_upperBound_attack]
  norm_num

/-- The conditional KoalaBear-sextic anchor frontier is nonnegative. This is the
order-only form of `securityGap_koalaIRS_anchors`, and depends only on the explicit
anchor residual assumptions; like that theorem it is vacuous, since `hLo` is refuted
(`ArkLib.KoalaBearAttack.not_arklib_lowerBound_irs_t128_residual`). -/
theorem securityGap_koalaIRS_anchors_nonneg
    (hLo : arklib_lowerBound_irs_t128_residual)
    (hHi : fenziSanso_upperBound_attack_residual) :
    0 ≤ securityGap (arklib_lowerBound_irs_t128 hLo) (fenziSanso_upperBound_attack hHi) := by
  exact securityGap_nonneg (arklib_lowerBound_irs_t128 hLo) (fenziSanso_upperBound_attack hHi)

/-! ## Concrete KoalaBear-sextic carrier

The anchor point `koalaIRS` is the genuine KoalaBear-sextic carrier over the real field
`F_{p^6}` (`KoalaBear.Sextic`, `p = 2^31 - 2^24 + 1`) and the genuine rate-`1/2` Reed-Solomon
code (`KoalaBear.rsCodeSet`, the range of an explicit `F`-linear evaluation encoder). Two things
are concrete, not owed:

* **the field size** — `|F| = p^6 ≈ 2^186` (`KoalaBear.card_sextic`), so the
  prize window `[2^(-116), 2^(-64)]` is genuinely representable; and
* **the code's `F`-linearity** — true *by construction*
  (`KoalaBear.rsCode_isLinear` is `⟨rsEncoder, rfl⟩`), which is exactly the
  `hClin` hypothesis the proven attack chain `epsCA_le_winningSetSoundness`
  requires and the opaque stand-in could not supply.

The numeric anchor reductions below discharge the **explicit-power arithmetic**
end-to-end (sorry-free, `norm_num` only), turning each obligation into a pure
coding-theory fact about a *winning-set cardinality*. For the existential-encoding
scalar those facts are now settled at this carrier, though not by the intended §6
content: the attack-side cardinality residual holds through the constraint
degeneracy (`ArkLib/ToMathlib/KoalaBearAttackInstance.lean`), and the provable-side
residual is refuted. What the §6 content would still have to supply is the
fixed-encoding version: bounds on `winningSetDensity KoalaBear.rsEncoder (3/10)`
(the correlated-agreement lower bound `epsCA_le_winningSetDensity_concrete` is
proved; the value of `ε_ca` of this RS code is not). -/

/-- Backward-compatible name for the genuine KoalaBear-sextic anchor. -/
noncomputable abbrev koalaIRSConcrete : ToyParams := koalaIRS

/-- The genuine carrier's field is the KoalaBear-sextic field, of size
`p^6 ≈ 2^186`. -/
theorem card_koalaIRSConcrete_F :
    Fintype.card koalaIRSConcrete.F = KoalaBear.fieldSize ^ 6 :=
  KoalaBear.card_sextic

/-! ### `2^(-bits)` as an explicit reciprocal power (the arithmetic core)

The leaderboard's `bits` exponents are *real* (`NNReal.rpow`); the anchor
inequalities compare them against the rational `|Ω|/|F|`. The bridge is purely
arithmetic: `(2 : ℝ≥0) ^ (-(b : ℝ)) = (2 ^ b)⁻¹` for a natural `b`. -/

/-- `(2 : ℝ≥0) ^ (-(b : ℝ)) = ((2 : ℝ≥0) ^ b)⁻¹` for natural `b`: the real
exponent `-(b)` collapses to the reciprocal natural power. The arithmetic core
of both numeric anchors. -/
theorem two_rpow_neg_natCast (b : ℕ) :
    (2 : ℝ≥0) ^ (-(b : ℝ)) = ((2 : ℝ≥0) ^ b)⁻¹ := by
  rw [show (-(b : ℝ)) = (((-(b : ℤ)) : ℤ) : ℝ) by push_cast; ring,
    NNReal.rpow_intCast, zpow_neg, zpow_natCast]

/-! ### Attack-side numeric reduction (`fenziSanso` ⇒ explicit power)

The proven backbone is `winningSetRatio_le_winningSetSoundness`: any violating
instance's winning fraction `|Ω|/|F|` lower-bounds `winningSetSoundness`. Over
the concrete field `|F| = p^6 ≤ 2^186`, a winning set of `≥ 2^70` challenges
already realises the `2^(-116)` attack floor (`2^70 / 2^186 = 2^(-116)`). This
turns the §6.4 attack obligation into a *single cardinality bound* — the genuine
code-theoretic content — with all field arithmetic discharged here. -/

/-- **Field-general attack floor from a winning-set cardinality bound.** A
violating instance whose winning set has at least `2^(N-b)` challenges, over a
field of size `≤ 2^N`, forces `winningSetSoundness ≥ 2^(-b)` (the `b`-bit attack
floor). Pure NNReal explicit-power arithmetic over the proven backbone
`winningSetRatio_le_winningSetSoundness` (`|Ω|/|F| ≥ 2^(N-b)/2^N = 2^(-b)`). This
is the parameter-general core of the concrete anchor below: it consumes a
winning-set *cardinality* hypothesis (the §6.4 construction's output), it does
not produce one, so it is reusable at any leaderboard parameter point. -/
theorem winningSetSoundness_ge_of_card_le {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    {b N : ℕ} (x : ExistentialEncoding.ViolatingInstance C δ k)
    (hF : (Fintype.card F : ℝ≥0) ≤ (2 : ℝ≥0) ^ N) (hb : b ≤ N)
    (hx : (2 : ℕ) ^ (N - b) ≤
      (winningSet C δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard) :
    (2 : ℝ≥0) ^ (-(b : ℝ)) ≤ winningSetSoundness (k := k) C δ := by
  -- `winningSetRatio x ≤ winningSetSoundness`; bound `2^(-b) ≤ winningSetRatio x`.
  refine le_trans ?_ (winningSetRatio_le_winningSetSoundness x)
  rw [ExistentialEncoding.winningSetRatio]
  rw [show (2 : ℝ≥0) ^ (-(b : ℝ)) = ((2 : ℝ≥0) ^ b)⁻¹ from two_rpow_neg_natCast b]
  -- Abbreviate the winning-set cardinality.
  set Ncard : ℕ :=
    (winningSet C δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard with hN
  have hFpos : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hNge : (2 : ℝ≥0) ^ (N - b) ≤ (Ncard : ℝ≥0) := by
    calc (2 : ℝ≥0) ^ (N - b) = (((2 : ℕ) ^ (N - b) : ℕ) : ℝ≥0) := by push_cast; ring
      _ ≤ (Ncard : ℝ≥0) := by exact_mod_cast hx
  -- `(2^b)⁻¹ ≤ Ncard / |F|`.
  rw [le_div_iff₀ hFpos]
  -- `(2^b)⁻¹ * |F| ≤ 2^(N-b) ≤ Ncard`, using `|F| ≤ 2^N = 2^b · 2^(N-b)`.
  calc ((2 : ℝ≥0) ^ b)⁻¹ * (Fintype.card F : ℝ≥0)
      ≤ ((2 : ℝ≥0) ^ b)⁻¹ * (2 : ℝ≥0) ^ N := by gcongr
    _ = (2 : ℝ≥0) ^ (N - b) := by
        have hsplit : (2 : ℝ≥0) ^ N = (2 : ℝ≥0) ^ b * (2 : ℝ≥0) ^ (N - b) := by
          rw [← pow_add, Nat.add_sub_cancel' hb]
        rw [hsplit, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    _ ≤ (Ncard : ℝ≥0) := hNge

/-- **Attack-side numeric anchor (concrete carrier), sorry-free.** A single
violating instance over the genuine KoalaBear-sextic RS code whose winning set
has at least `2^70` challenges forces `winningSetSoundness ≥ 2^(-116)` — the
attack floor. (`|F| = p^6 ≤ 2^186`, so `|Ω|/|F| ≥ 2^70/2^186 = 2^(-116)`.) The
hypothesis is exactly the §6.4 winning-set construction's *cardinality output*.
This is the `N = 186`, `b = 116` specialization of the field-general
`winningSetSoundness_ge_of_card_le`, with the concrete `|F| = p^6 ≤ 2^186`
bound supplied by `KoalaBear.card_sextic_le_186`. -/
theorem winningSetSoundness_concrete_ge_of_card
    (x : ExistentialEncoding.ViolatingInstance KoalaBear.rsCodeSet (3 / 10) 2)
    (hx : (2 : ℕ) ^ 70 ≤
      (winningSet KoalaBear.rsCodeSet (3 / 10) x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard) :
    (2 : ℝ≥0) ^ (-(116 : ℝ)) ≤
      winningSetSoundness (k := 2) KoalaBear.rsCodeSet (3 / 10) := by
  have hFle : (Fintype.card KoalaBear.Sextic : ℝ≥0) ≤ (2 : ℝ≥0) ^ 186 := by
    have hc := KoalaBear.card_sextic_le_186
    calc (Fintype.card KoalaBear.Sextic : ℝ≥0)
        ≤ (((2 : ℕ) ^ 186 : ℕ) : ℝ≥0) := by exact_mod_cast hc
      _ = (2 : ℝ≥0) ^ 186 := by push_cast; ring
  have := winningSetSoundness_ge_of_card_le (b := 116) (N := 186) x hFle (by norm_num)
    (by simpa using hx)
  simpa using this

/-- **The proven attack chain applies to the genuine code** (linearity supplied
by construction). `ε_ca(C, δ) ≤ winningSetSoundness C δ` at the concrete
KoalaBear-sextic RS code: this is `epsCA_le_winningSetSoundness` discharged with
the in-tree `δ`-bounds and the by-construction linear-encoder hypothesis
`KoalaBear.rsCode_isLinear` — exactly the `hClin` the opaque stand-in could not
provide. Through this route, a correlated-agreement attack at the genuine code needs
only the numeric `2^(-116) ≤ ε_ca`, which is not proved. (The existential scalar on
the right is already `1` by the constraint degeneracy; the fixed-encoding form of this
bound is `epsCA_le_winningSetDensity_concrete`.) -/
theorem epsCA_le_winningSetSoundness_concrete :
    epsCA (F := KoalaBear.Sextic) (A := KoalaBear.Sextic) KoalaBear.rsCodeSet (3 / 10) (3 / 10)
      ≤ (winningSetSoundness (k := 2) KoalaBear.rsCodeSet (3 / 10) : ENNReal) :=
  epsCA_le_winningSetSoundness (k := 2) KoalaBear.rsCodeSet (3 / 10)
    (by norm_num) (by norm_num) KoalaBear.rsCode_isLinear

/-- **The correlated-agreement attack lower-bounds the fixed-encoding scalar at the
genuine code.** `ε_ca(C, δ) ≤ winningSetDensity rsEncoder δ` for the concrete
KoalaBear-sextic RS code with its own encoder `KoalaBear.rsEncoder`, at `δ = 3/10`.
Unlike the existential scalar, `winningSetDensity` is not inflated by the
constraint degeneracy, so this is the attack-side bound a fixed-encoding leaderboard
would use; the value of `ε_ca` here is not computed. -/
theorem epsCA_le_winningSetDensity_concrete :
    epsCA (F := KoalaBear.Sextic) (A := KoalaBear.Sextic) KoalaBear.rsCodeSet (3 / 10) (3 / 10)
      ≤ (winningSetDensity KoalaBear.rsEncoder (3 / 10) : ENNReal) :=
  epsCA_le_winningSetDensity KoalaBear.rsCodeSet (3 / 10) (by norm_num)
    KoalaBear.rsEncoder rfl

/-- **Attack-side residual at the concrete carrier.** A violating instance (for the
existential-encoding relation) over the genuine KoalaBear-sextic RS code with
`≥ 2^70` winning challenges, stripped of all field arithmetic and linearity (the latter
holds by construction via `KoalaBear.rsCode_isLinear`). It was meant to be discharged by
the §6.4 winning-set combinatorics / an `ε_ca`-realising witness.

It is **true** for a different reason: `ArkLib.KoalaBearAttack.attackInstance` is a
violating instance whose winning set is all of `F`
(`ArkLib.KoalaBearAttack.fenziSanso_upperBound_attack_concrete_residual_holds`), by the
constraint degeneracy of the existential encoding. That proof is model-level evidence
(issue #339), not a list-decoding attack. -/
def fenziSanso_upperBound_attack_concrete_residual : Prop :=
  ∃ x : ExistentialEncoding.ViolatingInstance KoalaBear.rsCodeSet (3 / 10) 2,
    (2 : ℕ) ^ 70 ≤
      (winningSet KoalaBear.rsCodeSet (3 / 10) x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard

/-- **Winning-set attack upper bound (≈116 bits) at the GENUINE KoalaBear-sextic
carrier.** Same ceiling as `fenziSanso_upperBound_attack`, but over the real
field `F_{p^6}` and the genuine rate-`1/2` RS code, and conditional only on the
*coding-theory* residual `fenziSanso_upperBound_attack_concrete_residual` (a
cardinality bound on the attack winning set) — the field arithmetic
(`|F| = p^6`, `2^70/2^186 = 2^(-116)`) is fully discharged by
`winningSetSoundness_concrete_ge_of_card`. Its residual is proved by the constraint
degeneracy (`ArkLib.KoalaBearAttack.attackUpperBound`), so the ceiling is an artifact
of the existential-encoding model, not the paper's 116-bit attack. -/
noncomputable def fenziSanso_upperBound_attack_concrete
    (hConcrete : fenziSanso_upperBound_attack_concrete_residual) :
    SecurityUpperBound koalaIRSConcrete where
  bits := 116
  proof := by
    obtain ⟨x, hx⟩ := hConcrete
    show koalaIRSConcrete.soundnessError ≥ (2 : ℝ≥0) ^ (-(116 : ℝ))
    exact winningSetSoundness_concrete_ge_of_card x hx

/-- The concrete KoalaBear-sextic winning-set cardinality residual is strong
enough to discharge the original 116-bit leaderboard attack residual. This is
the bridge that lets downstream users keep depending on the canonical
`fenziSanso_upperBound_attack` name while proving only the concrete Phase-5
cardinality statement. -/
theorem fenziSanso_upperBound_attack_residual_of_concrete :
    fenziSanso_upperBound_attack_concrete_residual →
    fenziSanso_upperBound_attack_residual := by
  intro hConcrete
  exact (fenziSanso_upperBound_attack_concrete hConcrete).proof

/-- If the concrete Fenzi–Sanso winning-set residual holds, then the true
bits-of-security of the concrete KoalaBear-sextic anchor is at most `116`. The
residual is proved, via the existential-encoding degeneracy, and the actual value for
the bundled scalar is `0` (`ArkLib.KoalaBearAttack.koalaIRS_bitsOfSecurity_eq_zero`). -/
theorem koalaIRSConcrete_bitsOfSecurity_le_116
    (hConcrete : fenziSanso_upperBound_attack_concrete_residual)
    (hpos : 0 < koalaIRSConcrete.soundnessError) :
    bitsOfSecurity koalaIRSConcrete.soundnessError ≤ 116 := by
  simpa [fenziSanso_upperBound_attack_concrete] using
    (fenziSanso_upperBound_attack_concrete hConcrete).bitsOfSecurity_le hpos

/-- Interval-membership form of `koalaIRSConcrete_bitsOfSecurity_le_116`. -/
theorem koalaIRSConcrete_bitsOfSecurity_mem_Iic_116
    (hConcrete : fenziSanso_upperBound_attack_concrete_residual)
    (hpos : 0 < koalaIRSConcrete.soundnessError) :
    bitsOfSecurity koalaIRSConcrete.soundnessError ∈ Set.Iic (116 : ℝ) :=
  koalaIRSConcrete_bitsOfSecurity_le_116 hConcrete hpos

/-- If the explicit 64-bit lower-bound residual holds at the concrete
KoalaBear-sextic anchor, then the bits-of-security of the bundled scalar are at least
`64`. Vacuous: the residual is refuted
(`ArkLib.KoalaBearAttack.not_arklib_lowerBound_irs_t128_residual`); the bundled scalar
is `1`, with `0` bits of security
(`ArkLib.KoalaBearAttack.koalaIRS_bitsOfSecurity_eq_zero`). -/
theorem koalaIRSConcrete_64_le_bitsOfSecurity
    (hLower : arklib_lowerBound_irs_t128_residual)
    (hpos : 0 < koalaIRSConcrete.soundnessError) :
    (64 : ℝ) ≤ bitsOfSecurity koalaIRSConcrete.soundnessError := by
  simpa [koalaIRSConcrete, arklib_lowerBound_irs_t128] using
    (arklib_lowerBound_irs_t128 hLower).le_bitsOfSecurity hpos

/-- Conditional concrete leaderboard window for the bundled KoalaBear-sextic
bits-of-security: the explicit 64-bit lower residual and concrete Fenzi-Sanso
attack residual would place it in `[64, 116]`. Vacuous, because the lower residual
is refuted (`ArkLib.KoalaBearAttack.not_arklib_lowerBound_irs_t128_residual`); the
actual value for the existential-encoding scalar is `0`
(`ArkLib.KoalaBearAttack.koalaIRS_bitsOfSecurity_eq_zero`). -/
theorem koalaIRSConcrete_bitsOfSecurity_mem_Icc_64_116
    (hConcrete : fenziSanso_upperBound_attack_concrete_residual)
    (hLower : arklib_lowerBound_irs_t128_residual)
    (hpos : 0 < koalaIRSConcrete.soundnessError) :
    bitsOfSecurity koalaIRSConcrete.soundnessError ∈ Set.Icc (64 : ℝ) 116 :=
  ⟨koalaIRSConcrete_64_le_bitsOfSecurity hLower hpos,
    koalaIRSConcrete_bitsOfSecurity_le_116 hConcrete hpos⟩

/-! ### Provable-side numeric reduction (`arklib_lowerBound` ⇒ explicit power)

The provable side routes through the full-protocol RBR vehicle
`toySoundnessError`, whose binding cap at the prize regime is the spot-check
term `(1-δ)^t = (7/10)^128`. The *numeric* obligation
`toySoundnessError ≤ 2^(-64)` reduces to bounding that explicit power; the
remaining `winningSetSoundness ≤ toySoundnessError` step is ABF26 Lemma 6.10,
which is **DISPROVEN/NEEDS_CLASSICAL** in its up-to-capacity reading (see the STATUS
note before `winningSetSoundness_le_toySoundnessError_mcaSafe_residual`) and is left
as an explicit residual — *not* attempted here. For the existential scalar at
`koalaIRS` that step and the numeric cap cannot both hold, since the scalar is `1`
(`ArkLib.KoalaBearAttack.not_arklib_lowerBound_irs_t128_residual`); the spot-check
arithmetic below is unaffected. -/

/-- The spot-check branch dominates and is below `2^(-64)`: at `δ = 3/10`,
`t = 128`, the term `(1 - δ)^t = (7/10)^128 ≤ 2^(-64)`. Pure explicit-power
arithmetic over `ℝ≥0` (`(7/10)^128 ≈ 2^(-65.9)`); cross-multiplied to integers
and closed by `norm_num`. This is the binding numeric cap of the provable side. -/
theorem spotCheck_le_two_pow_neg_64 :
    ((1 : ℝ≥0) - 3 / 10) ^ (128 : ℕ) ≤ (2 : ℝ≥0) ^ (-(64 : ℝ)) := by
  rw [show (2 : ℝ≥0) ^ (-(64 : ℝ)) = ((2 : ℝ≥0) ^ 64)⁻¹ by
    exact two_rpow_neg_natCast 64]
  have hsub : (1 : ℝ≥0) - 3 / 10 = 7 / 10 := by
    apply NNReal.coe_injective
    have hle : (3 / 10 : ℝ≥0) ≤ 1 := by
      exact_mod_cast (by norm_num : (3 / 10 : ℝ) ≤ 1)
    rw [NNReal.coe_sub hle]
    norm_num
  rw [hsub]
  -- `(7/10)^128 = 7^128 / 10^128 ≤ (2^64)⁻¹ = 1 / 2^64`  ⇔  `7^128 · 2^64 ≤ 10^128`.
  rw [div_pow, show ((2 : ℝ≥0) ^ 64)⁻¹ = 1 / (2 : ℝ≥0) ^ 64 by rw [one_div],
    div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  norm_num

/-- Concrete-anchor form of the spot-check cap: `koalaIRSConcrete` has
`δ = 3/10` and `t = 128`, so its spot-check branch is below `2^(-64)`. -/
theorem koalaIRSConcrete_spotCheck_le_two_pow_neg_64 :
    ((1 : ℝ≥0) - koalaIRSConcrete.δ) ^ koalaIRSConcrete.t ≤
      (2 : ℝ≥0) ^ (-(64 : ℝ)) := by
  simpa [koalaIRSConcrete, koalaIRS] using spotCheck_le_two_pow_neg_64

end ToyProblem

-- Source-audit anchors for issue #18. These are the remaining ToyProblem
-- Lemma 6.10 / leaderboard residual fronts and their concrete-anchor adapters.
#print axioms ToyProblem.winningSetSoundness_le_toySoundnessError_mcaSafe_residual
#print axioms ToyProblem.winningSetSoundness_le_toySoundnessError
#print axioms ToyProblem.arklib_lowerBound_irs_t128_residual
#print axioms ToyProblem.arklib_lowerBound_irs_t128
#print axioms ToyProblem.fenziSanso_upperBound_attack_residual
#print axioms ToyProblem.fenziSanso_upperBound_attack
#print axioms ToyProblem.securityGap_koalaIRS_anchors
#print axioms ToyProblem.securityGap_koalaIRS_anchors_nonneg
#print axioms ToyProblem.winningSetSoundness_ge_of_card_le
#print axioms ToyProblem.winningSetSoundness_concrete_ge_of_card
#print axioms ToyProblem.epsCA_le_winningSetSoundness_concrete
#print axioms ToyProblem.fenziSanso_upperBound_attack_concrete_residual
#print axioms ToyProblem.fenziSanso_upperBound_attack_concrete
#print axioms ToyProblem.fenziSanso_upperBound_attack_residual_of_concrete
#print axioms ToyProblem.koalaIRSConcrete_bitsOfSecurity_le_116
#print axioms ToyProblem.koalaIRSConcrete_bitsOfSecurity_mem_Iic_116
#print axioms ToyProblem.koalaIRSConcrete_64_le_bitsOfSecurity
#print axioms ToyProblem.koalaIRSConcrete_bitsOfSecurity_mem_Icc_64_116
#print axioms ToyProblem.spotCheck_le_two_pow_neg_64
#print axioms ToyProblem.koalaIRSConcrete_spotCheck_le_two_pow_neg_64
-- Fixed-encoding soundness scalar and the correlated-agreement attack (audit 2026-10-28, L33).
#print axioms ToyProblem.not_relaxedRelation_two_zero_of_not_jointProximity
#print axioms ToyProblem.prob_relClose_le_winningSet_zero_ratio
#print axioms ToyProblem.epsCA_le_winningSetSoundness
#print axioms ToyProblem.winningSetDensity_le_one
#print axioms ToyProblem.epsCA_le_winningSetDensity
#print axioms ToyProblem.epsCA_le_winningSetDensity_concrete
