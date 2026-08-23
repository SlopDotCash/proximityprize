/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import ArkLib.ToMathlib.ToyProblemViolation
import ArkLib.ToMathlib.KoalaBearCode
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Proximity-Prize "bits of security" leaderboard (ABF26 §6)

A machine-checked **leaderboard contract** for the soundness of the §6 toy
protocol (Construction 6.2 / its simplified IOR Construction 6.9). The
Ethereum Foundation Proximity Prize (proximityprize.org) asks for the gap
between the *provable* security of small-field hash-based SNARGs and the
*best known attack*; at the KoalaBear-sextic regime (`ρ = 1/2`, `t = 128`)
this is the ≈64-vs-≈116-bit frontier (ABF26 §6.3 Tables 2–5, and the
standalone attack of Fenzi–Sanso, eprint 2025/2197).

This file states that frontier as two opposing Lean structures over **one
common quantity** — the soundness error of the simplified IOR `T'[C]`
(Construction 6.9, the §6.4 attack target), `winningSetSoundness` — so the
scalar gap between them is meaningful:

* `SecurityLowerBound p` — an inhabitant is a proof "we can *prove* `≥ bits`
  bits of security": `soundnessError ≤ 2^(-bits)`. The proof routes through
  the full-protocol round-by-round (RBR) upper bound `toySoundnessError`
  (Lemmas 6.10 / 6.6 / 6.8).
* `SecurityUpperBound p` — an inhabitant is a proof "no analysis can prove
  `> bits` bits": `soundnessError ≥ 2^(-bits)`. The witness is the
  winning-set attack of Lemmas 6.12 / 6.13.
* `securityGap lo hi := hi.bits - lo.bits` — the scalar contestants minimise.
  `SecurityLowerBound.bits_le_of` proves `lo.bits ≤ hi.bits` (so the gap is
  `≥ 0`) directly from the two inequalities, axiom-cleanly.

## The common quantity (central design decision)

The two sides **must** bound the same quantity or the gap is meaningless.
The trap: `toySoundnessError` (the full-protocol RBR max) is an *upper* bound,
while the attack lemmas L6.12/6.13 *lower* bound. So `attack ≤ error ≤
toySoundnessError`. We make the leaderboard quantity the **simplified-IOR
soundness error** `winningSetSoundness` — per `winningSet`'s Definition 6.11,
the worst-case winning-challenge fraction `|Ω|/|F|` over *violating* instances.
This is the object the §6.4 attacks directly lower-bound and Lemma 6.10
upper-bounds.

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
cannot "win" by inflating the RBR bound — they must exhibit a real attack.

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

/-! ## The soundness scalar (Definition 6.11 reading)

`winningSetSoundness` is the simplified IOR's actual soundness error: the
supremum, over instances `(v, μ₁, μ₂, f₁, f₂)` that *violate* the relaxed
relation `R̃_{C,δ}^2`, of the winning-challenge fraction `|Ω| / |F|`. The
violating constraint is essential — over *all* inputs a valid instance has
`Ω = F` (fraction `1`), so the unrestricted sup is the trivial `1`. -/

/-- An instance of the simplified IOR whose stack `(v, μ₁, μ₂, f₁, f₂)`
violates the relaxed relation `R̃_{C,δ}^2`. This is the index of the
worst-case soundness supremum of Definition 6.11. -/
structure ViolatingInstance (C : Set (ι → F)) (δ : ℝ≥0) (k : ℕ) where
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
noncomputable def winningSetRatio {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (x : ViolatingInstance C δ k) : ℝ≥0 :=
  ((winningSet C δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-- **Definition 6.11 of [ABF26]** (soundness error of the simplified IOR).

The worst-case winning-challenge fraction over violating instances:
`sup_{(v,μ₁,μ₂,f₁,f₂) violating R̃²} |Ω| / |F|`. This is the protocol's
*actual* soundness error after the combination-randomness round — the common
quantity the leaderboard's two sides bound from opposite directions. -/
noncomputable def winningSetSoundness {k : ℕ} (C : Set (ι → F)) (δ : ℝ≥0) : ℝ≥0 :=
  ⨆ x : ViolatingInstance C δ k, winningSetRatio x

/-- The winning-challenge fraction never exceeds `1` (`winningSet ⊆ F`). -/
theorem winningSetRatio_le_one {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (x : ViolatingInstance C δ k) : winningSetRatio x ≤ 1 := by
  haveI : Nonempty F := ⟨0⟩
  have hpos : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  rw [winningSetRatio, div_le_one hpos]
  have hle : (winningSet C δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard ≤ Fintype.card F := by
    have := Set.ncard_le_ncard (Set.subset_univ
      (winningSet C δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂)) (Set.finite_univ)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  exact_mod_cast hle

/-- The family of winning-challenge fractions is bounded above (by `1`), so
its supremum is well-behaved in the conditionally complete order `ℝ≥0`. -/
theorem bddAbove_winningSetRatio {k : ℕ} (C : Set (ι → F)) (δ : ℝ≥0) :
    BddAbove (Set.range (fun x : ViolatingInstance C δ k ↦ winningSetRatio x)) := by
  refine ⟨1, ?_⟩
  rintro r ⟨x, rfl⟩
  exact winningSetRatio_le_one x

/-- Each violating instance's winning fraction is a lower bound on the
soundness error of [ABF26] Definition 6.11 — the backbone of the attack (Y)
side: an explicit attack witness lower-bounds `winningSetSoundness`. -/
theorem winningSetRatio_le_winningSetSoundness {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (x : ViolatingInstance C δ k) :
    winningSetRatio x ≤ winningSetSoundness (k := k) C δ :=
  le_ciSup (bddAbove_winningSetRatio C δ) x

/-- The simplified-IOR soundness scalar is a genuine probability bound: it is at most `1`. -/
theorem winningSetSoundness_le_one {k : ℕ} (C : Set (ι → F)) (δ : ℝ≥0) :
    winningSetSoundness (k := k) C δ ≤ 1 := by
  exact ciSup_le' fun x : ViolatingInstance C δ k => winningSetRatio_le_one x

/-- **The correlated-agreement attack lower-bounds the simplified-IOR soundness**
(the §6.4.2 attack chain, end-to-end and machine-checked). For a linear code
`C`, the soundness error `winningSetSoundness` is at least the correlated
agreement error `ε_ca(C, δ)`. This is **Lemma 6.13 of [ABF26]**
(`simplified_iop_soundness_ca_lb`) packaged as a `ViolatingInstance` and pushed through
`winningSetRatio_le_winningSetSoundness`: the attack witness's winning fraction
`|Ω|/|F| ≥ ε_ca` is a genuine lower bound on the worst-case soundness.

This is the real content the §6.3-numeric attack anchors instantiate: a
`SecurityUpperBound` of `b` bits at a code with `ε_ca ≥ 2^(-b)` follows
immediately. **CLOSED (2026-06), axiom-clean** (`#print axioms` = `[propext,
Classical.choice, Quot.sound]`, no `sorryAx`): the §6.4.1 winning-set construction
is proved end-to-end here (the violation certificate is supplied per word-stack by the
in-tree bridge `relaxedRelation_two_zero_imp_jointProximity`). Only the *numeric*
`ε_ca ≥ 2^(-b)` at the genuine KoalaBear code remains owed downstream
(`fenziSanso_upperBound_attack`), which is a separate coding-theory obligation, not part of this
lemma. -/
theorem epsCA_le_winningSetSoundness {k : ℕ} [Nonempty ι] (C : Set (ι → F)) (δ : ℝ≥0)
    (hδpos : (0 : ℝ≥0) < δ) (hδlt : δ < 1)
    (hClin : ∃ enc : (Fin k → F) →ₗ[F] (ι → F), Set.range enc = C) :
    epsCA (F := F) (A := F) C δ δ ≤ (winningSetSoundness (k := k) C δ : ENNReal) := by
  classical
  -- **CLOSED (2026-06).** The §6.4.1 winning-set construction, end-to-end.  The
  -- merged `simplified_iop_soundness_ca_lb` does not surface the violation certificate;
  -- we therefore re-derive the bound per word-stack `u` over the `epsCA` supremum, and at
  -- each `u` in the non-trivial (`¬ jointProximity`) branch package the certificate via the
  -- in-tree bridge `relaxedRelation_two_zero_imp_jointProximity` (contrapositive), so the
  -- CA-maximising witness is a genuine `ViolatingInstance`. No statement is changed.
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
  -- `epsCA = ⨆ u, g u`; bound the supremum termwise.
  rw [show epsCA (F := F) (A := F) C δ δ
        = ⨆ u : WordStack F (Fin 2) ι,
            if jointProximity C (u := u) δ then (0 : ENNReal)
            else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ] from rfl]
  refine iSup_le (fun u => ?_)
  by_cases hjp : jointProximity C (u := u) δ
  · -- Trivial branch: the term is `0`.
    simp only [hjp, if_true]; exact zero_le _
  · -- Non-trivial branch: build the `ViolatingInstance` and bound `Pr · 1 ≤ winningSetSoundness`.
    simp only [hjp, if_false]
    -- Violation certificate via the bridge's contrapositive at `v = 0`, `μ = (0,0)`.
    have hviol : ¬ relaxedRelation (k := k) (ℓ := 2) C δ (0 : Fin k → F) ![0, 0]
        ![u 0, u 1] := by
      intro hrel
      -- `![u 0, u 1]` and `u` agree as `WordStack`s, so the bridge yields `jointProximity`.
      have hu_eq : (![u 0, u 1] : WordStack F (Fin 2) ι) = u := by
        funext i j; fin_cases i <;> rfl
      have := ToyProblem.relaxedRelation_two_zero_imp_jointProximity (k := k) C δ
        (![u 0, u 1] : WordStack F (Fin 2) ι) hrel
      rw [hu_eq] at this
      exact hjp this
    -- Package the violating instance.
    set x : ViolatingInstance C δ k :=
      { v := 0, μ₁ := 0, μ₂ := 0, f₁ := u 0, f₂ := u 1, violates := hviol } with hx
    -- The winning-set ratio of `x` lower-bounds `winningSetSoundness`.
    have hxle : winningSetRatio x ≤ winningSetSoundness (k := k) C δ :=
      winningSetRatio_le_winningSetSoundness x
    -- `Pr[…] = |S| / |F|` and `S ⊆ winningSet`, so `Pr[…] ≤ winningSetRatio x` in ENNReal.
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
      simp only [hS_def, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hγ
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
    -- Assemble: `Pr[…] = |S|/|F| ≤ |winningSet|/|F| = winningSetRatio x ≤ winningSetSoundness`.
    have hcardF_ne : (Fintype.card F : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hratio_eq : winningSetRatio x
        = (((winningSet (k := k) C δ (0 : Fin k → F) 0 0 (u 0) (u 1)).ncard : ℝ≥0)
            / (Fintype.card F : ℝ≥0)) := by
      rw [hx]; rfl
    rw [hPr]
    -- `|S|/|F| ≤ winningSetRatio x ≤ winningSetSoundness` in ℝ≥0; cast to ENNReal.
    have hdiv : ((S.card : ℝ≥0) / (Fintype.card F : ℝ≥0)) ≤ winningSetSoundness (k := k) C δ := by
      refine le_trans ?_ hxle
      rw [hratio_eq]
      gcongr ?_ / _
      exact_mod_cast hcard_le
    exact_mod_cast hdiv

/-! ## What the leaderboard quantity is, and is NOT

The common quantity is **`winningSetSoundness`** — the soundness error of the
*simplified IOR* `T'[C]` (Construction 6.9, the §6.4 attack target), per
Definition 6.11. This is the object the §6.4 attacks (Lemmas 6.12/6.13)
*directly* lower-bound and the §6.4 soundness analysis (Lemma 6.10) upper-bounds.

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

`toySoundnessError` reuses the *exact* per-round error terms of
`Spec.General.protocol62_knowledgeSound` / `protocol62_rbrKnowledgeSound`
(Lemmas 6.6 / 6.8): the `γ`-round error `ε_mca(C,δ) + |Λ(C^{≡2},δ)| / |F|` and
the spot-check error `(1-δ)^t`. It upper-bounds `winningSetSoundness` (via
Lemma 6.10, since the `γ`-round error already dominates the simplified IOR's
error) and is the X-side vehicle. -/

/-- The round-by-round soundness upper bound of **Lemmas 6.6 / 6.8 of [ABF26]**
(the *full* protocol C6.2): the `max` of the combination-randomness error
`ε_mca(C,δ) + |Λ(C^{≡2},δ)| / |F|` and the spot-check error `(1-δ)^t`. These are
the *exact* per-round terms of `protocol62_knowledgeSound`. It bounds the
simplified-IOR soundness `winningSetSoundness` from above (X-side vehicle); the
`(1-δ)^t` branch is what caps provable security at 64 bits at the prize regime. -/
noncomputable def toySoundnessError (C : Set (ι → F)) (δ : ℝ≥0) (t : ℕ) : ℝ≥0 :=
  max ((epsMCA (F := F) (A := F) C δ).toNNReal +
        ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
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
Johnson API upstream) — a genuine ground-up formalization, not a port. Do not
attempt to close the sorry; do not remove it. See
research/formal/arklib-proof-research-2026-06.md. The formerly executable hole
is now the explicit residual proposition
`winningSetSoundness_le_toySoundnessError_residual`; callers must provide it.
-/
/-- Residual content of ABF26 Lemma 6.10: the simplified-IOR winning-set
soundness is bounded by the first (`γ`-round) branch of `toySoundnessError`.
This is an explicit paper-proof obligation, not a Lean proof hidden behind a
hole. -/
def winningSetSoundness_le_toySoundnessError_mcaSafe_residual {k : ℕ} [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (hEnc : ∃ encode : (Fin k → F) →ₗ[F] (ι → F),
      (∀ m, encode m ∈ C) ∧ ∀ c ∈ C, ∃ m, encode m = c) :
    Prop :=
  δ < (minRelHammingDistCode C : ℝ≥0) →
  winningSetSoundness (k := k) C δ ≤
    (epsMCA (F := F) (A := F) C δ).toNNReal +
      ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
        / (Fintype.card F : ℝ≥0)

/-- **The simplified-IOR soundness is below the full-protocol RBR bound**
(**Lemma 6.10 of [ABF26]**). `winningSetSoundness ≤ toySoundnessError`: the
simplified IOR's worst-case winning fraction is at most the `γ`-round error
`ε_mca + |Λ|/|F|` (Lemma 6.10 — the soundness of Construction 6.9), which is the
first branch of the `max`. The X side routes through this to turn an
`ε_mca`/`Λ` bound (and the `(1-δ)^t` spot-check cap) into a provable security
lower bound. -/
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
the genuine KoalaBear-sextic carrier and RS code; the remaining Phase-5
obligations are the code-theoretic cardinality/RBR inequalities recorded below. -/

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
(Construction 6.9 / Definition 6.11) soundness error `winningSetSoundness`,
projected onto the bundled carrier. -/
noncomputable def ToyParams.soundnessError (p : ToyParams) : ℝ≥0 :=
  winningSetSoundness (k := p.k) p.C p.δ

/-- The bundled simplified-IOR soundness error is bounded by `1`. -/
theorem ToyParams.soundnessError_le_one (p : ToyParams) :
    p.soundnessError ≤ 1 :=
  _root_.ToyProblem.winningSetSoundness_le_one (k := p.k) p.C p.δ

/-- The bundled simplified-IOR soundness error lies in the probability interval `[0, 1]`. -/
theorem ToyParams.soundnessError_mem_Icc (p : ToyParams) :
    p.soundnessError ∈ Set.Icc 0 1 :=
  ⟨zero_le _, p.soundnessError_le_one⟩

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

Both are stated against the **same** common quantity `p.soundnessError`. A
submission is an *inhabitant*. -/

/-- **Provable security lower bound** at parameter point `p`: a number `bits`
and a proof that the simplified-IOR soundness error is `≤ 2^(-bits)` — i.e. "we
can *prove* at least `bits` bits of security." The intended proof route is
`soundnessError ≤ toySoundnessError ≤ 2^(-bits)` via [ABF26] Lemmas 6.10 / 6.6.
`bits : ℝ` because the security level *is* `bitsOfSecurity e = -log₂ e`, a real for
any soundness error `e ∈ (0,1)` (almost never an integer); the §6.3 figures the
anchors quote are themselves fractional (the attack is `2^(-116.49)`, the C6.9 MCA
branch `≈ 2^(-71.5)`, the spot-check `(1-δ)^128 ≈ 2^(-65.9)`). -/
structure SecurityLowerBound (p : ToyParams) where
  /-- The provable security level, in bits. -/
  bits : ℝ
  /-- The actual soundness error is at most `2^(-bits)`. -/
  proof : p.soundnessError ≤ (2 : ℝ≥0) ^ (-bits)

/-- **Provable security upper bound** at parameter point `p`: a number `bits`
and a proof that the actual soundness error is `≥ 2^(-bits)` — i.e. "no
analysis can prove *more* than `bits` bits of security." The witness is the
winning-set attack of [ABF26] Lemmas 6.12 / 6.13: `soundnessError ≥ |Ω|/|F| ≥
2^(-bits)`. -/
structure SecurityUpperBound (p : ToyParams) where
  /-- The provable security ceiling, in bits. -/
  bits : ℝ
  /-- The actual soundness error is at least `2^(-bits)`. -/
  proof : p.soundnessError ≥ (2 : ℝ≥0) ^ (-bits)

/-! ## The leaderboard metric -/

/-- **The leaderboard metric.** The scalar gap `Y − X` between the best known
attack (`hi`) and the best provable security (`lo`). Contestants minimise this
— at the KoalaBear-sextic regime it is the ≈116 − 64 = 52-bit frontier. -/
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
the true bits-of-security `bitsOfSecurity soundnessError`. Together these read:
`lo.bits ≤ bitsOfSecurity (soundnessError) ≤ hi.bits` (when the error is
positive), i.e. the certified provable level sits below the true level, which
sits below the attack ceiling. -/

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
hidden proof holes. Their remaining obligations are code-theoretic: the §6.3 RBR upper-bound
calculation for the provable side, and the Fenzi-Sanso winning-set construction for the attack
side. The field and code are no longer opaque stand-ins. -/

/-- The Proximity-Prize anchor parameter point: the genuine KoalaBear-sextic regime
(`q = 2^31 - 2^24 + 1`, sextic extension, `ρ = 1/2`, `t = 128`) over the real field
`F_{p^6}` and the genuine rate-`1/2` Reed-Solomon code. The proximity radius is set near capacity,
`δ = 3/10` (just above `1 - 1/√2 ≈ 0.293`), so the full-protocol spot-check term
`(1-δ)^128 ≈ 2^(-65.9) ≤ 2^(-64)` is consistent with the headline 64-bit provable ceiling
(cf. ABF26 §6.3, `.tex` 2819–2823). -/
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
-/
/-- Explicit residual assumptions needed for the 64-bit Koala anchor:
ABF26 Lemma 6.10 at `koalaIRS` plus the §6.3 numeric evaluation of the RBR
bound. -/
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

def arklib_lowerBound_irs_t128_residual : Prop :=
  winningSetSoundness_le_toySoundnessError_mcaSafe_residual
      (k := koalaIRS.k) koalaIRS.C koalaIRS.δ koalaIRS_linear_encoder ∧
  koalaIRS.δ < (minRelHammingDistCode koalaIRS.C : ℝ≥0) ∧
  koalaIRS.toySoundnessError ≤ (2 : ℝ≥0) ^ (-(64 : ℝ))

/-- **ArkLib provable lower bound (≈64 bits) at the IRS/KoalaBear/`t=128`
point.** Cites **Lemmas 6.10 / 6.6 / 6.8 of [ABF26]**: the simplified-IOR
soundness error is bounded by the full-protocol RBR error
`max (ε_mca + |Λ|/|F|) ((1-δ)^t)`, which evaluates to ≈`2^(-64)` at the §6.3
Table 2–3 numerics — the spot-check branch `(1-δ)^128 = (1/√2)^128 = 2^(-64)`
is the binding cap (`.tex` 2819–2823; the `ε_mca + |Λ|/|F|` branch is the even
tighter ≈`2^(-71.5)`). 64 is thus a *conservative* (improvable) provable bound on
`winningSetSoundness`. The proof routes `soundnessError ≤ toySoundnessError ≤
2^(-64)`. Conditional on `arklib_lowerBound_irs_t128_residual` (the §6.3
numeric evaluation is Phase 5). -/
noncomputable def arklib_lowerBound_irs_t128
    (h : arklib_lowerBound_irs_t128_residual) : SecurityLowerBound koalaIRS where
  bits := 64
  proof := by
    haveI : Nonempty koalaIRS.ι := inferInstance
    exact le_trans
      (koalaIRS.soundnessError_le_toySoundnessError koalaIRS_linear_encoder h.1 h.2.1)
      h.2.2

/-- **Winning-set attack upper bound (≈116 bits) at the IRS/KoalaBear/`t=128`
point.** Cites **Lemma 6.12 of [ABF26]** (§6.4.1; a similar observation appears
in Fenzi–Sanso, eprint 2025/2197, Lemma 4.4): the winning challenge set is large
enough that, at KoalaBear-sextic `ρ=1/2, t=128`, the simplified-IOR soundness
error is `≥ ≈2^(-116)` (ABF26 §6.3, `.tex` 2925: `2^(-116.49)`). The witness is
the attack instance, lower-bounding `winningSetSoundness` directly via
`winningSetRatio_le_winningSetSoundness`. This backward-compatible anchor is
conditional on the explicit proposition `fenziSanso_upperBound_attack_residual`;
the concrete carrier below refines the owed content to a KoalaBear winning-set
cardinality witness. -/
def fenziSanso_upperBound_attack_residual : Prop :=
  koalaIRS.soundnessError ≥ (2 : ℝ≥0) ^ (-(116 : ℝ))

noncomputable def fenziSanso_upperBound_attack
    (h : fenziSanso_upperBound_attack_residual) : SecurityUpperBound koalaIRS where
  bits := 116
  proof := h

/-- **The current leaderboard frontier.** At the KoalaBear-sextic anchor the
provable security is ≈64 bits and the best known attack is ≈116 bits, so the
gap the prize asks contestants to close is `116 − 64 = 52` bits (see [ABF26]
§6.3 Tables 2–5). The value is a
pure arithmetic readoff of the two `bits` fields — it does not depend on the
anchors' owed §6 *proofs* being correct beyond the explicit residual
hypotheses; the metric lemma `bits_le_of` is the anchor-independent,
axiom-clean guarantee. -/
theorem securityGap_koalaIRS_anchors :
    ∀ (hLo : arklib_lowerBound_irs_t128_residual)
      (hHi : fenziSanso_upperBound_attack_residual),
      securityGap (arklib_lowerBound_irs_t128 hLo) (fenziSanso_upperBound_attack hHi) = 52 := by
  intro hLo hHi
  simp only [securityGap, arklib_lowerBound_irs_t128, fenziSanso_upperBound_attack]
  norm_num

/-- The conditional KoalaBear-sextic anchor frontier is nonnegative. This is the
order-only form of `securityGap_koalaIRS_anchors`, and depends only on the explicit
anchor residual assumptions. -/
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

What remains genuinely owed at the concrete carrier is *only* the §6
code-theoretic content (the size of the attack winning set / the value of
`ε_ca` of the RS code), not field arithmetic or linearity. The numeric anchor
reductions below discharge the **explicit-power arithmetic** end-to-end (sorry-
free, `norm_num` only), turning each owed obligation into a pure coding-theory
fact about a *winning-set cardinality*. -/

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
    {b N : ℕ} (x : ViolatingInstance C δ k)
    (hF : (Fintype.card F : ℝ≥0) ≤ (2 : ℝ≥0) ^ N) (hb : b ≤ N)
    (hx : (2 : ℕ) ^ (N - b) ≤
      (winningSet C δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard) :
    (2 : ℝ≥0) ^ (-(b : ℝ)) ≤ winningSetSoundness (k := k) C δ := by
  -- `winningSetRatio x ≤ winningSetSoundness`; bound `2^(-b) ≤ winningSetRatio x`.
  refine le_trans ?_ (winningSetRatio_le_winningSetSoundness x)
  rw [winningSetRatio]
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
    (x : ViolatingInstance KoalaBear.rsCodeSet (3 / 10) 2)
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
provide. With this, the §6.4 attack obligation at the genuine code is *only* the
numeric `2^(-116) ≤ ε_ca`; the soundness-vehicle step is now a real theorem. -/
theorem epsCA_le_winningSetSoundness_concrete :
    epsCA (F := KoalaBear.Sextic) (A := KoalaBear.Sextic) KoalaBear.rsCodeSet (3 / 10) (3 / 10)
      ≤ (winningSetSoundness (k := 2) KoalaBear.rsCodeSet (3 / 10) : ENNReal) :=
  epsCA_le_winningSetSoundness (k := 2) KoalaBear.rsCodeSet (3 / 10)
    (by norm_num) (by norm_num) KoalaBear.rsCode_isLinear

/-- **Attack-side residual at the concrete carrier.** The §6.4 winning-set
construction over the genuine KoalaBear-sextic RS code: a violating instance
with `≥ 2^70` winning challenges. This is the *pure coding-theory* content owed
(Phase 4 winning-set combinatorics / the `ε_ca`-realising witness), now
stripped of all field arithmetic and linearity (the latter holds by
construction via `KoalaBear.rsCode_isLinear`). -/
def fenziSanso_upperBound_attack_concrete_residual : Prop :=
  ∃ x : ViolatingInstance KoalaBear.rsCodeSet (3 / 10) 2,
    (2 : ℕ) ^ 70 ≤
      (winningSet KoalaBear.rsCodeSet (3 / 10) x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard

/-- **Winning-set attack upper bound (≈116 bits) at the GENUINE KoalaBear-sextic
carrier.** Same ceiling as `fenziSanso_upperBound_attack`, but over the real
field `F_{p^6}` and the genuine rate-`1/2` RS code, and conditional only on the
*coding-theory* residual `fenziSanso_upperBound_attack_concrete_residual` (a
cardinality bound on the attack winning set) — the field arithmetic
(`|F| = p^6`, `2^70/2^186 = 2^(-116)`) is fully discharged by
`winningSetSoundness_concrete_ge_of_card`. -/
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
bits-of-security of the concrete KoalaBear-sextic anchor is at most `116`. -/
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
KoalaBear-sextic anchor, then the true bits-of-security are at least `64`. -/
theorem koalaIRSConcrete_64_le_bitsOfSecurity
    (hLower : arklib_lowerBound_irs_t128_residual)
    (hpos : 0 < koalaIRSConcrete.soundnessError) :
    (64 : ℝ) ≤ bitsOfSecurity koalaIRSConcrete.soundnessError := by
  simpa [koalaIRSConcrete, arklib_lowerBound_irs_t128] using
    (arklib_lowerBound_irs_t128 hLower).le_bitsOfSecurity hpos

/-- Current concrete leaderboard window for the true KoalaBear-sextic
bits-of-security: the explicit 64-bit lower residual and concrete Fenzi-Sanso
attack residual place it in `[64, 116]`. -/
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
which is **DISPROVEN/NEEDS_CLASSICAL** (see
`winningSetSoundness_le_toySoundnessError` docstring) and is left as the owed
residual — *not* attempted here. -/

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
  simpa [koalaIRSConcrete] using spotCheck_le_two_pow_neg_64

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
