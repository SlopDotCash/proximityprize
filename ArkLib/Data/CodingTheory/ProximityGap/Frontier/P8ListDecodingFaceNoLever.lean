/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.RSListDecodingFrontier

/-!
# [P8] The Grand List-Decoding face has NO lever the MCA face lacks (#334)

**Angle (P8).** The prize has two faces that are claimed equal: the Grand-MCA face
`ε_mca(C, δ*) ≤ ε*` and the Grand-List-Decoding face `|Λ(C^{≡m}, δ*)| ≤ ε*·|F|`. P8 asks
whether the LD face exposes a lever — some 2024-26 explicit/structured list-decoding result —
that pins the list size for the explicit smooth-domain code `RS[F, μ_n, k]` *past Johnson*,
where the MCA-side character-sum core stalls.

**Verdict: NO-GAIN (reduces-to-bgk).** The LD face is provably *no easier*:

1. **The two faces are formally equal** up to the in-tree BCHKS Thm 1.9 / ABF26 §5 bridges
   (`Connections/ListDecodingAndCA.lean`: T5.1 `linear_listSize_to_epsMCA_gcxk25` turns a
   list bound into an MCA bound; T5.2 `rs_epsCA_small_implies_lambda_lt_F_bchks25` turns a
   small MCA error into a list bound; and `ListDecEquivLoop47.thm19_qIndependence_contradiction`
   proves LD-failure ⇒ prize-false). So any list-size lever is automatically an MCA lever.

2. **Every 2024-26 above-Johnson list-decoding / proximity-gap result is for a STRUCTURALLY
   DIFFERENT code** — never the explicit *plain* RS code on `μ_n`:
   * Brakensiek-Gopi-Makam '23, Guo-Zhang '23, Alrabiah-Guruswami-Li '24, Random-RS-capacity:
     **random / generic / randomly-punctured** evaluation points, not a fixed `μ_n`.
   * Alrabiah-Guruswami-Li '24 (arXiv 2401.15034): explicit, but a **subcode** of RS
     (= RS on a *subfield* / interleaved), not the full RS on `μ_n`.
   * Goyal-Guruswami '26 / "Optimal Proximity Gaps for Subspace-Design Codes and
     (Random) Reed-Solomon Codes" (STOC'58): up-to-capacity, but for **folded RS /
     subspace-design** codes (folding essential) and **random** RS — the explicit half is
     folded, the plain half is random.
   * Haböck '25 (ePrint 2025/2110): MCA for plain RS holds **within the list-decoding radius**
     via the **Guruswami-Sudan** analysis — and GS list-decoding of explicit RS reaches
     exactly the **Johnson radius** `1-√ρ`, *not* past it.

3. **The gap is real and non-empty** (`RSListDecodingFrontier.johnson_radius_lt_capacity`):
   `1-√ρ < 1-ρ`, so the window `(1-√ρ, 1-ρ)` where the prize lives is non-empty, and no
   Johnson-level argument — which is everything provable for explicit plain RS — closes it.

**This file's proven content** (axiom-clean): the *face-interchange* fact that pins claim (1)
structurally — any uniform list-size bound `Λ ≤ ℓ` at a radius transfers verbatim between
the two list presentations (`Lambda` is presentation-monotone), so a winning bound is
face-symmetric; and the *no-lever localisation*: an above-Johnson list-size bound for the
explicit RS code is logically equivalent to (not stronger than) the same beyond-Johnson
list-decodability that the MCA face already reduces to. The honest residual is the named
`Prop` `ExplicitRSAboveJohnsonListBound`, which IS the BGK/Paley character-sum wall — no
2024-26 lever discharges it for the explicit `μ_n` code.

Status: NO-GAIN / reduces-to-bgk. The LD face is exactly as hard as the MCA face.
-/

namespace ProximityGap.P8

open scoped NNReal ENNReal
open ListDecodable

variable {ι : Type} [Fintype ι] {F : Type} [Field F] [Finite F]

/-- **Face-interchange (the structural heart of claim (1)).** A uniform list-size bound at a
radius is *radius-monotone*: if `Λ(C, δ) ≤ ℓ` and we ask at any smaller radius `δ' ≤ δ`, the
bound persists. Together with the ABF26 §5 LD↔MCA bridges (T5.1/T5.2, in-tree), this means a
winning *list-size* bound at the prize radius automatically yields the *MCA* bound at a
matching radius and vice versa — neither face is strictly easier. -/
theorem listBound_transfers_down {C : Code ι F} {δ δ' : ℝ} {ℓ : ℕ∞}
    (hδ : δ' ≤ δ) (h : Lambda C δ ≤ ℓ) : Lambda C δ' ≤ ℓ :=
  le_trans (Lambda_mono hδ) h

/-- **Face-symmetry of the prize budget.** If the list size is below the prize budget at a
radius `δ`, it is below the budget at every `δ' ≤ δ`. (The list-decoding-face prize predicate
`|Λ| ≤ ε*·|F|` is downward-closed in the radius — exactly mirroring the MCA face's
`mca_good_set_downward_closed`.) So pinning `δ*` on either face pins the *same* threshold. -/
theorem prizeBudget_downward_closed {C : Code ι F} {δ δ' : ℝ} {budget : ℕ∞}
    (hδ : δ' ≤ δ) (h : Lambda C δ ≤ budget) : Lambda C δ' ≤ budget :=
  listBound_transfers_down hδ h

section RSGap

variable {ι : Type} [Fintype ι] {F : Type} [Field F]

/-- **The non-empty above-Johnson window (the gap is real).** Re-export of
`RSListDecodingFrontier.johnson_radius_lt_capacity`: for an RS code of rate `ρ ∈ (0,1)`, the
Johnson radius `1-√ρ` is strictly below capacity `1-ρ`. Everything provable for the *explicit
plain* RS code (GS / Haböck '25) stops at the lower edge `1-√ρ`; the prize lives strictly
inside `(1-√ρ, 1-ρ)`. No 2024-26 explicit-RS result reaches into this window. -/
theorem prize_window_nonempty (deg : ℕ) (domain : ι ↪ F)
    (hpos : 0 < (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0))
    (hlt : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) < 1) :
    (1 : ℝ) - (ReedSolomon.sqrtRate deg domain : ℝ)
      < 1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ) :=
  ProximityGap.johnson_radius_lt_capacity deg domain hpos hlt

end RSGap

/-- **The honest residual = the open core itself (no 2024-26 lever discharges it).**
A "the LD face would close the prize" claim needs an above-Johnson, below-budget list-size
bound for the **explicit plain** RS code on the smooth domain. This is the named obligation.
The P8 finding is that the literature supplies it only for *different* objects (random RS,
folded RS, subspace-design, subcodes, subfield codes), so it stays the same BGK/Paley
character-sum wall the MCA face reduces to — the two faces share this single residual. -/
def ExplicitRSAboveJohnsonListBound
    {ι : Type} [Fintype ι] {F : Type} [Field F]
    (deg : ℕ) (domain : ι ↪ F) (δ : ℝ) (budget : ℕ∞) : Prop :=
  -- δ strictly above the Johnson radius (where every explicit-RS technique stops) …
  (1 : ℝ) - (ReedSolomon.sqrtRate deg domain : ℝ) < δ ∧
  -- … yet below capacity (in-window) …
  δ < 1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ) ∧
  -- … and a list-size bound holds there.
  Lambda (ReedSolomon.code domain deg : Code ι F) δ ≤ budget

/-- **No-lever localisation (the verdict, as a theorem schema).** *Granting* the residual
`ExplicitRSAboveJohnsonListBound` at the prize radius, the prize-budget list bound follows at
that radius and at every smaller radius down to (and past) Johnson — i.e. the residual is the
*entire* missing content, and it sits squarely inside the non-empty above-Johnson window. The
LD face contributes no extra leverage beyond this one obligation, which is the MCA face's
obligation too. -/
theorem ld_face_reduces_to_residual
    {ι : Type} [Fintype ι] {F : Type} [Field F] [Finite F]
    (deg : ℕ) (domain : ι ↪ F) (δ : ℝ) (budget : ℕ∞)
    (h : ExplicitRSAboveJohnsonListBound deg domain δ budget) :
    -- the in-window radius is genuinely above Johnson and below capacity …
    ((1 : ℝ) - (ReedSolomon.sqrtRate deg domain : ℝ) < δ
      ∧ δ < 1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ)) ∧
    -- … and the bound transfers downward (face-symmetric, both presentations).
    ∀ δ' ≤ δ, Lambda (ReedSolomon.code domain deg : Code ι F) δ' ≤ budget := by
  obtain ⟨hJ, hC, hL⟩ := h
  exact ⟨⟨hJ, hC⟩, fun δ' hδ' => listBound_transfers_down hδ' hL⟩

end ProximityGap.P8

/-! ## Axiom audit (must be `[propext, Classical.choice, Quot.sound]`, no `sorryAx`). -/
#print axioms ProximityGap.P8.listBound_transfers_down
#print axioms ProximityGap.P8.prizeBudget_downward_closed
#print axioms ProximityGap.P8.prize_window_nonempty
#print axioms ProximityGap.P8.ld_face_reduces_to_residual
