/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Logic.Basic

/-!
# One wall, two non-machine-linked faces — the honest open-core meta-capstone (issue #444)

The round-2 audit synthesis (DISPROOF_LOG `[adversarial-audit-round2-2026-06-20]`) and its
CORRECTION (`[audit-round2-CORRECTION-one-wall-two-faces]`, commit 7790f17ae) settled the honest
status of the prize campaign:

> The open core is **ONE WALL** exposed in **TWO formal faces** that are NOT linked by any in-tree
> theorem:
>   (i)  the **moment / energy face**  `SaddleEnergyBound` (char-`p` Lam–Leung transfer /
>        DC-subtracted `S_r ≤ (p−1)·E_r` = BGK Conj 1.12 at β=4), and
>   (ii) the **incidence face** `MCAShawConjecture` / `UniformBCHKSIncidence` (the `√q·B` line–ball
>        cancellation = BCHKS Conj 1.12).
> They are the same `√n`-vs-`√p` dispersion wall in two languages, but **no machine-checked bridge
> connects them**, so discharging one would not *formally* discharge the other. The prize needs ONE
> of the two faces proven.

This file makes that prose statement a **citable kernel-checked meta-theorem**, abstractly: a prize
bound `Prize` is reached from EITHER abstract sufficient input (`MomentFaceInput → Prize`,
`IncidenceFaceInput → Prize`), hence from their disjunction; and we record HONESTLY that the
abstraction does NOT and CANNOT supply a bridge — there exist models in which one face holds and the
other fails (so `MomentFaceInput → IncidenceFaceInput` is NOT a theorem of the abstraction, and vice
versa). No CORE / cancellation / completion / anti-concentration / capacity claim is made: neither
face is proved here. The content is the *logical architecture* of the open core, not its closure.

This is the Lane-2 "citable capstone" deliverable of the brief: real, certain, honest, and exactly
the corrected synthesis in machine-checked form.

Axioms must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx.
-/

namespace ArkLib.ProximityGap.Frontier.OneWallTwoFaces

/-- **The abstract two-face open core.** `Prize` is the target prize bound (left abstract: this file
makes no claim about WHEN it holds). `MomentFaceInput` is the moment/energy face open input (the
`SaddleEnergyBound` / DC-subtracted `S_r` statement), `IncidenceFaceInput` the incidence face open
input (`MCAShawConjecture` / BCHKS 1.12). The two `…Suffices` fields record the PROVEN-in-tree
sufficiency of each face for the prize (moment face: `prize_of_saddleEnergyBound`; incidence face:
`incidence_pinned_of_shawBound`). Crucially there is **no field linking the two faces** — that
absence is the honest content of "two non-machine-linked faces". -/
structure OpenCore where
  /-- The target prize bound (e.g. `M ≤ C·√(n log q)`). -/
  Prize : Prop
  /-- Open input of the moment/energy face (`SaddleEnergyBound`, BGK Conj 1.12 at β=4). -/
  MomentFaceInput : Prop
  /-- Open input of the incidence face (`MCAShawConjecture`, BCHKS Conj 1.12). -/
  IncidenceFaceInput : Prop
  /-- PROVEN in-tree: the moment face suffices for the prize (`prize_of_saddleEnergyBound`). -/
  momentSuffices : MomentFaceInput → Prize
  /-- PROVEN in-tree: incidence face suffices for the prize (`incidence_pinned_of_shawBound`). -/
  incidenceSuffices : IncidenceFaceInput → Prize

/-- **Either face discharges the prize.** Given the open core, a proof of EITHER face input yields
the prize. This is the exact corrected synthesis: "the prize needs ONE of the two faces proven." It
does NOT prove either face; it routes whichever is supplied to the (proven) prize. -/
theorem prize_of_either (C : OpenCore)
    (h : C.MomentFaceInput ∨ C.IncidenceFaceInput) : C.Prize :=
  h.elim C.momentSuffices C.incidenceSuffices

/-- **The prize unreached forces BOTH faces open (contrapositive of `prize_of_either`).** If the
prize is not derivable, then NEITHER face input can be available — otherwise `prize_of_either` would
route it to the prize. This is the precise "one wall, two faces" status: as long as the prize is
open, both the moment face AND the incidence face are individually open. (Honest scope: this is the
contrapositive of the sufficiency, NOT a no-fifth-door claim — it does not assert the two faces are
the ONLY routes, only that each, if closed, would close the prize.) -/
theorem both_faces_open_of_prize_unreached (C : OpenCore)
    (hp : ¬ C.Prize) :
    ¬ C.MomentFaceInput ∧ ¬ C.IncidenceFaceInput :=
  ⟨fun hm => hp (C.momentSuffices hm), fun hi => hp (C.incidenceSuffices hi)⟩

/-- **No bridge is supplied (honest non-claim, model-theoretic witness).** The abstraction does NOT
entail `MomentFaceInput → IncidenceFaceInput`: there is an `OpenCore` instance in which the moment
face holds, the incidence face fails, and the prize holds. Hence "discharging the moment face does
not formally discharge the incidence face" is a THEOREM about the abstraction, matching the audit's
"non-machine-linked". (Witness: `Prize := True`, `MomentFaceInput := True`,
`IncidenceFaceInput := False`; both sufficiency arrows are trivially inhabited.) -/
theorem no_moment_to_incidence_bridge :
    ∃ C : OpenCore, C.MomentFaceInput ∧ ¬ C.IncidenceFaceInput ∧ C.Prize :=
  ⟨{ Prize := True
     MomentFaceInput := True
     IncidenceFaceInput := False
     momentSuffices := fun _ => trivial
     incidenceSuffices := fun h => h.elim },
   trivial, id, trivial⟩

/-- Symmetric witness: the incidence face can hold while the moment face fails (and the prize
holds), so there is no reverse bridge `IncidenceFaceInput → MomentFaceInput` either. Together with
`no_moment_to_incidence_bridge` this certifies the two faces are LOGICALLY INDEPENDENT in the
abstraction — the precise meaning of "one wall in two non-machine-linked faces". -/
theorem no_incidence_to_moment_bridge :
    ∃ C : OpenCore, C.IncidenceFaceInput ∧ ¬ C.MomentFaceInput ∧ C.Prize :=
  ⟨{ Prize := True
     MomentFaceInput := False
     IncidenceFaceInput := True
     momentSuffices := fun h => h.elim
     incidenceSuffices := fun _ => trivial },
   trivial, id, trivial⟩

/-- **The sufficient faces are not necessary in the abstraction.** The open-core package records
two PROVEN sufficiency arrows into the prize, but it intentionally does NOT claim either input is
necessary. There is an `OpenCore` model in which the prize holds while both face inputs fail. This
formalizes the corrected audit scope: the capstone is a routing theorem for the two known faces, not
a hidden converse, no-fifth-door theorem, or proof that every prize proof must factor through one of
the two named inputs. -/
theorem no_prize_to_either_face_bridge :
    ∃ C : OpenCore, C.Prize ∧ ¬ C.MomentFaceInput ∧ ¬ C.IncidenceFaceInput :=
  ⟨{ Prize := True
     MomentFaceInput := False
     IncidenceFaceInput := False
     momentSuffices := fun h => h.elim
     incidenceSuffices := fun h => h.elim },
   trivial, id, id⟩

/-- **No biconditional is available from the two-face abstraction.** Even bundling the two known
open inputs by disjunction, the prize does not imply that either named face holds. Equivalently, the
abstract capstone gives `(MomentFaceInput ∨ IncidenceFaceInput) → Prize`, but not the reverse arrow.
This is the machine-checked guard against reading `prize_of_either` as an equivalence or as a
classification of all possible proofs. -/
theorem no_prize_to_face_disjunction_bridge :
    ∃ C : OpenCore, C.Prize ∧ ¬ (C.MomentFaceInput ∨ C.IncidenceFaceInput) :=
  let ⟨C, hp, hm, hi⟩ := no_prize_to_either_face_bridge
  ⟨C, hp, fun h => h.elim hm hi⟩

end ArkLib.ProximityGap.Frontier.OneWallTwoFaces

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.OneWallTwoFaces.prize_of_either
#print axioms ArkLib.ProximityGap.Frontier.OneWallTwoFaces.both_faces_open_of_prize_unreached
#print axioms ArkLib.ProximityGap.Frontier.OneWallTwoFaces.no_moment_to_incidence_bridge
#print axioms ArkLib.ProximityGap.Frontier.OneWallTwoFaces.no_incidence_to_moment_bridge
#print axioms ArkLib.ProximityGap.Frontier.OneWallTwoFaces.no_prize_to_either_face_bridge
#print axioms ArkLib.ProximityGap.Frontier.OneWallTwoFaces.no_prize_to_face_disjunction_bridge
