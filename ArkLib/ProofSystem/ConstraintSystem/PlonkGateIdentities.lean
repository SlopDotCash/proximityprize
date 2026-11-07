/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.ConstraintSystem.Plonk

/-!
# Scalar-form Plonk gate identities

This file restates the Plonk gate specialization identities in a *scalar* form, where the gate
selectors `(qL, qR, qO, qM, qC)` and the wire values `(a, b, c)` are given directly as ring
elements rather than through a wire-index assignment.

It does **not** introduce an independent gate model. The scalar gate evaluation `gateEval` is
defined as the canonical `Plonk.Gate.eval` of a three-wire gate (`Plonk.Gate 𝓡 3` with wire
indices `0, 1, 2`) on the assignment `![a, b, c]`, and `gateAccepts` is `Plonk.Gate.accepts`
of that same gate. The specialization identities below are derived from the canonical
`Plonk.Gate.add_accepts_iff`, `mul_accepts_iff`, `bool_accepts_iff`,
`bool_accepts_iff_of_domain`, and `eq_accepts` lemmas, so they cannot drift from the production
gate API.

## Scope

These are algebraic facts about a single gate (and, in `constraintSystem_accepts_iff`, about the
definitional unfolding of `Plonk.ConstraintSystem.accepts`). They say nothing about any Plonk
protocol: no polynomial IOP, Schwartz-Zippel soundness, succinctness, or zero knowledge is
formalized or claimed here.
-/

@[expose] public section

namespace ArkLib.ProofSystem.ConstraintSystem.PlonkGateIdentities

open Plonk

section Gate

variable {𝓡 : Type} [CommRing 𝓡]

/-- The canonical three-wire Plonk gate with the given selectors, reading its left, right, and
output wires from indices `0`, `1`, and `2`. -/
def scalarGate (qL qR qO qM qC : 𝓡) : Gate 𝓡 3 :=
  { qL := qL, qR := qR, qO := qO, qM := qM, qC := qC, a := 0, b := 1, c := 2 }

/-- The three-wire assignment `![a, b, c]`. -/
def wires (a b c : 𝓡) : Fin 3 → 𝓡 := ![a, b, c]

/-- Scalar gate evaluation, defined as the canonical `Plonk.Gate.eval` of `scalarGate` on
`wires a b c`. -/
def gateEval (qL qR qO qM qC a b c : 𝓡) : 𝓡 :=
  (scalarGate qL qR qO qM qC).eval (wires a b c)

/-- Scalar gate acceptance, defined as the canonical `Plonk.Gate.accepts`. -/
def gateAccepts (qL qR qO qM qC a b c : 𝓡) : Prop :=
  (scalarGate qL qR qO qM qC).accepts (wires a b c)

/-- The scalar evaluation is the gate polynomial `qL·a + qR·b + qO·c + qM·(a·b) + qC`. -/
theorem gateEval_eq (qL qR qO qM qC a b c : 𝓡) :
    gateEval qL qR qO qM qC a b c = qL * a + qR * b + qO * c + qM * (a * b) + qC := by
  simp [gateEval, scalarGate, wires, Gate.eval]

/-- Scalar acceptance is vanishing of the scalar evaluation. -/
theorem gateAccepts_iff (qL qR qO qM qC a b c : 𝓡) :
    gateAccepts qL qR qO qM qC a b c ↔ gateEval qL qR qO qM qC a b c = 0 :=
  Iff.rfl

/-- Acceptance of the scalar gate only depends on the gate polynomial: any canonical gate with
the same selectors, evaluated on an assignment whose wires read `a, b, c`, accepts iff the scalar
gate does. -/
theorem gateAccepts_iff_accepts {n : ℕ} (g : Gate 𝓡 n) (x : Fin n → 𝓡) :
    gateAccepts g.qL g.qR g.qO g.qM g.qC (x g.a) (x g.b) (x g.c) ↔ g.accepts x := by
  rw [gateAccepts_iff, gateEval_eq]
  rfl

/-- **Addition gate identity**, from `Plonk.Gate.add_accepts_iff`. -/
theorem add_gate_iff (a b c : 𝓡) :
    gateAccepts (1 : 𝓡) 1 (-1) 0 0 a b c ↔ c = a + b := by
  refine (gateAccepts_iff_accepts (Gate.add (0 : Fin 3) 1 2) (wires a b c)).trans ?_
  rw [Gate.add_accepts_iff]
  simp [wires]

/-- **Multiplication gate identity**, from `Plonk.Gate.mul_accepts_iff`. -/
theorem mul_gate_iff (a b c : 𝓡) :
    gateAccepts (0 : 𝓡) 0 (-1) 1 0 a b c ↔ c = a * b := by
  refine (gateAccepts_iff_accepts (Gate.mul (0 : Fin 3) 1 2) (wires a b c)).trans ?_
  rw [Gate.mul_accepts_iff]
  simp [wires]

/-- **Booleanity gate identity**, from `Plonk.Gate.bool_accepts_iff`. -/
theorem bool_gate_iff (j : 𝓡) :
    gateAccepts (-1 : 𝓡) 0 0 1 0 j j j ↔ j * (j - 1) = 0 := by
  have h := Gate.bool_accepts_iff (𝓡 := 𝓡) (j := (0 : Fin 1)) (x := fun _ => j)
  rw [← h]
  exact gateAccepts_iff_accepts (Gate.bool (0 : Fin 1)) (fun _ => j)

/-- Over an integral domain, booleanity forces `j ∈ {0, 1}`; from
`Plonk.Gate.bool_accepts_iff_of_domain`. -/
theorem bool_gate_iff_domain [IsDomain 𝓡] (j : 𝓡) :
    gateAccepts (-1 : 𝓡) 0 0 1 0 j j j ↔ j = 0 ∨ j = 1 := by
  have h := Gate.bool_accepts_iff_of_domain (𝓡 := 𝓡) (j := (0 : Fin 1)) (x := fun _ => j)
  rw [← h]
  exact gateAccepts_iff_accepts (Gate.bool (0 : Fin 1)) (fun _ => j)

/-- **Equality gate identity**, from `Plonk.Gate.eq_accepts`. -/
theorem eq_gate_iff (i k : 𝓡) :
    gateAccepts (1 : 𝓡) 0 0 0 (-k) i i i ↔ i = k := by
  rw [← Gate.eq_accepts (0 : Fin 1) k (fun _ => i)]
  exact gateAccepts_iff_accepts (Gate.eq (0 : Fin 1) k) (fun _ => i)

/-- A canonical constraint system accepts an assignment iff every gate polynomial vanishes at
it. This is only the definitional unfolding of `Plonk.ConstraintSystem.accepts`; it is not a
protocol soundness statement. -/
theorem constraintSystem_accepts_iff {numWires numGates : ℕ}
    (cs : ConstraintSystem 𝓡 numWires numGates) (x : Fin numWires → 𝓡) :
    cs.accepts x ↔ ∀ i, (cs i).eval x = 0 :=
  Iff.rfl

end Gate

end ArkLib.ProofSystem.ConstraintSystem.PlonkGateIdentities
