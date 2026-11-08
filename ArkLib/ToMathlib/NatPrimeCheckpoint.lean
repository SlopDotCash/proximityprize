/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Pow

/-!
# Kernel-checked primality certificates with bounded expression depth

`prime_checkpoint` uses Mathlib's `MinFacHelper` certificate steps, storing a proved
checkpoint every 128 steps. This avoids the deeply nested expressions produced by
`norm_num` for primes larger than 25 bits. Every checkpoint is checked by the kernel;
the tactic adds no axioms and does not use `native_decide`. The certificate constructors
come from Mathlib's `NormNum.Prime`; this module adds the checkpoint boundary.
-/

namespace ArkLib

open Lean Meta Elab Tactic Qq
open Mathlib.Meta.NormNum

meta section

private partial def checkpointMinFac (nn : Q(ℕ)) (n : ℕ) (ek : Q(ℕ))
    (progress : Q(MinFacHelper $nn $ek)) (steps : ℕ) :
    MetaM Q(IsNat (Nat.minFac $nn) $nn) := do
  let k := ek.natLit!
  if n < k * k then
    let tooLarge : Q(Nat.ble ($ek * $ek) $nn = false) := (q(Eq.refl false) : Expr)
    let self : Q(IsNat $nn $nn) := q(.raw_refl _)
    return q(isNat_minFac_4 $self $progress $tooLarge)
  have next : Q(ℕ) := mkRawNatLit (k + 2)
  let nextEq : Q($ek + 2 = $next) := (q(Eq.refl $next) : Expr)
  let factor := k.minFac
  let nextProof : Q(MinFacHelper $nn $next) ←
    if factor < k then
      let composite : Q(¬ Nat.Prime $ek) := deriveNotPrime k factor ek
      pure q(minFacHelper_2 $nextEq $composite $progress)
    else
      if n % k = 0 then
        throwError "prime_checkpoint: the candidate has factor {k}"
      let nonzero : Q(Nat.beq ($nn % $ek) 0 = false) := (q(Eq.refl false) : Expr)
      pure q(minFacHelper_3 $nextEq $nonzero $progress)
  let nextProof : Q(MinFacHelper $nn $next) ←
    if steps % 128 = 127 then
      mkAuxTheorem q(MinFacHelper $nn $next) nextProof
    else pure nextProof
  checkpointMinFac nn n next nextProof (steps + 1)

/-- Prove a closed natural-number primality goal using certified, shallow checkpoints. -/
elab "prime_checkpoint" : tactic => do
  let goal ← getMainGoal
  let proof ← goal.withContext do
    let .app (.const ``Nat.Prime _) (candidate : Q(ℕ)) ← whnfR (← goal.getType)
      | throwError "prime_checkpoint: expected a Nat.Prime goal"
    let ⟨nn, value⟩ ← deriveNat candidate q(Nat.instAddMonoidWithOne)
    let n := nn.natLit!
    if n < 2 || n.minFac != n then
      throwError "prime_checkpoint: {n} is not prime"
    let atLeastTwo : Q(Nat.ble 2 $nn = true) := (q(Eq.refl true) : Expr)
    if n = 2 then
      let factor : Q(IsNat (Nat.minFac $nn) $nn) :=
        (q(IsNat.raw_refl (Nat.minFac $nn)) : Expr)
      return q(isNat_prime_2 $value $atLeastTwo $factor)
    let odd : Q(nat_lit 1 = $nn % nat_lit 2) := (q(Eq.refl (nat_lit 1)) : Expr)
    let progress : Q(MinFacHelper $nn (nat_lit 3)) := q(minFacHelper_0 $nn $atLeastTwo $odd)
    let factor ← checkpointMinFac nn n q(nat_lit 3) progress 0
    return q(isNat_prime_2 $value $atLeastTwo $factor)
  goal.assign proof
  replaceMainGoal []

end

end ArkLib
