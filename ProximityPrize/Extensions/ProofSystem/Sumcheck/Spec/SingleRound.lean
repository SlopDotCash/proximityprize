/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.OracleReduction.Security.Basic
import ProximityPrize.Extensions.OracleReduction.Composition.Sequential.General
import ProximityPrize.Extensions.OracleReduction.LiftContext.OracleReduction
import ProximityPrize.Extensions.ProofSystem.Component.SendClaim
import ProximityPrize.Extensions.ProofSystem.Component.CheckClaim
import ProximityPrize.Extensions.ProofSystem.Component.RandomQuery
import ProximityPrize.Extensions.ProofSystem.Component.ReduceClaim
import ProximityPrize.Extensions.Data.Fin.Basic

/-!
# Single round of the Sum-check Protocol

We define a single round of the sum-check protocol as a two-message oracle reduction, and prove that
it is perfect complete and round-by-round knowledge sound. Specification & security proofs of the
full sum-check protocol are given in `Basic.lean`, following our sequential composition results.

## Protocol Description

The sum-check protocol is parameterized by the following:
- `R`: the underlying ring (for soundness, required to be finite and a domain)
- `n + 1 : ℕ+`: the number of variables (also number of rounds)
- `deg : ℕ`: the individual degree bound for the polynomial
- `D : Fin m ↪ R`: the set of `m` evaluation points for each variable (for some `m`), represented as
  an injection `Fin m ↪ R`. The image of `D` as a finite subset of `R` is written as
  `Finset.univ.map D`.
- `oSpec : OracleSpec ι`: the set of underlying oracles (e.g. random oracles) that may be needed for
  other reductions. However, the sum-check protocol does _not_ use any oracles.

The sum-check relation has no witness. The statement for the `i`-th round, where `i : Fin (n + 1)`,
 contains:
- `target : R`, which is the target value for sum-check
- `challenges : Fin i → R`, which is the list of challenges sent from the verifier to the prover in
  previous rounds

There is a single oracle statement, which is:
- `poly : MvPolynomial (Fin (n + 1)) R`, the multivariate polynomial that is summed over

The sum-check relation for the `i`-th round checks that:

  `∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨challenges, x⸩ = target`.

Note that the last statement (when `i = n`) is the output statement of the sum-check protocol.

For `i = 0, ..., n - 1`, the `i`-th round of the sum-check protocol consists of the following:

1. The prover sends a univariate polynomial `pᵢ ∈ R⦃≤ deg⦄[X]` of degree at most `deg`. If the
   prover is honest, then we have:

    `pᵢ(X) = ∑ x ∈ (univ.map D) ^ᶠ (n - i - 1), poly ⸨X ⦃i⦄, challenges, x⸩`.

  Here, `poly ⸨X ⦃i⦄, challenges, x⸩` is the polynomial `poly` evaluated at the concatenation of the
  prior challenges `challenges`, the `i`-th variable as the new indeterminate `X`, and the rest of
  the values `x ∈ (univ.map D) ^ᶠ (n - i - 1)`.

  In the oracle protocol, this polynomial `pᵢ` is turned into an oracle for which the verifier can
  query for evaluations at arbitrary points.

2. The verifier then sends the `i`-th challenge `rᵢ` sampled uniformly at random from `R`.

3. The (oracle) verifier then performs queries for the evaluations of `pᵢ` at all points in
   `(univ.map D)`, and checks that: `∑ x in (univ.map D), pᵢ.eval x = target`.

   If the check fails, then the verifier outputs `failure`.

   Otherwise, it outputs a statement for the next round as follows:
   - `target` is updated to `pᵢ.eval rᵢ`
   - `challenges` is updated to the concatenation of the previous challenges and `rᵢ`

## Simplification

We may break this down further into two one-message oracle reductions.

1. The first message from the prover to the verifier can be seen as invoking a ``virtual'' protocol
   as follows:

- `𝒫` holds some data `d` available as an oracle statement to `𝒱`, and wants to convince `𝒱` of
  some predicate `pred` on `d`, expressible as an oracle computation leveraging the oracle
  statement's query structure.
- `𝒫` sends `d'` to `𝒱` as an oracle message. `𝒱` directly checks `pred d'` by performing said
  oracle computation on `d'` and outputs the result.

2. The second message (a challenge) from the verifier to the prover can be seen as invoking a
   ``virtual'' protocol as follows:

- `𝒫` holds two data `d₁` and `d₂`, available as oracle statements, and wants to convince `𝒱` that
  `d₁ = d₂`.
- `𝒱` sends a random query `q` to `𝒫`. It then checks that `oracle d₁ q = oracle d₂ q = r`, and
  outputs `r` as the output statement.

The virtual aspect is because of the substitution: `d = d' = s_i(X)`, where recall
`s_i(X) = ∑ x ∈ D^{n - i - 1}, p(r_0, ..., r_{i-1}, X, x)`.

The predicate is that `∑ y ∈ D, s_i(y) = claim_i`.

-/


namespace Sumcheck

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

noncomputable section

namespace Spec

-- The variables for sum-check
variable (R : Type) [CommSemiring R] (n : ℕ) (deg : ℕ) {m : ℕ} (D : Fin m ↪ R)

namespace SingleRound

instance : IsSingleRound (pSpec R deg) where
  prover_first' := by aesop
  verifier_last' := by aesop

-- Don't know why instance synthesis requires restating these instances
-- Doesn't seem like instance synthesis can infer the instances for the appends
-- Note: may need to tweak synthesis?

/-- `simulateQ` of a query lifted from the middle summand of `spec₀ + (spec₁ + spec₂)`
is the implementation applied at the routed index. -/
private lemma simulateQ_double_lift_query {ι₀ ι₁ ι₂ : Type} {spec₀ : OracleSpec ι₀}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {m' : Type → Type} [Monad m']
    [LawfulMonad m'] (impl : QueryImpl (spec₀ + (spec₁ + spec₂)) m') (t : spec₁.Domain) :
    simulateQ impl
      (liftM (spec₁.query t) : OracleComp (spec₀ + (spec₁ + spec₂)) (spec₁.Range t)) =
      impl (Sum.inr (Sum.inl t)) := by
  change simulateQ impl (liftM ((spec₀ + (spec₁ + spec₂)).query (Sum.inr (Sum.inl t)))) = _
  rw [simulateQ_spec_query]

/-- `simulateQ` of a query lifted from the right summand of `spec₀ + (spec₁ + spec₂)`
is the implementation applied at the routed index. -/
private lemma simulateQ_double_right_lift_query {ι₀ ι₁ ι₂ : Type} {spec₀ : OracleSpec ι₀}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {m' : Type → Type} [Monad m']
    [LawfulMonad m'] (impl : QueryImpl (spec₀ + (spec₁ + spec₂)) m') (t : spec₂.Domain) :
    simulateQ impl
      (liftM (spec₂.query t) : OracleComp (spec₀ + (spec₁ + spec₂)) (spec₂.Range t)) =
      impl (Sum.inr (Sum.inr t)) := by
  change simulateQ impl (liftM ((spec₀ + (spec₁ + spec₂)).query (Sum.inr (Sum.inr t)))) = _
  rw [simulateQ_spec_query]

section VectorMapMTools

universe uM

/-- `Vector.mapM` over a pushed vector factors as mapM of the prefix, then the last element.
(Extracted from the proof of `Vector.support_mapM_index`.) -/
private lemma vector_mapM_push {m : Type → Type uM} [Monad m] [LawfulMonad m]
    {α β : Type} {L : ℕ} (xs : Vector β L) (x : β) (f : β → m α) :
    (xs.push x).mapM f =
      (xs.mapM f >>= (fun ys => f x >>= fun last => pure (ys.push last))) := by
  have hsingle : (#v[x]).mapM f = (fun last => #v[last]) <$> f x := by
    apply Vector.map_toArray_inj.mp
    simp
  rw [← Vector.append_singleton, Vector.mapM_append, hsingle]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
  rfl

/-- `Vector.mapM` on the empty vector is `pure`. -/
private lemma vector_mapM_empty {m : Type → Type uM} [Monad m] [LawfulMonad m]
    {α β : Type} (f : β → m α) :
    ((#v[] : Vector β 0).mapM f) = pure #v[] := by
  apply Vector.map_toArray_inj.mp
  simp

/-- `simulateQ` (into `OracleComp`) commutes with `Vector.mapM` of `OptionT` computations.
The `OptionT` ascriptions are load-bearing: without them `mapM` elaborates at the carrier. -/
private lemma simulateQ_optionT_vector_mapM {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} (impl : QueryImpl spec₁ (OracleComp spec₂))
    {α β : Type} {L : ℕ} (xs : Vector β L) (f : β → OptionT (OracleComp spec₁) α) :
    simulateQ impl (xs.mapM f : OptionT (OracleComp spec₁) (Vector α L)) =
      (xs.mapM (fun b => (simulateQ impl (f b) : OptionT (OracleComp spec₂) α)) :
        OptionT (OracleComp spec₂) (Vector α L)) := by
  induction L with
  | zero =>
    obtain rfl : xs = #v[] := by
      apply Vector.ext
      intro i h
      omega
    rw [vector_mapM_empty, vector_mapM_empty]
    erw [simulateQ_pure]
    rfl
  | succ L ih =>
    obtain ⟨xs0, x, rfl⟩ := Vector.exists_push (xs := xs)
    rw [vector_mapM_push, vector_mapM_push]
    rw [simulateQ_optionT_bind]
    rw [ih]
    refine bind_congr fun ys => ?_
    rw [simulateQ_optionT_bind]
    refine bind_congr fun last => ?_
    show simulateQ impl (pure (ys.push last) : OptionT (OracleComp spec₁) _)
      = (pure (ys.push last) : OptionT (OracleComp spec₂) _)
    erw [simulateQ_pure]
    rfl

/-- `Vector.mapM` of pure computations collapses to `pure` of the map. -/
private lemma vector_mapM_pure_comp {m : Type → Type uM} [Monad m] [LawfulMonad m]
    {α β : Type} {L : ℕ} (xs : Vector β L) (g : β → α) :
    xs.mapM (fun b => (pure (g b) : m α)) = pure (xs.map g) := by
  induction L with
  | zero =>
    obtain rfl : xs = #v[] := by
      apply Vector.ext
      intro i h
      omega
    rw [vector_mapM_empty]
    simp
  | succ L ih =>
    obtain ⟨xs0, x, rfl⟩ := Vector.exists_push (xs := xs)
    rw [vector_mapM_push, ih]
    simp

end VectorMapMTools

namespace Simpler

-- We further break it down into each message:
-- In order of (witness, oracle statement, public statement; relation):
-- (∅, p : R⦃≤ d⦄[X], old_claim : R; ∑ x ∈ univ.map D, p.eval x = old_claim) =>[Initial Context]
-- (∅, (p, q) : R⦃≤ d⦄[X] × R⦃≤ d⦄[X], old_claim : R;
--   ∑ x ∈ univ.map D, q.eval x = old_claim; p = q) =>[Send Claim] (note replaced `p` with `q`)
-- (∅, (p, q) : R⦃≤ d⦄[X] × R⦃≤ d⦄[X], old_claim : R; p = q) =>[Check Claim]
-- (∅, (p, q) : R⦃≤ d⦄[X] × R⦃≤ d⦄[X], ∅; p = q) =>[Reduce Claim]
-- (∅, (p, q) : R⦃≤ d⦄[X] × R⦃≤ d⦄[X], r : R; p.eval r = q.eval r) =>[Random Query]
-- (∅, p : R⦃≤ d⦄[X], new_claim : R; ∑ x ∈ univ.map D, p.eval x = new_claim) =>[Reduce Claim]

/-!
### Composing a single sum-check round from components

A single round of the sum-check protocol can be formally constructed by sequentially composing
several simpler, reusable oracle reductions defined in `ArkLib/ProofSystem/Component/`. This modular
construction simplifies the overall security proof, as we can prove security for each component and
then use a composition theorem.

The context for our single round is:
- **Public Statement**: `a: R` (the claimed sum).
- **Oracle Statement**: `p: R⦃≤ deg⦄[X]` (the claimed polynomial).
- **Initial Relation**: `∑_{x ∈ D} p.eval(x) = a`.

The protocol proceeds in four main steps, each corresponding to an oracle reduction:

1. **`SendClaim`**: The prover sends its claimed polynomial `q`.
   - **Action**: The prover, having oracle access to `p`, sends a polynomial `q` to the verifier. An
     honest prover sends `q = p`.
   - **Input Context**: `(Stmt: a, OStmt: p)` with relation `∑ p.eval = a`.
   - **Output Context**: `(Stmt: a, OStmt: (p, q))` with relation `(∑ p.eval = a) ∧ (p = q)`. The
     verifier now has oracle access to both the honest (`p`) and claimed (`q`) polynomials.

2. **`CheckClaim`**: The verifier checks if the sum of evaluations of `q` over `D` equals the
   target.
   - **Action**: The verifier queries `q` at all points in the domain `D`, computes the sum, and
     checks if it equals `a`. This is a non-interactive reduction (no messages exchanged).
   - **Input Context**: `(Stmt: a, OStmt: (p, q))` with relation `(∑ q.eval = a) ∧ (p = q)`. The
     predicate checked by `CheckClaim` is `∑ q.eval = a`.
   - **Output Context**: `(Stmt: a, OStmt: (p, q))` with the remaining relation `p = q`.

3. **`RandomQuery`**: The verifier sends a random challenge to reduce the polynomial identity check
   to a single point evaluation. This is the core of the Schwartz-Zippel lemma.
   - **Action**: The verifier samples a random challenge `r` from `R` and sends it to the prover.
   - **Input Context**: `(OStmt: (p, q))` with relation `p = q`.
   - **Output Context**: `(Stmt: r, OStmt: (p, q))` with relation `p.eval(r) = q.eval(r)`.

4. **`ReduceClaim`**: The claim is updated for the next round of sum-check.
   - **Action**: This is a non-interactive reduction to set up the context for the subsequent round.
     The new target is computed as `b := q.eval(r)`.
   - **Input Context**: `(Stmt: r, OStmt: (p, q))` with relation `p.eval(r) = q.eval(r)`.
   - **Output Context**:
     - `StmtOut`: `(b, r)` (to be part of the challenges for the next round).
     - `OStmtOut`: The new honest polynomial for the next round, which is conceptually the original
       multivariate polynomial with its first variable fixed to `r`.
     - `RelOut`: `p.eval(r) = b`. This is the starting relation for the next round.
-/

@[reducible, simp] def StmtIn : Type := R
@[reducible, simp] def OStmtIn : Unit → Type := fun _ => R⦃≤ deg⦄[X]

def inputRelation : Set (((StmtIn R) × (∀ i, OStmtIn R deg i)) × Unit) :=
  { ⟨⟨target, oStmt⟩, _⟩ | ∑ x ∈ (univ.map D), (oStmt ()).1.eval x = target }

@[reducible, simp] def StmtAfterSendClaim : Type := R
@[reducible, simp] def OStmtAfterSendClaim : Unit ⊕ Unit → Type := fun _ => R⦃≤ deg⦄[X]

def relationAfterSendClaim :
    Set (((StmtAfterSendClaim R) × (∀ i, OStmtAfterSendClaim R deg i)) × Unit) :=
  { ⟨⟨target, oStmt⟩, _⟩ |
    ∑ x ∈ (univ.map D), (oStmt (Sum.inl ())).1.eval x = target
      ∧ oStmt (Sum.inr ()) = oStmt (Sum.inl ()) }

@[reducible, simp] def StmtAfterCheckClaim : Type := R
@[reducible, simp] def OStmtAfterCheckClaim : Unit ⊕ Unit → Type := fun _ => R⦃≤ deg⦄[X]

def relationAfterCheckClaim :
    Set (((StmtAfterCheckClaim R) × (∀ i, OStmtAfterCheckClaim R deg i)) × Unit) :=
  { ⟨⟨_, oStmt⟩, _⟩ | oStmt (Sum.inr ()) = oStmt (Sum.inl ()) }

@[reducible, simp] def StmtAfterRandomQuery : Type := R
@[reducible, simp] def OStmtAfterRandomQuery : Unit ⊕ Unit → Type := fun _ => R⦃≤ deg⦄[X]

def relationAfterRandomQuery :
    Set (((StmtAfterRandomQuery R) × (∀ i, OStmtAfterRandomQuery R deg i)) × Unit) :=
  { ⟨⟨chal, oStmt⟩, _⟩ | (oStmt (Sum.inr ())).1.eval chal = (oStmt (Sum.inl ())).1.eval chal }

@[reducible, simp] def StmtOut : Type := R × R
@[reducible, simp] def OStmtOut : Unit → Type := fun _ => R⦃≤ deg⦄[X]

def outputRelation :
    Set (((StmtOut R) × (∀ i, OStmtOut R deg i)) × Unit) :=
  { ⟨⟨⟨newTarget, chal⟩, oStmt⟩, _⟩ | (oStmt ()).1.eval chal = newTarget }

variable {ι : Type} (oSpec : OracleSpec ι)

/-- The oracle prover for `sendClaim`. It reads the honest oracle polynomial `p` (index `()`), sends
it as the protocol message, and outputs the carried target together with both oracles `(p, q)`
(indexed by `Unit ⊕ Unit`, with `q` the just-sent message). Direct construction (mirrors
`SendClaim.oracleProver`, adapted to the carried-`R` statement). -/
def sendClaim.oracleProver : OracleProver oSpec
    (StmtIn R) (OStmtIn R deg) Unit
    (StmtAfterSendClaim R) (OStmtAfterSendClaim R deg) Unit ⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ where
  PrvState
  | 0 => StmtIn R × R⦃≤ deg⦄[X]
  | 1 => StmtIn R × R⦃≤ deg⦄[X]
  input := fun ⟨⟨target, oStmt⟩, _⟩ => (target, oStmt ())
  sendMessage | ⟨0, _⟩ => fun ⟨target, p⟩ => pure (p, (target, p))
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨target, p⟩ => pure
    ((target, fun x => match x with | .inl _ => p | .inr _ => p), ())

/-- The oracle verifier for `sendClaim`: it carries the input target `a` as the output statement and
performs no oracle checks. The output oracles are the input oracle `p` (index `inl ()`, `embed` to
`Sum.inl ()`) and the prover's message `q` (index `inr ()`, `embed` to `Sum.inr ⟨0, _⟩`). -/
def sendClaim.oracleVerifier : OracleVerifier oSpec
    (StmtIn R) (OStmtIn R deg)
    (StmtAfterSendClaim R) (OStmtAfterSendClaim R deg) ⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ where
  verify := fun target _ => pure target
  outputOracle := .inl {
    embed := {
      toFun := fun
        | .inl _ => .inl ()
        | .inr _ => .inr ⟨0, by simp⟩
      inj' := by
        intro a b h
        match a, b with
        | .inl _, .inl _ => rfl
        | .inl _, .inr _ => simp at h
        | .inr _, .inl _ => simp at h
        | .inr _, .inr _ => rfl }
    hEq := by
      intro i
      match i with
      | .inl _ => rfl
      | .inr _ => rfl
    outputInterface_heq := by
      intro i
      cases i <;> rfl }

def oracleReduction.sendClaim : OracleReduction oSpec (StmtIn R) (OStmtIn R deg) Unit
    (StmtAfterSendClaim R) (OStmtAfterSendClaim R deg) Unit ⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ :=
  {
    prover := {
      PrvState
      | 0 => StmtIn R × (∀ i, OStmtIn R deg i)
      | 1 => StmtIn R × (∀ i, OStmtIn R deg i) × R⦃≤ deg⦄[X]
      input := fun ctx => ctx.1
      sendMessage | ⟨0, _⟩ => fun ctx => pure (ctx.2 (), ctx.1, ctx.2, ctx.2 ())
      receiveChallenge | ⟨0, h⟩ => nomatch h
      output := fun (target, oStmt, sent) =>
        pure ((target, fun i => match i with
          | .inl () => oStmt ()
          | .inr () => sent), ())
    }
    verifier := sendClaim.oracleVerifier R deg oSpec
  }
  -- by
  -- refine SendClaim.oracleReduction oSpec (StmtIn R) (OStmtIn R deg) ?_
  -- (SendClaim.oracleReduction oSpec (StmtIn R) (OStmtIn R deg) Unit)

def oracleReduction.checkClaim : OracleReduction oSpec
    (StmtAfterSendClaim R) (OStmtAfterSendClaim R deg) Unit
    (StmtAfterCheckClaim R) (OStmtAfterCheckClaim R deg) Unit !p[] :=
  {
    prover := {
      PrvState | 0 => StmtAfterSendClaim R × (∀ i, OStmtAfterSendClaim R deg i)
      input := fun ctx => ctx.1
      sendMessage := fun i => nomatch i
      receiveChallenge := fun i => nomatch i
      output := fun ctx => pure (ctx, ())
    }
    verifier := {
      verify := fun target _ => by
        classical
        exact do
          let evals : Vector R m ← (Vector.finRange m).mapM
            (fun i => OptionT.lift <| OracleComp.liftComp
              (OracleComp.lift <|
                OracleSpec.query
                  (show [OStmtAfterSendClaim R deg]ₒ.Domain from ⟨.inr (), D i⟩))
              _)
          match Classical.decEq R evals.sum target with
          | isTrue _ => pure target
          | isFalse _ => OptionT.mk (pure none)
      outputOracle := .inl {
        embed := Function.Embedding.inl
        hEq := by intro i; rfl
        outputInterface_heq := by intro i; rfl }
    }
  }

def oracleReduction.randomQuery : OracleReduction oSpec
    (StmtAfterCheckClaim R) (OStmtAfterCheckClaim R deg) Unit
    (StmtAfterRandomQuery R) (OStmtAfterRandomQuery R deg) Unit ⟨!v[.V_to_P], !v[R]⟩ :=
  {
    prover := {
      PrvState
      | 0 => ∀ i, OStmtAfterCheckClaim R deg i
      | 1 => (∀ i, OStmtAfterCheckClaim R deg i) × R
      input := fun ctx => ctx.1.2
      sendMessage | ⟨0, h⟩ => nomatch h
      receiveChallenge | ⟨0, _⟩ => fun oStmt => pure fun r => (oStmt, r)
      output := fun (oStmt, r) => pure ((r, oStmt), ())
    }
    verifier := {
      verify := fun _ challenges => pure (challenges ⟨0, by simp⟩)
      outputOracle := .inl {
        embed := Function.Embedding.inl
        hEq := by intro i; rfl
        outputInterface_heq := by intro i; rfl }
    }
  }

def oracleReduction.reduceClaim : OracleReduction oSpec
    (StmtAfterRandomQuery R) (OStmtAfterRandomQuery R deg) Unit
    (StmtOut R) (OStmtOut R deg) Unit !p[] :=
  {
    prover := {
      PrvState := fun _ => (StmtAfterRandomQuery R ×
        (∀ i, OStmtAfterRandomQuery R deg i)) × Unit
      input := id
      sendMessage := fun i => nomatch i
      receiveChallenge := fun i => nomatch i
      output := fun ⟨⟨chal, oStmt⟩, _⟩ =>
        pure ((((oStmt (Sum.inr ())).1.eval chal, chal), fun _ => oStmt (Sum.inr ())), ())
    }
    verifier := {
      verify := fun chal _ => do
        let newTarget : R ← OptionT.lift <| OracleComp.liftComp
          (OracleComp.lift <|
            OracleSpec.query
              (show [OStmtAfterRandomQuery R deg]ₒ.Domain from ⟨.inr (), chal⟩))
          _
        pure (newTarget, chal)
      outputOracle := .inl {
        embed := ⟨fun _ => Sum.inl (Sum.inr ()), by intro _ _ _; rfl⟩
        hEq := by intro i; cases i; rfl
        outputInterface_heq := by intro i; cases i; rfl }
    }
  }

def oracleReduction : OracleReduction oSpec (StmtIn R) (OStmtIn R deg) Unit
    (StmtOut R) (OStmtOut R deg) Unit (pSpec R deg) :=
  ((oracleReduction.sendClaim R deg oSpec)
  |>.append (oracleReduction.checkClaim R deg D oSpec)
  |>.append (oracleReduction.randomQuery R deg oSpec)
  |>.append (oracleReduction.reduceClaim R deg oSpec))

end Simpler

namespace Simple

-- Let's try to simplify a single round of sum-check, and appeal to compositionality to lift
-- the result to the full protocol.

-- In this simplified setting, the sum-check protocol consists of a _univariate_ polynomial
-- `p : R⦃≤ d⦄[X]` of degree at most `d`, and the relation is that
-- `∑ x ∈ univ.map D, p.eval x = newTarget`.

variable {ι : Type} (oSpec : OracleSpec ι)

variable [DecidableEq R] [SampleableType R]

set_option maxHeartbeats 1000000 in
/-- The honest simple prover threads its input polynomial unchanged: any output statement in the
support of its run has output oracle statement equal to the input polynomial, and new target equal
to that polynomial evaluated at the sampled challenge. -/
private lemma prover_run_output (stmt : StmtIn R × (∀ i, OStmtIn R deg i))
    (out : (pSpec R deg).FullTranscript × (StmtOut R × ((i : Unit) → OStmtOut R deg i)) × Unit)
    (hout : out ∈ support ((prover R deg oSpec).run stmt ())) :
    out.2.1.2 () = stmt.2 () ∧
      out.2.1.1.1 = Polynomial.eval out.2.1.1.2 (stmt.2 ()).val := by
  simp only [prover, Prover.run, Prover.runToRound, Fin.induction_two, Prover.processRound,
    pSpec, bind_pure_comp] at hout
  -- Resolve round 0 direction (P_to_V): the match reduces to the P_to_V branch
  split at hout <;> rename_i hDir0
  · exact absurd hDir0 (by decide)
  -- Resolve round 1 direction (V_to_P)
  split at hout <;> rename_i hDir1
  swap
  · exact absurd hDir1 (by decide)
  -- Collapse all `pure`/`liftM`/`map` glue so only the challenge sampling remains a genuine bind
  simp only [liftM_pure, liftComp_pure, map_pure, pure_bind, bind_pure_comp,
    Functor.map_map, Function.comp_def, map_map] at hout
  -- Peel the outer bind: `out` is the (pure) prover output as a function of the round result
  -- `challenge`; `hchal` records that `challenge` arises from the two-round computation.
  rw [mem_support_bind_iff] at hout
  obtain ⟨challenge, hchal, hout⟩ := hout
  -- Round 1: `challenge = (concat sampled r0.1, r0.2, sampled)`, so `challenge.2.1 = stmt.2 ()`
  erw [support_map] at hchal
  rw [Set.mem_image] at hchal
  obtain ⟨c, _hc, rfl⟩ := hchal
  -- Resolve the outer pure to determine `out`
  erw [support_map] at hout
  rw [Set.mem_image] at hout
  obtain ⟨w, hw, rfl⟩ := hout
  simp only [liftM_pure, support_pure, Set.mem_singleton_iff] at hw
  subst hw
  exact ⟨rfl, rfl⟩

open Reduction
open scoped NNReal

-- instance : ∀ i, SampleableType (OracleInterface.Response (Challenge (pSpec R deg) i))
--   | ⟨1, _⟩ => by dsimp [pSpec, OracleInterface.Response]; infer_instance

-- instance : Nonempty []ₒ.QueryLog := by simp [QueryLog]; infer_instance
-- instance : Nonempty ((pSpec R deg).FullTranscript) := by
--   refine ⟨fun i => ?_⟩
--   rcases i with _ | _
--   · simp; exact default
--   · simp; exact default

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Closed form of the simulated oracle-verifier `verify`: the inner `simOracle2`
simulation collapses to a guard on the MESSAGE polynomial's `D`-sum followed by that polynomial's
evaluation at the challenge. -/
lemma simulateQ_oracleVerify_eq
    (target : StmtIn R) (oStmt : ∀ i, OStmtIn R deg i)
    (chal : ∀ i, (pSpec R deg).Challenge i)
    (msgs : ∀ i, (pSpec R deg).Message i) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      ((oracleVerifier R deg D oSpec).verify target chal) =
    (if ((Vector.finRange m).map (fun i => (msgs default).val.eval (D i))).sum = target
      then (pure ((msgs default).val.eval (chal default), chal default) :
        OptionT (OracleComp oSpec) (StmtOut R))
      else failure) := by
  have hcomp : ∀ x : R, (simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      (OptionT.lift ((OracleComp.lift (OracleSpec.query
        (spec := [(pSpec R deg).Message]ₒ) ⟨default, x⟩)).liftComp
        (oSpec + ([OStmtIn R deg]ₒ + [(pSpec R deg).Message]ₒ)))) :
      OptionT (OracleComp oSpec) R) = pure ((msgs default).val.eval x) := by
    intro x
    erw [simulateQ_optionT_lift]
    erw [OracleInterface.simulateQ_simOracle2_liftM_query_snd]
    rfl
  unfold oracleVerifier
  dsimp only
  rw [simulateQ_optionT_bind]
  rw [simulateQ_optionT_vector_mapM]
  have hfun : (fun b : Fin m => (simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
        ((OptionT.lift ((OracleComp.lift (OracleSpec.query
            (spec := [(pSpec R deg).Message]ₒ) ⟨default, D b⟩)).liftComp
          (oSpec + ([OStmtIn R deg]ₒ + [(pSpec R deg).Message]ₒ)))) :
            OptionT (OracleComp (oSpec + ([OStmtIn R deg]ₒ + [(pSpec R deg).Message]ₒ))) R) :
        OptionT (OracleComp oSpec) R))
      = (fun b : Fin m => (pure ((msgs default).val.eval (D b)) : OptionT (OracleComp oSpec) R)) :=
    by funext b; exact hcomp (D b)
  erw [hfun]
  rw [vector_mapM_pure_comp, pure_bind]
  by_cases hP : ((Vector.finRange m).map (fun i => (msgs default).val.eval (D i))).sum = target
  · simp only [guard, if_pos hP, pure_bind]
    rw [simulateQ_optionT_bind]
    erw [hcomp]
    erw [pure_bind]
    erw [simulateQ_pure]
    rfl
  · simp only [guard, if_neg hP]
    refine OptionT.ext ?_
    show simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
        (pure none : OracleComp (oSpec + ([OStmtIn R deg]ₒ + [(pSpec R deg).Message]ₒ))
          (Option (StmtOut R))) = _
    erw [simulateQ_pure]
    rfl

/-- Bridge: the vector `D`-evaluation sum equals the `Finset` sum over `univ.map D`. -/
lemma vector_finRange_map_sum_eq (g : Fin m → R) :
    ((Vector.finRange m).map g).sum = ∑ i : Fin m, g i := by
  rw [← Vector.sum_toList, Vector.toList_map, Fin.sum_univ_def]
  have h : (Vector.finRange m).toList = List.finRange m := by
    simp only [Vector.finRange, Array.finRange, Vector.toList_ofFn]
    exact List.ofFn_id m
  rw [h]

/-- Trivial round-by-round extractor (all witnesses are `Unit`). -/
def simpleRbrExtractor : Extractor.RoundByRound oSpec
    (StmtIn R × (∀ i, OStmtIn R deg i)) Unit Unit (pSpec R deg) (fun _ => Unit) where
  extractIn := fun _ _ => ()
  extractMid := fun _ _ _ _ => ()
  extractOut := fun _ _ _ => ()

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

end Simple

/-- Auxiliary lemma for proving that the polynomial sent by the honest prover is of degree at most
  `deg` -/
theorem sumcheck_roundPoly_degreeLE (i : Fin (n + 1)) {challenges : Fin i.castSucc → R}
    {poly : R[X Fin (n + 1)]} (hp : poly ∈ R⦃≤ deg⦄[X Fin (n + 1)]) :
      ∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨X ⦃i⦄, challenges, x⸩'
        (by simp; omega) ∈ R⦃≤ deg⦄[X] := by
  refine mem_degreeLE.mpr (le_trans (degree_sum_le ((univ.map D) ^ᶠ (n - i)) _) ?_)
  simp only [Finset.sup_le_iff, Fintype.mem_piFinset, mem_map, mem_univ, true_and]
  intro x hx
  refine le_trans (degree_map_le) (natDegree_le_iff_degree_le.mp ?_)
  rw [natDegree_finSuccEquivNth]
  exact degreeOf_le_iff.mpr fun m a ↦ hp a i

variable {ι : Type} (oSpec : OracleSpec ι) [DecidableEq R] [SampleableType R]

/-- The full `Fin n`-evaluation point that the virtual oracle-routing lens `simOStmt` uses to answer
an inner univariate evaluation query at `pt`, summing the outer multivariate polynomial over the
remaining coordinates.

We insert the queried point `pt` at coordinate `i` and fill the other `n - 1` coordinates with the
prior `challenges` (for the `j < i` slots) and the summation index `y` (for the rest). This mirrors
the `∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨X ⦃i⦄, challenges, x⸩` shape of `oStmtLens.toFunA`, so the
routing answers the inner univariate query exactly by the value `toFunA` would expose. -/
def sumPoint (i : Fin n) (pt : R) (stmtIn : StatementRound R n i.castSucc)
    (y : Fin (n - 1 - i) → R) : Fin n → R :=
  let h : n = n - 1 + 1 := by have := i.isLt; omega
  ((Fin.cast h i).insertNth pt
    (fun k => if hk : (k : ℕ) < (i : ℕ) then stmtIn.challenges ⟨k, by simpa using hk⟩
      else y ⟨(k : ℕ) - (i : ℕ), by have := k.isLt; omega⟩))
    ∘ Fin.cast h

/-- The concrete sum-check **oracle-routing lens** instantiating the new
`OracleStatement.OracleLens`
API (#433). The value layer reuses the existing value-level lens `oStmtLens` verbatim (so all the
soundness / completeness machinery still applies via `toLens`). The routing data is:

- `projStmt`/`liftStmt`: the non-oracle projection (drop to the round `target`) and lift (snoc the
new
  challenge onto the running challenge vector), matching `oStmtLens.toFunB`'s statement shape.
- `simOStmt`: answers each inner univariate evaluation query `⟨(), pt⟩` against the *outer*
  multivariate oracle by `∑ y ∈ (univ.map D) ^ᶠ (n - 1), outerPoly.eval (sumPoint i pt stmtIn y)` —
  the virtual `|D|^(n-1)`-fold summation, reading the prior `challenges` from the outer statement
  via
  `ReaderT`.
- `embedOStmt`/`hEqOStmt`: the single output oracle is the (unchanged) input oracle, so we draw it
  from the input side (`.inl`) with definitional type coherence. -/
noncomputable def sumcheckOracleLens (i : Fin n) :
    OracleStatement.OracleLens oSpec
      (StatementRound R n i.castSucc) (StatementRound R n i.succ)
      (Simple.StmtIn R) (Simple.StmtOut R)
      (OracleStatement R n deg) (OracleStatement R n deg)
      (Simple.OStmtIn R deg) (Simple.OStmtOut R deg)
      (pSpec R deg) where
  toLens := oStmtLens R n deg D i
  projStmt := fun stmtIn => stmtIn.target
  liftStmt := fun outerStmtIn innerStmtOut =>
    { target := innerStmtOut.1, challenges := Fin.snoc outerStmtIn.challenges innerStmtOut.2 }
  simOStmt := fun q =>
    match q with
    | ⟨(), pt⟩ => ReaderT.mk fun stmtIn =>
      (((univ.map D) ^ᶠ (n - 1 - i)).toList).foldlM
        (fun (acc : R) y => do
          let resp ← (OracleComp.lift <| OracleSpec.query
            (spec := [OracleStatement R n deg]ₒ)
            (show [OracleStatement R n deg]ₒ.Domain from ⟨(), sumPoint R n i pt stmtIn y⟩) :
            OracleComp (oSpec + [OracleStatement R n deg]ₒ) R)
          pure (acc + resp))
        (0 : R)
  embedOStmt := Function.Embedding.inl
  hEqOStmt := fun _ => rfl
  outputInterface_heq := fun _ => HEq.rfl

section Security

open Reduction
open scoped NNReal

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} (i : Fin n)

-- Showing that the lenses satisfy the completeness and rbr knowledge soundness conditions

/-- Keystone `Fin`-plumbing identity for the sum-check round split: inserting `a` at position `i`
into `append c y ∘ cast` agrees with appending the cons-extended tuple `cons a y` to `c`. -/
private lemma append_cons_eq_insertNth {n' : ℕ} {α : Type} (i : Fin (n' + 1)) (a : α)
    (c : Fin (i : ℕ) → α) (y : Fin (n' - i) → α)
    (hc1 : n' + 1 = (i : ℕ) + ((n' + 1) - i))
    (hc2 : n' = (i : ℕ) + (n' - i))
    (hc3 : (n' + 1) - (i : ℕ) = (n' - i) + 1) :
    (Fin.append c (Fin.cons a y ∘ Fin.cast hc3) ∘ Fin.cast hc1 : Fin (n' + 1) → α)
      = i.insertNth a (Fin.append c y ∘ Fin.cast hc2) := by
  rw [Fin.eq_insertNth_iff]
  refine ⟨?_, ?_⟩
  · simp only [Function.comp_apply]
    have : (Fin.cast hc1 i : Fin ((i : ℕ) + ((n' + 1) - i)))
        = Fin.natAdd (i : ℕ) ⟨0, by omega⟩ := by
      apply Fin.ext; simp
    rw [this, Fin.append_right]
    simp
  · ext j
    simp only [Fin.removeNth_apply, Function.comp_apply]
    rcases lt_or_ge (j : ℕ) (i : ℕ) with hlt | hge
    · have hsa : i.succAbove j = j.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def, hlt])
      rw [hsa]
      have hL : (Fin.cast hc1 j.castSucc : Fin ((i : ℕ) + ((n' + 1) - i)))
          = Fin.castAdd _ (⟨(j : ℕ), hlt⟩ : Fin (i : ℕ)) := by apply Fin.ext; simp
      have hR : (Fin.cast hc2 j : Fin ((i : ℕ) + (n' - i)))
          = Fin.castAdd _ (⟨(j : ℕ), hlt⟩ : Fin (i : ℕ)) := by apply Fin.ext; simp
      rw [hL, hR, Fin.append_left, Fin.append_left]
    · have hsa : i.succAbove j = j.succ :=
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def, hge])
      rw [hsa]
      have hL : (Fin.cast hc1 j.succ : Fin ((i : ℕ) + ((n' + 1) - i)))
          = Fin.natAdd (i : ℕ) (⟨(j : ℕ) - (i : ℕ) + 1, by omega⟩ : Fin ((n' + 1) - i)) := by
        apply Fin.ext; simp; omega
      have hR : (Fin.cast hc2 j : Fin ((i : ℕ) + (n' - i)))
          = Fin.natAdd (i : ℕ) (⟨(j : ℕ) - (i : ℕ), by omega⟩ : Fin (n' - i)) := by
        apply Fin.ext; simp; omega
      rw [hL, hR, Fin.append_right, Fin.append_right, Function.comp_apply]
      have : (Fin.cast hc3 ⟨(j : ℕ) - (i : ℕ) + 1, by omega⟩ : Fin ((n' - i) + 1))
          = Fin.succ (⟨(j : ℕ) - (i : ℕ), by omega⟩ : Fin (n' - i)) := by
        apply Fin.ext; simp
      rw [this, Fin.cons_succ]

/-- The sum-check round split: the `(n'+1-i)`-fold sum factors as a sum over the first coordinate
of a sum over the remaining `(n'-i)` coordinates, with the inserted-variable evaluation. -/
lemma sumcheck_round_split {n' : ℕ} {m' : ℕ} (D' : Fin m' ↪ R) (i : Fin (n' + 1))
    (c : Fin (i : ℕ) → R) (p : MvPolynomial (Fin (n' + 1)) R)
    (hc1 : n' + 1 = (i : ℕ) + ((n' + 1) - i))
    (hc2 : n' = (i : ℕ) + (n' - i))
    (hc3 : (n' + 1) - (i : ℕ) = (n' - i) + 1) :
    (∑ a : Fin m', ∑ y ∈ (univ.map D') ^ᶠ (n' - i),
        MvPolynomial.eval (i.insertNth (D' a) (Fin.append c y ∘ Fin.cast hc2)) p)
      = ∑ z ∈ (univ.map D') ^ᶠ ((n' + 1) - i),
          MvPolynomial.eval (Fin.append c z ∘ Fin.cast hc1) p := by
  rw [show (∑ a : Fin m', ∑ y ∈ (univ.map D') ^ᶠ (n' - i),
        MvPolynomial.eval (i.insertNth (D' a) (Fin.append c y ∘ Fin.cast hc2)) p)
      = ∑ a ∈ (univ.map D'), ∑ y ∈ (univ.map D') ^ᶠ (n' - i),
        MvPolynomial.eval (i.insertNth a (Fin.append c y ∘ Fin.cast hc2)) p from by
    rw [Finset.sum_map]]
  rw [← Finset.sum_product']
  refine Finset.sum_bij'
    (i := fun ay _ => (Fin.cons ay.1 ay.2 : Fin ((n' - i) + 1) → R) ∘ Fin.cast hc3)
    (j := fun z _ => (z (Fin.cast hc3.symm 0),
        fun k => z (Fin.cast hc3.symm k.succ)))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, y⟩ hay
    rw [Finset.mem_product] at hay
    simp only [Fintype.mem_piFinset] at hay ⊢
    intro k
    simp only [Function.comp_apply]
    rcases Fin.eq_zero_or_eq_succ (Fin.cast hc3 k) with hk | ⟨k'', hk⟩
    · rw [hk, Fin.cons_zero]; exact hay.1
    · rw [hk, Fin.cons_succ]; exact hay.2 k''
  · intro z hz
    simp only [Fintype.mem_piFinset] at hz
    rw [Finset.mem_product]
    exact ⟨hz _, by simp only [Fintype.mem_piFinset]; intro k; exact hz _⟩
  · rintro ⟨a, y⟩ hay
    simp only [Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.cons_zero, Fin.cons_succ]
  · intro z hz
    funext w
    simp only [Function.comp_apply]
    rcases Fin.eq_zero_or_eq_succ (Fin.cast hc3 w) with hk | ⟨w'', hk⟩
    · rw [hk, Fin.cons_zero]
      congr 1
      apply Fin.ext
      have hval : (Fin.cast hc3 w : Fin ((n' - i) + 1)).val = (0 : Fin ((n' - i) + 1)).val := by
        rw [hk]
      simp only [Fin.val_cast, Fin.val_zero] at hval ⊢
      omega
    · rw [hk, Fin.cons_succ]
      congr 1
      apply Fin.ext
      have hval : (Fin.cast hc3 w : Fin ((n' - i) + 1)).val = w''.succ.val := by rw [hk]
      simp only [Fin.val_cast, Fin.val_succ] at hval ⊢
      omega
  · rintro ⟨a, y⟩ hay
    rw [append_cons_eq_insertNth i a c y hc1 hc2 hc3]

/-- Lift-side round identity: the `(n'+1-(i+1))`-fold sum of the polynomial with the new
challenge `a` appended via `Fin.snoc` equals the round polynomial (partial evaluation leaving
variable `i` intact) evaluated at `a`. This is the completeness core of the round update. -/
private lemma sumcheck_round_eval_snoc {n' : ℕ} {m' : ℕ} (D' : Fin m' ↪ R) (i : Fin (n' + 1))
    (c : Fin (i : ℕ) → R) (a : R) (p : MvPolynomial (Fin (n' + 1)) R)
    (h₁ : n' + 1 = ((i : ℕ) + 1) + (n' + 1 - ((i : ℕ) + 1)))
    (h₂ : n' = (i : ℕ) + (n' - (i : ℕ))) :
    ∑ z ∈ (univ.map D') ^ᶠ (n' + 1 - ((i : ℕ) + 1)),
        MvPolynomial.eval (Fin.append (Fin.snoc c a) z ∘ Fin.cast h₁) p
      = Polynomial.eval a (∑ y ∈ (univ.map D') ^ᶠ (n' - (i : ℕ)),
          Polynomial.map (MvPolynomial.eval (Fin.append c y ∘ Fin.cast h₂))
            (MvPolynomial.finSuccEquivNth R i p)) := by
  have hidx : n' + 1 - ((i : ℕ) + 1) = n' - (i : ℕ) := by omega
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_nbij' (i := fun z => z ∘ Fin.cast hidx.symm)
    (j := fun y => y ∘ Fin.cast hidx) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Fintype.mem_piFinset] at hz ⊢
    exact fun k => hz _
  · intro y hy
    simp only [Fintype.mem_piFinset] at hy ⊢
    exact fun k => hy _
  · intro z _
    funext k
    exact congrArg z (Fin.ext rfl)
  · intro y _
    funext k
    exact congrArg y (Fin.ext rfl)
  · intro z _
    rw [← MvPolynomial.eval_eq_eval_mv_eval_finSuccEquivNth]
    refine congrArg (fun v => MvPolynomial.eval v p) ?_
    funext j
    by_cases hji : j = i
    · subst hji
      simp only [Function.comp_apply, Fin.insertNth_apply_same]
      have hcast : Fin.cast h₁ j
          = Fin.castAdd (n' + 1 - ((j : ℕ) + 1)) (Fin.last (j : ℕ)) := by
        apply Fin.ext; simp
      rw [hcast, Fin.append_left, Fin.snoc_last]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
      simp only [Function.comp_apply, Fin.insertNth_apply_succAbove]
      rcases le_or_gt i k.castSucc with hk | hk
      · rw [Fin.succAbove_of_le_castSucc _ _ hk]
        have hkv : (i : ℕ) ≤ (k : ℕ) := hk
        have hL : Fin.cast h₁ k.succ
            = Fin.natAdd ((i : ℕ) + 1)
                (⟨(k : ℕ) - (i : ℕ), by omega⟩ : Fin (n' + 1 - ((i : ℕ) + 1))) := by
          apply Fin.ext; simp; omega
        have hR : Fin.cast h₂ k
            = Fin.natAdd (i : ℕ)
                (⟨(k : ℕ) - (i : ℕ), by omega⟩ : Fin (n' - (i : ℕ))) := by
          apply Fin.ext; simp; omega
        rw [hL, Fin.append_right, hR, Fin.append_right]
        simp only [Function.comp_apply]
        congr 1
      · rw [Fin.succAbove_of_castSucc_lt _ _ hk]
        have hkv : (k : ℕ) < (i : ℕ) := hk
        have hL : Fin.cast h₁ k.castSucc
            = Fin.castAdd (n' + 1 - ((i : ℕ) + 1))
                (⟨(k : ℕ), by omega⟩ : Fin ((i : ℕ) + 1)) := by
          apply Fin.ext; simp
        have hR : Fin.cast h₂ k
            = Fin.castAdd (n' - (i : ℕ)) (⟨(k : ℕ), hkv⟩ : Fin (i : ℕ)) := by
          apply Fin.ext; simp
        rw [hL, Fin.append_left, hR, Fin.append_left]
        have hsnoc : (⟨(k : ℕ), by omega⟩ : Fin ((i : ℕ) + 1))
            = (⟨(k : ℕ), hkv⟩ : Fin (i : ℕ)).castSucc := by
          apply Fin.ext; simp
        rw [hsnoc, Fin.snoc_castSucc]



/-- Variant of `oCtxLens_complete` for the PLAIN `Simple.reduction`'s compatibility
relation (used by the lifted completeness without the false `oracleReduction_eq_reduction`). -/
instance oCtxLens_complete' :
    (oCtxLens R n deg D i).toContext.IsComplete
      (relationRound R n deg D i.castSucc) (Simple.inputRelation R deg D)
      (relationRound R n deg D i.succ) (Simple.outputRelation R deg)
      ((Simple.reduction R deg D oSpec).compatContext
        (oCtxLens R n deg D i).toContext)
where
  proj_complete := by
    rintro ⟨stmt, os⟩ ⟨⟩ h
    exact (oCtxLens_complete (R := R) (n := n) (deg := deg) (D := D)
      (oSpec := oSpec) (i := i)).proj_complete (stmt, os) () h
  lift_complete := by
    induction n with
    | zero => exact Fin.elim0 i
    | succ n' _ih =>
    rintro ⟨⟨target, challenges⟩, oStmt⟩ _ ⟨⟨newTarget, chal⟩, oStmt'⟩ _ hCompat hRelIn hRelOut'
    simp only [Simple.outputRelation, Set.mem_ofPred_eq] at hRelOut'
    -- From `hCompat`: the inner output context is the honest reduction's prover output.
    -- Plain-reduction compat variant: the prover is literally `Simple.prover`,
    -- and only the prover side is used below.
    rw [Reduction.compatContext] at hCompat
    simp only [Simple.reduction, Set.mem_image, Function.comp_apply] at hCompat
    obtain ⟨out, hout, heq⟩ := hCompat
    -- The reduction run's first component is the prover run; extract it.
    simp only [Reduction.run, OptionT.run_bind, Option.elimM] at hout
    rw [mem_support_bind_iff] at hout
    obtain ⟨proverResOpt, hprover, _hout⟩ := hout
    -- `out.1 = proverResOpt`, and `heq` pins `out.1.2`, so `proverResOpt.2.1 = ((newTarget, chal),
    -- oStmt')`
    have hout1 : out.1 = proverResOpt := by
      simp only [support_bind, Set.mem_iUnion] at _hout
      obtain ⟨_, _, _hout⟩ := _hout
      obtain ⟨_, _, _hout⟩ := _hout
      rw [support_pure, Set.mem_singleton_iff] at _hout
      exact congrArg Prod.fst _hout
    rw [hout1] at heq
    -- Characterize the prover output via `prover_run_output`.
    have hprover' : proverResOpt ∈
        support ((Simple.prover R deg oSpec).run
          (Statement.Lens.proj (oCtxLens R (n' + 1) deg D i).stmt
            ({ target := target, challenges := challenges }, oStmt)) ()) := by
      rw [OptionT.support_liftM] at hprover
      simpa using hprover
    have hpo := Simple.prover_run_output R deg oSpec _ proverResOpt hprover'
    -- `heq : proverResOpt.2 = (((newTarget, chal), oStmt'), innerWitOut)`
    obtain ⟨hpoO, hpoT⟩ := hpo
    rw [heq] at hpoO hpoT
    -- Now `hpoT : newTarget = eval chal roundPoly`; assemble the round update.
    dsimp only at hpoT ⊢
    dsimp only [Statement.Lens.proj, Statement.Lens.lift, OracleContext.Lens.toContext,
      oCtxLens, oStmtLens, Witness.Lens.trivial] at hpoT ⊢
    simp only [relationRound, Set.mem_ofPred_eq]
    rw [hpoT]
    exact sumcheck_round_eval_snoc D i challenges chal _ (by omega) (by omega)

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

local instance : Inhabited R := ⟨0⟩

-- /-- State function for round-by-round soundness. No need for this manual definition -/
-- def stateFunction (i : Fin (n + 1)) : Verifier.StateFunction pSpec oSpec
--     (relationRound R n deg D i.castSucc).language (relationRound R n deg D i.succ).language
--     (reduction R n deg D oSpec i).verifier where
--   toFun := fun m ⟨stmt, oStmt⟩ partialTranscript => match m with
--    -- If `m = 0` (e.g. the transcript is empty), returns whether
--     -- the statement satisfies the relation
--     | 0 => relationRound R n deg D i.castSucc ⟨stmt, oStmt⟩ ()
--     -- If `m = 1`, so the transcript contains the new polynomial `p_i`, returns the above check,
--     -- and also whether `p_i` is as expected
--     | 1 => relationRound R n deg D i.castSucc ⟨stmt, oStmt⟩ ()
--       ∧ (by simpa using partialTranscript ⟨0, by simp⟩ : R⦃≤ deg⦄[X]) =
--         ⟨∑ x ∈ (univ.map D) ^ᶠ (n - i), (oStmt 0).1 ⸨X ⦃i⦄, stmt.challenges, x⸩'(by simp; omega),
--           sumcheck_roundPoly_degreeLE R n deg D i (oStmt 0).2⟩
--     -- If `m = 2`, so we get the full transcript, returns the above checks, and also whether the
--     -- updated statement satisfies the new relation
--     | 2 => relationRound R n deg D i.succ ⟨⟨stmt.target,
--       by simpa using
--          Fin.snoc stmt.challenges (by simpa using partialTranscript ⟨1, by simp⟩ : R)⟩,
--        oStmt⟩ ()
--   toFun_empty := fun stmt hStmt => by simp_all [Function.language]
--   toFun_next := fun m hDir => match m with
--     | 0 => fun stmt tr hFalse => by simp_all
--     | 1 => nomatch hDir
--   toFun_full := fun stmt tr hFalse => by
--     simp_all [Function.language]
--     -- intro stmt' oStmt log h ()
--     -- simp [Verifier.run] at h
--     -- have h' : ⟨stmt', oStmt⟩ ∈ Prod.fst ''
--     --   (simulate loggingOracle ∅ ((verifier R n deg D oSpec i).verify stmt tr)).support := by
--     --   simp [h]; exact ⟨log, h⟩
--     -- contrapose! h'
--     -- rw [← OracleComp.support_map]
--     -- simp [verifier]
-- /-- Trivial extractor since witness is `Unit` -/
-- def rbrExtractor : Extractor.RoundByRound (pSpec R deg) oSpec (Statement R n i.castSucc) Unit :=
--   fun _ _ _ _ => ()

end Security

namespace Unfolded

-- The rest of the below are for equivalence checking. We have deduced the construction & security
-- of the single round protocol from its simplified version via context lifting.

end Unfolded

end SingleRound

end Spec

-- end for noncomputable section
end

end Sumcheck

#print axioms Sumcheck.Spec.SingleRound.Simple.simulateQ_oracleVerify_eq
#print axioms Sumcheck.Spec.SingleRound.oCtxLens_complete'
#print axioms Sumcheck.Spec.SingleRound.Simpler.sendClaim.oracleVerifier
