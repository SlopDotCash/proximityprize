/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.LiftContext.OracleReduction
import ArkLib.ProofSystem.Component.SendClaim
import ArkLib.ProofSystem.Component.CheckClaim
import ArkLib.ProofSystem.Component.RandomQuery
import ArkLib.ProofSystem.Component.ReduceClaim
import ArkLib.Data.Fin.Basic

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

set_option linter.style.longFile 2100

namespace Sumcheck

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

noncomputable section

namespace Spec

-- The variables for sum-check
variable (R : Type) [CommSemiring R] (n : ℕ) (deg : ℕ) {m : ℕ} (D : Fin m ↪ R)

/-- The input statement for sum-check, which just consists of the target value for the sum -/
def InputStatement := R

/-- Statement for sum-check, parameterized by the ring `R`, the number of variables `n`,
and the round index `i : Fin (n + 1)`

Note that when `i = Fin.last n`, this is the output statement of the sum-check protocol.
When `i = 0`, this has the (redundant) empty challenge vector.
See `InputStatement` for the non-redundant version. -/
structure StatementRound (i : Fin (n + 1)) where
  -- The target value for sum-check
  target : R
  -- The challenges sent from the verifier to the prover from previous rounds
  challenges : Fin i → R

abbrev OutputStatement := StatementRound R _ (.last n)

/-- Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of
  individual degree at most `deg`, equipped with the poly evaluation oracle interface. -/
@[reducible]
def OracleStatement : Unit → Type := fun _ => R⦃≤ deg⦄[X Fin n]

/-- The sum-check relation for the `i`-th round, for `i ≤ n` -/
def relationRound (i : Fin (n + 1)) :
    Set (((StatementRound R n i) × (∀ i, OracleStatement R n deg i)) × Unit) :=
  { ⟨⟨⟨target, challenges⟩, polyOracle⟩, _⟩ |
    ∑ x ∈ (univ.map D) ^ᶠ (n - i), (polyOracle ()).val ⸨challenges, x⸩ = target }

namespace SingleRound

/-- The protocol specification for a single round of sum-check.
Has the form `⟨!v[.P_to_V, .V_to_P], !v[R⦃≤ deg⦄[X], R]⟩` -/
@[reducible]
def pSpec : ProtocolSpec 2 :=
  ⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ ++ₚ !p[] ++ₚ ⟨!v[.V_to_P], !v[R]⟩ ++ₚ !p[]

instance : IsSingleRound (pSpec R deg) where
  prover_first' := by aesop
  verifier_last' := by aesop

-- Don't know why instance synthesis requires restating these instances
-- Doesn't seem like instance synthesis can infer the instances for the appends
-- Note: may need to tweak synthesis?

instance instOI₁ : ∀ i, OracleInterface ((⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ ++ₚ !p[]).Message i) :=
  instOracleInterfaceMessageAppend

instance instOI₂ : ∀ i, OracleInterface
    ((⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ ++ₚ !p[] ++ₚ ⟨!v[.V_to_P], !v[R]⟩).Message i) :=
  instOracleInterfaceMessageAppend

instance instOracleInterfaceMessagePSpec : ∀ i, OracleInterface ((pSpec R deg).Message i) :=
  instOracleInterfaceMessageAppend

instance instST₁ : ∀ i, SampleableType ((⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ ++ₚ !p[]).Challenge i) :=
  instSampleableTypeChallengeAppend

instance instST₂ [SampleableType R] : ∀ i, SampleableType
    ((⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ ++ₚ !p[] ++ₚ ⟨!v[.V_to_P], !v[R]⟩).Challenge i) :=
  instSampleableTypeChallengeAppend

instance instSampleableTypeChallengePSpec [SampleableType R] :
    ∀ i, SampleableType ((pSpec R deg).Challenge i) :=
  instSampleableTypeChallengeAppend

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
    verifier := {
      verify := fun target _ => pure target
      embed := {
        toFun
        | .inl () => .inl ()
        | .inr () => .inr ⟨0, by simp⟩
        inj' := by
          intro a b h
          cases a <;> cases b <;> simp at h ⊢
      }
      hEq := by
        intro i
        cases i <;> rfl
    }
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
      embed := Function.Embedding.inl
      hEq := by intro i; rfl
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
      embed := Function.Embedding.inl
      hEq := by intro i; rfl
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
      embed := ⟨fun _ => Sum.inl (Sum.inr ()), by intro _ _ _; rfl⟩
      hEq := by intro i; cases i; rfl
    }
  }

/-- All oracle statements in the single-round sumcheck reduction are the (homogeneous) bounded
polynomial type `R⦃≤ deg⦄[X]`, so the `AppendCoherent` coherence conditions for each step of the
`.append` chain hold definitionally. -/
local instance instSendClaimAppendCoherent :
    OracleVerifier.Append.AppendCoherent (oracleReduction.sendClaim R deg oSpec).verifier where
  hCohInl := fun i k h => by
    cases i <;>
      (first
        | (simp only [oracleReduction.sendClaim, Function.Embedding.coeFn_mk] at h; cases h; rfl)
        | (exfalso; simp_all [oracleReduction.sendClaim]))
  hCohInr := fun i k h => by
    cases i <;>
      (first
        | (simp only [oracleReduction.sendClaim, Function.Embedding.coeFn_mk] at h;
            obtain rfl := Sum.inr.inj h; rfl)
        | (exfalso; simp_all [oracleReduction.sendClaim]))

local instance instCheckClaimAppendCoherent :
    OracleVerifier.Append.AppendCoherent (oracleReduction.checkClaim R deg D oSpec).verifier where
  hCohInl := fun i k h => by
    simp only [oracleReduction.checkClaim, Function.Embedding.inl_apply] at h
    obtain rfl := Sum.inl.inj h; rfl
  hCohInr := fun i k h => by
    simp only [oracleReduction.checkClaim, Function.Embedding.inl_apply] at h
    cases h

local instance instRandomQueryAppendCoherent :
    OracleVerifier.Append.AppendCoherent (oracleReduction.randomQuery R deg oSpec).verifier where
  hCohInl := fun i k h => by
    simp only [oracleReduction.randomQuery, Function.Embedding.inl_apply] at h
    obtain rfl := Sum.inl.inj h; rfl
  hCohInr := fun i k h => by
    simp only [oracleReduction.randomQuery, Function.Embedding.inl_apply] at h
    cases h

local instance instReduceClaimAppendCoherent :
    OracleVerifier.Append.AppendCoherent (oracleReduction.reduceClaim R deg oSpec).verifier where
  hCohInl := fun i k h => by
    simp only [oracleReduction.reduceClaim, Function.Embedding.coeFn_mk] at h
    obtain rfl := Sum.inl.inj h; rfl
  hCohInr := fun i k h => by
    simp only [oracleReduction.reduceClaim, Function.Embedding.coeFn_mk] at h
    cases h

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

@[reducible, simp]
def StmtIn : Type := R

@[reducible, simp]
def StmtOut : Type := R × R

@[reducible, simp]
def OStmtIn : Unit → Type := fun _ => R⦃≤ deg⦄[X]

@[reducible, simp]
def OStmtOut : Unit → Type := fun _ => R⦃≤ deg⦄[X]

def inputRelation : Set ((StmtIn R × (∀ i, OStmtIn R deg i)) × Unit) :=
  { ⟨⟨target, oStmt⟩, _⟩ | ∑ x ∈ (univ.map D), (oStmt ()).1.eval x = target }

def outputRelation : Set ((StmtOut R × (∀ i, OStmtOut R deg i)) × Unit) :=
  { ⟨⟨⟨newTarget, chal⟩, oStmt⟩, _⟩ | (oStmt ()).1.eval chal = newTarget }

variable {ι : Type} (oSpec : OracleSpec ι)

/-- The prover in the simple description of a single round of sum-check.

  Takes in input `target : R` and `poly : R⦃≤ deg⦄[X]`, and:
  - Sends a message `poly' := poly` to the verifier
  - Receive `chal` from the verifier
  - Outputs `(newTarget, chal) : R × R`, where `newTarget := poly.eval chal`
-/
def prover : OracleProver oSpec (StmtIn R) (OStmtIn R deg) Unit (StmtOut R) (OStmtOut R deg) Unit
    (pSpec R deg) where
  PrvState
    | 0 => R⦃≤ deg⦄[X]
    | 1 => R⦃≤ deg⦄[X]
    | 2 => R⦃≤ deg⦄[X] × R

  input := fun ⟨⟨_, oStmt⟩, _⟩ => oStmt ()

  sendMessage
  | ⟨0, _⟩ => fun polyLE => pure ⟨polyLE, polyLE⟩
  | ⟨1, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun polyLE => pure fun chal => ⟨polyLE, chal⟩

  output := fun ⟨polyLE, chal⟩ => pure (((polyLE.val.eval chal, chal), fun _ => polyLE), ())

variable [DecidableEq R] [SampleableType R]

/-- The verifier for the simple description of a single round of sum-check -/
def verifier : Verifier oSpec (StmtIn R × (∀ i, OStmtIn R deg i))
    (StmtOut R × (∀ i, OStmtOut R deg i)) (pSpec R deg) where
  verify := fun ⟨target, oStmt⟩ transcript => do
    letI polyLE := transcript 0
    guard (∑ x ∈ (univ.map D), polyLE.val.eval x = target)
    letI chal := transcript 1
    pure ⟨⟨(oStmt ()).val.eval chal, chal⟩, fun _ => oStmt ()⟩

/-- The reduction for the simple description of a single round of sum-check -/
def reduction : Reduction oSpec (StmtIn R × (∀ i, OStmtIn R deg i)) Unit
    (StmtOut R × (∀ i, OStmtOut R deg i)) Unit (pSpec R deg) where
  prover := prover R deg oSpec
  verifier := verifier R deg D oSpec

-- dtumad: Why is this instance needed?
instance t {ι₁ ι₂ ι₃}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {spec₃ : OracleSpec ι₃} : MonadLiftT (OracleQuery spec₂)
  (OracleQuery (spec₁ + (spec₂ + spec₃))) := by
  infer_instance

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
  -- Peel the round-0 (send poly) bind inside `hchal` to learn `challenge.2.1 = stmt.2 ()`
  erw [support_bind] at hchal
  rw [Set.mem_iUnion] at hchal
  obtain ⟨r0, hchal⟩ := hchal
  rw [Set.mem_iUnion] at hchal
  obtain ⟨hr0, hchal⟩ := hchal
  -- Round 0: `r0 = (concat (stmt.2 ()) default, stmt.2 ())`, so `r0.2 = stmt.2 ()`
  erw [support_map, support_pure] at hr0
  simp only [Set.image_singleton, Set.mem_singleton_iff] at hr0
  subst hr0
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

open Function in
def oracleVerifier : OracleVerifier oSpec (StmtIn R) (OStmtIn R deg) (StmtOut R) (OStmtOut R deg)
    (pSpec R deg) where
  verify := fun target chal => do
    let evals : Vector R m ← (Vector.finRange m).mapM
      (fun i => OptionT.lift <| OracleComp.liftComp
        (OracleComp.lift <|
          OracleSpec.query (show [OStmtIn R deg]ₒ.Domain from ⟨(), D i⟩))
        _)
    guard (evals.sum = target)
    -- The new target is the evaluation of the oracle polynomial at the challenge point.
    -- The verifier obtains it directly via an evaluation query at `chal default`.
    let newTarget : R ← OptionT.lift <| OracleComp.liftComp
      (OracleComp.lift <|
        OracleSpec.query (show [OStmtIn R deg]ₒ.Domain from ⟨(), chal default⟩))
      _
    pure (newTarget, chal default)
  embed := .inl
  hEq := fun i => by simp [pSpec]; rfl

def oracleReduction : OracleReduction oSpec (StmtIn R) (OStmtIn R deg) Unit
    (StmtOut R) (OStmtOut R deg) Unit (pSpec R deg) where
  prover := prover R deg oSpec
  verifier := oracleVerifier R deg D oSpec

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

/-- Perfect completeness for the (non-oracle) reduction -/
theorem reduction_perfectCompleteness :
    (reduction R deg D oSpec).perfectCompleteness init impl
      (inputRelation R deg D) (outputRelation R deg) := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness, ENNReal.coe_zero, tsub_zero]
  intro ⟨target, oStmt⟩ () hValid
  simp only [inputRelation, Set.mem_setOf_eq] at hValid
  -- 1. Unfold reduction and expand pSpec to resolve directions
  simp only [reduction, Reduction.run, Prover.run, Verifier.run, prover, verifier,
    Prover.runToRound, Prover.processRound, Fin.induction_two, pSpec,
    bind_pure_comp, Functor.map_map, Function.comp]
  -- 2. Resolve round 0 direction (P_to_V)
  split <;> rename_i hDir0
  · exact absurd hDir0 (by decide)
  try simp only [pure_bind, map_pure, Functor.map_map, Function.comp, bind_pure_comp]
  -- 3. Resolve round 1 direction (V_to_P)
  split <;> rename_i hDir1
  swap
  · exact absurd hDir1 (by decide)
  -- 4. Inline pure computations via liftComp_pure, evaluate transcript access, resolve guard
  simp only [MonadLift.monadLift, liftM, monadLift, MonadLiftT.monadLift,
    OracleComp.liftComp_pure, pure_bind, map_pure, Functor.map_map, Function.comp,
    bind_pure_comp, Transcript.concat, Fin.snoc_last, Fin.snoc_castSucc,
    guard, if_pos hValid]
  -- 5. After full simplification, the computation should be OptionT-free
  -- Prove Pr[event | comp] ≥ 1
  simp only [ENNReal.coe_zero, tsub_zero]
  rw [ge_iff_le]
  rw [one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- No failure
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hmem
    obtain ⟨⟨_, s'⟩, hmem, rfl⟩ := hmem
    -- The computation always returns some (guard passes by hValid, output by construction).
    -- Needs: support decomposition through simulateQ's PFunctor.FreeM.mapM representation.
    -- Peel outer OptionT bind via simulateQ_bind
    erw [simulateQ_bind] at hmem
    erw [StateT.run_bind] at hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨⟨x, s''⟩, hx, hs⟩ := hmem
    -- OptionT.lift wraps in some: peel via simulateQ_map
    erw [simulateQ_map] at hx
    rw [StateT.run_map] at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨⟨val, s₀⟩, hval, heq⟩ := hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    -- x = some val; OptionT bind matches on some → takes some branch
    -- Peel second OptionT bind (stmtOut)
    erw [simulateQ_bind] at hs
    erw [StateT.run_bind] at hs
    rw [mem_support_bind_iff] at hs
    obtain ⟨⟨y, s'''⟩, hy, hs⟩ := hs
    -- OptionT.lift wraps in some; peel via simulateQ_map (inner + outer)
    erw [simulateQ_map] at hy
    erw [simulateQ_map] at hy
    rw [StateT.run_map] at hy
    simp only [support_map, Set.mem_image] at hy
    obtain ⟨⟨val2, s₁⟩, hval2, heq2⟩ := hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq2
    -- y = some val2; match on some → continues
    -- val2 : Option output_type; if some, getM succeeds; if none, getM fails
    dsimp only [] at hs
    rcases val2 with _ | ⟨out⟩
    · -- val2 = none: getM fails → produces none. But guard always passes.
      exfalso
      -- Decompose hval: peel the do block's first bind
      erw [simulateQ_bind] at hval
      erw [StateT.run_bind] at hval
      rw [mem_support_bind_iff] at hval
      obtain ⟨⟨chal_res, s₂⟩, hchal, hval⟩ := hval
      -- v4.29.0: hchal is a do-block (pure + liftComp query), need extra bind peel
      erw [simulateQ_bind] at hchal
      erw [StateT.run_bind] at hchal
      rw [mem_support_bind_iff] at hchal
      obtain ⟨⟨discr_val, s_d⟩, hchal_fst, hchal_rest⟩ := hchal
      erw [simulateQ_map] at hchal_fst
      erw [simulateQ_pure] at hchal_fst
      rw [StateT.run_map, StateT.run_pure] at hchal_fst
      simp only [support_map, support_pure, Set.mem_image, Set.mem_singleton_iff] at hchal_fst
      obtain ⟨_, rfl, heq_d⟩ := hchal_fst
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq_d
      -- Second part: f <$> liftComp query — peel map, then liftComp, then query
      erw [simulateQ_map] at hchal_rest
      erw [StateT.run_map] at hchal_rest
      simp only [support_map, Set.mem_image] at hchal_rest
      obtain ⟨⟨inner_val, s_inner⟩, hinner, heq_c⟩ := hchal_rest
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq_c
      simp only [QueryImpl.addLift_def,
        QueryImpl.simulateQ_add_liftComp_right, QueryImpl.simulateQ_add_liftComp_left] at hinner
      erw [simulateQ_query] at hinner
      erw [StateT.run_map] at hinner
      simp only [support_map, Set.mem_image] at hinner
      obtain ⟨⟨oracle_resp, s_o⟩, _, heq_q⟩ := hinner
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq_q
      erw [simulateQ_pure] at hval
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hval
      -- Now decompose hval2
      simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_apply,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        simulateQ_query, simulateQ_pure, simulateQ_bind, simulateQ_map,
        QueryImpl.simulateQ_add_liftComp_right, QueryImpl.simulateQ_add_liftComp_left,
        OracleComp.liftComp_map, OracleComp.liftComp_pure,
        pure_bind, map_pure, Functor.map_map, Function.comp,
        OracleQuery.cont, OracleQuery.input_query,
        StateT.run_bind, StateT.run_map, StateT.run_pure,
        support_map, support_pure, Set.mem_singleton_iff, Set.mem_image,
        Prod.mk.injEq, Option.some.injEq, Fin.snoc] at hval2
      norm_num at hval2
      rw [Finset.sum_map] at hValid
      simp only [apply_ite, simulateQ_ite, OptionT.run_pure] at hval2
      erw [if_pos hValid] at hval2
      simp only [simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hval2
      simp at hval2
    · -- val2 = some out: getM succeeds, final map wraps in some, contradicts none
      simp only [Option.getM, pure_bind] at hs
      erw [simulateQ_pure] at hs
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hs
      exact absurd (congr_arg Prod.fst hs) (by simp)
  · -- All outputs satisfy the event
    intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hx
    obtain ⟨⟨_, s'⟩, hx, rfl⟩ := hx
    -- Same decomposition as above: peel the outer OptionT bind.
    erw [simulateQ_bind] at hx
    erw [StateT.run_bind] at hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨⟨x_opt, s''⟩, hx_first, hx_rest⟩ := hx
    -- Peel some <$> from OptionT.lift
    erw [simulateQ_map] at hx_first
    rw [StateT.run_map] at hx_first
    simp only [support_map, Set.mem_image] at hx_first
    obtain ⟨⟨val, s₀⟩, hval, heq⟩ := hx_first
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    -- x_opt = some val; peel second OptionT bind
    erw [simulateQ_bind] at hx_rest
    erw [StateT.run_bind] at hx_rest
    rw [mem_support_bind_iff] at hx_rest
    obtain ⟨⟨y, s'''⟩, hy, hx_rest⟩ := hx_rest
    -- Peel some <$> from inner computation
    erw [simulateQ_map] at hy
    erw [simulateQ_map] at hy
    rw [StateT.run_map] at hy
    simp only [support_map, Set.mem_image] at hy
    obtain ⟨⟨val2, s₁⟩, hval2, heq2⟩ := hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq2
    -- y = some val2; case split on val2
    dsimp only [] at hx_rest
    rcases val2 with _ | ⟨out⟩
    · -- val2 = none: getM fails, produces none, but x is some — contradiction
      simp only [Option.getM, pure_bind] at hx_rest
      erw [simulateQ_pure] at hx_rest
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx_rest
      exact absurd (congr_arg Prod.fst hx_rest) (by simp)
    · -- val2 = some out: getM succeeds, x is concrete
      simp only [Option.getM, pure_bind] at hx_rest
      erw [simulateQ_pure] at hx_rest
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx_rest
      obtain ⟨rfl, rfl⟩ := hx_rest
      erw [simulateQ_bind] at hval
      erw [StateT.run_bind] at hval
      rw [mem_support_bind_iff] at hval
      obtain ⟨⟨chal_res, s₂⟩, hchal, hval⟩ := hval
      -- v4.29.0: hchal is a do-block, need extra bind peel
      erw [simulateQ_bind] at hchal
      erw [StateT.run_bind] at hchal
      rw [mem_support_bind_iff] at hchal
      obtain ⟨⟨discr_val, s_d⟩, hchal_fst, hchal_rest⟩ := hchal
      erw [simulateQ_map] at hchal_fst
      erw [simulateQ_pure] at hchal_fst
      rw [StateT.run_map, StateT.run_pure] at hchal_fst
      simp only [support_map, support_pure, Set.mem_image, Set.mem_singleton_iff] at hchal_fst
      obtain ⟨_, rfl, heq_d⟩ := hchal_fst
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq_d
      -- Second part: f <$> liftComp query — peel map, then liftComp, then query
      erw [simulateQ_map] at hchal_rest
      erw [StateT.run_map] at hchal_rest
      simp only [support_map, Set.mem_image] at hchal_rest
      obtain ⟨⟨inner_val, s_inner⟩, hinner, heq_c⟩ := hchal_rest
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq_c
      simp only [QueryImpl.addLift_def,
        QueryImpl.simulateQ_add_liftComp_right, QueryImpl.simulateQ_add_liftComp_left] at hinner
      erw [simulateQ_query] at hinner
      erw [StateT.run_map] at hinner
      simp only [support_map, Set.mem_image] at hinner
      obtain ⟨⟨oracle_resp, s_o⟩, _, heq_q⟩ := hinner
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq_q
      erw [simulateQ_pure] at hval
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hval
      -- Decompose hval2: resolve guard
      simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_apply,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        simulateQ_query, simulateQ_pure, simulateQ_bind, simulateQ_map,
        QueryImpl.simulateQ_add_liftComp_right, QueryImpl.simulateQ_add_liftComp_left,
        OracleComp.liftComp_map, OracleComp.liftComp_pure,
        pure_bind, map_pure, Functor.map_map, Function.comp,
        OracleQuery.cont, OracleQuery.input_query,
        StateT.run_bind, StateT.run_map, StateT.run_pure,
        support_map, support_pure, Set.mem_singleton_iff, Set.mem_image,
        Prod.mk.injEq, Option.some.injEq, Fin.snoc] at hval2
      norm_num at hval2
      rw [Finset.sum_map] at hValid
      simp only [apply_ite, simulateQ_ite, OptionT.run_pure] at hval2
      erw [if_pos hValid] at hval2
      simp only [simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hval2
      obtain ⟨_, ⟨_, rfl⟩, _, rfl⟩ := hval2
      simp only [Set.mem_setOf_eq, outputRelation]
      constructor <;> simp


/-- Closed form of the simulated oracle-verifier `verify`: the inner `simOracle2`
simulation collapses to a guard on the ORACLE's `D`-sum followed by the oracle's
evaluation at the challenge. -/
lemma simulateQ_oracleVerify_eq
    (target : StmtIn R) (oStmt : ∀ i, OStmtIn R deg i)
    (chal : ∀ i, (pSpec R deg).Challenge i)
    (msgs : ∀ i, (pSpec R deg).Message i) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      ((oracleVerifier R deg D oSpec).verify target chal) =
    (if ((Vector.finRange m).map (fun i => (oStmt ()).val.eval (D i))).sum = target
      then (pure ((oStmt ()).val.eval (chal default), chal default) :
        OptionT (OracleComp oSpec) (StmtOut R))
      else failure) := by
  have hcomp : ∀ x : R, (simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      (OptionT.lift ((OracleComp.lift (OracleSpec.query
        (spec := [OStmtIn R deg]ₒ) ⟨(), x⟩)).liftComp
        (oSpec + ([OStmtIn R deg]ₒ + [(pSpec R deg).Message]ₒ)))) :
      OptionT (OracleComp oSpec) R) = pure ((oStmt ()).val.eval x) := by
    intro x
    erw [simulateQ_optionT_lift]
    erw [simulateQ_double_lift_query]
    rfl
  unfold oracleVerifier
  dsimp only
  rw [simulateQ_optionT_bind]
  rw [simulateQ_optionT_vector_mapM]
  have hfun : (fun b : Fin m => (simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
        ((OptionT.lift ((OracleComp.lift (OracleSpec.query
            (spec := [OStmtIn R deg]ₒ) ⟨(), D b⟩)).liftComp
          (oSpec + ([OStmtIn R deg]ₒ + [(pSpec R deg).Message]ₒ)))) :
            OptionT (OracleComp (oSpec + ([OStmtIn R deg]ₒ + [(pSpec R deg).Message]ₒ))) R) :
        OptionT (OracleComp oSpec) R))
      = (fun b : Fin m => (pure ((oStmt ()).val.eval (D b)) : OptionT (OracleComp oSpec) R)) :=
    by funext b; exact hcomp (D b)
  rw [hfun]
  rw [vector_mapM_pure_comp, pure_bind]
  by_cases hP : ((Vector.finRange m).map (fun i => (oStmt ()).val.eval (D i))).sum = target
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

/-- Bridge (early copy for the completeness proof below; see also
`vector_finRange_map_sum_eq`): the vector `D`-evaluation sum equals the `Fin` sum. -/
private lemma vector_finRange_map_sum_eq' (g : Fin m → R) :
    ((Vector.finRange m).map g).sum = ∑ i : Fin m, g i := by
  rw [← Vector.sum_toList, Vector.toList_map, Fin.sum_univ_def]
  have h : (Vector.finRange m).toList = List.finRange m := by
    simp only [Vector.finRange, Array.finRange, Vector.toList_ofFn]
    exact List.ofFn_id m
  rw [h]

/-- Perfect completeness for the oracle reduction -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction R deg D oSpec).perfectCompleteness init impl
      (inputRelation R deg D) (outputRelation R deg) := by
  -- Direct proof (no detour through `oracleReduction_eq_reduction`): the oracle verifier
  -- collapses to a guard on the ORACLE's D-sum, which holds by `hValid`.
  unfold OracleReduction.perfectCompleteness
  simp only [Reduction.perfectCompleteness, Reduction.completeness, ENNReal.coe_zero, tsub_zero]
  intro ⟨target, oStmt⟩ () hValid
  simp only [inputRelation, Set.mem_setOf_eq] at hValid
  have hValid' : ((Vector.finRange m).map (fun i => (oStmt ()).val.eval (D i))).sum = target := by
    rw [vector_finRange_map_sum_eq']
    simpa [Finset.sum_map] using hValid
  simp only [oracleReduction, OracleReduction.toReduction, Reduction.run, Prover.run,
    Verifier.run, prover, OracleVerifier.toVerifier,
    Prover.runToRound, Prover.processRound, Fin.induction_two, pSpec,
    bind_pure_comp, Function.comp]
  split <;> rename_i hDir0
  · exact absurd hDir0 (by decide)
  try simp only [pure_bind, map_pure, Functor.map_map, Function.comp, bind_pure_comp]
  split <;> rename_i hDir1
  swap
  · exact absurd hDir1 (by decide)
  simp only [simulateQ_oracleVerify_eq R deg D oSpec, hValid', eq_self_iff_true, if_true]
  simp only [liftM_pure, liftComp_pure, map_pure, pure_bind, bind_pure_comp,
    Functor.map_map, Function.comp_def, map_map, OptionT.run_pure, Option.getM,
    Transcript.concat, Fin.snoc_last, Fin.snoc_castSucc]
  simp only [OptionT.run_map, OptionT.run_mk]
  simp only [OptionT.run_pure, Option.map_some, liftM_pure, pure_bind, bind_pure_comp]
  simp only [ENNReal.coe_zero, tsub_zero]
  rw [ge_iff_le]
  rw [one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- No failure: the computation is a `some`-producing map over the challenge sample.
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    erw [simulateQ_bind] at hmem
    rw [StateT.run'_bind_lib, mem_support_bind_iff] at hmem
    obtain ⟨⟨proverResult, s'⟩, hProver, hmem⟩ := hmem
    cases proverResult with
    | none =>
        rw [OptionT.liftM_eq_mk_map_some] at hProver
        change (none, s') ∈ _root_.support
          (StateT.run (simulateQ (impl.addLift challengeQueryImpl)
            ((some <$> _) : OracleComp _ (Option _))) s) at hProver
        erw [simulateQ_map] at hProver
        rw [StateT.run_map] at hProver
        simp only [support_map, Set.mem_image, Prod.exists] at hProver
        obtain ⟨_, _, _, _, _, _, _, hEq⟩ := hProver
        cases hEq
    | some proverResult =>
        simp only [liftM_pure] at hmem
        erw [simulateQ_pure] at hmem
        rw [StateT.run'_pure_lib] at hmem
        simp only [support_pure, Set.mem_singleton_iff] at hmem
        cases hmem
  · -- Event: holds for every sampled challenge by construction.
    intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    erw [simulateQ_bind] at hx
    rw [StateT.run'_bind_lib, mem_support_bind_iff] at hx
    obtain ⟨⟨proverResult, s'⟩, hw, hx⟩ := hx
    cases proverResult with
    | none =>
        rw [OptionT.liftM_eq_mk_map_some] at hw
        change (none, s') ∈ _root_.support
          (StateT.run (simulateQ (impl.addLift challengeQueryImpl)
            ((some <$> _) : OracleComp _ (Option _))) s) at hw
        erw [simulateQ_map] at hw
        rw [StateT.run_map] at hw
        simp only [support_map, Set.mem_image, Prod.exists] at hw
        obtain ⟨_, _, _, _, _, _, _, hEq⟩ := hw
        cases hEq
    | some proverResult =>
        simp only [liftM_pure] at hx
        erw [simulateQ_pure] at hx
        rw [StateT.run'_pure_lib] at hx
        simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hx
        subst x
        simp only [outputRelation, Set.mem_setOf_eq]
        refine ⟨rfl, ?_⟩
        erw [simulateQ_bind] at hw
        rw [StateT.run_bind] at hw
        rw [mem_support_bind_iff] at hw
        obtain ⟨⟨g1, sg⟩, hg1, hw⟩ := hw
        rcases g1 with ⟨tr1, polyLE, chal⟩
        erw [simulateQ_pure] at hw
        rw [StateT.run_pure] at hw
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
        obtain ⟨⟨rfl, rfl⟩, -⟩ := hw
        erw [simulateQ_map] at hg1
        rw [StateT.run_map] at hg1
        simp only [support_map, Set.mem_image] at hg1
        obtain ⟨⟨c, sc⟩, hleft, hmap⟩ := hg1
        erw [simulateQ_bind] at hleft
        rw [StateT.run_bind] at hleft
        rw [mem_support_bind_iff] at hleft
        obtain ⟨⟨d, sd⟩, hd, hleft⟩ := hleft
        erw [simulateQ_map] at hd
        erw [simulateQ_pure] at hd
        rw [StateT.run_map, StateT.run_pure] at hd
        simp only [support_map, support_pure, Set.mem_image, Set.mem_singleton_iff] at hd
        obtain ⟨_, rfl, hd⟩ := hd
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
        erw [simulateQ_map] at hleft
        rw [StateT.run_map] at hleft
        simp only [support_map, Set.mem_image] at hleft
        obtain ⟨⟨challenge, sch⟩, _, hchallenge⟩ := hleft
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hchallenge
        obtain ⟨hmain, rfl⟩ := Prod.mk.inj hmap
        obtain ⟨htr, hrest⟩ := Prod.mk.inj hmain
        subst tr1
        obtain ⟨hpoly, hchal⟩ := Prod.mk.inj hrest
        subst polyLE
        subst chal
        simp [FullTranscript.challenges, FullTranscript.messages, oracleVerifier]
        simp [Fin.snoc]
        constructor
        · constructor <;> rfl
        · ext x
          rfl

/-- Trivial round-by-round extractor (all witnesses are `Unit`). -/
def simpleRbrExtractor : Extractor.RoundByRound oSpec
    (StmtIn R × (∀ i, OStmtIn R deg i)) Unit Unit (pSpec R deg) (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ _ => ()
  extractOut := fun _ _ _ => ()

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The transcript-independent knowledge state function for the oracle verifier: its guard
checks the ORACLE's `D`-sum, which is precisely the input relation.

De-privatized (#13) so the downstream plain round-by-round soundness weakening can read off its
transcript-independence by `Iff.rfl`: its `toFun` ignores the message index, transcript, and
mid-witness, so the per-round knowledge-flip event is identically `False`. -/
def simpleKnowledgeStateFunction :
    ((oracleVerifier R deg D oSpec).toVerifier).KnowledgeStateFunction init impl
      (inputRelation R deg D) (outputRelation R deg)
      (simpleRbrExtractor R deg oSpec) where
  toFun := fun _ stmtIn _ _ => (stmtIn, ()) ∈ inputRelation R deg D
  toFun_empty := fun stmtIn witMid => Iff.rfl
  toFun_next := fun _ _ _ _ _ _ h => h
  toFun_full := fun ⟨target, oStmt⟩ tr witOut h => by
    show (⟨target, oStmt⟩, ()) ∈ inputRelation R deg D
    by_contra hInput
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, _hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have hGuard :
        ((Vector.finRange m).map (fun i => (oStmt ()).val.eval (D i))).sum ≠ target := by
      intro hsum
      apply hInput
      simp only [inputRelation, Set.mem_setOf_eq]
      rw [Finset.sum_map]
      simpa [vector_finRange_map_sum_eq] using hsum
    have hrun :
        ((oracleVerifier R deg D oSpec).toVerifier).run ⟨target, oStmt⟩ tr =
          (failure : OptionT (OracleComp oSpec) (StmtOut R × (∀ i, OStmtOut R deg i))) := by
      simp only [Verifier.run, OracleVerifier.toVerifier]
      rw [simulateQ_oracleVerify_eq]
      rw [if_neg hGuard]
      rfl
    have key :
        (simulateQ impl (((oracleVerifier R deg D oSpec).toVerifier).run ⟨target, oStmt⟩ tr)).run'
            s =
          pure none := by
      rw [hrun]
      change (simulateQ impl (pure none : OracleComp oSpec
        (Option (StmtOut R × (∀ i, OStmtOut R deg i))))).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$> (pure (none :
        Option (StmtOut R × (∀ i, OStmtOut R deg i))) : StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]
      simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    exact absurd hx (by simp)

/-- Round-by-round knowledge soundness for the oracle verifier -/
theorem oracleVerifier_rbrKnowledgeSoundness [Fintype R] :
    (oracleVerifier R deg D oSpec).rbrKnowledgeSoundness init impl
    (inputRelation R deg D) (outputRelation R deg) (fun _ => (deg : ℝ≥0) / (Fintype.card R)) := by
  unfold OracleVerifier.rbrKnowledgeSoundness Verifier.rbrKnowledgeSoundness
  refine ⟨fun _ => Unit, simpleRbrExtractor R deg oSpec,
    simpleKnowledgeStateFunction R deg D oSpec, ?_⟩
  intro stmtIn witIn rbrP i
  refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
  rintro ⟨tr, chal, log⟩ - ⟨w, hn, hy⟩
  exact hn hy

-- Note: break down the oracle reduction into a series of oracle reductions as stated above

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

/-- The oracle statement lens that connect the simple to the full single-round sum-check protocol

For `n = 0`, since `poly : R[X Fin 0]` is just a constant, we need to embed it as a constant poly.

For other `n := n + 1`, we proceed with the sum `∑ x ∈ D ^ (n - i), poly ⸨challenges, X, x⸩` -/
def oStmtLens (i : Fin n) : OracleStatement.Lens
    (StatementRound R n i.castSucc) (StatementRound R n i.succ) (Simple.StmtIn R) (Simple.StmtOut R)
    (OracleStatement R n deg) (OracleStatement R n deg)
    (Simple.OStmtIn R deg) (Simple.OStmtOut R deg) where

  toFunA := fun ⟨⟨target, challenges⟩, oStmt⟩ =>
    ⟨target, fun _ =>
      match h : n with
      | 0 => ⟨Polynomial.C <| MvPolynomial.isEmptyAlgEquiv R (Fin 0) (oStmt ()), by
        rw [Polynomial.mem_degreeLE]; exact le_trans Polynomial.degree_C_le (by simp)⟩
      | n + 1 =>
      ⟨∑ x ∈ (univ.map D) ^ᶠ (n - i), (oStmt ()).val ⸨X ⦃i⦄, challenges, x⸩'(by simp; omega),
        sumcheck_roundPoly_degreeLE R n deg D i (oStmt ()).property⟩⟩

  toFunB := fun ⟨⟨_oldTarget, challenges⟩, oStmt⟩ ⟨⟨newTarget, chal⟩, oStmt'⟩ =>
    ⟨⟨newTarget, Fin.snoc challenges chal⟩, oStmt⟩

@[simp]
def oCtxLens (i : Fin n) : OracleContext.Lens
    (StatementRound R n i.castSucc) (StatementRound R n i.succ) (Simple.StmtIn R) (Simple.StmtOut R)
    (OracleStatement R n deg) (OracleStatement R n deg)
    (Simple.OStmtIn R deg) (Simple.OStmtOut R deg)
    Unit Unit Unit Unit where
  wit := Witness.Lens.trivial
  stmt := oStmtLens R n deg D i

@[simp]
def extractorLens (i : Fin n) : Extractor.Lens
    (StatementRound R n i.castSucc × (∀ i, OracleStatement R n deg i))
    (StatementRound R n i.succ × (∀ i, OracleStatement R n deg i))
    (Simple.StmtIn R × (∀ i, Simple.OStmtIn R deg i))
    (Simple.StmtOut R × (∀ i, Simple.OStmtOut R deg i))
    Unit Unit Unit Unit where
  stmt := oStmtLens R n deg D i
  wit := Witness.InvLens.trivial

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

/-- The verifier for the `i`-th round of the sum-check protocol -/
def verifier (i : Fin n) : Verifier oSpec
    (StatementRound R n i.castSucc × (∀ i, OracleStatement R n deg i))
    (StatementRound R n i.succ × (∀ i, OracleStatement R n deg i)) (pSpec R deg) :=
  (Simple.verifier R deg D oSpec).liftContext (oStmtLens R n deg D i)

/-- The oracle verifier for the `i`-th round of the sum-check protocol.

Migrated to the new `OracleStatement.OracleLens` API (#433): the oracle-routing lens
`sumcheckOracleLens` supplies the `simOStmt`/`embedOStmt` data that the value-level `oStmtLens`
cannot express. -/
def oracleVerifier (i : Fin n) : OracleVerifier oSpec (StatementRound R n i.castSucc)
    (OracleStatement R n deg) (StatementRound R n i.succ) (OracleStatement R n deg) (pSpec R deg) :=
  (Simple.oracleVerifier R deg D oSpec).liftContext (sumcheckOracleLens R n deg D oSpec i)

/-- The `i`-th-round oracle verifier routes its (single) output oracle to the (unchanged) input
oracle (`sumcheckOracleLens.embedOStmt = Function.Embedding.inl`, `hEqOStmt = rfl`), so its
`AppendCoherent` coherence holds definitionally. -/
instance instOracleVerifierAppendCoherent (i : Fin n) :
    OracleVerifier.Append.AppendCoherent (oracleVerifier R n deg D oSpec i) where
  hCohInl := fun a k h => by
    have hk : a = k := by
      simpa only [oracleVerifier, OracleVerifier.liftContext, sumcheckOracleLens,
        Function.Embedding.inl_apply, Sum.inl.injEq] using h
    subst hk; rfl
  hCohInr := fun a k h => by
    simp only [oracleVerifier, OracleVerifier.liftContext, sumcheckOracleLens,
      Function.Embedding.inl_apply, reduceCtorEq] at h

/-- The sum-check reduction for the `i`-th round of the sum-check protocol -/
def reduction (i : Fin n) : Reduction oSpec
    ((StatementRound R n i.castSucc) × (∀ i, OracleStatement R n deg i)) Unit
    ((StatementRound R n i.succ) × (∀ i, OracleStatement R n deg i)) Unit (pSpec R deg) :=
  (Simple.reduction R deg D oSpec).liftContext (oCtxLens R n deg D i).toContext

/-- The sum-check oracle reduction for the `i`-th round of the sum-check protocol.

Migrated to the new `OracleReduction.liftContext` signature (#433), which takes the separate
oracle-routing `stmtLens := sumcheckOracleLens` (carrying `simOStmt`/`embedOStmt`) alongside the
value-level context lens. -/
def oracleReduction (i : Fin n) : OracleReduction oSpec
    (StatementRound R n i.castSucc) (OracleStatement R n deg) Unit
    (StatementRound R n i.succ) (OracleStatement R n deg) Unit (pSpec R deg) :=
  (Simple.oracleReduction R deg D oSpec).liftContext (oCtxLens R n deg D i)
    (sumcheckOracleLens R n deg D oSpec i)

/-- The `i`-th-round oracle *reduction*'s verifier is definitionally `oracleVerifier i`, so it
inherits `AppendCoherent` (used to seqCompose the rounds at the reduction level). -/
instance instOracleReductionVerifierAppendCoherent (i : Fin n) :
    OracleVerifier.Append.AppendCoherent (oracleReduction R n deg D oSpec i).verifier :=
  instOracleVerifierAppendCoherent R n deg D oSpec i

omit [SampleableType R] in
@[simp]
lemma reduction_verifier_eq_verifier {i : Fin n} :
    (reduction R n deg D oSpec i).verifier = verifier R n deg D oSpec i := by
  rfl

omit [SampleableType R] in
@[simp]
lemma oracleReduction_verifier_eq_verifier {i : Fin n} :
    (oracleReduction R n deg D oSpec i).verifier = oracleVerifier R n deg D oSpec i := by
  rfl

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
  rw [Polynomial.eval_finset_sum]
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
    dsimp only
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



instance oCtxLens_complete :
    (oCtxLens R n deg D i).toContext.IsComplete
      (relationRound R n deg D i.castSucc) (Simple.inputRelation R deg D)
      (relationRound R n deg D i.succ) (Simple.outputRelation R deg)
      ((Simple.oracleReduction R deg D oSpec).toReduction.compatContext
        (oCtxLens R n deg D i).toContext)
where
  proj_complete := by
    simp [relationRound, Simple.inputRelation]
    unfold oStmtLens
    induction n with
    | zero => exact Fin.elim0 i
    | succ n ih =>
      intro stmt oStmt hRelIn
      simp [← hRelIn]
      simp_rw [Polynomial.eval_finset_sum]
      simp_rw [← eval_eq_eval_mv_eval_finSuccEquivNth]
      -- Round split: ∑ a ∈ D, ∑ y ∈ D^(n-i), eval (insertNth i a (append c y ∘ cast)) p
      --            = ∑ z ∈ D^(n+1-i), eval (append c z ∘ cast) p
      exact sumcheck_round_split D i _ _ (by omega) (by omega) (by omega)
  lift_complete := by
    induction n with
    | zero => exact Fin.elim0 i
    | succ n' _ih =>
    rintro ⟨⟨target, challenges⟩, oStmt⟩ _ ⟨⟨newTarget, chal⟩, oStmt'⟩ _ hCompat hRelIn hRelOut'
    simp only [Simple.outputRelation, Set.mem_setOf_eq] at hRelOut'
    -- From `hCompat`: the inner output context is the honest reduction's prover output.
    -- (No detour through the false `oracleReduction_eq_reduction`: the compiled reduction's
    -- prover is literally `Simple.prover`, and only the prover side is used below.)
    rw [Reduction.compatContext] at hCompat
    simp only [OracleReduction.toReduction, Simple.oracleReduction,
      Set.mem_image, Function.comp_apply] at hCompat
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
    simp only [relationRound, Set.mem_setOf_eq]
    rw [hpoT]
    exact sumcheck_round_eval_snoc D i challenges chal _ (by omega) (by omega)

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
    simp [relationRound, Simple.inputRelation]
    unfold oStmtLens
    induction n with
    | zero => exact Fin.elim0 i
    | succ n ih =>
      intro stmt oStmt hRelIn
      simp [← hRelIn]
      simp_rw [Polynomial.eval_finset_sum]
      simp_rw [← eval_eq_eval_mv_eval_finSuccEquivNth]
      -- Round split: ∑ a ∈ D, ∑ y ∈ D^(n-i), eval (insertNth i a (append c y ∘ cast)) p
      --            = ∑ z ∈ D^(n+1-i), eval (append c z ∘ cast) p
      exact sumcheck_round_split D i _ _ (by omega) (by omega) (by omega)
  lift_complete := by
    induction n with
    | zero => exact Fin.elim0 i
    | succ n' _ih =>
    rintro ⟨⟨target, challenges⟩, oStmt⟩ _ ⟨⟨newTarget, chal⟩, oStmt'⟩ _ hCompat hRelIn hRelOut'
    simp only [Simple.outputRelation, Set.mem_setOf_eq] at hRelOut'
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
    simp only [relationRound, Set.mem_setOf_eq]
    rw [hpoT]
    exact sumcheck_round_eval_snoc D i challenges chal _ (by omega) (by omega)

instance extractorLens_rbr_knowledge_soundness :
    Extractor.Lens.IsKnowledgeSound
      (relationRound R n deg D i.castSucc) (Simple.inputRelation R deg D)
      (relationRound R n deg D i.succ) (Simple.outputRelation R deg)
      ((Simple.oracleVerifier R deg D oSpec).toVerifier.compatStatement (oStmtLens R n deg D i))
      (fun _ _ => True)
      ⟨oStmtLens R n deg D i, Witness.InvLens.trivial⟩ where
  proj_knowledgeSound := by
    rintro ⟨⟨target, challenges⟩, oStmt⟩ ⟨⟨newTarget, chal⟩, oStmt'⟩ _ hCompat _hLift
    simp only [Verifier.compatStatement] at hCompat
    obtain ⟨tr, htr⟩ := hCompat
    simp [Verifier.run, OracleVerifier.toVerifier, Simple.oracleVerifier,
      OracleInterface.simOracle2, Statement.Lens.proj, guard] at htr
    obtain ⟨htr1, htr2⟩ := htr
    -- peel the three binds at the OptionT level (its support-bind law avoids Option splits)
    erw [simulateQ_optionT_bind] at htr1
    rw [mem_support_bind_iff] at htr1
    obtain ⟨evals, hEvals, htr1⟩ := htr1
    erw [simulateQ_optionT_bind] at htr1
    rw [mem_support_bind_iff] at htr1
    obtain ⟨u, hGuard, htr1⟩ := htr1
    erw [simulateQ_optionT_bind] at htr1
    rw [mem_support_bind_iff] at htr1
    obtain ⟨nTval, hQuery, htr1⟩ := htr1
    -- final pure pins (newTarget, chal) = (nTval, tr.challenges default)
    erw [simulateQ_pure, mem_support_pure_iff] at htr1
    rw [Prod.mk.injEq] at htr1
    obtain ⟨rfl, rfl⟩ := htr1
    -- the query collapses through the simOracle0 to the oracle's evaluation
    erw [simulateQ_optionT_lift] at hQuery
    rw [OptionT.support_lift] at hQuery
    erw [simulateQ_double_lift_query] at hQuery
    simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply] at hQuery
    -- the output oracle is the projected round polynomial
    have hO : oStmt' () = ((oStmtLens R n deg D i).toFunA
        ({ target := target, challenges := challenges }, oStmt)).2 () := by
      rw [← htr2]
      rfl
    simp only [Simple.outputRelation, Set.mem_setOf_eq, hO]
    simp only [QueryImpl.add, OracleInterface.simOracle0] at hQuery
    simp at hQuery
    exact hQuery.symm

  lift_knowledgeSound := by
    simp [relationRound, Simple.inputRelation, Statement.Lens.proj]
    unfold oStmtLens
    induction n with
    | zero => exact Fin.elim0 i
    | succ n ih =>
      intro stmt oStmt hRelIn
      simp at hRelIn ⊢
      rw [← hRelIn]
      simp_rw [Polynomial.eval_finset_sum]
      simp_rw [← MvPolynomial.eval_eq_eval_mv_eval_finSuccEquivNth]
      exact (sumcheck_round_split D i _ _ (by omega) (by omega) (by omega)).symm


variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

theorem reduction_perfectCompleteness :
    (reduction R n deg D oSpec i).perfectCompleteness init impl
    (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ) :=
  Reduction.liftContext_perfectCompleteness
    (lens := (oCtxLens R n deg D i).toContext)
    (lensComplete := inferInstance)
    (Simple.reduction_perfectCompleteness R deg D oSpec)

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

@[reducible]
def proverState (i : Fin n) : ProverState 2 where
  PrvState
  | 0 => (StatementRound R n i.castSucc) × (∀ i, OracleStatement R n deg i)
  | 1 => (StatementRound R n i.castSucc) × (∀ i, OracleStatement R n deg i)
  | 2 => (StatementRound R n i.succ) × (∀ i, OracleStatement R n deg i)

/-- Prover input for the `i`-th round of the sum-check protocol, where `i < n` -/
def proverInput (i : Fin n) : ProverInput
    ((StatementRound R n i.castSucc) × (∀ i, OracleStatement R n deg i))
    Unit ((proverState R n deg i).PrvState 0) where
  input := Prod.fst

/-- Prover interaction for the `i`-th round of the sum-check protocol, where `i < n`. -/
def proverRound (i : Fin n) : ProverRound oSpec (pSpec R deg) where
  PrvState := (proverState R n deg i).PrvState

  sendMessage
  | ⟨0, _⟩ => fun state =>
    match n with
    | 0 => Fin.elim0 i
    | n + 1 =>
      let ⟨⟨_, challenges⟩, oStmt⟩ := state
      let ⟨poly, hp⟩ := oStmt 0
      pure ⟨ ⟨∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨X ⦃i⦄, challenges, x⸩'(by simp; omega),
        sumcheck_roundPoly_degreeLE R n deg D i hp⟩,
          state⟩
  | ⟨1, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨target, challenges⟩, oStmt⟩ => pure fun chal =>
    let ⟨poly, hp⟩ := oStmt 0
    letI newChallenges : Fin i.succ → R := Fin.snoc challenges chal
    letI newTarget := ∑ x ∈ (univ.map D) ^ᶠ (n - i - 1), poly ⸨newChallenges, x⸩'(by simp; omega)
    ⟨⟨newTarget, newChallenges⟩, fun _ => ⟨poly, hp⟩⟩

/-- Since there is no witness, the prover's output for each round `i < n` of the sum-check protocol
  is trivial -/
def proverOutput (i : Fin n) : ProverOutput oSpec
    ((StatementRound R n i.succ × (∀ i, OracleStatement R n deg i)) × Unit)
    ((proverState R n deg i).PrvState (Fin.last 2)) where
  output := fun x => pure (x, ())

/-- The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only
  well-defined for `n > 0`, since when `n = 0` there is no protocol. -/
def prover (i : Fin n) : OracleProver oSpec
    (StatementRound R n i.castSucc) (OracleStatement R n deg) Unit
    (StatementRound R n i.succ) (OracleStatement R n deg) Unit (pSpec R deg) where
  toProverState := proverState R n deg i
  toProverInput := proverInput R n deg i
  sendMessage := (proverRound R n deg D oSpec i).sendMessage
  receiveChallenge := (proverRound R n deg D oSpec i).receiveChallenge
  toProverOutput := proverOutput R n deg oSpec i

/-- The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1` -/
def verifier (i : Fin n) : Verifier oSpec
    ((StatementRound R n i.castSucc) × (∀ i, OracleStatement R n deg i))
    (StatementRound R n i.succ × (∀ i, OracleStatement R n deg i)) (pSpec R deg) where
  verify := fun ⟨⟨target, challenges⟩, oStmt⟩ transcript => do
    let ⟨p_i, _⟩ : R⦃≤ deg⦄[X] := transcript 0
    let r_i : R := transcript 1
    guard (∑ x ∈ (univ.map D), p_i.eval x = target)
    pure ⟨⟨p_i.eval r_i, Fin.snoc challenges r_i⟩, oStmt⟩

-- /-- The oracle verifier for the `i`-th round, where `i < n + 1` -/
-- def oracleVerifier --[Inhabited ((i : (pSpec R deg).MessageIdx) × OracleInterface.Query ((pSpec R
-- deg).Message i))]
--     (i : Fin n) : OracleVerifier oSpec
--     (StatementRound R n i.castSucc) (OracleStatement R n deg)
--     (StatementRound R n i.succ) (OracleStatement R n deg) (pSpec R deg) where
--   -- Queries for the evaluations of the polynomial at all points in `D`,
--   -- plus one query for the evaluation at the challenge `r_i`
--   -- Check that the sum of the evaluations equals the target, and updates the statement
-- accordingly
--   -- (the new target is the evaluation of the polynomial at the challenge `r_i`)
--   verify := fun ⟨target, challenges⟩ chal => do
--     let evals : List R ← (List.finRange m).mapM
--       (fun i => do
--         return ← query
--           (spec := (oSpec + ([OracleStatement R n deg]ₒ + [(pSpec R deg).Message]ₒ)))
--             (Sum.inr <| Sum.inr (D i)))
--     guard (evals.sum = target)
--     let newTarget ← query
--       (spec := (oSpec + ([OracleStatement R n deg]ₒ + [(pSpec R deg).Message]ₒ)))
--         (Sum.inr <| Sum.inr (D i)) --(by simpa only using chal default)
--     letI newTarget : R := by simpa only
--     pure ⟨newTarget, Fin.snoc challenges (chal default)⟩

--   embed := Function.Embedding.inl

--   hEq := fun _ => rfl

end Unfolded

end SingleRound

end Spec

-- end for noncomputable section
end

end Sumcheck
