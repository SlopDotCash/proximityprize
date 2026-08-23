/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.ProofSystem.ConstraintSystem.R1CS
import ArkLib.ProofSystem.Spartan.Basic

/-!
# Spartan R1CS-to-sumcheck MLE equivalences (issue #114)

r1cs_residual_iff_mle_zero / r1cs_hadamard_iff_mle_zero (the Az∘Bz-Cz=0 <-> MLE-vanishing reduction)
and final_check_consistency. The sumcheck composition + extractor are separate.
-/

/-!
# Issue #114 — Spartan: extractable algebraic math (scratch / hand-verified)

This scratch module isolates the GENUINE, mathlib- and substrate-reducible algebraic content of
issue #114 (the Spartan PIOP: first zero-check + first sum-check + send eval claims + linear
combination + SECOND sum-check + final `CheckClaim`).

The issue asks (paraphrased) to:
  (a) build the second-sum-check oracle reduction and the final `CheckClaim`;
  (b) compose all phases via the sequential-composition / lifting theorems;
  (c) prove perfect completeness and round-by-round knowledge soundness.

Most of (a)/(b)/(c) is PROTOCOL CONSTRUCTION and SECURITY-COMPOSITION PLUMBING (oracle reductions,
lenses, `liftContext`, `append`), NOT extractable algebra — see the report. The genuinely
*mathematical* core, the part that is a clean algebraic identity reducible to the proven `MLE`
API in `ArkLib/Data/MvPolynomial/Multilinear.lean`, is:

  1.  **The R1CS → zero-check reduction identity.**  The first phase claims `A𝕫 ∘ B𝕫 − C𝕫 = 0`
      on the Boolean hypercube. The honest math is: this Hadamard-product vanishing is EQUIVALENT
      to the multilinear extension of the row-product residual being the zero polynomial — which is
      exactly the polynomial the (zero-check + first) sum-check is run on. We prove both directions
      of this equivalence (`r1cs_iff_residual_mle_zero`).

  2.  **The matrix-vector / MLE scaled-sum decomposition.**  Each bundled evaluation claim
      `v_idx = MLE(M_idx *ᵥ 𝕫)(r_x)` splits as `∑_j 𝕫 j · MLE(col_j)(r_x)` — this is the
      sum-check-friendly form the SECOND sum-check opens. (This is the result already landed on
      `main` as `evalClaimValue_eq_scaled_sum`, re-derived here in self-contained form as
      `mulVec_MLE_eval_eq_scaled_sum` so the scratch file is standalone and the proof is auditable.)

  3.  **The final `CheckClaim` evaluation-consistency identity.**  The terminal value the verifier
      reconstructs, `MLE(M *ᵥ 𝕫)(r_x) = ∑_y eq̃(r_x's-row-shape) …`, is exactly the bundled claim
      value — i.e. the final check `target = expected` is the SAME number the second sum-check was
      reducing. We give the eq̃-weighted-sum form (`mulVec_MLE_eval_eq_eqTilde_sum`) that the
      `zEvalFromFinalOracles` / `finalExpectedClaimFromOracles` reconstruction in `SpartanBricks`
      is computing pointwise.

EVERYTHING here is reduced to lemmas already PROVEN in `Multilinear.lean`:
`MLE_eval_zeroOne`, `MLE_eval_scaled_sum`, `MLE_eval_eq_sum_eqTilde`, and the
`is_multilinear`/`eq_MLE_of_isMultilinear_of_eval_eq` uniqueness layer. No `sorry`/`axiom`.

The NON-extractable residue (second-sum-check oracle reduction, the routing lens, the seven-phase
`append` composition, the composed completeness / rbr-knowledge-soundness theorems) is reported as
construction/plumbing, not fabricated here.
-/

noncomputable section

open MvPolynomial BigOperators

namespace Spartan.Scratch114

universe u

variable {R : Type u} [CommRing R]

/-! ## 1. The R1CS → zero-check reduction identity

The first Spartan phase reduces R1CS satisfiability to a zero-check. The R1CS relation
(`R1CS.relation`) says the Hadamard product `(A𝕫) ∘ (B𝕫) = (C𝕫)`, equivalently the *residual*
row vector

  `resid x := (A𝕫) x * (B𝕫) x − (C𝕫) x`

is identically zero on the row index set `Fin (2 ^ ℓ_m)`. The zero-check / first sum-check is run
on the multilinear extension `MLE (resid ∘ finFunctionFinEquiv)`. The genuine algebraic content of
the reduction is that these two statements are EQUIVALENT.

We state it abstractly over the residual function `f : (Fin ℓ → Fin 2) → R` (the row residual,
re-indexed to the Boolean cube). The `∘ finFunctionFinEquiv` re-indexing used in Spartan is a
bijection, so vanishing on `Fin (2^ℓ)` ⟺ vanishing on `Fin ℓ → Fin 2`; we record that bridge too.
-/

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **Hypercube-vanishing ⟺ MLE is the zero polynomial.**

`f = 0` on the whole Boolean cube `σ → Fin 2` **iff** its multilinear extension `MLE f` is the
zero polynomial. This is the exact equivalence the first Spartan phase relies on: the prover claims
the row residual vanishes on the cube, and the (zero-check / first) sum-check is run on `MLE f`.

Forward: from `MLE f = 0`, evaluate at each Boolean point and use `MLE_eval_zeroOne`.
Backward: if `f` vanishes pointwise, `MLE f` is a sum of terms each carrying a `C (f x) = 0`
factor, hence the zero polynomial. -/
theorem mle_eq_zero_iff_forall_cube (f : (σ → Fin 2) → R) :
    MLE f = 0 ↔ ∀ x : σ → Fin 2, f x = 0 := by
  constructor
  · intro h x
    have := congrArg (eval (x : σ → R)) h
    rwa [MLE_eval_zeroOne, map_zero] at this
  · intro h
    unfold MLE
    refine Finset.sum_eq_zero ?_
    intro x _
    rw [h x, map_zero, mul_zero]

/-- **The R1CS residual vanishes on the cube ⟺ its MLE is zero.**

Phrased directly with the Spartan residual `resid x = (A𝕫) x * (B𝕫) x − (C𝕫) x` written as a
function `(σ → Fin 2) → R`. This is the reduction identity the first phase certifies; the right
side is exactly the polynomial the zero-check / first sum-check is run on. -/
theorem r1cs_residual_iff_mle_zero
    (Az Bz Cz : (σ → Fin 2) → R) :
    (∀ x : σ → Fin 2, Az x * Bz x - Cz x = 0)
      ↔ MLE (fun x => Az x * Bz x - Cz x) = 0 := by
  rw [mle_eq_zero_iff_forall_cube]

/-- **Hadamard product form of the residual equivalence.**

The R1CS Hadamard equation `Az ∘ Bz = Cz` (pointwise) is equivalent to the MLE of the residual
being the zero polynomial. This is the cleanest statement of "R1CS satisfiability ⟺ the zero-check
claim", matching `R1CS.relation`'s `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`. -/
theorem r1cs_hadamard_iff_mle_zero
    (Az Bz Cz : (σ → Fin 2) → R) :
    (∀ x : σ → Fin 2, Az x * Bz x = Cz x)
      ↔ MLE (fun x => Az x * Bz x - Cz x) = 0 := by
  rw [mle_eq_zero_iff_forall_cube]
  exact forall_congr' fun x => sub_eq_zero.symm

/-! ### Bridge: re-indexing the cube along `finFunctionFinEquiv`

Spartan works with row index `Fin (2 ^ ℓ_m)` and uses `MLE (resid ∘ finFunctionFinEquiv)` (the
`MLE'` shape). Vanishing on `Fin (2 ^ ℓ)` is equivalent to vanishing of the re-indexed function on
`Fin ℓ → Fin 2`, since `finFunctionFinEquiv` is a bijection. We record this so the abstract
equivalence above transfers verbatim to the concrete Spartan row residual. -/

/-- **R1CS satisfiability (row index form) ⟺ the first-sum-check polynomial `MLE'` is zero.**

`g : Fin (2 ^ n) → R` is the concrete Spartan residual on the row index. It vanishes on every row
**iff** `MLE' g = MLE (g ∘ finFunctionFinEquiv)` is the zero polynomial — the actual polynomial the
zero-check / first sum-check is run on. -/
theorem mle'_eq_zero_iff_forall {n : ℕ}
    (g : Fin (2 ^ n) → R) :
    MLE' g = 0 ↔ ∀ i : Fin (2 ^ n), g i = 0 := by
  unfold MLE'
  rw [mle_eq_zero_iff_forall_cube]
  constructor
  · intro h i
    have := h (finFunctionFinEquiv.symm i)
    rwa [Function.comp_apply, Equiv.apply_symm_apply] at this
  · intro h x
    exact h (finFunctionFinEquiv x)

/-! ### Bridge to the actual `R1CS.relation`

The equivalences above are stated over abstract residual functions. The genuine reduction the first
Spartan phase certifies is between the concrete `R1CS.relation` (the Hadamard equation
`(A𝕫) ∘ (B𝕫) = (C𝕫)` defined in `ConstraintSystem/R1CS.lean`) and the MLE-vanishing claim the
zero-check is run on. We bridge the two here so the abstract MLE equivalence transfers verbatim to
the protocol-level relation. -/

open Matrix in
/-- **`R1CS.relation` ⟺ pointwise row equality.**

`R1CS.relation` is the `Pi`-valued Hadamard equation `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`; this
unfolds to the pointwise statement that every row satisfies `(A𝕫)i · (B𝕫)i = (C𝕫)i`. -/
theorem r1cs_relation_iff_forall_row {sz : R1CS.Size}
    (stmt : Fin sz.n_x → R) (M : R1CS.MatrixIdx → Matrix (Fin sz.m) (Fin sz.n) R)
    (wit : Fin sz.n_w → R) :
    R1CS.relation R sz stmt M wit
      ↔ ∀ i : Fin sz.m,
          (M .A *ᵥ R1CS.𝕫 stmt wit) i * (M .B *ᵥ R1CS.𝕫 stmt wit) i
            = (M .C *ᵥ R1CS.𝕫 stmt wit) i := by
  simp only [R1CS.relation]
  rw [funext_iff]
  rfl

open Matrix in
/-- **`R1CS.relation` ⟺ the row residual vanishes pointwise.**

Rephrasing the Hadamard equality as the vanishing of the row residual
`(A𝕫)i · (B𝕫)i − (C𝕫)i`, which is exactly the function the zero-check / first sum-check extends. -/
theorem r1cs_relation_iff_forall_residual {sz : R1CS.Size}
    (stmt : Fin sz.n_x → R) (M : R1CS.MatrixIdx → Matrix (Fin sz.m) (Fin sz.n) R)
    (wit : Fin sz.n_w → R) :
    R1CS.relation R sz stmt M wit
      ↔ ∀ i : Fin sz.m,
          (M .A *ᵥ R1CS.𝕫 stmt wit) i * (M .B *ᵥ R1CS.𝕫 stmt wit) i
            - (M .C *ᵥ R1CS.𝕫 stmt wit) i = 0 := by
  rw [r1cs_relation_iff_forall_row]
  exact forall_congr' fun _ => (sub_eq_zero).symm

open Matrix in
/-- The R1CS row residual on `Fin sz.m`: `(A𝕫)i · (B𝕫)i − (C𝕫)i`. -/
def r1csResidual {sz : R1CS.Size}
    (stmt : Fin sz.n_x → R) (M : R1CS.MatrixIdx → Matrix (Fin sz.m) (Fin sz.n) R)
    (wit : Fin sz.n_w → R) : Fin sz.m → R :=
  fun i => (M .A *ᵥ R1CS.𝕫 stmt wit) i * (M .B *ᵥ R1CS.𝕫 stmt wit) i
            - (M .C *ᵥ R1CS.𝕫 stmt wit) i

open Matrix in
/-- **The R1CS zero-check reduction on the actual `R1CS.relation`.**

When the row count is `sz.m = 2 ^ k`, `R1CS.relation` holds **iff** the multilinear extension `MLE'`
of the row residual is the zero polynomial — the exact polynomial Spartan's zero-check / first
sum-check is run on. This connects the abstract residual/MLE equivalence (`mle'_eq_zero_iff_forall`)
to the concrete `R1CS.relation` from `ConstraintSystem/R1CS.lean`, closing the first-phase reduction
identity at the protocol-relation level. -/
theorem r1cs_relation_iff_mle'_residual_zero {k : ℕ} {sz : R1CS.Size} (hm : sz.m = 2 ^ k)
    (stmt : Fin sz.n_x → R) (M : R1CS.MatrixIdx → Matrix (Fin sz.m) (Fin sz.n) R)
    (wit : Fin sz.n_w → R) :
    R1CS.relation R sz stmt M wit
      ↔ MLE' (fun i : Fin (2 ^ k) =>
            r1csResidual stmt M wit (Fin.cast hm.symm i)) = 0 := by
  rw [r1cs_relation_iff_forall_residual, mle'_eq_zero_iff_forall]
  constructor
  · intro h i; exact h (Fin.cast hm.symm i)
  · intro h i
    have := h (Fin.cast hm i)
    simpa [r1csResidual, Fin.cast_cast] using this

open Matrix in
/-- **The in-tree zero-check virtual polynomial is the MLE of the R1CS row residual.**

`Spartan.Spec.zeroCheckVirtualPolynomial` is the concrete polynomial used by Spartan's
`firstChallenge` virtual-oracle surface. This theorem identifies it with `MLE'` of the same row
residual used by `r1cs_relation_iff_mle'_residual_zero`, reindexing the Boolean cube through
`finFunctionFinEquiv`. -/
theorem zeroCheckVirtualPolynomial_eq_mle'_r1csResidual
    {S : Type} [CommRing S]
    (pp : Spartan.PublicParams)
    (stmt : Spartan.Spec.Statement.AfterFirstMessage S pp)
    (oStmt : ∀ i, Spartan.Spec.OracleStatement.AfterFirstMessage S pp i) :
    Spartan.Spec.zeroCheckVirtualPolynomial S pp stmt oStmt =
      MLE' (fun i : Fin (2 ^ pp.ℓ_m) =>
        r1csResidual stmt (fun idx => oStmt (.inl idx)) (oStmt (.inr 0)) i) := by
  simp only [Spartan.Spec.zeroCheckVirtualPolynomial, MLE', MLE, r1csResidual,
    Function.comp_apply]
  exact Fintype.sum_equiv finFunctionFinEquiv.symm _ _ (by
    intro x
    simp)

open Matrix in
/-- **The actual Spartan zero-check polynomial vanishes exactly on satisfying R1CS instances.**

This is the first-phase reduction identity stated over the real `zeroCheckVirtualPolynomial`
surface in `Spartan.Basic`: for the matrices and witness threaded through
`OracleStatement.AfterFirstMessage`, the R1CS relation holds iff the virtual zero-check polynomial
is zero. -/
theorem r1cs_relation_iff_zeroCheckVirtualPolynomial_zero
    {S : Type} [CommRing S]
    (pp : Spartan.PublicParams)
    (stmt : Spartan.Spec.Statement.AfterFirstMessage S pp)
    (oStmt : ∀ i, Spartan.Spec.OracleStatement.AfterFirstMessage S pp i) :
    R1CS.relation S pp.toSizeR1CS stmt (fun idx => oStmt (.inl idx)) (oStmt (.inr 0))
      ↔ Spartan.Spec.zeroCheckVirtualPolynomial S pp stmt oStmt = 0 := by
  rw [zeroCheckVirtualPolynomial_eq_mle'_r1csResidual]
  simpa using
    (r1cs_relation_iff_mle'_residual_zero (R := S) (k := pp.ℓ_m)
      (sz := pp.toSizeR1CS) rfl stmt (fun idx => oStmt (.inl idx)) (oStmt (.inr 0)))

/-! ## 2. The matrix-vector / MLE scaled-sum decomposition (second sum-check input)

`v_idx = MLE(M *ᵥ 𝕫)(r_x)` decomposes as `∑_j 𝕫 j · MLE(col_j)(r_x)`. This is the
sum-check-friendly form the SECOND sum-check opens; it is precisely the content already on `main`
as `Spartan.Spec.Bricks.evalClaimValue_eq_scaled_sum`, re-derived here standalone from
`MLE_eval_scaled_sum`. (We work with the residual function directly to keep the scratch file's
imports minimal — the `Matrix.mulVec` repackaging is the same `simp [Matrix.mulVec, dotProduct]`
step used in `SpartanBricks.lean`.) -/

open Matrix in
/-- **MLE of a matrix-vector product, evaluated at a point, is the `𝕫`-scaled sum of column MLEs.**

`MLE((M *ᵥ 𝕫) ∘ e)(r) = ∑_j 𝕫 j · MLE((fun x => M (e x) j))(r)`, where `e := finFunctionFinEquiv`.
This is the algebraic engine behind the second sum-check: the bundled claim value is rewritten as a
sum over the witness/public columns, each a multilinear matrix-column extension. Reduces to the
proven `MLE_eval_scaled_sum`. -/
theorem mulVec_MLE_eval_eq_scaled_sum {m n : ℕ}
    (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R) (z : Fin (2 ^ n) → R)
    (r : Fin m → R) :
    eval r (MLE ((M *ᵥ z) ∘ finFunctionFinEquiv))
      = ∑ j : Fin (2 ^ n),
          z j * eval r (MLE (fun xBits : Fin m → Fin 2 => M (finFunctionFinEquiv xBits) j)) := by
  classical
  have hfun :
      ((M *ᵥ z) ∘ finFunctionFinEquiv)
        = fun xBits : Fin m → Fin 2 =>
            ∑ j : Fin (2 ^ n), z j * M (finFunctionFinEquiv xBits) j := by
    funext xBits
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [hfun]
  simpa using
    (MvPolynomial.MLE_eval_scaled_sum
      (σ := Fin m) (R := R) (s := (Finset.univ : Finset (Fin (2 ^ n))))
      (z := z)
      (g := fun j (xBits : Fin m → Fin 2) => M (finFunctionFinEquiv xBits) j)
      r)

/-! ## 2b. The second sum-check INPUT correctness identity (claimed sum = target)

The previous lemma rewrites a *single* bundled evaluation claim `v_idx = MLE(M *ᵥ 𝕫)(r_x)` as a
`𝕫`-weighted sum over the witness/public column index. The second sum-check then runs over the
*Boolean hypercube* of the column variable `Y`, on the virtual polynomial

  `ℳ(Y) = ∑_idx r_idx · (MLE M_idx)(r_x, Y) · (MLE 𝕫)(Y)`.

Its initial claim (the "sum side" of the sum-check) is that the *sum of `ℳ` over the Boolean cube*
equals the random-linear-combination of the bundled evaluation claims `∑_idx r_idx · v_idx` — this is
exactly the value the linear-combination round handed to the second sum-check, and is the honest
target the prover opens. The genuine algebraic content is below.

The first foundational lemma is the structural sum-check fact, valid for *any* multilinear
extension: summing an `MLE` over the Boolean hypercube reproduces the sum of the underlying
evaluations (because each `MLE` collapses to its evaluation on a Boolean point). This is the
"`∑_cube poly = ∑ evals`" primitive underlying every sum-check completeness argument; it is genuinely
missing from the `MLE` API. -/

omit [Fintype σ] [DecidableEq σ] in
/-- **Hypercube sum of an MLE.** The sum of `MLE f` over the Boolean hypercube `σ → Fin 2` equals
the sum of the underlying evaluations `f`. (`MLE f` agrees with `f` on every Boolean point by
`MLE_eval_zeroOne`, so the two finite sums are termwise equal.) This is the structural sum-side
identity that every sum-check round's claimed sum rests on. -/
theorem MLE_hypercubeSum [Fintype σ] [DecidableEq σ] (f : (σ → Fin 2) → R) :
    ∑ x : σ → Fin 2, MvPolynomial.eval (x : σ → R) (MLE f) = ∑ x : σ → Fin 2, f x :=
  Finset.sum_congr rfl fun x _ => MLE_eval_zeroOne x f

omit [Fintype σ] [DecidableEq σ] in
/-- **Weighted hypercube sum of an MLE.** For an arbitrary weight `w` on the cube,
`∑_x MLE(f)(x) · w x = ∑_x f x · w x`. Same mechanism as `MLE_hypercubeSum`: on each Boolean point
`MLE f` collapses to `f`. This is the per-`Y` form consumed when the second sum-check's product
`ℳ(Y)` is summed over the cube. -/
theorem MLE_hypercubeSum_weighted [Fintype σ] [DecidableEq σ]
    (f : (σ → Fin 2) → R) (w : (σ → Fin 2) → R) :
    ∑ x : σ → Fin 2, MvPolynomial.eval (x : σ → R) (MLE f) * w x = ∑ x : σ → Fin 2, f x * w x :=
  Finset.sum_congr rfl fun x _ => by rw [MLE_eval_zeroOne x f]

open Matrix in
/-- **Random-coefficient bundled claim as a hypercube sum (per matrix).** The
random-coefficient-scaled bundled evaluation claim `c · MLE(M *ᵥ 𝕫)(r_x)` equals the `𝕫`-weighted
Boolean-cube sum of the column-MLE evaluations at `r_x`, each scaled by `c`. This is the per-matrix
"sum = target" content of the second sum-check: the bundled claim the linear-combination round emits
is a sum over the column-variable cube `j` of a per-column summand. Reduces to the scaled-sum
decomposition `mulVec_MLE_eval_eq_scaled_sum` and distributing `c`. -/
theorem rlc_evalClaim_eq_cube_sum {m n : ℕ}
    (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R) (z : Fin (2 ^ n) → R)
    (r_x : Fin m → R) (c : R) :
    c * eval r_x (MLE ((M *ᵥ z) ∘ finFunctionFinEquiv))
      = ∑ j : Fin (2 ^ n),
          z j * (c *
            eval r_x (MLE (fun xBits : Fin m → Fin 2 => M (finFunctionFinEquiv xBits) j))) := by
  rw [mulVec_MLE_eval_eq_scaled_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

open Matrix in
/-- **Second sum-check input correctness (random linear combination of bundled claims).** The
random-linear-combination over a finite index set `s` of bundled evaluation claims
`∑_{idx ∈ s} coeff idx · MLE(M_idx *ᵥ 𝕫)(r_x)` — the value the linear-combination round hands to the
second sum-check — equals the `𝕫`-weighted Boolean-cube sum over the column variable `j` of
`∑_{idx ∈ s} coeff idx · (column-MLE of M_idx)(r_x)`.

This is the honest "claimed sum = target" identity of the second sum-check: the per-`j` summand is
exactly `(MLE 𝕫)(j) ·` (the matrix linear combination at `(r_x, j)`), summed over the cube. It is the
aggregate of `rlc_evalClaim_eq_cube_sum` over the matrices, commuting the finite sums. Stated over a
generic index `Finset s` (the R1CS application instantiates `s = {A, B, C}`), so it needs no
`Fintype` instance on the matrix index type. -/
theorem secondSumcheck_target_eq_cube_sum {ι : Type*} {m n : ℕ} (s : Finset ι)
    (Mat : ι → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R) (z : Fin (2 ^ n) → R)
    (r_x : Fin m → R) (coeff : ι → R) :
    (∑ idx ∈ s, coeff idx * eval r_x (MLE ((Mat idx *ᵥ z) ∘ finFunctionFinEquiv)))
      = ∑ j : Fin (2 ^ n),
          z j * (∑ idx ∈ s,
            coeff idx *
              eval r_x (MLE (fun xBits : Fin m → Fin 2 => Mat idx (finFunctionFinEquiv xBits) j))) := by
  classical
  -- Expand each summand via the per-matrix identity, then swap the two finite sums.
  have hLHS :
      (∑ idx ∈ s,
          coeff idx * eval r_x (MLE ((Mat idx *ᵥ z) ∘ finFunctionFinEquiv)))
        = ∑ idx ∈ s, ∑ j : Fin (2 ^ n),
            z j * (coeff idx *
              eval r_x (MLE (fun xBits : Fin m → Fin 2 => Mat idx (finFunctionFinEquiv xBits) j))) :=
    Finset.sum_congr rfl fun idx _ => rlc_evalClaim_eq_cube_sum (Mat idx) z r_x (coeff idx)
  rw [hLHS, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

/-! ## 3. The final `CheckClaim` evaluation-consistency identity

The terminal `CheckClaim` checks that the value the second sum-check produced (`target`) equals the
value the verifier reconstructs from the oracles at the final point. The genuine math is that the
bundled claim value `MLE(M *ᵥ 𝕫)(r_x)` equals the `eq̃`-weighted sum over the column index that the
`SpartanBricks.zEvalFromFinalOracles` / `finalExpectedClaimFromOracles` reconstruction computes
pointwise. We give the standard MLE-evaluation-as-`eq̃`-sum form. -/

/-- **MLE evaluation as an `eq̃`-weighted hypercube sum (general-ring form).**

`eval r (MLE f) = ∑_{x ∈ cube} eq̃(r, x) · f x`. This is the identity the final-check oracle
reconstruction is computing term-by-term (`zEvalFromFinalOracles` folds `eqPolynomial`-weighted
witness/public values; `finalExpectedClaimFromOracles` multiplies by the matrix evaluation). It is
already proven in `Multilinear.lean` as `MLE_eval_eq_sum_eqTilde`; recorded here as the bridge to
the final-check semantics. -/
theorem mle_eval_eq_eqTilde_sum (f : (σ → Fin 2) → R) (r : σ → R) :
    eval r (MLE f) = ∑ x : σ → Fin 2, eqTilde r (x : σ → R) * f x :=
  MvPolynomial.MLE_eval_eq_sum_eqTilde f r

open Matrix in
/-- **Final-check consistency: the reconstructed terminal value equals the bundled claim value.**

The verifier's terminal reconstruction `∑_x eq̃(r, x) · (M *ᵥ 𝕫)(e x)` (the `eq̃`-weighted hypercube
sum over rows that `finalExpectedClaimFromOracles` accumulates) equals the bundled claim value
`MLE((M *ᵥ 𝕫) ∘ e)(r)`. Hence `target = expected` in the final `CheckClaim` is the SAME number the
second sum-check was reducing — the honest-prover terminal identity. Reduces to
`MLE_eval_eq_sum_eqTilde`. -/
theorem final_check_consistency {m n : ℕ}
    (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R) (z : Fin (2 ^ n) → R)
    (r : Fin m → R) :
    eval r (MLE ((M *ᵥ z) ∘ finFunctionFinEquiv))
      = ∑ x : Fin m → Fin 2,
          eqTilde r (x : Fin m → R) * (M *ᵥ z) (finFunctionFinEquiv x) :=
  MvPolynomial.MLE_eval_eq_sum_eqTilde ((M *ᵥ z) ∘ finFunctionFinEquiv) r

#print axioms mle_eq_zero_iff_forall_cube
#print axioms r1cs_residual_iff_mle_zero
#print axioms r1cs_hadamard_iff_mle_zero
#print axioms mle'_eq_zero_iff_forall
#print axioms r1cs_relation_iff_forall_row
#print axioms r1cs_relation_iff_forall_residual
#print axioms r1cs_relation_iff_mle'_residual_zero
#print axioms zeroCheckVirtualPolynomial_eq_mle'_r1csResidual
#print axioms r1cs_relation_iff_zeroCheckVirtualPolynomial_zero
#print axioms mulVec_MLE_eval_eq_scaled_sum
#print axioms MLE_hypercubeSum
#print axioms MLE_hypercubeSum_weighted
#print axioms rlc_evalClaim_eq_cube_sum
#print axioms secondSumcheck_target_eq_cube_sum
#print axioms mle_eval_eq_eqTilde_sum
#print axioms final_check_consistency

end Scratch114

end Spartan
