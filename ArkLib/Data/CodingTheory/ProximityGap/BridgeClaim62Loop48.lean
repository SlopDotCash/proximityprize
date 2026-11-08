/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListDecEquivLoop47
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Loop 48 (BRIDGE) — BCHKS Claim 6.2, the rational-function bridge, formalized over polynomials.

Loop47 (`CandidateListDecEquivLoop47.lean`) reduced the #232 prize's forward direction
("list-decoding failure ⟹ prize false") to a single opaque arithmetic hypothesis
`hMany_bridge : q ≤ 2·D·bad`, attributed to **BCHKS Claim 6.2** — the *rational-function bridge*

  `f(x) = c(x)/(x − α)`,  `g(x) = −1/(x − α)`,  so  `f(x) + z·g(x) = (c(x) − z)/(x − α)`.

The algebraic heart of Claim 6.2 is the elementary fact that **at `z = c(α)` the quotient
`(c − c(α))/(X − α)` is a polynomial** of lower degree, because `(X − α) ∣ (c − c(α))`; its
evaluation is a codeword of the degree-`(deg − 1)` RS code.  It agrees with the rational line
point `f(x) + z·g(x)` only at points `x ≠ α` (`bridge_eval_eq_div_of_ne`); at the node itself
the two differ in general (`bridge_eval_ne_div_at_node`), so the rational-line reading needs the
punctured domain (`bridge_evalOnPoints_eq_div_of_ne`).  This file proves, sorry-free and
axiom-clean:

* `bridge_isCodeword` / `bridge_quotient_natDegree_lt` / `bridge_eval_mem_code` — the algebraic
  core (the quotient exists, has degree `< deg c`, and evaluates to a lower-degree RS codeword);
* `bridge_evalOnPoints_eq_div_of_ne` — the punctured-domain identification with the rational
  line point;
* `card_values_le_badScalars` — the counting step: if every realized value `c.eval α` lies in a
  set `badSet`, then `B := #values ≤ #badSet` (the value map is the identity, hence injective).

**What is not proved.**  The hypothesis `hLineMeetsCode` of `realized_values_are_bad` /
`bad_ge_distinct_values` is equivalent to the membership obligation `∀ c ∈ S, c(α) ∈ badSet`
itself (`lineMeetsCode_iff`), because the quotient always exists.  No fixed received word or
line, no closeness transfer, and no MCA no-joint-agreement property is established; the
statement that these realized values are actually bad scalars for one fixed far line (the
geometric bridge of Claim 6.2) remains an explicit external assumption, as does the
many-values input.  See `Research/ProximityPrize/DISPROOF_LOG.md` (Loop48).
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.BridgeClaim62Loop48

variable {F : Type*} [Field F]

/-! ## Part A — the algebraic core of Claim 6.2 (the bridge function is a codeword at `z = c(α)`) -/

/-- **Claim 6.2, algebraic core.** For a polynomial `c` and a domain point `α`, the bridge value
`z = c.eval α` makes `c − z` divisible by `X − α`: there is a polynomial `quot` with
`c − C z = (X − C α) · quot`.  At every `x ≠ α`, `quot(x) = (c(x) − z)/(x − α) = f(x) + z·g(x)` is
the rational line point (`bridge_eval_eq_div_of_ne`); at `x = α` it is not in general
(`bridge_eval_ne_div_at_node`). -/
theorem bridge_isCodeword (c : F[X]) (α : F) :
    ∃ quot : F[X], c - C (c.eval α) = (X - C α) * quot := by
  obtain ⟨quot, hquot⟩ := X_sub_C_dvd_sub_C_eval (a := α) (p := c)
  exact ⟨quot, hquot⟩

/-- **The bridge drops the degree by exactly one.** If `c` is non-constant (`1 ≤ deg c`) then the
bridge quotient `(c − c(α))/(X − α)` has degree `deg c − 1 < deg c`: dividing a degree-`d` codeword by
`X − α` lands in the degree-`(d−1)` code. This is why Claim 6.2's bridge maps the RS code of degree
`< k` into the once-punctured code of degree `< k − 1`. -/
theorem bridge_quotient_natDegree_lt (c : F[X]) (α : F) (hc : 1 ≤ c.natDegree)
    {quot : F[X]} (hquot : c - C (c.eval α) = (X - C α) * quot) :
    quot.natDegree < c.natDegree := by
  -- `c − C z` is non-zero (else `c` would be the constant `C z`, contradicting `1 ≤ deg c`)
  have hne : c - C (c.eval α) ≠ 0 := by
    intro h
    have : c = C (c.eval α) := sub_eq_zero.mp h
    rw [this, natDegree_C] at hc
    exact absurd hc (by norm_num)
  -- and its degree is exactly `deg c`, since subtracting a constant does not touch the leading term
  have hdeg : (c - C (c.eval α)).natDegree = c.natDegree := natDegree_sub_C
  -- factor the degree across the product `(X − α) · quot`
  have hXne : (X - C α : F[X]) ≠ 0 := X_sub_C_ne_zero α
  have hquotne : quot ≠ 0 := by
    rintro rfl; rw [mul_zero] at hquot; exact hne hquot
  have hmul : (c - C (c.eval α)).natDegree = (X - C α : F[X]).natDegree + quot.natDegree := by
    rw [hquot, natDegree_mul hXne hquotne]
  rw [hdeg, natDegree_X_sub_C] at hmul
  omega

/-! ## Part B — counting: many values ⟹ many bad scalars (the proven injectivity step) -/

/-- **Injectivity / counting step of Claim 6.2.** Suppose every value `c.eval α` realized by a
codeword `c` in a finite family `S` lands in `badSet`. Then the number of *distinct realized
values* is a lower bound on `#badSet`: `B := #(S.image (·.eval α)) ≤ #badSet`, since the
value-to-scalar map is the identity on values.  The membership hypothesis is assumed, not
derived: showing each such `z` is a bad scalar for a fixed far line is the geometric part of
Claim 6.2 and is not proved in this file. -/
theorem card_values_le_badScalars [DecidableEq F] (α : F) (S : Finset F[X]) (badSet : Finset F)
    (hbad : ∀ c ∈ S, c.eval α ∈ badSet) :
    (S.image (fun c => c.eval α)).card ≤ badSet.card := by
  apply Finset.card_le_card
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨c, hcS, rfl⟩
  exact hbad c hcS

/-- **Unpacking `hLineMeetsCode`.**  If `badSet` contains `c.eval α` whenever a bridge quotient
exists for `c ∈ S`, then (since the quotient always exists, Part A) every realized value is in
`badSet`.  This is a restatement, not a derivation of badness: `hLineMeetsCode` is equivalent to
the conclusion (`lineMeetsCode_iff`), and `badSet` is an arbitrary finset here, not tied to any
received line. -/
theorem realized_values_are_bad (α : F) (S : Finset F[X]) (badSet : Finset F)
    (hLineMeetsCode : ∀ c ∈ S, ∀ quot : F[X],
        c - C (c.eval α) = (X - C α) * quot → c.eval α ∈ badSet) :
    ∀ c ∈ S, c.eval α ∈ badSet := by
  intro c hc
  obtain ⟨quot, hquot⟩ := bridge_isCodeword c α
  exact hLineMeetsCode c hc quot hquot

/-! ## Part C — assembly: discharge the Loop47 black box from the bridge + many-values -/

/-- **`#badSet ≥ B` from the membership hypothesis.** If `badSet` contains every realized value
`c.eval α` (`hLineMeetsCode`, equivalent to that membership by `lineMeetsCode_iff`), the number
of distinct codeword values at `α` is at most `#badSet`.  This is only the image-cardinality
count; the geometric input that these values are bad scalars of one fixed far line (with the
closeness and no-joint-agreement properties) is not proved and remains external. -/
theorem bad_ge_distinct_values [DecidableEq F] (α : F) (S : Finset F[X]) (badSet : Finset F)
    (hLineMeetsCode : ∀ c ∈ S, ∀ quot : F[X],
        c - C (c.eval α) = (X - C α) * quot → c.eval α ∈ badSet) :
    (S.image (fun c => c.eval α)).card ≤ badSet.card :=
  card_values_le_badScalars α S badSet (realized_values_are_bad α S badSet hLineMeetsCode)

/-- **Many-values arithmetic: the ball bound `L·q ≤ B·(q + L·A)` yields `q ≤ 2·D·B`.**
This is the nat inequality the BCHKS §6 reduction runs on, with the point set taken to be the field
of combining scalars (`|ι| = q`), `A = k − 1` the pairwise agreement, `L > q` the (list-decoding-
failure) number of codewords in the ball, and `D = 2^m ≥ k − 1` the domain size. From the
`manyValues_of_pairwise_agree` output `L·q ≤ B·(q + L·A)` we extract `q ≤ 2·D·B`: since `q < L` and
`A + 1 ≤ 2D`, we have `q + L·A < 2·D·L`, so `L·q ≤ B·(q+L·A) ≤ 2·D·B·L` and cancelling `L` finishes. -/
theorem manyValues_arith {q D B L A : ℕ}
    (hLq : L * q ≤ B * (q + L * A))   -- `manyValues_of_pairwise_agree` at `|ι| = q`
    (hqL : q < L)                     -- list-decoding failure: the ball holds `> q` codewords
    (hAD : A + 1 ≤ 2 * D) :           -- `A = k − 1 < n ≤ D`, hence `A + 1 ≤ 2D`
    q ≤ 2 * D * B := by
  have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le _) hqL
  -- `q + L·A < 2·D·L`, since `(A+1)·L ≤ 2D·L` and `q < L`
  have hbig : q + L * A ≤ 2 * D * L := by nlinarith [Nat.mul_le_mul_right L hAD, hqL]
  -- chain `L·q ≤ B·(q+LA) ≤ B·(2DL) = (2DB)·L`, then cancel `L`
  have hchain : q * L ≤ (2 * D * B) * L := by
    calc q * L = L * q := by ring
      _ ≤ B * (q + L * A) := hLq
      _ ≤ B * (2 * D * L) := by gcongr
      _ = (2 * D * B) * L := by ring
  exact Nat.le_of_mul_le_mul_right hchain hL

/-- **Loop47's `prize_false_of_listDecoding_failure`, re-derived with the bridge proven.**
We keep only the two genuinely-external inputs:
* `hManyValues : q ≤ 2·D·B` — the many-values output (from `manyValues_of_pairwise_agree`, a counting
  fact about the ball of `> q` codewords), and
* `hbridge : B ≤ bad` — an explicit hypothesis.  `bad_ge_distinct_values` supplies it only
  under its own membership assumption (every realized value lies in the bad set), which is the
  unproved geometric part of Claim 6.2.
together with the prize bound `bad ≤ D^c₁` and a large field `2·D^{c₁+1} < q`. The contradiction
follows by arithmetic.  The opaque `hMany_bridge` of Loop47 is thereby split into these two
named inputs; neither is proved here. -/
theorem prize_false_of_listDecoding_failure_bridged
    {q D B bad c₁ : ℕ}
    (hManyValues : q ≤ 2 * D * B) -- many-values: ball of > q codewords ⟹ ≥ B distinct values
    (hbridge : B ≤ bad) -- Claim 6.2 geometric bridge: distinct values ↪ bad scalars (assumed)
    (hprize : bad ≤ D ^ c₁)
    (hq : 2 * D ^ (c₁ + 1) < q) :
    False := by
  have hMany_bridge : q ≤ 2 * D * bad :=
    le_trans hManyValues (by gcongr)
  exact ArkLib.ProximityGap.ListDecEquivLoop47.prize_false_of_listDecoding_failure
    hMany_bridge hprize hq

/-- **Full assembly (Loop48): list-decoding failure ⟹ prize false, conditional on the bridge.**
Chaining `manyValues_arith` (arithmetic on the in-tree `manyValues_of_pairwise_agree` output),
the assumed `bad ≥ B` (the geometric Claim 6.2 bridge, not proved here), the prize bound, and a
large field, the arithmetic yields `False`.  The inputs remain explicit hypotheses: the ball
holds `> q` codewords pairwise agreeing on `≤ A` points (list-decoding failure at the prize
radius), the realized values are bad scalars of one fixed far line (`hbridge`), and the field is
large relative to the fixed domain. -/
theorem prize_false_of_listDecoding_failure_full
    {q D B bad L A c₁ : ℕ}
    (hLq : L * q ≤ B * (q + L * A)) -- many-values output (combinatorial)
    (hqL : q < L) -- list-decoding failure
    (hAD : A + 1 ≤ 2 * D) -- `A = k − 1 ≤ 2D − 1`
    (hbridge : B ≤ bad) -- Claim 6.2 geometric bridge: distinct values ↪ bad scalars (assumed)
    (hprize : bad ≤ D ^ c₁) -- prize's `q`-independent bound
    (hq : 2 * D ^ (c₁ + 1) < q) : -- large field
    False :=
  prize_false_of_listDecoding_failure_bridged (manyValues_arith hLq hqL hAD) hbridge hprize hq

/-! ## Part D — grounding the bridge in the *formalized* Reed–Solomon code

The algebraic core above is about raw polynomials. Here we connect it to the repository's actual RS
code `ReedSolomon.code domain deg = (degreeLT F deg).map (evalOnPoints domain)`, confirming the bridge
maps the degree-`deg` code into the degree-`(deg−1)` ("once-punctured") code — exactly Claim 6.2's
"the line point is a codeword of the shifted code". -/

/-- **The bridge quotient drops a degree class: `degreeLT deg → degreeLT (deg−1)`.**
If `c` has degree `< deg` then the bridge quotient `(c − c(α))/(X − α)` has degree `< deg − 1`. -/
theorem bridge_mem_degreeLT (c : F[X]) (α : F) {deg : ℕ}
    (hc : c ∈ Polynomial.degreeLT F deg)
    {quot : F[X]} (hbridge : c - C (c.eval α) = (X - C α) * quot) :
    quot ∈ Polynomial.degreeLT F (deg - 1) := by
  rw [Polynomial.mem_degreeLT] at hc ⊢
  by_cases hq0 : quot = 0
  · simp only [hq0, Polynomial.degree_zero]; exact bot_lt_iff_ne_bot.mpr (by simp)
  rcases Nat.eq_zero_or_pos c.natDegree with hcd | hcd
  · -- `c` is a constant: `c − C (c.eval α) = 0`, forcing `quot = 0`, contradiction
    exfalso
    have hCeq : c = C (c.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hcd
    have hzero : c - C (c.eval α) = 0 := by
      rw [hCeq]; simp [Polynomial.eval_C]
    rw [hzero] at hbridge
    have := (mul_eq_zero.mp hbridge.symm).resolve_left (X_sub_C_ne_zero α)
    exact hq0 this
  · -- non-constant case: `natDegree quot < natDegree c ≤ deg − 1`
    have hlt := bridge_quotient_natDegree_lt c α hcd hbridge
    have hcne : c ≠ 0 := fun h => by simp [h] at hcd
    have hcdeg : c.natDegree < deg := by
      have := hc; rw [Polynomial.degree_eq_natDegree hcne, Nat.cast_lt] at this; exact this
    rw [Polynomial.degree_eq_natDegree hq0, Nat.cast_lt]
    omega

/-- **Claim 6.2 over the formalized RS code: the bridge maps `code domain deg` into
`code domain (deg − 1)`.** For a codeword polynomial `c` of degree `< deg` and any `α`, the
evaluation of the bridge quotient is a codeword of the degree-`(deg − 1)` RS code on the same
domain.  This is a statement about the quotient polynomial only.  It is identified with the
rational line point `f + z·g` at `z = c(α)` only on domain points `≠ α`
(`bridge_evalOnPoints_eq_div_of_ne`); this theorem allows domains containing `α`, where the
identification fails (`bridge_eval_ne_div_at_node`). -/
theorem bridge_eval_mem_code {ι : Type*} (domain : ι ↪ F) (c : F[X]) (α : F) {deg : ℕ}
    (hc : c ∈ Polynomial.degreeLT F deg)
    {quot : F[X]} (hbridge : c - C (c.eval α) = (X - C α) * quot) :
    ReedSolomon.evalOnPoints domain quot ∈ ReedSolomon.code domain (deg - 1) :=
  Submodule.mem_map_of_mem (bridge_mem_degreeLT c α hc hbridge)

/-! ## Part E — the rational-line interpretation holds only off the node `α`

The quotient polynomial agrees with the rational expression `(c(x) − c(α))/(x − α)` exactly at
points `x ≠ α`.  At `x = α` the field expression is `0/0 = 0` in Lean, while the quotient takes
the value `c'(α)` in general, so the identification needs a punctured evaluation domain. -/

/-- **Off the node, the bridge quotient is the rational line point.**  For `x ≠ α`,
`quot(x) = (c(x) − c(α))/(x − α)`. -/
theorem bridge_eval_eq_div_of_ne (c : F[X]) (α : F) {quot : F[X]}
    (hquot : c - C (c.eval α) = (X - C α) * quot) {x : F} (hx : x ≠ α) :
    quot.eval x = (c.eval x - c.eval α) / (x - α) := by
  have h := congrArg (Polynomial.eval x) hquot
  simp only [eval_sub, eval_C, eval_mul, eval_X] at h
  rw [eq_div_iff (sub_ne_zero.mpr hx), h, mul_comm]

/-- **Punctured-domain bridge.**  On every domain point other than the node `α`, the RS
evaluation of the bridge quotient equals the rational line point
`(c(x) − c(α))/(x − α)`.  Together with `bridge_eval_mem_code` this is the precise statement
"the rational line meets the shifted code at `z = c(α)`" on the punctured domain. -/
theorem bridge_evalOnPoints_eq_div_of_ne {ι : Type*} (domain : ι ↪ F) (c : F[X]) (α : F)
    {quot : F[X]} (hquot : c - C (c.eval α) = (X - C α) * quot) {i : ι}
    (hi : domain i ≠ α) :
    ReedSolomon.evalOnPoints domain quot i
      = (c.eval (domain i) - c.eval α) / (domain i - α) :=
  bridge_eval_eq_div_of_ne c α hquot hi

/-- **The node must be excluded.**  For `c = X` and `α = 0` the bridge quotient is `1`, which
evaluates to `1` at the node, while the field expression `(c(0) − c(0))/(0 − 0)` is `0`.  So
`bridge_eval_mem_code`, which accepts domains containing `α`, does not by itself give a
rational-line equality there. -/
theorem bridge_eval_ne_div_at_node :
    ∃ (c quot : F[X]) (α : F), c - C (c.eval α) = (X - C α) * quot ∧
      quot.eval α ≠ (c.eval α - c.eval α) / (α - α) :=
  ⟨X, 1, 0, by simp, by simp⟩

/-- **The `hLineMeetsCode` hypothesis is the membership obligation itself.**  Since the
bridge quotient always exists (`bridge_isCodeword`), the hypothesis of
`realized_values_are_bad` / `bad_ge_distinct_values` is equivalent to "every realized value
`c(α)`, `c ∈ S`, lies in `badSet`".  So those theorems do not derive badness from algebra:
the geometric input (that these scalars are bad for a fixed received line, with the needed
closeness and no-joint-agreement properties) remains an explicit assumption. -/
theorem lineMeetsCode_iff (α : F) (S : Finset F[X]) (badSet : Finset F) :
    (∀ c ∈ S, ∀ quot : F[X], c - C (c.eval α) = (X - C α) * quot → c.eval α ∈ badSet) ↔
      ∀ c ∈ S, c.eval α ∈ badSet :=
  ⟨realized_values_are_bad α S badSet, fun h c hc _ _ => h c hc⟩

end ArkLib.ProximityGap.BridgeClaim62Loop48

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeClaim62Loop48.bridge_isCodeword
#print axioms ArkLib.ProximityGap.BridgeClaim62Loop48.bridge_quotient_natDegree_lt
#print axioms ArkLib.ProximityGap.BridgeClaim62Loop48.card_values_le_badScalars
#print axioms ArkLib.ProximityGap.BridgeClaim62Loop48.bad_ge_distinct_values
#print axioms ArkLib.ProximityGap.BridgeClaim62Loop48.manyValues_arith
#print axioms ArkLib.ProximityGap.BridgeClaim62Loop48.prize_false_of_listDecoding_failure_bridged
#print axioms ArkLib.ProximityGap.BridgeClaim62Loop48.prize_false_of_listDecoding_failure_full
#print axioms ArkLib.ProximityGap.BridgeClaim62Loop48.bridge_mem_degreeLT
#print axioms ArkLib.ProximityGap.BridgeClaim62Loop48.bridge_eval_mem_code
#print axioms ArkLib.ProximityGap.BridgeClaim62Loop48.bridge_eval_eq_div_of_ne
#print axioms ArkLib.ProximityGap.BridgeClaim62Loop48.bridge_evalOnPoints_eq_div_of_ne
#print axioms ArkLib.ProximityGap.BridgeClaim62Loop48.bridge_eval_ne_div_at_node
#print axioms ArkLib.ProximityGap.BridgeClaim62Loop48.lineMeetsCode_iff
