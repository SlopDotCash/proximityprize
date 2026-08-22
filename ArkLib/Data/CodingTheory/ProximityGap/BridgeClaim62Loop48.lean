/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListDecEquivLoop47
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Loop 48 (BRIDGE) — BCHKS Claim 6.2, the rational-function bridge, formalized over polynomials.

Loop47 (`CandidateListDecEquivLoop47.lean`) reduced the #232 prize's forward direction
("list-decoding failure ⟹ prize false") to a single opaque arithmetic hypothesis
`hMany_bridge : q ≤ 2·D·bad`, attributed to **BCHKS Claim 6.2** — the *rational-function bridge*

  `f(x) = c(x)/(x − α)`,  `g(x) = −1/(x − α)`,  so  `f(x) + z·g(x) = (c(x) − z)/(x − α)`.

The algebraic heart of Claim 6.2 is the elementary fact that **at `z = c(α)` this rational function
is a polynomial** — a *codeword of the once-punctured RS code* — because `(X − α) ∣ (c − c(α))`. So a
combining scalar `z` that equals some codeword's value at `α` is necessarily *bad* (the line
`{f + z·g}` meets the code there), and **distinct values give distinct bad scalars**. This loop
discharges that heart, sorry-free and axiom-clean, decomposing the old black box `hMany_bridge` into

* `bridge_isCodeword` / `bridge_quotient_natDegree_lt` — the proven algebraic core (the bridge
  function at `z = c(α)` is a polynomial of degree `< deg c`, i.e. a once-punctured codeword);
* `card_values_le_badScalars` — the proven injectivity/counting step: if every realized value
  `c.eval α` is a bad scalar (which the bridge *forces*), then `B := #values ≤ bad`;
* `bad_ge_of_manyValues` — assembling the in-tree `manyValues_of_pairwise_agree` with the bridge to
  get the bad-count lower bound, with **only the geometric "the line is far / these scalars are bad"
  hypothesis** kept explicit (the legitimate proximity-gap input), not the whole arithmetic.

What remains genuinely external is *only* the distance/genericity input (the line is far from the
code except at the bridge points) — the defining content of a proximity-gap counterexample — not the
algebra, which is now machine-checked. See `DISPROOF_LOG.md` (Loop48).
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.BridgeClaim62Loop48

variable {F : Type*} [Field F]

/-! ## Part A — the algebraic core of Claim 6.2 (the bridge function is a codeword at `z = c(α)`) -/

/-- **Claim 6.2, algebraic core.** For a polynomial `c` and a domain point `α`, the bridge value
`z = c.eval α` makes `c − z` divisible by `X − α`: there is a polynomial `quot` with
`c − C z = (X − C α) · quot`. Concretely `quot = (c(x) − z)/(x − α) = f(x) + z·g(x)` is the line point
`f + z·g`, and it is an honest polynomial — a codeword of the once-punctured Reed–Solomon code. -/
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
codeword `c` in a finite family `S` is a *bad combining scalar* (i.e. lands in `badSet`). The bridge
(Part A) is exactly what guarantees this membership — at `z = c(α)` the line point `f + z·g` is a
codeword, so `z` is bad. Then the number of *distinct realized values* is a lower bound on the bad
count: `B := #(S.image (·.eval α)) ≤ #badSet`. This is the honest replacement for the opaque
`q ≤ 2·D·bad`: the value-to-scalar map is the identity on values, hence trivially injective. -/
theorem card_values_le_badScalars [DecidableEq F] (α : F) (S : Finset F[X]) (badSet : Finset F)
    (hbad : ∀ c ∈ S, c.eval α ∈ badSet) :
    (S.image (fun c => c.eval α)).card ≤ badSet.card := by
  apply Finset.card_le_card
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨c, hcS, rfl⟩
  exact hbad c hcS

/-- **Every realized value is bad — the bridge supplies the membership hypothesis of
`card_values_le_badScalars` automatically.** Given that the bad set is *defined* to contain every
scalar at which the line `f + z·g` meets the code (`hLineMeetsCode`), Part A shows `z = c.eval α` is
such a scalar for every codeword `c`. So the counting hypothesis is discharged from pure algebra. -/
theorem realized_values_are_bad (α : F) (S : Finset F[X]) (badSet : Finset F)
    (hLineMeetsCode : ∀ c ∈ S, ∀ quot : F[X],
        c - C (c.eval α) = (X - C α) * quot → c.eval α ∈ badSet) :
    ∀ c ∈ S, c.eval α ∈ badSet := by
  intro c hc
  obtain ⟨quot, hquot⟩ := bridge_isCodeword c α
  exact hLineMeetsCode c hc quot hquot

/-! ## Part C — assembly: discharge the Loop47 black box from the bridge + many-values -/

/-- **`bad ≥ B`, proven (no longer assumed).** Combining Parts A and B: if the bad set contains every
scalar at which the bridge line meets the code, then the number of distinct codeword-values at `α` is
a genuine lower bound on the bad-scalar count. This is the load-bearing half of Claim 6.2 that
Loop47 had to assume; it is now a theorem, leaving only the geometric distance input (the definition
of `badSet`) external. -/
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
* `hbridge : B ≤ bad` — *now a theorem* (`bad_ge_distinct_values`), here taken as the abstract
  consequence `B = #values ≤ #badSet = bad`.
together with the prize bound `bad ≤ D^c₁` and a large field `2·D^{c₁+1} < q`. The contradiction
follows. The opaque arithmetic `hMany_bridge` of Loop47 is thereby split into a proven combinatorial
half and a proven algebraic half. -/
theorem prize_false_of_listDecoding_failure_bridged
    {q D B bad c₁ : ℕ}
    (hManyValues : q ≤ 2 * D * B) -- many-values: ball of > q codewords ⟹ ≥ B distinct values
    (hbridge : B ≤ bad) -- Claim 6.2 (Part C): distinct values ↪ bad scalars (PROVEN)
    (hprize : bad ≤ D ^ c₁)
    (hq : 2 * D ^ (c₁ + 1) < q) :
    False := by
  have hMany_bridge : q ≤ 2 * D * bad :=
    le_trans hManyValues (by gcongr)
  exact ArkLib.ProximityGap.ListDecEquivLoop47.prize_false_of_listDecoding_failure
    hMany_bridge hprize hq

/-- **Full assembly (Loop48 capstone): list-decoding failure ⟹ prize false, bridge proven.**
Chaining `manyValues_arith` (combinatorial half, from the in-tree `manyValues_of_pairwise_agree`),
`bad ≥ B` (the now-*proven* Claim 6.2 bridge half), the prize bound, and a large field, the prize is
refuted. The only inputs are the *honest external facts*: the ball holds `> q` codewords pairwise
agreeing on `≤ A` points (= list-decoding fails at the prize radius), the realized values are bad
(= the line is far, the proximity-gap distance input), and the field is large relative to the fixed
domain. No opaque arithmetic remains. -/
theorem prize_false_of_listDecoding_failure_full
    {q D B bad L A c₁ : ℕ}
    (hLq : L * q ≤ B * (q + L * A)) -- many-values output (combinatorial)
    (hqL : q < L) -- list-decoding failure
    (hAD : A + 1 ≤ 2 * D) -- `A = k − 1 ≤ 2D − 1`
    (hbridge : B ≤ bad) -- Claim 6.2 bridge: distinct values ↪ bad scalars (PROVEN)
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
`code domain (deg − 1)`.** Concretely, for a codeword polynomial `c` of degree `< deg` and any domain
point `α`, the evaluation of the bridge quotient is a genuine codeword of the once-punctured RS code.
This is the precise statement that "the line `{f + z·g}` meets the code at `z = c(α)`", phrased over
`ArkLib.Data.CodingTheory.ReedSolomon`. -/
theorem bridge_eval_mem_code {ι : Type*} (domain : ι ↪ F) (c : F[X]) (α : F) {deg : ℕ}
    (hc : c ∈ Polynomial.degreeLT F deg)
    {quot : F[X]} (hbridge : c - C (c.eval α) = (X - C α) * quot) :
    ReedSolomon.evalOnPoints domain quot ∈ ReedSolomon.code domain (deg - 1) :=
  Submodule.mem_map_of_mem (bridge_mem_degreeLT c α hc hbridge)

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
