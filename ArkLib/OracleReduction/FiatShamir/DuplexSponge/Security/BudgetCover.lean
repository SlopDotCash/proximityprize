/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaFoundations

/-!
# Budget recombination for predicate-targeted query bounds (CO25 Lemma 5.8, step 3)

The third documented step of `Lemma5_8EagerBirthdayFalseStatement` (BirthdayBound.lean) is the
*budget split*: the per-flavor budgets `(tₕ, tₚ, tₚᵢ)` of the Key-Lemma surface must be
recombined into a single total trace-length bound (`IsTotalQueryBound`), since CO25
Lemma 5.8 is applied at the total trace length `T`. VCVio provides
`IsTotalQueryBound.of_perIndex` (per-index budgets, `Fintype ι` required) but no
recombination for the *predicate-targeted* bounds `IsQueryBoundP` that the DSFS budgets
use. This file fills that gap, with no finiteness assumptions:

* `OracleComp.IsQueryBoundP.union` — `p`-budget `n₁` and `q`-budget `n₂` combine into an
  `(p ∨ q)`-budget `n₁ + n₂` (structural induction; the validity side conditions supply
  the positivity needed when both predicates fire on one index).
* `OracleComp.isTotalQueryBound_of_queryBoundP_univ` — a `p`-budget is a total budget
  once `p` covers every index (an `isQueryBound_congr` transport).
* `OracleComp.isTotalQueryBound_of_cover` — binary cover: two predicate budgets whose
  predicates cover the index set yield a total bound at the sum.
* `DuplexSpongeFS.dsBaseQueryFlavor` + `isTotalQueryBound_of_dsBaseFlavorBudgets` — the
  DSFS instantiation on the bare duplex-sponge challenge oracle (the oracle of the
  `Lemma5_8EagerBirthdayFalseStatement` adversary): hash/perm/permInv budgets `(tₕ, tₚ, tₚᵢ)`
  give `IsTotalQueryBound P (tₕ + tₚ + tₚᵢ)`.
* `DuplexSpongeFS.isTotalQueryBound_of_dsFlavorBudgets` — the same on the full Key-Lemma
  surface `oSpec + duplexSpongeChallengeOracle` with the shared budget included.

What this does **not** do: steps 1 (eager-carrier coupling through
`removeRedundantEntryDS`) and 2 (decomposition of `E = E_dup ∨ E_func` into
collision/landing families) of the Lemma 5.8 plan remain open.
-/

universe u

open OracleComp OracleSpec

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α : Type u}

/-- **Union of predicate-targeted budgets**: if `oa` makes at most `n₁` queries to
`p`-indices and at most `n₂` queries to `q`-indices, it makes at most `n₁ + n₂` queries
to `(p ∨ q)`-indices. -/
theorem IsQueryBoundP.union {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    {oa : OracleComp spec α} {n₁ n₂ : ℕ}
    (h1 : IsQueryBoundP oa p n₁) (h2 : IsQueryBoundP oa q n₂) :
    IsQueryBoundP oa (fun i => p i ∨ q i) (n₁ + n₂) := by
  induction oa using OracleComp.inductionOn generalizing n₁ n₂ with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h1 h2
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨?_, fun u => ?_⟩
      · by_cases hpt : p t
        · exact Or.inr (Nat.lt_of_lt_of_le (h1.1.resolve_left (not_not_intro hpt))
            (Nat.le_add_right _ _))
        · by_cases hqt : q t
          · exact Or.inr (Nat.lt_of_lt_of_le (h2.1.resolve_left (not_not_intro hqt))
              (Nat.le_add_left _ _))
          · exact Or.inl (by simp [hpt, hqt])
      · refine (ih u (h1.2 u) (h2.2 u)).mono ?_
        by_cases hpt : p t
        · have hn₁ : 0 < n₁ := h1.1.resolve_left (not_not_intro hpt)
          by_cases hqt : q t
          · simp only [if_pos hpt, if_pos hqt, if_pos (Or.inl hpt)]
            omega
          · simp only [if_pos hpt, if_neg hqt, if_pos (Or.inl hpt)]
            omega
        · by_cases hqt : q t
          · have hn₂ : 0 < n₂ := h2.1.resolve_left (not_not_intro hqt)
            simp only [if_neg hpt, if_pos hqt, if_pos (Or.inr hqt)]
            omega
          · simp only [if_neg hpt, if_neg hqt,
              if_neg (show ¬ (p t ∨ q t) by simp [hpt, hqt])]
            exact le_rfl

/-- A predicate-targeted budget whose predicate covers every index is a total budget. -/
theorem isTotalQueryBound_of_queryBoundP_univ {p : ι → Prop} [DecidablePred p]
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n) (hp : ∀ i, p i) : IsTotalQueryBound oa n := by
  unfold IsTotalQueryBound
  unfold IsQueryBoundP at h
  exact (isQueryBound_congr
    (fun t b => by simp [hp t])
    (fun t b => by simp [hp t])).mp h

/-- **Binary cover recombination**: two predicate budgets whose predicates cover the
index set give a total budget at the sum. -/
theorem isTotalQueryBound_of_cover {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    {oa : OracleComp spec α} {n₁ n₂ : ℕ}
    (h1 : IsQueryBoundP oa p n₁) (h2 : IsQueryBoundP oa q n₂)
    (hcov : ∀ i, p i ∨ q i) : IsTotalQueryBound oa (n₁ + n₂) :=
  isTotalQueryBound_of_queryBoundP_univ (h1.union h2) hcov

end OracleComp

namespace DuplexSpongeFS

open OracleComp

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-- Flavor of a single query index of the bare duplex-sponge challenge oracle
`duplexSpongeChallengeOracle StmtIn U` (the oracle of the `Lemma5_8EagerBirthdayFalseStatement`
adversary, with no shared `oSpec` component): `(h, p, p⁻¹)` of CO25 §5.4. -/
def dsBaseQueryFlavor :
    (StmtIn ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U) → DSQueryFlavor
  | .inl _ => .hash
  | .inr (.inl _) => .perm
  | .inr (.inr _) => .permInv

/-- The three bare flavors cover every query index. -/
lemma dsBaseQueryFlavor_cover
    (j : StmtIn ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U) :
    dsBaseQueryFlavor j = DSQueryFlavor.hash ∨
      (dsBaseQueryFlavor j = DSQueryFlavor.perm ∨
        dsBaseQueryFlavor j = DSQueryFlavor.permInv) := by
  rcases j with _ | _ | _ <;> simp [dsBaseQueryFlavor]

/-- **CO25 Lemma 5.8, step 3 (budget split), bare-oracle form**: per-flavor budgets
`(tₕ, tₚ, tₚᵢ)` for a duplex-sponge adversary recombine into the total query bound
`tₕ + tₚ + tₚᵢ` — the trace-length input of the Lemma 5.8 birthday bound. -/
theorem isTotalQueryBound_of_dsBaseFlavorBudgets {α : Type}
    {P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α} {tₕ tₚ tₚᵢ : ℕ}
    (hHash : IsQueryBoundP P (fun j => dsBaseQueryFlavor j = DSQueryFlavor.hash) tₕ)
    (hPerm : IsQueryBoundP P (fun j => dsBaseQueryFlavor j = DSQueryFlavor.perm) tₚ)
    (hPermInv :
      IsQueryBoundP P (fun j => dsBaseQueryFlavor j = DSQueryFlavor.permInv) tₚᵢ) :
    IsTotalQueryBound P (tₕ + (tₚ + tₚᵢ)) :=
  isTotalQueryBound_of_cover hHash (hPerm.union hPermInv) dsBaseQueryFlavor_cover

variable {ι : Type} {oSpec : OracleSpec ι}

/-- The four `dsQueryFlavor` classes cover every index of the full Key-Lemma surface. -/
lemma dsQueryFlavor_cover
    (j : ι ⊕ (StmtIn ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U)) :
    dsQueryFlavor j = DSQueryFlavor.shared ∨
      (dsQueryFlavor j = DSQueryFlavor.hash ∨
        (dsQueryFlavor j = DSQueryFlavor.perm ∨
          dsQueryFlavor j = DSQueryFlavor.permInv)) := by
  rcases j with _ | (_ | _ | _) <;> simp [dsQueryFlavor]

/-- **CO25 Lemma 5.8, step 3 (budget split), full-surface form**: the shared and
per-flavor budgets `(tₒ, tₕ, tₚ, tₚᵢ)` of the Key-Lemma adversary surface
`oSpec + duplexSpongeChallengeOracle` recombine into a total query bound. -/
theorem isTotalQueryBound_of_dsFlavorBudgets {α : Type}
    {P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α}
    {tₒ tₕ tₚ tₚᵢ : ℕ}
    (hShared : IsQueryBoundP P (fun j => dsQueryFlavor j = DSQueryFlavor.shared) tₒ)
    (hHash : IsQueryBoundP P (fun j => dsQueryFlavor j = DSQueryFlavor.hash) tₕ)
    (hPerm : IsQueryBoundP P (fun j => dsQueryFlavor j = DSQueryFlavor.perm) tₚ)
    (hPermInv : IsQueryBoundP P (fun j => dsQueryFlavor j = DSQueryFlavor.permInv) tₚᵢ) :
    IsTotalQueryBound P (tₒ + (tₕ + (tₚ + tₚᵢ))) :=
  isTotalQueryBound_of_cover hShared (hHash.union (hPerm.union hPermInv))
    dsQueryFlavor_cover

end DuplexSpongeFS

#print axioms OracleComp.IsQueryBoundP.union
#print axioms OracleComp.isTotalQueryBound_of_cover
#print axioms DuplexSpongeFS.isTotalQueryBound_of_dsBaseFlavorBudgets
#print axioms DuplexSpongeFS.isTotalQueryBound_of_dsFlavorBudgets
