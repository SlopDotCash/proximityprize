/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MeanDegreeCauchySchwarz

/-!
# The mean-degree law is FALSE below Johnson at `q = Θ(n)` (#389, countermodel)

The issue-thread conjecture (`MeanDegreeLaw`): every word's capped large-agreement
family satisfies `Σ_c a_c ≤ 2n`.  Above Johnson it is a theorem
(`meanDegreeLaw_above_johnson`).  This file refutes it below Johnson:

> **`meanDegreeLaw_subJohnson_REFUTED`** — at `q = n = 19`, `k = 2`, `t = 4`,
> `cap = 6` (band `m = 1`, `t² = 16 < 38 = 2(k−1)n`, strictly sub-Johnson): an
> explicit word `w` and ten explicit lines, each agreeing with `w` on `4` or `5`
> points, with `Σ a_c = 41 > 38 = 2n`.

> **`w19_globally_capped`** — the countermodel word is GLOBALLY capped: every
> codeword of `rsCode dom19 2` (all `19²` lines) agrees with `w` on `≤ 5 ≤ cap`
> points, so the violation is not an artifact of family selection.

**Why the census missed it**: the first moment.  A *random* word over the full
domain `n = q` has `≈ q²·C(n,t)/qᵗ` lines of agreement `≥ t`, giving
`Σ a_c ≈ t·C(n,t)/q^{t−2} = Θ(n²)` at `q = Θ(n)`, fixed `t` — the quadratic
set-system optimum is realized by RANDOM words once `n³ ≳ t!·q²`.  The census
probes (`n ≤ 20`, `q = 31`) sat just below that visibility threshold.  The law is
a `q ≫ n^{(t−1)/(t−2)}` phenomenon, not a universal one; at production scaling
`q = Θ(n)` the sub-Johnson supply target must be the supply `Σ_c C(a_c, t)`
itself (which stays polynomial for random words — the open content is adversarial
*concentration*, the class-structure bound), NOT the linear mean-degree law.

**Relation to the Frobenius/subplane refutations** (`FrobeniusSubfieldBlowup.lean`,
`SubplaneSupplyFloor.lean`, same day): those realize the blowup through subfield
structure (`𝔽_p`-affine-closed domains, secants of the Frobenius graph) and conclude
the mechanism "needs a proper subfield".  This countermodel shows the MASS law needs
no structure at all: `q = 19` is PRIME, the domain is the full affine line (no proper
subfield, no additive subspace), the word is random, the band is the production shape
`(k, m) = (2, 1)`.  Counting alone kills the mass law at `q = Θ(n)`; only the SUPPLY
law (`Σ_c C(a_c,t)`, which the Frobenius word makes quadratic but a random word keeps
polynomial) is domain-coupled.

Probe: `scripts/probes/probe_mean_degree_refutation.py`.  Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

set_option maxRecDepth 40000

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

instance primeFact_MeanDegreeLawRefuted_1 : Fact (Nat.Prime 19) := ⟨by decide⟩

/-- The identity evaluation domain `Fin 19 ↪ ZMod 19`. -/
def dom19 : Fin 19 ↪ ZMod 19 :=
  ⟨fun i => (i.val : ZMod 19), by decide⟩

/-- The countermodel word (probe-found, globally `5`-capped). -/
def w19 : Fin 19 → ZMod 19 :=
  ![3, 10, 14, 10, 1, 14, 16, 13, 15, 2, 6, 16, 8, 2, 14, 8, 17, 14, 1]

/-- The line `x ↦ a·x + b` as a word on the domain. -/
def line19 (a b : ZMod 19) : Fin 19 → ZMod 19 :=
  fun i => a * (i.val : ZMod 19) + b

/-- The ten countermodel lines `(a, b)`. -/
def pairs19 : List (ZMod 19 × ZMod 19) :=
  [(15, 3), (0, 14), (2, 3), (2, 4), (3, 1), (4, 4), (5, 5), (5, 13), (11, 12), (12, 17)]

/-- The countermodel family: the ten lines as codeword-words. -/
def fam19 : Finset (Fin 19 → ZMod 19) :=
  (pairs19.map (fun p => line19 p.1 p.2)).toFinset

/-- Every line is a codeword of `rsCode dom19 2`. -/
theorem line19_mem_rsCode (a b : ZMod 19) :
    line19 a b ∈ (rsCode dom19 2 : Submodule (ZMod 19) (Fin 19 → ZMod 19)) := by
  refine ⟨a • Polynomial.X + Polynomial.C b, ?_, ?_⟩
  · refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_smul_le a Polynomial.X)
        (by rw [Polynomial.degree_X]; exact_mod_cast one_lt_two)
    · exact lt_of_le_of_lt (Polynomial.degree_C_le)
        (by exact_mod_cast (by norm_num : (0 : ℕ) < 2))
  · funext i
    simp [line19, dom19, Polynomial.eval_smul, smul_eq_mul]

/-- **THE COUNTERMODEL**: the mean-degree law fails at `q = n = 19`, `k = 2`,
`t = 4`, `cap = 6` — strictly sub-Johnson (`t² = 16 < 38 = 2(k−1)n`). -/
theorem meanDegreeLaw_subJohnson_REFUTED :
    ¬ MeanDegreeLaw (ZMod 19) dom19 2 4 6 := by
  intro h
  have hbound := h w19 fam19 ?_ ?_
  · have hgt : 2 * 19 < ∑ c ∈ fam19, (agreeSet c w19).card := by decide
    omega
  · intro c hc
    rw [fam19, List.mem_toFinset] at hc
    obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp hc
    exact line19_mem_rsCode p.1 p.2
  · have hlist : ∀ p ∈ pairs19,
        4 ≤ (agreeSet (line19 p.1 p.2) w19).card
          ∧ (agreeSet (line19 p.1 p.2) w19).card ≤ 6 := by decide
    intro c hc
    rw [fam19, List.mem_toFinset] at hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact hlist p hp

/-- **Global cap**: every codeword of `rsCode dom19 2` agrees with `w19` on `≤ 5`
points — the countermodel word is not a concentration artifact; the violation
happens under the strictest admissible cap. -/
theorem w19_globally_capped :
    ∀ c ∈ (rsCode dom19 2 : Submodule (ZMod 19) (Fin 19 → ZMod 19)),
      (agreeSet c w19).card ≤ 5 := by
  have hline : ∀ a b : ZMod 19, (agreeSet (line19 a b) w19).card ≤ 5 := by decide
  rintro c ⟨P, hPdeg, rfl⟩
  have hP1 : P.degree ≤ 1 := by
    rcases eq_or_ne P 0 with rfl | hP0
    · simp
    · have hlt : P.natDegree ≤ 1 :=
        Nat.lt_succ_iff.mp ((Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg)
      have := Polynomial.natDegree_le_iff_degree_le (p := P) (n := 1) |>.mp hlt
      simpa using this
  have hrepr := Polynomial.eq_X_add_C_of_degree_le_one hP1
  have heq : (fun i => P.eval (dom19 i)) = line19 (P.coeff 1) (P.coeff 0) := by
    funext i
    rw [hrepr]
    simp [line19, dom19]
  rw [heq]
  exact hline _ _

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.meanDegreeLaw_subJohnson_REFUTED
#print axioms ProximityGap.PairRank.w19_globally_capped
