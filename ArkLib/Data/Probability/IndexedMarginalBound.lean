/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Probability.MarginalBound

/-!
# Prefix-indexed uniform-marginal domination (issue #13, the `hOuter` measure capstone)

`probEvent_bind_le_uniform_marginal_indexed` generalizes the fixed-set
`probEvent_bind_le_uniform_marginal` to a **prefix-indexed** bad set with a uniform cardinality
bound: in a two-stage game `m₀ >>= fun c => mx c >>= k c` where the second stage's draw is
uniformly dominated and, for each prefix `c`, the event is supported inside a bad set `L c` of
size at most `d`, the whole game's event probability is at most `d / |F|`.

This is exactly the shape of the adversarial-multiplicity outer Schwartz–Zippel step of LogUp
(issue #13): the prover's round-`0` multiplicity message (the prefix `c`) determines an
`m`-dependent root set `L c` of the cleared grand-sum numerator, with the *uniform* degree bound
`d = (M+1)·2ⁿ − 1`; the round-`1` challenge draw is uniform; and acceptance at a challenge outside
`L c` is impossible. The fixed-set capstone does not apply (the root set genuinely varies with the
prover's message); this indexed form is its plain composition with the support-quantified bind
domination.

No `sorry`; axiom audit at the bottom.
-/

universe u v

open OracleComp
open scoped ENNReal NNReal

section IndexedMarginal

variable {γ β : Type} {m : Type → Type v} [Monad m] [HasEvalSPMF m]

/-- **Prefix-indexed uniform-marginal domination.** If, after a first stage `m₀`, the game draws
from a uniformly-dominated distribution and the event is supported inside a prefix-dependent bad
set `L c` of size at most `d`, then the event probability is at most `d / |F|`. -/
lemma probEvent_bind_le_uniform_marginal_indexed {F : Type} [Fintype F]
    (m₀ : m γ) (mx : γ → m F) (k : γ → F → m β) (q : β → Prop)
    (L : γ → Set F) [∀ c, DecidablePred (· ∈ L c)] (d : ℕ)
    (hunif : ∀ c, ∀ x : F, Pr[= x | mx c] ≤ (Fintype.card F : ℝ≥0∞)⁻¹)
    (hcard : ∀ c, ((Finset.univ.filter (· ∈ L c)).card) ≤ d)
    (hsupp : ∀ c, ∀ x : F, x ∉ L c → Pr[ q | k c x] = 0) :
    Pr[ q | m₀ >>= fun c => mx c >>= k c] ≤ (d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine probEvent_bind_le_of_forall_support m₀ _ q _ (fun c _ => ?_)
  refine le_trans
    (probEvent_bind_le_uniform_marginal (mx c) (k c) q (L c) (hunif c) (hsupp c)) ?_
  apply ENNReal.div_le_div_right
  exact_mod_cast hcard c

end IndexedMarginal

/- Axiom audit. -/
#print axioms probEvent_bind_le_uniform_marginal_indexed
