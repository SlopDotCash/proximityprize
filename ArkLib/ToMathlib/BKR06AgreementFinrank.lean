/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.BKR06Agreement

/-!
# BKR06 Lemma 3.5: the agreement count in canonical `q^v` form

`BKR06.evalOnPoints_agreement_card` (`ArkLib.ToMathlib.BKR06Agreement`) shows the evaluation
vectors of `pivot` and `pivot − s_W` agree on exactly `Fintype.card W` points.  BKR06 state this
count in the dimension form `q^v` where `q = |𝔽|` and `v = dim_𝔽 W`.  This file records that
identification:

* `evalOnPoints_agreement_card_eq_pow_finrank` — the agreement count is exactly
  `q ^ dim_𝔽 W` (`= |W|`, by `Module.card_eq_pow_finrank`).

This is the agreement count in the exact form used by BKR06 Lemma 3.5 ("agreement `= q^v`"),
completing the agreement-count bridge to the paper's statement.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`); `sorry`/`axiom`-free.
-/

open Polynomial BigOperators Finset

namespace BKR06

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [Module F K]

/-- **BKR06 Lemma 3.5 agreement count in `q^v` form.**  When `domain` is surjective, the
evaluation vectors of `pivot` and `pivot − s_W` agree on exactly `q ^ dim_𝔽 W` points
(`q = |𝔽|`, `v = dim_𝔽 W`) — the canonical form of BKR06's "agreement `= q^v`". -/
theorem evalOnPoints_agreement_card_eq_pow_finrank
    (domain : K ↪ K) (hsurj : Function.Surjective domain)
    (pivot : K[X]) (W : Submodule F K) [Fintype W] :
    (Finset.univ.filter (fun x =>
        (ReedSolomon.evalOnPoints domain pivot) x
          = (ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W))) x)).card
      = Fintype.card F ^ Module.finrank F W := by
  rw [evalOnPoints_agreement_card domain hsurj pivot W]
  exact Module.card_eq_pow_finrank (K := F) (V := W)

end BKR06
